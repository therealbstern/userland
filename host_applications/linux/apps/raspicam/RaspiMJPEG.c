/*
Copyright (c) 2013, Broadcom Europe Ltd
Copyright (c) 2013, Silvan Melchior
Copyright (c) 2013, James Hughes
Copyright (c) 2014, Ralf Schmidt
Copyright (c) 2017, Ben Stern
All rights reserved.

Redistribution and use in source and binary forms, with or without modification,
are permitted provided that the following conditions are met:
* Redistributions of source code must retain the above copyright notice, this
  list of conditions and the following disclaimer.
* Redistributions in binary form must reproduce the above copyright notice, this
  list of conditions and the following disclaimer in the documentation and/or
  other materials provided with the distribution.
* Neither the name of the copyright holder nor the names of its contributors may
  be used to endorse or promote products derived from this software without
  specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR
ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*/

/**
 * \file RaspiMJPEG.c
 * Command line program to capture a camera video stream and encode it to file.
 * Also optionally stream a preview of current camera input wth MJPEG.
 *
 * \date 25th Nov 2013
 * \Author: Silvan Melchior
 *
 * Description
 *
 * RaspiMJPEG is an OpenMAX-Application based on the mmal-library, which is
 * comparable to and inspired by RaspiVid and RaspiStill. RaspiMJPEG can record
 * 1080p 30fps videos and 5 Mpx images into a file. But instead of showing the
 * preview on a screen, RaspiMJPEG streams the preview as MJPEG into a file.
 * The update-rate and the size of the preview are customizable with parameters
 * and independent of the image/video. Once started, the application receives
 * commands with a unix-pipe and showes its status on stdout and writes it into
 * a status-file. The program terminates itself after receiving a SIGINT or
 * SIGTERM.
 *
 * Usage information in README_RaspiMJPEG.md
 *
 *
 * General connection overview:
 *
 *                       OUT -->  IN       OUT --> IN             ATTACHED
 *   --------------------------------------------------------------------------------------------
 *   camera port 0 / preview --> image resizer --> JPEG encoder 1 <-- callback 1 to save JPEG
 *   camera port 1 / video                     --> H264 encoder   <-- callback to save video file
 *   camera port 2 / stills                    --> JPEG encoder 2 <-- callback 2 to save JPEG
 */

#define VERSION "4.2.3"

// We use some GNU extensions (asprintf)
#define _GNU_SOURCE

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <memory.h>
#include <semaphore.h>
#include <signal.h>
#include <fcntl.h>
#include <time.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <sys/statvfs.h>
#include <errno.h>

#include "bcm_host.h"
#include "interface/vcos/vcos.h"
#include "interface/mmal/mmal.h"
#include "interface/mmal/mmal_logging.h"
#include "interface/mmal/mmal_buffer.h"
#include "interface/mmal/util/mmal_util.h"
#include "interface/mmal/util/mmal_util_params.h"
#include "interface/mmal/util/mmal_default_components.h"
#include "interface/mmal/util/mmal_connection.h"

// Standard port setting for the camera component
#define PREVIEW_PORT 0
#define VIDEO_PORT 1
#define CAPTURE_PORT 2

// default settings
#define MJPG_DEF_CFG_FILE  "/etc/raspimjpeg"

// helper macros
#define DIM(x)  (sizeof(x) / sizeof(x[0]))
#define TESTERR(cond, s) { if (cond) { error(s, __function__, __LINE__); } }
#define MMAL_STATUS(s) { if (status != MMAL_SUCCESS) { error(s, __FUNCTION__, __LINE__); } }
#define S(x) #x
#define SS(x) S(x)
 
struct cam_settings {
    unsigned int sharpness;
    unsigned int contrast;
    unsigned int brightness;
    unsigned int saturation;
    unsigned int iso;
    unsigned int vs;
    unsigned int ec;
    unsigned int rotation;
    unsigned int quality;
    unsigned int raw;
    unsigned int ce_en;
    unsigned int ce_u;
    unsigned int ce_v;
    unsigned int hflip;
    unsigned int vflip;
    unsigned int annback;
    char em[20];
    char wb[20];
    char ie[20];
    char mm[20];
    unsigned long int bitrate;
    unsigned long int roi_x;
    unsigned long int roi_y;
    unsigned long int roi_w;
    unsigned long int roi_h;
    unsigned long int ss;
    char *annotation;
} cset = {
    0, 0, 50, 0, 0, 0, 0, 0, 85, 0, 0, 128, 128, 0, 0, 0, "auto", "auto",
    "none", "average", 17000000, 0, 0, 65536, 65536, 0, NULL,
};

MMAL_STATUS_T status;
MMAL_COMPONENT_T *camera = NULL, *jpegencoder = NULL,
    *jpegencoder2 = NULL, *h264encoder = NULL, *resizer = NULL;
MMAL_CONNECTION_T *con_cam_res, *con_res_jpeg, *con_cam_h264, *con_cam_jpeg;
MMAL_POOL_T *pool_jpegencoder, *pool_jpegencoder2, *pool_h264encoder;
FILE *jpegoutput_file = NULL, *jpegoutput2_file = NULL,
    *h264output_file = NULL, *status_file = NULL;
unsigned int tl_cnt = 0, mjpeg_cnt = 0, width = 320, divider = 5, image_cnt = 0,
    image2_cnt = 0, video_cnt = 0;
unsigned int video_width = 1920, video_height = 1080, video_fps = 25,
    MP4Box_fps = 25, image_width = 2592, image_height = 1944;
char *jpeg_filename = NULL, *jpeg2_filename = NULL, *h264_filename = NULL,
    *pipe_filename = NULL, *status_filename = NULL, *space_limit = NULL,
    jpeg2_root = 0;
unsigned char timelapse = 0, mp4box = 0, autostart = 1, quality = 85,
    idle = 0, capturing = 0, motion_detection = 0;
int time_between_pic;
time_t currTime;
struct tm *localTime;
volatile int running = 1;

/* Struct used to pass information in encoder port userdata to callback */
typedef struct port_userdata {
    FILE *file_handle;          // File handle to write buffer data to.
    VCOS_SEMAPHORE_T complete_semaphore;        // semaphore which is posted when we reach end of frame (indicates end of capture or fault)
} PORT_USERDATA;

PORT_USERDATA callback_data;

void cam_set_annotation();
void stop_all(void);

void error(const char *string, const char *where, int line) {
    fprintf(stderr, "Error in %s: %d: %s (%s)\n",
        where, line, string, strerror(errno));
    if (status_filename != 0) {
        status_file = fopen(status_filename, "w");
        if (status_file != NULL) {
            fprintf(status_file, "Error in %s: %d: %s", where, line, string);
            fclose(status_file);
        }
    }
    stop_all();
    exit(1);
}

void term(int signum) {
    running = 0;
}

static void camera_control_callback(MMAL_PORT_T *port,
    MMAL_BUFFER_HEADER_T *buffer) {
    TESTERR(buffer->cmd != MMAL_EVENT_PARAMETER_CHANGED,
        "Camera sent invalid data");
    mmal_buffer_header_release(buffer);
}

static void jpegencoder_buffer_callback(MMAL_PORT_T *port,
    MMAL_BUFFER_HEADER_T *buffer) {
    int bytes_written = buffer->length;
    char *filename_temp, *filename_temp2;

    if (mjpeg_cnt == 0) {
        if (!jpegoutput_file) {
            asprintf(&filename_temp, jpeg_filename, image_cnt);
            asprintf(&filename_temp2, "%s.part", filename_temp);
            jpegoutput_file = fopen(filename_temp2, "wb");
            if (filename_temp != NULL) {
                free(filename_temp);
                filename_temp = NULL;
            }
            if (filename_temp2 != NULL) {
                free(filename_temp2);
                filename_temp2 = NULL;
            }
            if (!jpegoutput_file) {
                error("Could not open mjpeg-destination");
            }
        }
        if (buffer->length) {
            mmal_buffer_header_mem_lock(buffer);
            bytes_written = fwrite(buffer->data, 1, buffer->length,
                jpegoutput_file);
            mmal_buffer_header_mem_unlock(buffer);
        }
        TESTERR(bytes_written != buffer->length, "Could not write all bytes");
    }

    if (buffer->flags & (MMAL_BUFFER_HEADER_FLAG_FRAME_END |
        MMAL_BUFFER_HEADER_FLAG_TRANSMISSION_FAILED)) {
        mjpeg_cnt++;
        if (mjpeg_cnt == divider) {
            fclose(jpegoutput_file);
            jpegoutput_file = NULL;
            asprintf(&filename_temp, jpeg_filename, image_cnt);
            asprintf(&filename_temp2, "%s.part", filename_temp);
            rename(filename_temp2, filename_temp);
            free(filename_temp);
            filename_temp = NULL;
            free(filename_temp2);
            filename_temp2 = NULL;
            image_cnt++;
            mjpeg_cnt = 0;
            cam_set_annotation();
        }
    }

    mmal_buffer_header_release(buffer);

    if (port->is_enabled) {
        MMAL_STATUS_T status = MMAL_SUCCESS;
        MMAL_BUFFER_HEADER_T *new_buffer;

        new_buffer = mmal_queue_get(pool_jpegencoder->queue);
        if (new_buffer) {
            status = mmal_port_send_buffer(port, new_buffer);
        }
        TESTERR((!new_buffer) || (status != MMAL_SUCCESS),
            "Could not send buffers to port");
    } else {
        fprintf(stderr,
            "%s: %d: ERROR - port disabled, could not get/send buffer\n",
            __function__, __LINE__);
}

static void
jpegencoder2_buffer_callback(MMAL_PORT_T * port,
    MMAL_BUFFER_HEADER_T * buffer) {
    int complete = 0;
    int bytes_written = buffer->length;
    PORT_USERDATA *pData = (PORT_USERDATA *)port->userdata;

    if (pData != NULL) {
        if (buffer->length) {
            mmal_buffer_header_mem_lock(buffer);
            bytes_written = fwrite(buffer->data, 1, buffer->length,
                jpegoutput2_file);
            mmal_buffer_header_mem_unlock(buffer);
        }
        if (bytes_written != buffer->length) {
            complete = 1;
            error("Could not write all bytes", __function__, __LINE__);
        }

        if (buffer->
            flags & (MMAL_BUFFER_HEADER_FLAG_FRAME_END |
                MMAL_BUFFER_HEADER_FLAG_TRANSMISSION_FAILED)) {
            fclose(jpegoutput2_file);
            if (status_filename != 0) {
                if (!timelapse) {
                    status_file = fopen(status_filename, "w");
                    fputs("ready", status_file);
                    fclose(status_file);
                }
            }
            image2_cnt++;
            capturing = 0;
        }
    } else {
        fprintf(stderr, "%s: %d: Received buffer with no userdata\n",
            __function__, __line__);
    }

    // Do not forget to check image end to cleanup state.
    if (buffer->
        flags & (MMAL_BUFFER_HEADER_FLAG_FRAME_END |
            MMAL_BUFFER_HEADER_FLAG_TRANSMISSION_FAILED)) {
        complete = 1;
        capturing = 0;
    }

    mmal_buffer_header_release(buffer);

    if (port->is_enabled) {
        MMAL_STATUS_T status = MMAL_SUCCESS;
        MMAL_BUFFER_HEADER_T *new_buffer;

        new_buffer = mmal_queue_get(pool_jpegencoder2->queue);

        if (new_buffer) {
            status = mmal_port_send_buffer(port, new_buffer);
        }
        TESTERR((!new_buffer) || (status != MMAL_SUCCESS),
            "Could not send buffers to port");
    } else {
        fprintf(stderr,
            "%s: %d: TESTERR - port disabled, could not get/send buffer\n",
            __function__, __LINE__);
    }
    if (complete) {
        // fprintf(stderr, "%s: %d: vcos_semaphore_post\n",
        //    __function__, __LINE__);
        vcos_semaphore_post(&(pData->complete_semaphore));
    }
}

static void h264encoder_buffer_callback(MMAL_PORT_T *port,
    MMAL_BUFFER_HEADER_T *buffer) {
    int bytes_written = buffer->length;
    MMAL_STATUS_T status = MMAL_SUCCESS;
    MMAL_BUFFER_HEADER_T *new_buffer;

    if (buffer->length) {
        mmal_buffer_header_mem_lock(buffer);
        bytes_written = fwrite(buffer->data, 1, buffer->length,
            h264output_file);
        mmal_buffer_header_mem_unlock(buffer);
        TESTERR(bytes_written != buffer->length,
            "Could not write all bytes");
    }

    mmal_buffer_header_release(buffer);

    if (port->is_enabled) {
        MMAL_STATUS_T status = MMAL_SUCCESS;
        MMAL_BUFFER_HEADER_T *new_buffer;

        new_buffer = mmal_queue_get(pool_h264encoder->queue);
        if (new_buffer) {
            status = mmal_port_send_buffer(port, new_buffer);
        }
        TESTERR((!new_buffer) || (status != MMAL_SUCCESS),
            "Could not send buffers to port");
    }
}

void cam_set_sharpness() {
    MMAL_RATIONAL_T value = { cset.sharpness, 100 };

    status = mmal_port_parameter_set_rational(camera->control,
        MMAL_PARAMETER_SHARPNESS, value);
    MMAL_STATUS("Could not set sharpness");
}

void cam_set_contrast() {
    MMAL_RATIONAL_T value = { cset.contrast, 100 };

    status = mmal_port_parameter_set_rational(camera->control,
        MMAL_PARAMETER_CONTRAST, value);
    MMAL_STATUS("Could not set contrast");
}

void cam_set_brightness() {
    MMAL_RATIONAL_T value = { cset.brightness, 100 };

    status = mmal_port_parameter_set_rational(camera->control,
        MMAL_PARAMETER_BRIGHTNESS, value);
    MMAL_STATUS("Could not set brightness");
}

void cam_set_saturation() {
    MMAL_RATIONAL_T value = { cset.saturation, 100 };

    status = mmal_port_parameter_set_rational(camera->control,
        MMAL_PARAMETER_SATURATION, value);
    if (status != MMAL_SUCCESS)
        error("Could not set saturation");
}

void cam_set_iso() {
    status = mmal_port_parameter_set_uint32(camera->control,
        MMAL_PARAMETER_ISO, cset.iso);
    MMAL_STATUS("Could not set ISO");
}

void cam_set_vs() {
    status = mmal_port_parameter_set_boolean(camera->control,
        MMAL_PARAMETER_VIDEO_STABILISATION, cset.vs);
    MMAL_STATUS("Could not set video stabilisation");
}

void cam_set_ec() {
    status = mmal_port_parameter_set_int32(camera->control,
        MMAL_PARAMETER_EXPOSURE_COMP, cset.ec);
    MMAL_STATUS("Could not set exposure compensation");
}

void cam_set_em() {
    MMAL_PARAMETER_EXPOSUREMODE_T exp = { {MMAL_PARAMETER_EXPOSURE_MODE,
        sizeof (MMAL_PARAMETER_EXPOSUREMODE_T)}
    };

    if (!strcmp(cset.em, "off")) {
        exp.value = MMAL_PARAM_EXPOSUREMODE_OFF;
    } else if (!strcmp(cset.em, "auto")) {
        exp.value = MMAL_PARAM_EXPOSUREMODE_AUTO;
    } else if (!strcmp(cset.em, "night")) {
        exp.value = MMAL_PARAM_EXPOSUREMODE_NIGHT;
    } else if (!strcmp(cset.em, "nightpreview")) {
        exp.value = MMAL_PARAM_EXPOSUREMODE_NIGHTPREVIEW;
    } else if (!strcmp(cset.em, "backlight")) {
        exp.value = MMAL_PARAM_EXPOSUREMODE_BACKLIGHT;
    } else if (!strcmp(cset.em, "spotlight")) {
        exp.value = MMAL_PARAM_EXPOSUREMODE_SPOTLIGHT;
    } else if (!strcmp(cset.em, "sports")) {
        exp.value = MMAL_PARAM_EXPOSUREMODE_SPORTS;
    } else if (!strcmp(cset.em, "snow")) {
        exp.value = MMAL_PARAM_EXPOSUREMODE_SNOW;
    } else if (!strcmp(cset.em, "beach")) {
        exp.value = MMAL_PARAM_EXPOSUREMODE_BEACH;
    } else if (!strcmp(cset.em, "verylong")) {
        exp.value = MMAL_PARAM_EXPOSUREMODE_VERYLONG;
    } else if (!strcmp(cset.em, "fixedfps")) {
        exp.value = MMAL_PARAM_EXPOSUREMODE_FIXEDFPS;
    } else if (!strcmp(cset.em, "antishake")) {
        exp.value = MMAL_PARAM_EXPOSUREMODE_ANTISHAKE;
    } else if (!strcmp(cset.em, "fireworks")) {
        exp.value = MMAL_PARAM_EXPOSUREMODE_FIREWORKS;
    } else {
        error("Invalid exposure mode", __function__, __LINE);
    }
    status = mmal_port_parameter_set(camera->control, &exp);
    MMAL_STATUS("Could not set exposure mode");
}

void cam_set_wb() {
    MMAL_PARAMETER_AWBMODE_T awb = {
        { MMAL_PARAMETER_AWB_MODE, sizeof (MMAL_PARAMETER_AWBMODE_T) }
    };

    if (!strcmp(cset.wb, "off")) {
        awb.value = MMAL_PARAM_AWBMODE_OFF;
    } else if (!strcmp(cset.wb, "auto")) {
        awb.value = MMAL_PARAM_AWBMODE_AUTO;
    } else if (!strcmp(cset.wb, "sun")) {
        awb.value = MMAL_PARAM_AWBMODE_SUNLIGHT;
    } else if (!strcmp(cset.wb, "cloudy")) {
        awb.value = MMAL_PARAM_AWBMODE_CLOUDY;
    } else if (!strcmp(cset.wb, "shade")) {
        awb.value = MMAL_PARAM_AWBMODE_SHADE;
    } else if (!strcmp(cset.wb, "tungsten")) {
        awb.value = MMAL_PARAM_AWBMODE_TUNGSTEN;
    } else if (!strcmp(cset.wb, "fluorescent")) {
        awb.value = MMAL_PARAM_AWBMODE_FLUORESCENT;
    } else if (!strcmp(cset.wb, "incandescent")) {
        awb.value = MMAL_PARAM_AWBMODE_INCANDESCENT;
    } else if (!strcmp(cset.wb, "flash")) {
        awb.value = MMAL_PARAM_AWBMODE_FLASH;
    } else if (!strcmp(cset.wb, "horizon")) {
        awb.value = MMAL_PARAM_AWBMODE_HORIZON;
    } else {
        error("Invalid white balance", __function__, __LINE__);
    }
    status = mmal_port_parameter_set(camera->control, &param.hdr);
    MMAL_STATUS("Could not set white balance");
}

void cam_set_mm() {
    MMAL_PARAMETER_EXPOSUREMETERINGMODE_T m_mode = { {
        MMAL_PARAMETER_EXP_METERING_MODE,
        sizeof (MMAL_PARAMETER_EXPOSUREMETERINGMODE_T)
    } };

    if (!strcmp(cset.mm, "average")) {
        m_mode.value = MMAL_PARAM_EXPOSUREMETERINGMODE_AVERAGE;
    } else if (!strcmp(cset.mm, "spot")) {
        m_mode.value = MMAL_PARAM_EXPOSUREMETERINGMODE_SPOT;
    } else if (!strcmp(cset.mm, "backlit")) {
        m_mode.value = MMAL_PARAM_EXPOSUREMETERINGMODE_BACKLIT;
    } else if (!strcmp(cset.mm, "matrix")) {
        m_mode.value = MMAL_PARAM_EXPOSUREMETERINGMODE_MATRIX;
    } else {
        error("Invalid metering mode");
    }
    status = mmal_port_parameter_set(camera->control, &m_mode);
    MMAL_STATUS("Could not set metering mode");
}

void cam_set_ie() {
    MMAL_PARAMETER_IMAGEFX_T imageFX = {
        { MMAL_PARAMETER_IMAGE_EFFECT, sizeof (MMAL_PARAMETER_IMAGEFX_T) }
    };

    if (!strcmp(cset.ie, "none")) {
        imageFX.value = MMAL_PARAM_IMAGEFX_NONE;
    } else if (!strcmp(cset.ie, "negative")) {
        imageFX.value = MMAL_PARAM_IMAGEFX_NEGATIVE;
    } else if (!strcmp(cset.ie, "solarise")) {
        imageFX.value = MMAL_PARAM_IMAGEFX_SOLARIZE;
    } else if (!strcmp(cset.ie, "sketch")) {
        imageFX.value = MMAL_PARAM_IMAGEFX_SKETCH;
    } else if (!strcmp(cset.ie, "denoise")) {
        imageFX.value = MMAL_PARAM_IMAGEFX_DENOISE;
    } else if (!strcmp(cset.ie, "emboss")) {
        imageFX.value = MMAL_PARAM_IMAGEFX_EMBOSS;
    } else if (!strcmp(cset.ie, "oilpaint")) {
        imageFX.value = MMAL_PARAM_IMAGEFX_OILPAINT;
    } else if (!strcmp(cset.ie, "hatch")) {
        imageFX.value = MMAL_PARAM_IMAGEFX_HATCH;
    } else if (!strcmp(cset.ie, "gpen")) {
        imageFX.value = MMAL_PARAM_IMAGEFX_GPEN;
    } else if (!strcmp(cset.ie, "pastel")) {
        imageFX.value = MMAL_PARAM_IMAGEFX_PASTEL;
    } else if (!strcmp(cset.ie, "watercolour")) {
        imageFX.value = MMAL_PARAM_IMAGEFX_WATERCOLOUR;
    } else if (!strcmp(cset.ie, "film")) {
        imageFX.value = MMAL_PARAM_IMAGEFX_FILM;
    } else if (!strcmp(cset.ie, "blur")) {
        imageFX.value = MMAL_PARAM_IMAGEFX_BLUR;
    } else if (!strcmp(cset.ie, "saturation")) {
        imageFX.value = MMAL_PARAM_IMAGEFX_SATURATION;
    } else if (!strcmp(cset.ie, "colourswap")) {
        imageFX.value = MMAL_PARAM_IMAGEFX_COLOURSWAP;
    } else if (!strcmp(cset.ie, "washedout")) {
        imageFX.value = MMAL_PARAM_IMAGEFX_WASHEDOUT;
    } else if (!strcmp(cset.ie, "posterise")) {
        imageFX.value = MMAL_PARAM_IMAGEFX_POSTERISE;
    } else if (!strcmp(cset.ie, "colourpoint")) {
        imageFX.value = MMAL_PARAM_IMAGEFX_COLOURPOINT;
    } else if (!strcmp(cset.ie, "colourbalance")) {
        imageFX.value = MMAL_PARAM_IMAGEFX_COLOURBALANCE;
    } else if (!strcmp(cset.ie, "cartoon")) {
        imageFX.value = MMAL_PARAM_IMAGEFX_CARTOON;
    } else {
        error("Invalid image effect");
    }
    status = mmal_port_parameter_set(camera->control, &imageFX);
    MMAL_STATUS("Could not set image effect");
}

void cam_set_ce() {
    MMAL_PARAMETER_COLOURFX_T colfx = {
        { MMAL_PARAMETER_COLOUR_EFFECT, sizeof (MMAL_PARAMETER_COLOURFX_T) },
        0, 0, 0
    };

    colfx.enable = cset.ce_en;
    colfx.u = cset.ce_u;
    colfx.v = cset.ce_v;
    status = mmal_port_parameter_set(camera->control, &colfx.hdr);
    MMAL_STATUS("Could not set exposure compensation");
}

void cam_set_rotation() {
    status = mmal_port_parameter_set_int32(
        camera->output[PREVIEW_PORT], MMAL_PARAMETER_ROTATION,
        cset.rotation);
    MMAL_STATUS("Could not set rotation (" S(PREVIEW_PORT) ")");
    status = mmal_port_parameter_set_int32(
        camera->output[VIDEO_PORT], MMAL_PARAMETER_ROTATION,
        cam_setting_rotation);
    MMAL_STATUS("Could not set rotation (" S(VIDEO_PORT) ")");
    status =
        mmal_port_parameter_set_int32(camera->
        output[CAPTURE_PORT], MMAL_PARAMETER_ROTATION,
        cam_setting_rotation);
    MMAL_STATUS("Could not set rotation (" S(CAPTURE_PORT) ")");
}

void cam_set_flip() {
    MMAL_PARAMETER_MIRROR_T mirror = {
        { MMAL_PARAMETER_MIRROR, sizeof (MMAL_PARAMETER_MIRROR_T) },
    MMAL_PARAM_MIRROR_NONE };
    if (cset.hflip && cset.vflip) {
        mirror.value = MMAL_PARAM_MIRROR_BOTH;
    } else if (cset.hflip) {
        mirror.value = MMAL_PARAM_MIRROR_HORIZONTAL;
    } else if (cset.vflip) {
        mirror.value = MMAL_PARAM_MIRROR_VERTICAL;
    }
    status = mmal_port_parameter_set(camera->output[PREVIEW_PORT], &mirror);
    MMAL_STATUS("Could not set flip (" S(PREVIEW_PORT) ")");
    status = mmal_port_parameter_set(camera->output[VIDEO_PORT], &mirror);
    MMAL_STATUS("Could not set flip (" S(VIDEO_PORT) ")");
    status = mmal_port_parameter_set(camera->output[CAPTURE_PORT], &mirror.hdr);
    MMAL_STATUS("Could not set flip (" S(CAPTURE_PORT) ")");
}

void cam_set_roi() {
    MMAL_PARAMETER_INPUT_CROP_T crop = {
        { MMAL_PARAMETER_INPUT_CROP, sizeof (MMAL_PARAMETER_INPUT_CROP_T) }
    };
    crop.rect.x = cset.roi_x;
    crop.rect.y = cset.roi_y;
    crop.rect.width = cset.roi_w;
    crop.rect.height = cset.roi_h;
    status = mmal_port_parameter_set(camera->control, &crop.hdr);
    MMAL_STATUS("Could not set sensor area");
}

void cam_set_ss() {
    status = mmal_port_parameter_set_uint32(camera->control,
        MMAL_PARAMETER_SHUTTER_SPEED, cset.ss);
    MMAL_STATUS("Could not set shutter speed");
}

void cam_set_quality() {
    status = mmal_port_parameter_set_uint32(jpegencoder2->output[0],
        MMAL_PARAMETER_JPEG_Q_FACTOR, cset.quality);
    MMAL_STATUS("Could not set quality");
}

void cam_set_raw() {
    status = mmal_port_parameter_set_boolean(camera->output[CAPTURE_PORT],
        MMAL_PARAMETER_ENABLE_RAW_CAPTURE, cset.raw);
    MMAL_STATUS("Could not set raw layer");
}

void cam_set_bitrate() {
    h264encoder->output[0]->format->bitrate = cset.bitrate;
    status = mmal_port_format_commit(h264encoder->output[0]);
    if (status != MMAL_SUCCESS)
        error("Could not set bitrate");
}

/* Checks if specified port is valid and enabled, then disables it.
port  Pointer to the port */
static void check_disable_port(MMAL_PORT_T *port) {
    if ((port != NULL) && port->is_enabled) {
        mmal_port_disable(port);
    }
}

void cam_set_annotation() {
    char *filename_temp;
    MMAL_PARAMETER_CAMERA_ANNOTATE_V2_T anno =
        { {MMAL_PARAMETER_ANNOTATE,
                sizeof (MMAL_PARAMETER_CAMERA_ANNOTATE_V2_T)}
    };

    if (cset.annotation != 0) {
        currTime = time(NULL);
        localTime = localtime(&currTime);
        asprintf(&filename_temp, cset.annotation,
            localTime->tm_year + 1900, localTime->tm_mon + 1,
            localTime->tm_mday, localTime->tm_hour, localTime->tm_min,
            localTime->tm_sec);
        anno.enable = 1;
        strcpy(anno.text, filename_temp);
        free(filename_temp);
    } else {
        anno.enable = 0;
    }
    anno.show_shutter = 0;
    anno.show_analog_gain = 0;
    anno.show_lens = 0;
    anno.show_caf = 0;
    anno.show_motion = 0;
    anno.black_text_background = cset.annback;

    status = mmal_port_parameter_set(camera->control, &anno.hdr);
    if (status != MMAL_SUCCESS)
        error("Could not set annotation");
}

void start_all(void) {
    MMAL_ES_FORMAT_T *format;
    int max, i;
    VCOS_STATUS_T vcos_status;

    // create camera
    status = mmal_component_create(MMAL_COMPONENT_DEFAULT_CAMERA, &camera);
    MMAL_STATUS("Could not create camera");
    status = mmal_port_enable(camera->control, camera_control_callback);
    MMAL_STATUS("Could not enable camera control port");

    MMAL_PARAMETER_CAMERA_CONFIG_T cam_config = {
        {
            MMAL_PARAMETER_CAMERA_CONFIG,
            sizeof (MMAL_PARAMETER_CAMERA_CONFIG_T)
        },
        .max_stills_w = image_width,
        .max_stills_h = image_height,
        .stills_yuv422 = 0,
        .one_shot_stills = 1,
        .max_preview_video_w = video_width,
        .max_preview_video_h = video_height,
        .num_preview_video_frames = 3,
        .stills_capture_circular_buffer_height = 0,
        .fast_preview_resume = 0,
        .use_stc_timestamp = MMAL_PARAM_TIMESTAMP_MODE_RESET_STC
    };
    mmal_port_parameter_set(camera->control, cam_config);

    format = camera->output[PREVIEW_PORT]->format;
    format->es->video.width = VCOS_ALIGN_UP(video_width, 32);
    format->es->video.height = VCOS_ALIGN_UP(video_height, 16);
    format->es->video.crop.x = 0;
    format->es->video.crop.y = 0;
    format->es->video.crop.width = video_width;
    format->es->video.crop.height = video_height;
    format->es->video.frame_rate.num = 0;
    format->es->video.frame_rate.den = 1;
    status =
        mmal_port_format_commit(camera->output[PREVIEW_PORT]);
    MMAL_STATUS("Could not set preview format");

    format = camera->output[VIDEO_PORT]->format;
    format->encoding_variant = MMAL_ENCODING_I420;
    format->encoding = MMAL_ENCODING_OPAQUE;
    format->es->video.width = VCOS_ALIGN_UP(video_width, 32);
    format->es->video.height = VCOS_ALIGN_UP(video_height, 16);
    format->es->video.crop.x = 0;
    format->es->video.crop.y = 0;
    format->es->video.crop.width = video_width;
    format->es->video.crop.height = video_height;
    format->es->video.frame_rate.num = video_fps;
    format->es->video.frame_rate.den = 1;
    status = mmal_port_format_commit(camera->output[VIDEO_PORT]);
    MMAL_STATUS("Could not set video format");
    if (camera->output[VIDEO_PORT]->buffer_num < 3) {
        camera->output[VIDEO_PORT]->buffer_num = 3;
    }

    format = camera->output[CAPTURE_PORT]->format;
    format->encoding = MMAL_ENCODING_OPAQUE;
    format->es->video.width = VCOS_ALIGN_UP(image_width, 32);
    format->es->video.height = VCOS_ALIGN_UP(image_height, 16);
    format->es->video.crop.x = 0;
    format->es->video.crop.y = 0;
    format->es->video.crop.width = image_width;
    format->es->video.crop.height = image_height;
    format->es->video.frame_rate.num = 0;
    format->es->video.frame_rate.den = 1;
    status = mmal_port_format_commit(camera->output[CAPTURE_PORT]);
    MMAL_STATUS("Could not set still format");
    if (camera->output[CAPTURE_PORT]->buffer_num < 3)
        camera->output[CAPTURE_PORT]->buffer_num = 3;

    status = mmal_component_enable(camera);
    MMAL_STATUS("Could not enable camera");

    // create jpeg-encoder
    status = mmal_component_create(MMAL_COMPONENT_DEFAULT_IMAGE_ENCODER,
        &jpegencoder);
    if (status != MMAL_SUCCESS && status != MMAL_ENOSYS)
        error("Could not create image encoder", __function__, __LINE__);

    mmal_format_copy(jpegencoder->output[0]->format,
        jpegencoder->input[0]->format);
    jpegencoder->output[0]->format->encoding = MMAL_ENCODING_JPEG;
    jpegencoder->output[0]->buffer_size =
        jpegencoder->output[0]->buffer_size_recommended;
    if (jpegencoder->output[0]->buffer_size <
        jpegencoder->output[0]->buffer_size_min)
        jpegencoder->output[0]->buffer_size =
            jpegencoder->output[0]->buffer_size_min;
    jpegencoder->output[0]->buffer_num =
        jpegencoder->output[0]->buffer_num_recommended;
    if (jpegencoder->output[0]->buffer_num <
        jpegencoder->output[0]->buffer_num_min)
        jpegencoder->output[0]->buffer_num =
            jpegencoder->output[0]->buffer_num_min;
    status = mmal_port_format_commit(jpegencoder->output[0]);
    MMAL_STATUS("Could not set image format");
    status = mmal_port_parameter_set_uint32(jpegencoder->output[0],
        MMAL_PARAMETER_JPEG_Q_FACTOR, quality);
    MMAL_STATUS("Could not set jpeg quality");

    status = mmal_component_enable(jpegencoder);
    MMAL_STATUS("Could not enable image encoder");
    pool_jpegencoder =
        mmal_port_pool_create(jpegencoder->output[0],
        jpegencoder->output[0]->buffer_num,
        jpegencoder->output[0]->buffer_size);
    if (!pool_jpegencoder) {
        error("Could not create image buffer pool", __function__, __LINE__);
    }

    // create second jpeg-encoder
    status = mmal_component_create(MMAL_COMPONENT_DEFAULT_IMAGE_ENCODER,
        &jpegencoder2);
    if (status != MMAL_SUCCESS && status != MMAL_ENOSYS) {
        error("Could not create image encoder 2", __function__, __LINE__);
    }

    mmal_format_copy(jpegencoder2->output[0]->format,
        jpegencoder2->input[0]->format);
    jpegencoder2->output[0]->format->encoding = MMAL_ENCODING_JPEG;
    jpegencoder2->output[0]->buffer_size =
        jpegencoder2->output[0]->buffer_size_recommended;
    if (jpegencoder2->output[0]->buffer_size <
        jpegencoder2->output[0]->buffer_size_min) {
        jpegencoder2->output[0]->buffer_size =
            jpegencoder2->output[0]->buffer_size_min;
    }
    jpegencoder2->output[0]->buffer_num =
        jpegencoder2->output[0]->buffer_num_recommended;
    if (jpegencoder2->output[0]->buffer_num <
        jpegencoder2->output[0]->buffer_num_min) {
        jpegencoder2->output[0]->buffer_num =
            jpegencoder2->output[0]->buffer_num_min;
    }
    status = mmal_port_format_commit(jpegencoder2->output[0]);
    MMAL_STATUS("Could not set image format 2");
    status = mmal_port_parameter_set_uint32(jpegencoder2->output[0],
        MMAL_PARAMETER_JPEG_Q_FACTOR, 85);
    MMAL_STATUS("Could not set jpeg quality 2");

    status = mmal_component_enable(jpegencoder2);
    MMAL_STATUS("Could not enable image encoder 2");
    pool_jpegencoder2 = mmal_port_pool_create(jpegencoder2->output[0],
        jpegencoder2->output[0]->buffer_num,
        jpegencoder2->output[0]->buffer_size);
    if (!pool_jpegencoder2) {
        error("Could not create image buffer pool 2", __function__, __LINE__);
    }

    // create h264-encoder
    status = mmal_component_create(MMAL_COMPONENT_DEFAULT_VIDEO_ENCODER,
        &h264encoder);
    if (status != MMAL_SUCCESS && status != MMAL_ENOSYS)
        error("Could not create video encoder");

    mmal_format_copy(h264encoder->output[0]->format,
        h264encoder->input[0]->format);
    h264encoder->output[0]->format->encoding = MMAL_ENCODING_H264;
    h264encoder->output[0]->format->bitrate = 17000000;
    h264encoder->output[0]->buffer_size =
        h264encoder->output[0]->buffer_size_recommended;
    if (h264encoder->output[0]->buffer_size <
        h264encoder->output[0]->buffer_size_min) {
        h264encoder->output[0]->buffer_size =
            h264encoder->output[0]->buffer_size_min;
    }
    h264encoder->output[0]->buffer_num =
        h264encoder->output[0]->buffer_num_recommended;
    if (h264encoder->output[0]->buffer_num <
        h264encoder->output[0]->buffer_num_min) {
        h264encoder->output[0]->buffer_num =
            h264encoder->output[0]->buffer_num_min;
    }
    h264encoder->output[0]->format->es->video.frame_rate.num = 0;
    h264encoder->output[0]->format->es->video.frame_rate.den = 1;
    status = mmal_port_format_commit(h264encoder->output[0]);
    MMAL_STATUS("Could not set video format");

    MMAL_PARAMETER_UINT32_T param2 = { {
        MMAL_PARAMETER_VIDEO_ENCODE_INITIAL_QUANT,
        sizeof (MMAL_PARAMETER_UINT32_T)
    }, 25 };
    status = mmal_port_parameter_set(h264encoder->output[0], &param2);
    MMAL_PARAMETER_UINT32_T("Could not set video quantisation");

    MMAL_PARAMETER_UINT32_T param3 = { {
        MMAL_PARAMETER_VIDEO_ENCODE_QP_P, sizeof (MMAL_PARAMETER_UINT32_T)
    }, 31 };
    status = mmal_port_parameter_set(h264encoder->output[0], &param3);
    MMAL_STATUS("Could not set video quantisation");

    MMAL_PARAMETER_VIDEO_PROFILE_T param4;
    param4.hdr.id = MMAL_PARAMETER_PROFILE;
    param4.hdr.size = sizeof (param4);
    param4.profile[0].profile = MMAL_VIDEO_PROFILE_H264_HIGH;
    param4.profile[0].level = MMAL_VIDEO_LEVEL_H264_4;
    status = mmal_port_parameter_set(h264encoder->output[0], &param4);
    MMAL_STATUS("Could not set video port format");

    status = mmal_port_parameter_set_boolean(h264encoder->input[0],
        MMAL_PARAMETER_VIDEO_IMMUTABLE_INPUT, 1);
    MMAL_STATUS("Could not set immutable flag");

    status = mmal_port_parameter_set_boolean(h264encoder->output[0],
        MMAL_PARAMETER_VIDEO_ENCODE_INLINE_HEADER, 0);
    MMAL_STATUS("Could not set inline flag");

    //
    // create image-resizer
    //
    unsigned int height_temp = width * video_height / video_width;
    height_temp -= height_temp % 16;
    status = mmal_component_create("vc.ril.resize", &resizer);
    if (status != MMAL_SUCCESS && status != MMAL_ENOSYS)
        error("Could not create image resizer");

    format = resizer->output[0]->format;
    format->encoding = MMAL_ENCODING_I420;
    format->es->video.width = VCOS_ALIGN_UP(width, 32);
    format->es->video.height = VCOS_ALIGN_UP(height_temp, 16);
    format->es->video.crop.x = 0;
    format->es->video.crop.y = 0;
    format->es->video.crop.width = width;
    format->es->video.crop.height = height_temp;
    format->es->video.frame_rate.num = 30;
    format->es->video.frame_rate.den = 1;
    status = mmal_port_format_commit(resizer->output[0]);
    MMAL_STATUS("Could not set image resizer output");

    status = mmal_component_enable(resizer);
    MMAL_STATUS("Could not enable image resizer");

    // connect
    status = mmal_connection_create(&con_cam_res,
        camera->output[PREVIEW_PORT], resizer->input[0],
        MMAL_CONNECTION_FLAG_TUNNELLING |
        MMAL_CONNECTION_FLAG_ALLOCATION_ON_INPUT);
    MMAL_STATUS("Could not create connection camera -> resizer");
    status = mmal_connection_enable(con_cam_res);
    MMAL_STATUS("Could not enable connection camera -> resizer");

    status = mmal_connection_create(&con_res_jpeg, resizer->output[0],
        jpegencoder->input[0],
        MMAL_CONNECTION_FLAG_TUNNELLING |
        MMAL_CONNECTION_FLAG_ALLOCATION_ON_INPUT);
    MMAL_STATUS("Could not create connection resizer -> encoder");
    status = mmal_connection_enable(con_res_jpeg);
    MMAL_STATUS("Could not enable connection resizer -> encoder");

    status = mmal_port_enable(jpegencoder->output[0],
        jpegencoder_buffer_callback);
    MMAL_STATUS("Could not enable jpeg port");
    max = mmal_queue_length(pool_jpegencoder->queue);
    for (i = 0; i < max; i++) {
        MMAL_BUFFER_HEADER_T *jpegbuffer =
            mmal_queue_get(pool_jpegencoder->queue);

        if (!jpegbuffer)
            error("Could not create jpeg buffer header");
        status =
            mmal_port_send_buffer(jpegencoder->output[0], jpegbuffer);
        MMAL_STATUS("Could not send buffers to jpeg port");
    }

    status = mmal_connection_create(&con_cam_jpeg,
        camera->output[CAPTURE_PORT], jpegencoder2->input[0],
        MMAL_CONNECTION_FLAG_TUNNELLING |
        MMAL_CONNECTION_FLAG_ALLOCATION_ON_INPUT);
    MMAL_STATUS("Could not create connection camera -> encoder");
    status = mmal_connection_enable(con_cam_jpeg);
    MMAL_STATUS("Could not enable connection camera -> encoder");

    status = mmal_port_enable(jpegencoder2->output[0],
        jpegencoder2_buffer_callback);
    MMAL_STATUS("Could not enable jpeg port 2");
    max = mmal_queue_length(pool_jpegencoder2->queue);
    for (i = 0; i < max; i++) {
        MMAL_BUFFER_HEADER_T *jpegbuffer2 =
            mmal_queue_get(pool_jpegencoder2->queue);

        if (!jpegbuffer2) {
            error("Could not create jpeg buffer header 2");
        }
        status = mmal_port_send_buffer(jpegencoder2->output[0], jpegbuffer2);
        MMAL_STATUS("Could not send buffers to jpeg port 2");
    }

    // settings
    cam_set_sharpness();
    cam_set_contrast();
    cam_set_brightness();
    cam_set_saturation();
    cam_set_iso();
    cam_set_vs();
    cam_set_ec();
    cam_set_em();
    cam_set_wb();
    cam_set_mm();
    cam_set_ie();
    cam_set_ce();
    cam_set_rotation();
    cam_set_flip();
    cam_set_roi();
    cam_set_ss();
    cam_set_quality();
    cam_set_raw();
    cam_set_bitrate();
    cam_set_annotation();

}


void stop_all(void) {
    // disable components
    if (resizer) {
        mmal_component_disable(resizer);
        mmal_component_destroy(resizer);
        resizer = NULL;
    }
    if (camera) {
        mmal_component_disable(camera);
        mmal_component_destroy(camera);
        camera = NULL;
    }

    // destroy encoders and remaining components
    if (jpegencoder != NULL) {
        check_disable_port(jpegencoder->output[0]);
        mmal_component_disable(jpegencoder);
        if (pool_jpegencoder) {
            mmal_port_pool_destroy(jpegencoder->output[0], pool_jpegencoder);
        }
        mmal_component_destroy(jpegencoder);
        jpegencoder = NULL;
    }

    if (jpegencoder2 != NULL) {
        check_disable_port(jpegencoder2->output[0]);
        mmal_component_disable(jpegencoder2);
        if (pool_jpegencoder2) {
            mmal_port_pool_destroy(jpegencoder2->output[0], pool_jpegencoder2);
        }
        mmal_component_destroy(jpegencoder2);
        jpegencoder2 = NULL;
    }

    if (h264encoder != NULL) {
        check_disable_port(h264encoder->output[0]);
        mmal_component_disable(h264encoder);
        mmal_component_destroy(h264encoder);
        h264encoder = NULL;
    }

    // destroy connections
    if (con_cam_res) {
        mmal_connection_destroy(con_cam_res);
    }
    if (con_res_jpeg) {
        mmal_connection_destroy(con_res_jpeg);
    }
    if (con_cam_jpeg) {
        mmal_connection_destroy(con_cam_jpeg);
    }
    if (con_cam_h264) {
        mmal_connection_destroy(con_cam_h264);
    }

    // cleanup semaphores
    vcos_semaphore_delete(&callback_data.complete_semaphore);
}

void capt_img(void) {
    char *filename_temp;
    struct statvfs buf;
    long limit = atoi(space_limit);

    currTime = time(NULL);
    localTime = localtime(&currTime);
    asprintf(&filename_temp, jpeg2_filename, localTime->tm_year + 1900,
        localTime->tm_mon + 1, localTime->tm_mday, localTime->tm_hour,
        localTime->tm_min, localTime->tm_sec, image2_cnt);
    if (!statvfs(jpeg2_root, &buf)) {
        TESTERR((limit > 0) && ((buf.f_bsize * buf.f_bavail) < limit),
            "Insufficient disk space");
    } else {
        error("statvfs", __function__, __LINE__);
    }
    jpegoutput2_file = fopen(filename_temp, "wb");
    free(filename_temp);
    TESTERR(jpegoutput2_file != NULL, "Could not open/create image-file");

    if (status_filename != 0) {
        if (!timelapse) {
            status_file = fopen(status_filename, "w");
            fputs("image", status_file);
            fclose(status_file);
        }
    }
    capturing = 1;

    status = mmal_port_parameter_set_boolean(camera->output[CAPTURE_PORT],
        MMAL_PARAMETER_CAPTURE, 1);
    MMAL_STATUS("Could not start image capture");
    puts("Capturing image");
    // Wait for capture to complete
    // For some reason using vcos_semaphore_wait_timeout sometimes returns immediately with bad parameter error
    // even though it appears to be all correct, so reverting to untimed one until figure out why its erratic
    vcos_semaphore_wait(&callback_data.complete_semaphore);
    puts("Capture complete");

}

int main(int argc, char *argv[]) {
    int i, max, fd, length;
    char readbuf[60];
    char *filename_temp, *filename_recording, *cmd_temp;
    struct timeval now, delta, interval;
    FILE *fp;
    struct timeval prev = { 0 };
    char *line = NULL;

    bcm_host_init();

    // read arguments
    for (i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "--version")) {
            puts("RaspiMJPEG Version " VERSION);
            exit(0);
        } else if (!strcmp(argv[i], "-ic")) {
            i++;
            image2_cnt = atoi(argv[i]);
        } else if (!strcmp(argv[i], "-vc")) {
            i++;
            video_cnt = atoi(argv[i]);
        } else if (!strcmp(argv[i], "-md")) {
            motion_detection = 1;
        } else {
            error("Invalid arguments", __function__, __LINE__);
        }
    }

    // read config file
    fp = fopen(MJPG_DEF_CFG_FILE, "r");
    if (fp != NULL) {
        // XXX dike this out and use fgets like a normal human being
        unsigned int len = 0;
        while ((length = getline(&line, &len, fp)) != -1) {
            line[length - 1] = 0;
            if (!strncmp(line, "width ", 6)) {
                width = atoi(line + 6);
            } else if (!strncmp(line, "quality ", 8)) {
                quality = atoi(line + 8);
            } else if (!strncmp(line, "divider ", 8)) {
                divider = atoi(line + 8);
            } else if (!strncmp(line, "preview_path ", 13)) {
                asprintf(&jpeg_filename, "%s", line + 13);
            } else if (!strncmp(line, "spacelimit", 11)) {
                asprintf(&space_limit, "%s", line + 11);
            } else if (!strncmp(line, "image_path ", 11)) {
                asprintf(&jpeg2_filename, "%s", line + 11);
            } else if (!strncmp(line, "image_path_root", 16)) {
                asprintf(&jpeg2_root, "%s", line + 16);
            } else if (!strncmp(line, "video_path ", 11)) {
                asprintf(&h264_filename, "%s", line + 11);
            } else if (!strncmp(line, "status_file ", 12)) {
                asprintf(&status_filename, "%s", line + 12);
            } else if (!strncmp(line, "control_file ", 13)) {
                asprintf(&pipe_filename, "%s", line + 13);
            } else if (!strncmp(line, "annotation ", 11)) {
                asprintf(&cset.annotation, "%s", line + 11);
            } else if (!strncmp(line, "anno_background true", 20)) {
                cset.annback = 1;
            } else if (!strncmp(line, "MP4Box true", 11)) {
                mp4box = 1;
            } else if (!strncmp(line, "autostart idle", 14)) {
                autostart = 0;
                idle = 1;
            } else if (!strncmp(line, "motion_detection true", 21)) {
                motion_detection = 1;
            } else if (!strncmp(line, "sharpness ", 10)) {
                cset.sharpness = atoi(line + 10);
            } else if (!strncmp(line, "contrast ", 9)) {
                cset.contrast = atoi(line + 9);
            } else if (!strncmp(line, "brightness ", 11)) {
                cset.brightness = atoi(line + 11);
            } else if (!strncmp(line, "saturation ", 11)) {
                cset.saturation = atoi(line + 11);
            } else if (!strncmp(line, "iso ", 4)) {
                cset.iso = atoi(line + 4);
            } else if (!strncmp(line, "video_stabilisation true", 24)) {
                cset.vs = 1;
            } else if (!strncmp(line, "exposure_compensation ", 22)) {
                cset.ec = atoi(line + 22);
            } else if (!strncmp(line, "exposure_mode ", 14)) {
                sprintf(cset.em, "%s", line + 14);
            } else if (!strncmp(line, "white_balance ", 14)) {
                sprintf(cset.wb, "%s", line + 14);
            } else if (!strncmp(line, "metering_mode ", 14)) {
                sprintf(cset.mm, "%s", line + 14);
            } else if (!strncmp(line, "image_effect ", 13)) {
                sprintf(cset.ie, "%s", line + 13);
            } else if (!strncmp(line, "colour_effect_en ", 17)) {
                if (!strncmp(line + 17, "true", 4))
                    cset.ce_en = 1;
            } else if (!strncmp(line, "colour_effect_u ", 16)) {
                cset.ce_u = atoi(line + 16);
            } else if (!strncmp(line, "colour_effect_v ", 16)) {
                cset.ce_v = atoi(line + 16);
            } else if (!strncmp(line, "rotation ", 9)) {
                cset.rotation = atoi(line + 9);
            } else if (!strncmp(line, "hflip ", 6)) {
                if (!strncmp(line + 6, "true", 4))
                    cset.hflip = 1;
            } else if (!strncmp(line, "vflip ", 6)) {
                if (!strncmp(line + 6, "true", 4))
                    cset.vflip = 1;
            } else if (!strncmp(line, "sensor_region_x ", 16)) {
                cset.roi_x = strtoull(line + 16, NULL, 0);
            } else if (!strncmp(line, "sensor_region_y ", 16)) {
                cset.roi_y = strtoull(line + 16, NULL, 0);
            } else if (!strncmp(line, "sensor_region_w ", 16)) {
                cset.roi_w = strtoull(line + 16, NULL, 0);
            } else if (!strncmp(line, "sensor_region_h ", 16)) {
                cset.roi_h = strtoull(line + 16, NULL, 0);
            } else if (!strncmp(line, "shutter_speed ", 14)) {
                cset.ss = strtoull(line + 14, NULL, 0);
            } else if (!strncmp(line, "image_quality ", 14)) {
                cset.quality = atoi(line + 14);
            } else if (!strncmp(line, "raw_layer ", 10)) {
                if (!strncmp(line + 10, "true", 4))
                    cset.raw = 1;
            } else if (!strncmp(line, "video_bitrate ", 14)) {
                cset.bitrate = strtoull(line + 14, NULL, 0);
            } else if (!strncmp(line, "video_width ", 12)) {
                video_width = atoi(line + 12);
            } else if (!strncmp(line, "video_height ", 13)) {
                video_height = atoi(line + 13);
            } else if (!strncmp(line, "video_fps ", 10)) {
                video_fps = atoi(line + 10);
            } else if (!strncmp(line, "MP4Box_fps ", 11)) {
                MP4Box_fps = atoi(line + 11);
            } else if (!strncmp(line, "image_width ", 12)) {
                image_width = atoi(line + 12);
            } else if (!strncmp(line, "image_height ", 13)) {
                image_height = atoi(line + 13);
            } else if (!strncmp(line, "#", 1)) {
            } else if (!strcmp(line, "")) {
                // skip
            } else {
                printf("Unknown command in config file: %s\n", line);
                error("Invalid config file", __function__, __LINE__);
            }

        }
        if (line != NULL) {
            free(line);
            line = NULL;
        }
    }

    // init
    if (autostart) {
        start_all();
    }
    if (motion_detection) {
        if (system("motion") < 0) {
            error("Could not start Motion", __function__, __MAIN__);
        }
    }

    // run
    if (autostart) {
        if (pipe_filename != NULL) {
            puts("MJPEG streaming, ready to receive commands");
        } else {
            puts("MJPEG streaming");
        }
    } else {
        if (pipe_filename != NULL) {
            puts("MJPEG idle, ready to receive commands");
        } else {
            puts("MJPEG idle");
        }
    }

    struct sigaction action;
    memset(&action, 0, sizeof (struct sigaction));
    action.sa_handler = term;
    sigaction(SIGTERM, &action, NULL);
    sigaction(SIGINT, &action, NULL);

    if (status_filename != 0) {
        status_file = fopen(status_filename, "w");
        if (status_file == NULL) {
            error("Could not open/create status-file", __function__, __LINE__);
        }
        if (autostart) {
            if (!motion_detection) {
                fputs("ready", status_file);
            } else {
                fputs("md_ready", status_file);
            }
        } else {
            fputs("halted", status_file);
        }
        fclose(status_file);
    }

    while (running) {
        if (pipe_filename != 0) {

            fd = open(pipe_filename, O_RDONLY | O_NONBLOCK);
            if (fd < 0) {
                error("Could not open PIPE", __function__, __LINE__);
            }
            fcntl(fd, F_SETFL, 0);
            length = read(fd, readbuf, 60);
            close(fd);

            if (length) {
                if ((readbuf[0] == 'c') && (readbuf[1] == 'a')) {
                    if (readbuf[3] == '1') {
                        if (!capturing) {
                            status = mmal_component_enable(h264encoder);
                            MMAL_STATUS("Could not enable h264encoder");
                            pool_h264encoder =
                                mmal_port_pool_create(h264encoder->output[0],
                                h264encoder->output[0]->buffer_num,
                                h264encoder->output[0]->buffer_size);
                            if (!pool_h264encoder) {
                                error("Could not create pool");
                            }
                            status = mmal_connection_create(&con_cam_h264,
                                camera->output[VIDEO_PORT],
                                h264encoder->input[0],
                                MMAL_CONNECTION_FLAG_TUNNELLING |
                                MMAL_CONNECTION_FLAG_ALLOCATION_ON_INPUT);
                            MMAL_STATUS("Could not create connecton camera -> video converter");
                            status = mmal_connection_enable(con_cam_h264);
                            MMAL_STATUS("Could not enable connection camera -> video converter");
                            currTime = time(NULL);
                            localTime = localtime(&currTime);
                            if (mp4box) {
                                asprintf(&filename_recording, h264_filename,
                                    localTime->tm_year + 1900,
                                    localTime->tm_mon + 1,
                                    localTime->tm_mday, localTime->tm_hour,
                                    localTime->tm_min, localTime->tm_sec,
                                    video_cnt);
                                asprintf(&filename_temp, "%s.h264",
                                    filename_recording);
                            } else {
                                asprintf(&filename_temp, h264_filename,
                                    video_cnt, localTime->tm_year + 1900,
                                    localTime->tm_mon + 1,
                                    localTime->tm_mday, localTime->tm_hour,
                                    localTime->tm_min, localTime->tm_sec);
                            }
                            h264output_file = fopen(filename_temp, "wb");
                            free(filename_temp);
                            TESTERR(h264output_file != NULL,
                                "Could not open/create video-file");
                            status = mmal_port_enable(h264encoder->output[0],
                                h264encoder_buffer_callback);
                            MMAL_STATUS("Could not enable video port");
                            max = mmal_queue_length(pool_h264encoder->queue);
                            for (i = 0; i < max; i++) {
                                MMAL_BUFFER_HEADER_T *h264buffer =
                                    mmal_queue_get(pool_h264encoder->queue);
                                TESTERR(h264buffer != NULL,
                                    "Could not create video pool header");
                                status = mmal_port_send_buffer(
                                    h264encoder->output[0], h264buffer);
                                MMAL_STATUS("Could not send buffers to video port");
                            }
                            mmal_port_parameter_set_boolean(
                                camera->output[VIDEO_PORT],
                                MMAL_PARAMETER_CAPTURE, 1);
                            MMAL_STATUS("Could not start capture");
                            puts("Capturing started");
                            if (status_filename != 0) {
                                status_file = fopen(status_filename, "w");
                                if (!motion_detection) {
                                    fputs("video", status_file);
                                } else {
                                    fputs("md_video", status_file);
                                }
                                fclose(status_file);
                            }
                            capturing = 1;
                        }
                    } else if (capturing) {
                        mmal_port_parameter_set_boolean(
                            camera->output[VIDEO_PORT],
                            MMAL_PARAMETER_CAPTURE, 0);
                        MMAL_STATUS("Could not stop capture");
                        status = mmal_port_disable(h264encoder->output[0]);
                        MMAL_STATUS("Could not disable video port");
                        status = mmal_connection_destroy(con_cam_h264);
                        MMAL_STATUS("Could not destroy connection camera -> video encoder");
                        mmal_port_pool_destroy(h264encoder->output[0],
                            pool_h264encoder);
                        MMAL_STATUS("Could not destroy video buffer pool");
                        status = mmal_component_disable(h264encoder);
                        MMAL_STATUS("Could not disable video converter");
                        fclose(h264output_file);
                        h264output_file = NULL;
                        puts("Capturing stopped");
                        if (mp4box) {
                            puts("Boxing started");
                            status_file = fopen(status_filename, "w");
                            if (!motion_detection) {
                                fputs("boxing", status_file);
                            } else {
                                fputs("md_boxing", status_file);
                            }
                            fclose(status_file);
                            asprintf(&cmd_temp,
                                "MP4Box -fps %i -add %s.h264 %s > /dev/null",
                                MP4Box_fps, filename_recording,
                                filename_recording);
                            if (system(cmd_temp) < 0) {
                                error("Could not start MP4Box", __function__, __LINE__);
                            }
                            asprintf(&filename_temp, "%s.h264",
                                filename_recording);
                            remove(filename_temp);
                            free(filename_temp);
                            free(filename_recording);
                            free(cmd_temp);
                            puts("Boxing stopped");
                        }
                        video_cnt++;
                        if (status_filename != 0) {
                            status_file = fopen(status_filename, "w");
                            if (!motion_detection) {
                                fputs("ready", status_file);
                            } else {
                                fputs("md_ready", status_file);
                            }
                            fclose(status_file);
                        }
                        capturing = 0;
                    }
                } else if ((readbuf[0] == 'i') && (readbuf[1] == 'm')) {
                    capt_img();
                } else if ((readbuf[0] == 't') && (readbuf[1] == 'l')) {
                    readbuf[0] = ' ';
                    readbuf[1] = ' ';
                    readbuf[length] = 0;
                    time_between_pic = atoi(readbuf);
                    if (time_between_pic) {
                        if (status_filename != 0) {
                            status_file = fopen(status_filename, "w");
                            fputs("timelapse", status_file);
                            fclose(status_file);
                        }
                        timelapse = 1;
                        interval.tv_sec = time_between_pic / 1000;
                        interval.tv_usec =
                            (time_between_pic % 1000) * 1000;
                        puts("Timelapse started");
                    } else {
                        if (status_filename != 0) {
                            status_file = fopen(status_filename, "w");
                            fputs("ready", status_file);
                            fclose(status_file);
                        }
                        timelapse = 0;
                        puts("Timelapse stopped");
                    }
                } else if ((readbuf[0] == 'p') && (readbuf[1] == 'x')) {
                    stop_all();
                    readbuf[0] = ' ';
                    readbuf[1] = ' ';
                    readbuf[7] = 0;
                    readbuf[12] = 0;
                    readbuf[15] = 0;
                    readbuf[18] = 0;
                    readbuf[23] = 0;
                    readbuf[length] = 0;
                    video_width = atoi(readbuf);
                    video_height = atoi(readbuf + 8);
                    video_fps = atoi(readbuf + 13);
                    MP4Box_fps = atoi(readbuf + 16);
                    image_width = atoi(readbuf + 19);
                    image_height = atoi(readbuf + 24);
                    start_all();
                    puts("Changed resolutions and framerates");
                } else if ((readbuf[0] == 'a') && (readbuf[1] == 'n')) {
                    readbuf[0] = ' ';
                    readbuf[1] = ' ';
                    readbuf[length] = 0;
                    asprintf(&cset.annotation, "%s", readbuf + 3);
                    puts("Annotation changed");
                } else if ((readbuf[0] == 'a') && (readbuf[1] == 'b')) {
                    if (readbuf[3] == '0') {
                        cset.annback = 0;
                    } else {
                        cset.annback = 1;
                    }
                    puts("Annotation background changed.");
                } else if ((readbuf[0] == 's') && (readbuf[1] == 'h')) {
                    readbuf[0] = ' ';
                    readbuf[1] = ' ';
                    readbuf[length] = 0;
                    cset.sharpness = atoi(readbuf);
                    cam_set_sharpness();
                    printf("Sharpness: %d\n", cset.sharpness);
                } else if ((readbuf[0] == 'c') && (readbuf[1] == 'o')) {
                    readbuf[0] = ' ';
                    readbuf[1] = ' ';
                    readbuf[length] = 0;
                    cset.contrast = atoi(readbuf);
                    cam_set_contrast();
                    printf("Contrast: %d\n", cset.contrast);
                } else if ((readbuf[0] == 'b') && (readbuf[1] == 'r')) {
                    readbuf[0] = ' ';
                    readbuf[1] = ' ';
                    readbuf[length] = 0;
                    cset.brightness = atoi(readbuf);
                    cam_set_brightness();
                    printf("Brightness: %d\n", cset.brightness);
                } else if ((readbuf[0] == 's') && (readbuf[1] == 'a')) {
                    readbuf[0] = ' ';
                    readbuf[1] = ' ';
                    readbuf[length] = 0;
                    cset.saturation = atoi(readbuf);
                    cam_set_saturation();
                    printf("Saturation: %d\n", cset.saturation);
                } else if ((readbuf[0] == 'i') && (readbuf[1] == 's')) {
                    readbuf[0] = ' ';
                    readbuf[1] = ' ';
                    readbuf[length] = 0;
                    cset.iso = atoi(readbuf);
                    cam_set_iso();
                    printf("ISO: %d\n", cset.iso);
                } else if ((readbuf[0] == 'v') && (readbuf[1] == 's')) {
                    if (readbuf[3] == '1')
                        cset.vs = 1;
                    else
                        cset.vs = 0;
                    cam_set_vs();
                    puts("Changed video stabilisation");
                } else if ((readbuf[0] == 'r') && (readbuf[1] == 'l')) {
                    if (readbuf[3] == '1')
                        cset.raw = 1;
                    else
                        cset.raw = 0;
                    cam_set_raw();
                    puts("Changed raw layer");
                } else if ((readbuf[0] == 'e') && (readbuf[1] == 'c')) {
                    readbuf[0] = ' ';
                    readbuf[1] = ' ';
                    readbuf[length] = 0;
                    cset.ec = atoi(readbuf);
                    cam_set_ec();
                    printf("Exposure compensation: %d\n", cset.ec);
                } else if ((readbuf[0] == 'e') && (readbuf[1] == 'm')) {
                    readbuf[length] = 0;
                    sprintf(cset.em, "%s", readbuf + 3);
                    cam_set_em();
                    puts("Exposure mode changed");
                } else if ((readbuf[0] == 'w') && (readbuf[1] == 'b')) {
                    readbuf[length] = 0;
                    sprintf(cset.wb, "%s", readbuf + 3);
                    cam_set_wb();
                    puts("White balance changed");
                } else if ((readbuf[0] == 'm') && (readbuf[1] == 'm')) {
                    readbuf[length] = 0;
                    sprintf(cset.mm, "%s", readbuf + 3);
                    cam_set_mm();
                    puts("Metering mode changed");
                } else if ((readbuf[0] == 'i') && (readbuf[1] == 'e')) {
                    readbuf[length] = 0;
                    sprintf(cset.ie, "%s", readbuf + 3);
                    cam_set_ie();
                    puts("Image effect changed");
                } else if ((readbuf[0] == 'c') && (readbuf[1] == 'e')) {
                    readbuf[4] = 0;
                    readbuf[8] = 0;
                    readbuf[length] = 0;
                    cset.ce_en = atoi(readbuf + 3);
                    cset.ce_u = atoi(readbuf + 5);
                    cset.ce_v = atoi(readbuf + 9);
                    cam_set_ce();
                    puts("Colour effect changed");
                } else if ((readbuf[0] == 'r') && (readbuf[1] == 'o')) {
                    readbuf[0] = ' ';
                    readbuf[1] = ' ';
                    readbuf[length] = 0;
                    cset.rotation = atoi(readbuf);
                    cam_set_rotation();
                    printf("Rotation: %d\n", cset.rotation);
                } else if ((readbuf[0] == 'f') && (readbuf[1] == 'l')) {
                    if (readbuf[3] == '0') {
                        cset.hflip = 0;
                        cset.vflip = 0;
                    } else if (readbuf[3] == '1') {
                        cset.hflip = 1;
                        cset.vflip = 0;
                    } else if (readbuf[3] == '2') {
                        cset.hflip = 0;
                        cset.vflip = 1;
                    } else {
                        cset.hflip = 1;
                        cset.vflip = 1;
                    }
                    cam_set_flip();
                    puts("Flip changed");
                } else if ((readbuf[0] == 'r') && (readbuf[1] == 'i')) {
                    readbuf[8] = 0;
                    readbuf[14] = 0;
                    readbuf[20] = 0;
                    readbuf[length] = 0;
                    cset.roi_x = strtoull(readbuf + 3, NULL, 0);
                    cset.roi_y = strtoull(readbuf + 9, NULL, 0);
                    cset.roi_w = strtoull(readbuf + 15, NULL, 0);
                    cset.roi_h = strtoull(readbuf + 21, NULL, 0);
                    cam_set_roi();
                    puts("Changed Sensor Region");
                } else if ((readbuf[0] == 's') && (readbuf[1] == 's')) {
                    readbuf[0] = ' ';
                    readbuf[1] = ' ';
                    readbuf[length] = 0;
                    cset.ss = strtoull(readbuf, NULL, 0);
                    cam_set_ss();
                    printf("Shutter Speed: %lu\n", cset.ss);
                } else if ((readbuf[0] == 'q') && (readbuf[1] == 'u')) {
                    readbuf[0] = ' ';
                    readbuf[1] = ' ';
                    readbuf[length] = 0;
                    cset.quality = atoi(readbuf);
                    cam_set_quality();
                    printf("Quality: %d\n", cset.quality);
                } else if ((readbuf[0] == 'b') && (readbuf[1] == 'i')) {
                    readbuf[0] = ' ';
                    readbuf[1] = ' ';
                    readbuf[length] = 0;
                    cset.bitrate = strtoull(readbuf, NULL, 0);
                    cam_set_bitrate();
                    printf("Bitrate: %lu\n", cset.bitrate);
                } else if ((readbuf[0] == 'r') && (readbuf[1] == 'u')) {
                    if (readbuf[3] == '0') {
                        stop_all();
                        idle = 1;
                        puts("Stream halted");
                        if (status_filename != 0) {
                            status_file = fopen(status_filename, "w");
                            fputs("halted", status_file);
                            fclose(status_file);
                        }
                    } else {
                        start_all();
                        idle = 0;
                        puts("Stream continued");
                        if (status_filename != 0) {
                            status_file = fopen(status_filename, "w");
                            fputs("ready", status_file);
                            fclose(status_file);
                        }
                    }
                } else if ((readbuf[0] == 'm') && (readbuf[1] == 'd')) {
                    if (readbuf[3] == '0') {
                        motion_detection = 0;
                        if (system("pkill motion") < 0) {
                            error("Could not stop Motion", __function__, __LINE__);
                        }
                        puts("Motion detection stopped");
                        if (status_filename != 0) {
                            status_file = fopen(status_filename, "w");
                            fputs("ready", status_file);
                            fclose(status_file);
                        }
                    } else {
                        motion_detection = 1;
                        if (system("motion") < 0) {
                            error("Could not start Motion", __function__, __LINE__);
                        }
                        printf("Motion detection started\n");
                        if (status_filename != 0) {
                            status_file = fopen(status_filename, "w");
                            fputs("md_ready", status_file);
                            fclose(status_file);
                        }
                    }
                }
            }

        }
        if (timelapse) {
            gettimeofday(&now, NULL);
            timersub(&now, &prev, &delta);
            if (timercmp(&delta, &interval, >)) {
                if (capturing == 0) {
                    capt_img();
                }
                gettimeofday(&prev, NULL);
            }
        }
        usleep(100000);
    }

    puts("SIGINT/SIGTERM received, stopping");

    // tidy up
    if (!idle) {
        stop_all();
    }

    return 0;
}

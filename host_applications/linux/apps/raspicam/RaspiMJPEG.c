/*
Copyright (c) 2013, Broadcom Europe Ltd
Copyright (c) 2013, Silvan Melchior
Copyright (c) 2013, James Hughes
Copyright (c) 2014, Ralf Schmidt
Copyright (c) 2015, Robert Tidey
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

/* Command line program to capture a camera video stream and encode it to file.
Also optionally stream a preview of current camera input with MJPEG.

RaspiMJPEG is an OpenMAX-Application based on the mmal-library, which is
comparable to and inspired by RaspiVid and RaspiStill.  RaspiMJPEG can record
1080p 30fps videos and 5 Mpx images into a file.  Instead of showing the preview
on a screen, RaspiMJPEG streams the preview as MJPEG into a file.  The
update-rate and the size of the preview are customizable with parameters and
independent of the image/video.  Once started, the application receives commands
with a unix-pipe and showes its status on stdout and writes it into a
status-file. The program terminates itself after receiving a SIGINT or SIGTERM.

Usage information is in README_RaspiMJPEG.md


General connection overview:

Camera Port      OUT -->  IN       OUT --> IN             ATTACHED
--------------------------------------------------------------------------------
0 / preview --> image resizer --> JPEG encoder 1 <-- callback 1 to save JPEG
1 / video                     --> H264 encoder   <-- callback to save video file
2 / stills                    --> JPEG encoder 2 <-- callback 2 to save JPEG */

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
#include <dirent.h>
#include <unistd.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <sys/statvfs.h>
#include <errno.h>
#include <sysexits.h>

#include "bcm_host.h"
#include "interface/vcos/vcos.h"
#include "interface/mmal/mmal.h"
#include "interface/mmal/mmal_logging.h"
#include "interface/mmal/mmal_buffer.h"
#include "interface/mmal/util/mmal_util.h"
#include "interface/mmal/util/mmal_util_params.h"
#include "interface/mmal/util/mmal_default_components.h"
#include "interface/mmal/util/mmal_connection.h"

#include "RaspiMJPEG.h"

MMAL_STATUS_T status;
/* time_t currTime; */
struct tm *gmTime;
struct timespec currTime;
char readbuf[FIFO_MAX][2 * MAX_COMMAND_LEN], header_bytes[29];

int cb_len, cb_wptr, cb_wrap, iframe_buff[IFRAME_BUFSIZE], iframe_buff_wpos,
    iframe_buff_rpos, header_wptr, fd[FIFO_MAX], readi[FIFO_MAX],
    time_between_pic, motion_width, motion_height,
    motion_img_width, motion_img_height, motion_frame_count, motion_changes,
    motion_state, vector_buffer_index, mask_valid;
unsigned int video_frame;
char *box_files[MAX_BOX_FILES], *cfg_strd[KEY_COUNT + 1],
    *cfg_stru[KEY_COUNT + 1];
unsigned char *vector_buffer, *mask_buffer_mem, *mask_buffer;
long int cfg_val[KEY_COUNT + 1];

MMAL_COMPONENT_T *camera = NULL, *jpegencoder = NULL, *jpegencoder2 = NULL,
    *h264encoder = NULL, *resizer = NULL, *null_sink = NULL,
    *splitter = NULL;
MMAL_CONNECTION_T *con_cam_pre = NULL, *con_spli_res = NULL, *con_spli_h264 = NULL,
    *con_cam_res = NULL, *con_res_jpeg = NULL, *con_cam_h264 = NULL,
    *con_cam_jpeg = NULL;
MMAL_POOL_T *pool_jpegencoder = NULL, *pool_jpegencoder_in = NULL,
    *pool_jpegencoder2 = NULL, *pool_h264encoder = NULL;
FILE *jpegoutput_file = NULL, *jpegoutput2_file = NULL,
    *h264output_file = NULL, *status_file = NULL, *vector_file = NULL;
int box_head = 0, box_tail = 0;
char *cb_buff = NULL, *filename_recording = NULL, *filename_image = NULL,
    *jpeg_filename = NULL, *jpeg2_filename = NULL, *h264_filename = NULL,
    *pipe_filename = NULL, *status_filename = NULL, *space_limit = NULL;
char jpeg2_root = 0;
unsigned char timelapse = 0, mp4box = 0, autostart = 1, quality = 85,
    idle = 0, capturing = 0, motion_detection = 0, a_error = 0, v_capturing = 0,
    i_capturing = 0, v_boxing = 0, buffering = 0, buffering_toggle = 0;
unsigned int tl_cnt = 0, mjpeg_cnt = 0, width = 320, divider = 5, image_cnt = 0,
    image2_cnt = 0, video_cnt = 0, lapse_cnt = 0, video_stoptime = 0,
    video_width = 1920, video_height = 1080, video_fps = 25, MP4Box_fps = 25,
    image_width = 2592, image_height = 1944;
volatile int running = 1;

struct cam_settings cset = {
    0, 0, 50, 0, 0, 0, 0, 0, 85, 0, 0, 128, 128, 0, 0, 0, "auto", "auto",
    "none", "average", 17000000, 0, 0, 65536, 65536, 0, NULL,
};

PORT_USERDATA callback_data;

char *cfg_key[] = { "annotation", "anno_background",
    "anno3_custom_background_colour", "anno3_custom_background_Y",
    "anno3_custom_background_U", "anno3_custom_background_V",
    "anno3_custom_text_colour", "anno3_custom_text_Y", "anno3_custom_text_U",
    "anno3_custom_text_V", "anno_text_size", "sharpness", "contrast",
    "brightness", "saturation", "iso", "metering_mode", "video_stabilisation",
    "exposure_compensation", "exposure_mode", "white_balance", "image_effect",
    "autowbgain_r", "autowbgain_b", "colour_effect_en", "colour_effect_u",
    "colour_effect_v", "rotation", "hflip", "vflip", "sensor_region_x",
    "sensor_region_y", "sensor_region_w", "sensor_region_h", "video_width",
    "video_height", "video_fps", "video_bitrate", "video_buffer", "video_split",
    "MP4Box", "MP4Box_fps", "boxing_path", "MP4Box_cmd", "image_width",
    "image_height", "image_quality", "tl_interval", "base_path", "preview_path",
    "image_path", "lapse_path", "video_path", "status_file", "control_file",
    "media_path", "macros_path", "subdir_char", "thumb_gen", "autostart",
    "motion_detection", "motion_file", "vector_preview", "vector_mode",
    "motion_external", "motion_noise", "motion_threshold", "motion_image",
    "motion_startframes", "motion_stopframes", "motion_pipe", "motion_clip",
    "motion_logfile", "user_config", "log_file", "log_size",
    "watchdog_interval", "watchdog_errors", "h264_buffer_size", "h264_buffers",
    "callback_timeout", "error_soft",  "error_hard",  "start_img",  "end_img",
    "start_vid",  "end_vid",  "end_box",  "do_cmd", "motion_event", "startstop",
    "camera_num", "stat_pass", "user_annotate", "count_format", "minimise_frag",
    "mmal_logfile", "stop_pause" };

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
    exit(EX_SOFTWARE);
}

void term(int signum) {
    running = 0;
}

void set_counts() {
    image2_cnt = findNextCount(cfg_stru[c_image_path], "it");
    video_cnt = findNextCount(cfg_stru[c_video_path], "v");
}

int getKey(char *key) {
    int i;

    for (i = 0; i < KEY_COUNT; i++) {
        if (!strcmp(key, cfg_key[i])) {
            return i;
        }
    }
    return KEY_COUNT;
}

void addValue(int keyI, char *value, int both) {
    int val;

    free(cfg_stru[keyI]);
    cfg_stru[keyI] = NULL;

    if (both) {
        free(cfg_strd[keyI]);
        cfg_strd[keyI] = NULL;
    }

    if (value == NULL || !value[0]) {
        cfg_val[keyI] = NULL;
    } else {
        val = strtol(value, NULL, 10);
        asprintf(&cfg_stru[keyI], "%s", value);
        if (both) {
            asprintf(&cfg_strd[keyI], "%s", value);
        }
        if (!strcmp(value, "true")) {
            val = 1;
        } else if (!strcmp(value, "false")) {
            val = 0;
        }
        switch (keyI) {
            case c_autostart:
                if (!strcmp(value, "idle")) {
                    val = 0;
                    idle = 1;
                } else if (!strcmp(value, "standard")) { 
                    val = 1;
                    idle = 0;
                }
                updateStatus();
                break;
            case c_MP4Box:
                if (!strcmp(value, "background")) {
                    val = 2;
                }
        }
        cfg_val[keyI] = val;
    }
}

void addUserValue(int key, char *value){
    DPRINTF(1, "Change: %s = %s\n", cfg_key[key], value);
    addValue(key, value, 0);
}

void saveUserConfig(char *cfilename) {
    FILE *fp;
    int i;

    fp = fopen(cfilename, "w");
    if (fp != NULL) {
        for (i = 0; i < KEY_COUNT; i++) {
            if (cfg_key[i][0]) {
                if ((cfg_stru[i] == NULL) && (cfg_strd[i] == NULL)) {
                    next;
                }
                if (cfg_stru[i] == NULL) {
                    fprintf(fp, "%s\n", cfg_key[i]);
                } else if ((cfg_strd[i] == NULL) ||
                    strcmp(cfg_strd[i], cfg_stru[i])) {
                    fprintf(fp, "%s %s\n", cfg_key[i], cfg_stru[i]);
                }
            }
        }
        fclose(fp);
    }
}

void read_config(char *cfilename, int type) {
    FILE *fp;
    int length;
    int key;
    unsigned int len = 0;
    char *line = NULL;
    char *value = NULL;
    int lineno = 0;

    fp = fopen(cfilename, "r");
    if (fp != NULL) {
        // XXX dike this out and use fgets like a normal human being
        while ((length = getline(&line, &len, fp)) != -1) {
            lineno++;
            if (length > 3 && *line != '#') {
                line[length - 1] = 0;
                value = strchr(line, ' ');
                if (value != NULL) {
                    // split line into key, value
                    *value = 0;
                    value++;
                }
                key = getKey(line);
                if (key < KEY_COUNT) {
                    if (key != c_annotation) {
                        value = trim(value);
                    }
                    addValue(key, value, type);
                } else {
                    fprintf(stderr,
                        "Unknown command in config file at line %d: %s\n",
                        lineno, line);
                }
            }
        }
        if (line != NULL) {
            free(line);
            line = NULL;
        }
    }    
}

void checkPipe(int pipe) {
    char *lf;
    int length, hPipe;

    hPipe = fd[pipe];
    if (hPipe >= 0) {
        length = read(hPipe, readbuf[pipe] + readi[pipe], MAX_COMMAND_LEN - 2);
        if (length > 0) readi[pipe] +=length;

        if (readi[pipe] != 0) {
            lf = strchr(readbuf[pipe], 10);
            if (lf != NULL) {
                *lf = 0;
                length = lf - readbuf[pipe];
                readi[pipe] -= length + 1;
                process_cmd(readbuf[pipe], length);
                length = readbuf[pipe] + 2 * MAX_COMMAND_LEN - 1 - lf;
                strncpy(readbuf[pipe], lf + 1, length);
            } else {
                if (length == 0) {
                    process_cmd(readbuf[pipe], readi[pipe]);
                    readi[pipe] = 0;			
                }
            }
        }
    }
}

static void camera_control_callback(MMAL_PORT_T *port,
    MMAL_BUFFER_HEADER_T *buffer) {
    TESTERR(buffer->cmd != MMAL_EVENT_PARAMETER_CHANGED,
        "Camera sent invalid data");
    mmal_buffer_header_release(buffer);
}

static void jpegencoder_buffer_callback(MMAL_PORT_T *port,
    MMAL_BUFFER_HEADER_T *buffer) {
    char *filename_temp, *filename_temp2;
    int bytes_written = buffer->length;
    MMAL_STATUS_T status = MMAL_SUCCESS;
    MMAL_BUFFER_HEADER_T *new_buffer;

    if (mjpeg_cnt == 0) {
        if (jpegoutput_file == NULL) {
            asprintf(&filename_temp, cfg_stru[c_preview_path], image_cnt);
            asprintf(&filename_temp2, "%s.part", filename_temp);
            jpegoutput_file = fopen(filename_temp2, "wb");
            free(filename_temp);
            filename_temp = NULL;
            free(filename_temp2);
            filename_temp2 = NULL;
            TESTERR(jpegoutput_file == NULL, "Could not open mjpeg-destination");
        }
        if (buffer->length) {
            mmal_buffer_header_mem_lock(buffer);
            bytes_written = fwrite(buffer->data, 1, buffer->length,
                jpegoutput_file);
            mmal_buffer_header_mem_unlock(buffer);
        }
        TESTERR(bytes_written != buffer->length,
            "Could not write all bytes to jpeg");
    }

    if (buffer->flags & (MMAL_BUFFER_HEADER_FLAG_FRAME_END |
        MMAL_BUFFER_HEADER_FLAG_TRANSMISSION_FAILED)) {
        mjpeg_cnt++;
        video_frame++;
        if (video_frame >= cfg_val[c_video_fps]) {
            video_frame = 0;
        }
        if (mjpeg_cnt == cfg_val[c_divider]) {
            if (jpegoutput_file != NULL) {
                fclose(jpegoutput_file);
                jpegoutput_file = NULL;
                asprintf(&filename_temp, cfg_stru[c_preview_path], image_cnt);
                asprintf(&filename_temp2, "%s.part", filename_temp);
                rename(filename_temp2, filename_temp);
                free(filename_temp);
                free(filename_temp2);
            }
            image_cnt++;
            mjpeg_cnt = 0;
            cam_set_annotation();
        }
    }

    mmal_buffer_header_release(buffer);

    if (port->is_enabled) {
        new_buffer = mmal_queue_get(pool_jpegencoder->queue);
        if (new_buffer != NULL) {
            status = mmal_port_send_buffer(port, new_buffer);
        }
        TESTERR((new_buffer == NULL) || (status != MMAL_SUCCESS),
            "Could not send buffers to port");
    } else {
        DPRINTF(1, "%s: %d: ERROR: port disabled, could not get/send buffer\n");
    }
}

static void jpegencoder2_buffer_callback(MMAL_PORT_T *port,
    MMAL_BUFFER_HEADER_T *buffer) {
    MMAL_BUFFER_HEADER_T *new_buffer;
    int complete = 0;
    MMAL_STATUS_T status = MMAL_SUCCESS;
    int bytes_written = buffer->length;
    PORT_USERDATA *pData = (PORT_USERDATA *)port->userdata;

    if (pData != NULL) {
        if (buffer->length) {
            mmal_buffer_header_mem_lock(buffer);
            if (jpegoutput2_file != NULL) {
                bytes_written = fwrite(buffer->data, 1, buffer->length,
                    jpegoutput2_file);
            } else {
                bytes_written = 0
            }
            mmal_buffer_header_mem_unlock(buffer);
        }
        if (bytes_written != buffer->length) {
            complete = 1;
            DPERROR(1, "Could not write all bytes");
        }

        if (buffer->flags & (MMAL_BUFFER_HEADER_FLAG_FRAME_END |
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
    if (buffer->flags & (MMAL_BUFFER_HEADER_FLAG_FRAME_END |
            MMAL_BUFFER_HEADER_FLAG_TRANSMISSION_FAILED)) {
        complete = 1;
        capturing = 0;
    }

    mmal_buffer_header_release(buffer);

    if (port->is_enabled) {
        new_buffer = mmal_queue_get(pool_jpegencoder2->queue);
        if (new_buffer != NULL) {
            status = mmal_port_send_buffer(port, new_buffer);
        }
        TESTERR((new_buffer == NULL) || (status != MMAL_SUCCESS),
            "Could not send buffers to port");
    } else {
        DPRINTF(1, "%s: %d: ERROR: port disabled, could not get/send buffer\n");
    }
    if (complete) {
        vcos_semaphore_post(&(pData->complete_semaphore));
    }
}

static void h264encoder_buffer_callback(MMAL_PORT_T *port,
    MMAL_BUFFER_HEADER_T *buffer) {
    int i, p, row, col;
    MMAL_BUFFER_HEADER_T *new_buffer;
    int bytes_written = buffer->length;
    int space_in_buff = cb_len - cb_wptr;
    int copy_to_end = space_in_buff > buffer->length ? buffer->length : space_in_buff;
    int copy_to_start = buffer->length - copy_to_end;
    MMAL_STATUS_T status = MMAL_SUCCESS;
    static int frame_start = -1, no_iframe_bytes = 0, iframe_requested = 0,
        no_buffer = 0;

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
        new_buffer = mmal_queue_get(pool_h264encoder->queue);
        if (new_buffer != NULL) {
            status = mmal_port_send_buffer(port, new_buffer);
        }
        if ((new_buffer != NULL) || (status != MMAL_SUCCESS)) {
            DPERROR(1, "Could not send buffers to port");
        }
    }
}

inline void cam_set_sharpness() {
    MMAL_RATIONAL_T value = { cset.sharpness, 100 };

    status = mmal_port_parameter_set_rational(camera->control,
        MMAL_PARAMETER_SHARPNESS, value);
    MMAL_STATUS("Could not set sharpness");
}

inline void cam_set_contrast() {
    MMAL_RATIONAL_T value = { cset.contrast, 100 };

    status = mmal_port_parameter_set_rational(camera->control,
        MMAL_PARAMETER_CONTRAST, value);
    MMAL_STATUS("Could not set contrast");
}

inline void cam_set_brightness() {
    MMAL_RATIONAL_T value = { cset.brightness, 100 };

    status = mmal_port_parameter_set_rational(camera->control,
        MMAL_PARAMETER_BRIGHTNESS, value);
    MMAL_STATUS("Could not set brightness");
}

inline void cam_set_saturation() {
    MMAL_RATIONAL_T value = { cset.saturation, 100 };

    status = mmal_port_parameter_set_rational(camera->control,
        MMAL_PARAMETER_SATURATION, value);
    MMAL_STATUS("Could not set saturation");
}

inline void cam_set_iso() {
    status = mmal_port_parameter_set_uint32(camera->control,
        MMAL_PARAMETER_ISO, cset.iso);
    MMAL_STATUS("Could not set ISO");
}

inline void cam_set_vs() {
    status = mmal_port_parameter_set_boolean(camera->control,
        MMAL_PARAMETER_VIDEO_STABILISATION, cset.vs);
    MMAL_STATUS("Could not set video stabilisation");
}

inline void cam_set_ec() {
    status = mmal_port_parameter_set_int32(camera->control,
        MMAL_PARAMETER_EXPOSURE_COMP, cset.ec);
    MMAL_STATUS("Could not set exposure compensation");
}

inline void cam_set_em() {
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
        DPRINTF(1, "Invalid exposure mode: %s\n", cset.em);
        exit(EX_CONFIG);
    }
    status = mmal_port_parameter_set(camera->control, &exp);
    MMAL_STATUS("Could not set exposure mode");
}

inline void cam_set_wb() {
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
        DPRINTF(1, "Invalid white balance: %s\n", cset.wb);
        exit(EX_CONFIG);
    }
    status = mmal_port_parameter_set(camera->control, &param.hdr);
    MMAL_STATUS("Could not set white balance");
}

inline void cam_set_mm() {
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
        DPRINTF(1, "Invalid metering mode: %s\n", cset.mm);
        exit(EX_CONFIG);
    }
    status = mmal_port_parameter_set(camera->control, &m_mode);
    MMAL_STATUS("Could not set metering mode");
}

inline void cam_set_ie() {
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
        DPRINTF(1, "Invalid image effect: %s\n", cset.ie);
        exit(EX_CONFIG);
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
    MMAL_STATUS("Could not set flip (" SS(PREVIEW_PORT) ")");
    status = mmal_port_parameter_set(camera->output[VIDEO_PORT], &mirror);
    MMAL_STATUS("Could not set flip (" SS(VIDEO_PORT) ")");
    status = mmal_port_parameter_set(camera->output[CAPTURE_PORT], &mirror.hdr);
    MMAL_STATUS("Could not set flip (" SS(CAPTURE_PORT) ")");
}

void cam_set_roi() {
    MMAL_PARAMETER_INPUT_CROP_T crop = {
        { MMAL_PARAMETER_INPUT_CROP, sizeof (MMAL_PARAMETER_INPUT_CROP_T) }
    };
    crop.rect.x = cset.roi_x;
    crop.rect.y = cset.roi_y;
    crop.rect.width = cset.roi_w;
    crop.rect.height = cset.roi_h;
    status = mmal_port_parameter_set(camera->control, &crop);
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
    MMAL_STATUS("Could not set bitrate");
}

/* Checks if specified port is valid and enabled, then disables it.
port  Pointer to the port */
static void check_disable_port(MMAL_PORT_T *port) {
    if ((port != NULL) && port->is_enabled) {
        mmal_port_disable(port);
    }
}

void cam_set_annotation() {
    MMAL_PARAMETER_CAMERA_ANNOTATE_V3_T anno = { {
        MMAL_PARAMETER_ANNOTATE, sizeof (MMAL_PARAMETER_CAMERA_ANNOTATE_V3_T)
    } };
    char *filename_temp = NULL;
    int prev_sec = gmTime->tm_sec;

    if (cfg_stru[c_annotation]) {
        currTime = time(NULL);
        gmTime = gmtime(&currTime);
        if (localTime->tm_sec != prev_sec) {
            video_frame = 0;
        }
        asprintf(&filename_temp, cset.annotation,
            gmTime->tm_year + 1900, gmTime->tm_mon + 1,
            gmTime->tm_mday, gmTime->tm_hour, gmTime->tm_min,
            gmTime->tm_sec);
        strcpy(anno.text, filename_temp);
        free(filename_temp);
        anno.enable = MMAL_TRUE;
        anno.show_shutter = 0;
        anno.show_analog_gain = 0;
        anno.show_lens = 0;
        anno.show_caf = 0;
        anno.show_motion = 0;
        anno.enable_text_background = cfg_val[c_anno_background];
        anno.custom_background_colour = cfg_val[c_anno3_custom_background_colour];
        anno.custom_background_Y = cfg_val[c_anno3_custom_background_Y];
        anno.custom_background_U = cfg_val[c_anno3_custom_background_U];
        anno.custom_background_V = cfg_val[c_anno3_custom_background_V];
        anno.custom_text_colour = cfg_val[c_anno3_custom_text_colour];
        anno.custom_text_Y = cfg_val[c_anno3_custom_text_Y];
        anno.custom_text_U = cfg_val[c_anno3_custom_text_U];
        anno.custom_text_V = cfg_val[c_anno3_custom_text_V];
        anno.text_size = cfg_val[c_anno_text_size];
    } else {
        anno.enable = MMAL_FALSE;
    }


    status = mmal_port_parameter_set(camera->control, &anno);
    MMAL_STATUS("Could not set annotation");
}

void start_all(int load_conf) {
    int max, i, h264_size;
    unsigned int height_temp;
    MMAL_ES_FORMAT_T *format;
    VCOS_STATUS_T vcos_status;
    MMAL_BUFFER_HEADER_T *jpegbuffer2;
    MMAL_PARAMETER_INT32_T cam_num = { {
        MMAL_PARAMETER_CAMERA_NUM, sizeof (MMAL_PARAMETER_INT32_T)
    } };
    MMAL_PARAMETER_UINT32_T veiq = { {
        MMAL_PARAMETER_VIDEO_ENCODE_INITIAL_QUANT,
        sizeof (MMAL_PARAMETER_UINT32_T)
    }, 25 }, veqp = { {
        MMAL_PARAMETER_VIDEO_ENCODE_QP_P, sizeof (MMAL_PARAMETER_UINT32_T)
    }, 31 };
    MMAL_PARAMETER_CAMERA_CONFIG_T cam_config = { {
        MMAL_PARAMETER_CAMERA_CONFIG,
        sizeof (MMAL_PARAMETER_CAMERA_CONFIG_T)
    } };
    MMAL_PARAMETER_VIDEO_PROFILE_T vp = {
        { MMAL_PARAMETER_PROFILE, sizeof (MMAL_PARAMETER_VIDEO_PROFILE_T) },
        { MMAL_VIDEO_PROFILE_H264_HIGH, MMAL_VIDEO_LEVEL_H264_4 }
    };

    set_counts();

    // reload config if requested
    if (load_conf != 0) {
        read_config(MJPG_DEF_CFG_FILE, 1);
        if (cfg_stru[c_user_config]) {
            read_config(cfg_stru[c_user_config],0);
        }
    }

    // create camera
    status = mmal_component_create(MMAL_COMPONENT_DEFAULT_CAMERA, &camera);
    MMAL_STATUS("Could not create camera");

    if (cfg_val[c_camera_num] > 0) {
        cam_num.value = cfg_val[c_camera_num] - 1;
        status = mmal_port_parameter_set(camera->control, &cam_num.hdr);
        MMAL_STATUS("Could not select camera");
        if (!camera->output_num) {
            status = MMAL_ENOSYS;
            error("Camera doesn't have output ports", __function__, __LINE__);
        }
    }
    status = mmal_port_enable(camera->control, camera_control_callback);
    MMAL_STATUS("Could not enable camera control port");

    cam_config.max_stills_w = cfg_val[c_image_width];
    cam_config.max_stills_h = cfg_val[c_image_height];
    cam_config.stills_yuv422 = 0;
    cam_config.one_shot_stills = 1;
    cam_config.max_preview_video_w = cfg_val[c_video_width];
    cam_config.max_preview_video_h = cfg_val[c_video_height];
    cam_config.num_preview_video_frames = 3;
    cam_config.stills_capture_circular_buffer_height = 0;
    cam_config.fast_preview_resume = 0;
    cam_config.use_stc_timestamp = MMAL_PARAM_TIMESTAMP_MODE_RESET_STC;
    mmal_port_parameter_set(camera->control, &cam_config);

    format = camera->output[PREVIEW_PORT]->format;
    format->es->video.width = VCOS_ALIGN_UP(cfg_val[c_video_width], 32);
    format->es->video.height = VCOS_ALIGN_UP(cfg_val[c_video_height], 16);
    format->es->video.crop.x = 0;
    format->es->video.crop.y = 0;
    format->es->video.crop.width = cfg_val[c_video_width];
    format->es->video.crop.height = cfg_val[c_video_height];
    format->es->video.frame_rate.num = 0;
    format->es->video.frame_rate.den = 1;
    status = mmal_port_format_commit(camera->output[PREVIEW_PORT]);
    MMAL_STATUS("Could not set preview format");

    format = camera->output[VIDEO_PORT]->format;
    format->encoding_variant = MMAL_ENCODING_I420;
    format->encoding = MMAL_ENCODING_OPAQUE;
    format->es->video.width = VCOS_ALIGN_UP(cfg_val[c_video_width], 32);
    format->es->video.height = VCOS_ALIGN_UP(cfg_val[c_video_height], 16);
    format->es->video.crop.x = 0;
    format->es->video.crop.y = 0;
    format->es->video.crop.width = cfg_val[c_video_width];
    format->es->video.crop.height = cfg_val[c_video_height];
    format->es->video.frame_rate.num = cfg_val[c_video_fps];
    format->es->video.frame_rate.den = 1;
    status = mmal_port_format_commit(camera->output[VIDEO_PORT]);
    MMAL_STATUS("Could not set video format");
    if (camera->output[VIDEO_PORT]->buffer_num < 3) {
        camera->output[VIDEO_PORT]->buffer_num = 3;
    }

    format = camera->output[CAPTURE_PORT]->format;
    format->encoding = MMAL_ENCODING_OPAQUE;
    format->es->video.width = VCOS_ALIGN_UP(cfg_val[c_image_width], 32);
    format->es->video.height = VCOS_ALIGN_UP(cfg_val[c_image_height], 16);
    format->es->video.crop.x = 0;
    format->es->video.crop.y = 0;
    format->es->video.crop.width = cfg_val[c_image_width];
    format->es->video.crop.height = cfg_val[c_image_height];
    format->es->video.frame_rate.num = 0;
    format->es->video.frame_rate.den = 1;
    status = mmal_port_format_commit(camera->output[CAPTURE_PORT]);
    MMAL_STATUS("Could not set still format");
    if (camera->output[CAPTURE_PORT]->buffer_num < 3) {
        camera->output[CAPTURE_PORT]->buffer_num = 3;
    }

    status = mmal_component_enable(camera);
    MMAL_STATUS("Could not enable camera");

    // create jpeg-encoder
    status = mmal_component_create(MMAL_COMPONENT_DEFAULT_IMAGE_ENCODER,
        &jpegencoder);
    TESTERR((status != MMAL_SUCCESS) && (status != MMAL_ENOSYS),
        "Could not create image encoder");

    motion_width = VCOS_ALIGN_UP(cfg_val[c_video_width], 32);
    motion_height = VCOS_ALIGN_UP(cfg_val[c_video_height], 16);

    if (cfg_val[c_vector_preview]) {
        motion_img_width = motion_width;
        motion_img_height = motion_height;
        format = jpegencoder->input[0]->format;
        format->encoding = MMAL_ENCODING_I420;
        format->es->video.width = motion_img_width;
        format->es->video.height = motion_img_height;
        format->es->video.crop.x = 0;
        format->es->video.crop.y = 0;
        format->es->video.crop.width = motion_width;
        format->es->video.crop.height = motion_height;
        format->es->video.frame_rate.num = cfg_val[c_video_fps];
        format->es->video.frame_rate.den = 1;
        format->flags = MMAL_ES_FORMAT_FLAG_FRAMED;
        status = mmal_port_format_commit(jpegencoder->input[0]);
        MMAL_STATUS("Could not set preview image input format");

        jpegencoder->input[0]->buffer_num = jpegencoder->input[0]->buffer_num_min;
        jpegencoder->input[0]->buffer_size = jpegencoder->input[0]->buffer_size_min;
        pool_jpegencoder_in =
            mmal_pool_create(jpegencoder->input[0]->buffer_num,
                jpegencoder->input[0]->buffer_size);
        TESTERR(pool_jpegencoder_in == NULL,
            "Could not create image output buffer pool");
    }

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
    MMAL_STATUS("Could not set image output format");
    status = mmal_port_parameter_set_uint32(jpegencoder->output[0],
        MMAL_PARAMETER_JPEG_Q_FACTOR, cfg_val[c_quality]);
    MMAL_STATUS("Could not set jpeg quality");

    status = mmal_component_enable(jpegencoder);
    MMAL_STATUS("Could not enable image encoder");
    pool_jpegencoder = mmal_port_pool_create(jpegencoder->output[0],
        jpegencoder->output[0]->buffer_num,
        jpegencoder->output[0]->buffer_size);
    TESTERR(!pool_jpegencoder, "Could not create image buffer pool");

    // create second jpeg-encoder
    status = mmal_component_create(MMAL_COMPONENT_DEFAULT_IMAGE_ENCODER,
        &jpegencoder2);
    TESTERR((status != MMAL_SUCCESS) && (status != MMAL_ENOSYS),
        "Could not create image encoder 2");

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
    status = mmal_port_parameter_set_boolean(camera->control,
        MMAL_PARAMETER_CAPTURE_STATS_PASS, cfg_val[c_stat_pass]);
    MMAL_STATUS("Could not set stat_pass");

    status = mmal_component_enable(jpegencoder2);
    MMAL_STATUS("Could not enable image encoder 2");
    pool_jpegencoder2 = mmal_port_pool_create(jpegencoder2->output[0],
        jpegencoder2->output[0]->buffer_num,
        jpegencoder2->output[0]->buffer_size);
    TESTERR(pool_jpegencoder2 == NULL, "Could not create image buffer pool 2");

    // create h264-encoder
    status = mmal_component_create(MMAL_COMPONENT_DEFAULT_VIDEO_ENCODER,
        &h264encoder);
    TESTERR((status != MMAL_SUCCESS) && (status != MMAL_ENOSYS),
        "Could not create video encoder");

    mmal_format_copy(h264encoder->output[0]->format,
        h264encoder->input[0]->format);
    status = mmal_port_parameter_set_boolean(h264encoder->output[0],
        MMAL_PARAMETER_MINIMISE_FRAGMENTATION,
        cfg_val[c_minimise_frag] ? MMAL_TRUE : MMAL_FALSE);
    MMAL_STATUS("Could not set fragmentation false");

    h264encoder->output[0]->format->encoding = MMAL_ENCODING_H264;
    h264encoder->output[0]->format->bitrate = cfg_val[c_video_bitrate];
    DPRINTF(1, "Recommended video buffer size %d\n",
        h264encoder->output[0]->buffer_size_recommended);
    h264_size = cfg_val[c_h264_buffer_size] ? cfg_val[c_h264_buffer_size] : 
        h264encoder->output[0]->buffer_size_recommended;
    if (h264_size < h264encoder->output[0]->buffer_size_min) {
        h264_size = h264encoder->output[0]->buffer_size_min;
    }
    h264encoder->output[0]->buffer_size = h264_size;
    DPRINTF(1, "h264 size set to %d\n", h264_size);
    DPRINTF(1, "recommended video buffers %d\n",
        h264encoder->output[0]->buffer_num_recommended);
    h264encoder->output[0]->buffer_num = cfg_val[c_h264_buffers] ?
        cfg_val[c_h264_buffers] :
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

    status = mmal_port_parameter_set(h264encoder->output[0], &veiq);
    MMAL_STATUS("Could not set video quantisation 1");

    status = mmal_port_parameter_set(h264encoder->output[0], &veqp);
    MMAL_STATUS("Could not set video quantisation 2");

    status = mmal_port_parameter_set(h264encoder->output[0], &vp);
    MMAL_STATUS("Could not set video port format");

    status = mmal_port_parameter_set_boolean(h264encoder->input[0],
        MMAL_PARAMETER_VIDEO_IMMUTABLE_INPUT, 1);
    MMAL_STATUS("Could not set immutable flag");

    status = mmal_port_parameter_set_boolean(h264encoder->output[0],
        MMAL_PARAMETER_VIDEO_ENCODE_INLINE_HEADER, 0);
    MMAL_STATUS("Could not set inline flag");

    status = mmal_port_parameter_set_boolean(h264encoder->output[0],
        MMAL_PARAMETER_VIDEO_ENCODE_INLINE_VECTORS, 1);
    MMAL_STATUS("Could not set motion vector flag");

    status = mmal_component_enable(h264encoder);
    MMAL_STATUS("Could not enable h264encoder");

    pool_h264encoder = mmal_port_pool_create(h264encoder->output[0],
        h264encoder->output[0]->buffer_num,
        h264encoder->output[0]->buffer_size);
    TESTERR(pool_h264encoder == NULL, "Could not create h264 pool");

    // create image-resizer
    height_temp = VCOS_ALIGN_UP(cfg_val[c_width] * cfg_val[c_video_height] /
        cfg_val[c_video_width], 16);
    status = mmal_component_create("vc.ril.resize", &resizer);
    TESTERR((status != MMAL_SUCCESS) && (status != MMAL_ENOSYS)),
        "Could not create image resizer");

    format = resizer->output[0]->format;
    format->es->video.width = cfg_val[c_width];
    format->es->video.height = height_temp;
    format->es->video.width = VCOS_ALIGN_UP(cfg_val[c_width], 32);
    format->encoding = MMAL_ENCODING_I420;
    format->es->video.crop.x = 0;
    format->es->video.crop.y = 0;
    format->es->video.crop.width = cfg_val[c_width];
    format->es->video.crop.height = height_temp;
    format->es->video.frame_rate.num = 30;
    format->es->video.frame_rate.den = 1;
    status = mmal_port_format_commit(resizer->output[0]);
    MMAL_STATUS("Could not set image resizer output");

    status = mmal_component_enable(resizer);
    MMAL_STATUS("Could not enable image resizer");

    // create null-sink
    status = mmal_component_create("vc.null_sink", &null_sink);
    MMAL_STATUS("Could not create null_sink");
    status = mmal_component_enable(null_sink);
    MMAL_STATUS("Could not enable null_sink");

    // create splitter
    status = mmal_component_create(MMAL_COMPONENT_DEFAULT_VIDEO_SPLITTER,
        &splitter);
    TESTERR((status != MMAL_SUCCESS) && (status != MMAL_ENOSYS),
        "Could not create video spltter");
    status = mmal_component_enable(splitter);
    MMAL_STATUS("Could not enable video spltter");

    // connect
    if (!cfg_val[c_vector_preview]) {
        if (cfg_val[c_motion_detection]) {
            status = mmal_connection_create(&con_cam_pre,
                camera->output[PREVIEW_PORT], splitter->input[0],
                MMAL_CONNECTION_FLAG_TUNNELLING |
                MMAL_CONNECTION_FLAG_ALLOCATION_ON_INPUT);
            MMAL_STATUS("Could not create connection camera -> splitter");
            status = mmal_connection_enable(con_cam_pre);
            MMAL_STATUS("Could not enable connection camera -> splitter");

            status = mmal_connection_create(&con_spli_res, splitter->output[0],
                resizer->input[0], MMAL_CONNECTION_FLAG_TUNNELLING |
                MMAL_CONNECTION_FLAG_ALLOCATION_ON_INPUT);
            MMAL_STATUS("Could not create connection splitter -> resizer");
            status = mmal_connection_enable(con_spli_res);
            MMAL_STATUS("Could not enable connection splitter -> resizer");

            status = mmal_connection_create(&con_res_jpeg, resizer->output[0],
                jpegencoder->input[0], MMAL_CONNECTION_FLAG_TUNNELLING |
                MMAL_CONNECTION_FLAG_ALLOCATION_ON_INPUT);
            MMAL_STATUS("Could not create connection resizer -> encoder");
            status = mmal_connection_enable(con_res_jpeg);
            MMAL_STATUS("Could not enable connection resizer -> encoder");

            status = mmal_connection_create(&con_spli_h264, splitter->output[1],
                h264encoder->input[0], MMAL_CONNECTION_FLAG_TUNNELLING |
                MMAL_CONNECTION_FLAG_ALLOCATION_ON_INPUT);
            MMAL_STATUS("Could not create connection splitter -> video converter");
            status = mmal_connection_enable(con_spli_h264);
            MMAL_STATUS("Could not enable connection splitter -> video converter");
        } else {
            status = mmal_connection_create(&con_cam_pre, camera->output[0],
                resizer->input[0], MMAL_CONNECTION_FLAG_TUNNELLING |
                MMAL_CONNECTION_FLAG_ALLOCATION_ON_INPUT);
            MMAL_STATUS("Could not create connection camera -> resizer");
            status = mmal_connection_enable(con_cam_pre);
            MMAL_STATUS("Could not enable connection camera -> resizer");

            status = mmal_connection_create(&con_res_jpeg, resizer->output[0],
                jpegencoder->input[0], MMAL_CONNECTION_FLAG_TUNNELLING |
                MMAL_CONNECTION_FLAG_ALLOCATION_ON_INPUT);
            MMAL_STATUS("Could not create connection resizer -> encoder");
            status = mmal_connection_enable(con_res_jpeg);
            MMAL_STATUS("Could not enable connection resizer -> encoder");
    } else {
        status = mmal_connection_create(&con_cam_pre, camera->output[0],
            h264encoder->input[0], MMAL_CONNECTION_FLAG_TUNNELLING |
            MMAL_CONNECTION_FLAG_ALLOCATION_ON_INPUT);
        MMAL_STATUS("Could not create connection camera -> video converter");
        status = mmal_connection_enable(con_cam_pre);
        MMAL_STATUS("Could not enable connection camera -> video converter");

        status = mmal_port_enable(jpegencoder->input[0],
            jpegencoder_input_callback);
        MMAL_STATUS("Could not enable jpeg input port");
        status = mmal_port_enable(jpegencoder->control,
            jpegencoder_input_callback);
        MMAL_STATUS("Could not enable jpeg control port");
    }

    h264_enable_output();

    status = mmal_port_enable(jpegencoder->output[0],
        jpegencoder_buffer_callback);
    MMAL_STATUS("Could not enable jpeg input port");
    max = mmal_queue_length(pool_jpegencoder->queue);
    for (i = 0; i < max; i++) {
        MMAL_BUFFER_HEADER_T *jpegbuffer =
            mmal_queue_get(pool_jpegencoder->queue);

        TESTERR(jpegbuffer == NULL, "Could not create jpeg buffer header");
        status = mmal_port_send_buffer(jpegencoder->output[0], jpegbuffer);
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

        TESTERR(jpegbuffer2 == NULL, "Could not create jpeg buffer header 2");
        status = mmal_port_send_buffer(jpegencoder2->output[0], jpegbuffer2);
        MMAL_STATUS("Could not send buffers to jpeg port 2");
    }

    // settings
    cam_set_rational(cset.sharpness, MMAL_PARAMETER_SHARPNESS);
    cam_set_contrast();
    cam_set_brightness();
    cam_set_saturation();
    cam_set_iso();
    cam_set_video_stabilisation();
    cam_set_exposure_compensation();
    cam_set_raw_layer();
    cam_set_shutter_speed();
    cam_set_image_quality();
    cam_set_video_buffer();
    cam_set_rotation();
    cam_set_exposure_mode();
    cam_set_white_balance();
    cam_set_metering_mode();
    cam_set_image_effect();
    cam_set_colour_effect_en();
    cam_set_hflip();
    cam_set_autowbgain_r();
    cam_set_roi();
    cam_set_bitrate();
    cam_set_annotation();

    setup_motiondetect();
}

void stop_all(void) {
    // Make sure any current recording is terminated before starting this
    if (v_capturing) {
        stop_video(0);
    }
    cam_stop_buffering();

    // disable components
    if (jpegencoder->output[0]->is_enabled) {
        mmal_port_disable(jpegencoder->output[0]);
    }
    if (cfg_val[c_vector_preview] && jpegencoder->input[0]->is_enabled) {
        mmal_port_disable(jpegencoder->input[0]);
    }
    if (jpegencoder2->output[0]->is_enabled) {
        mmal_port_disable(jpegencoder2->output[0]);
    }
    if (h264encoder->output[0]->is_enabled) {
        mmal_port_disable(h264encoder->output[0]);
    }
    if (con_cam_pre != NULL) {
        mmal_connection_destroy(con_cam_pre);
        con_cam_pre = NULL;
    }
    if (con_spli_res != NULL) {
        mmal_connection_destroy(con_spli_res);
        con_spli_res = NULL;
    }
    if (con_spli_h264 != NULL) {
        mmal_connection_destroy(con_spli_h264);
        con_spli_h264 = NULL;
    }
    if (con_res_jpeg != NULL) {
        mmal_connection_destroy(con_res_jpeg);
        con_res_jpeg = NULL;
    }
    if (con_cam_h264 != NULL) {
        mmal_connection_destroy(con_cam_h264);
        con_cam_h264 = NULL;
    }
    if (con_cam_jpeg != NULL) {
        mmal_connection_destroy(con_cam_jpeg);
        con_cam_jpeg = NULL;
    }
    if (resizer != NULL) {
        mmal_component_disable(resizer);
        mmal_component_destroy(resizer);
        resizer = NULL;
    }
    if (camera != NULL) {
        mmal_component_disable(camera);
        mmal_component_destroy(camera);
        camera = NULL;
    }

    // destroy encoders and remaining components
    if (jpegencoder != NULL) {
        check_disable_port(jpegencoder->output[0]);
        mmal_component_disable(jpegencoder);
        if (pool_jpegencoder != NULL) {
            mmal_port_pool_destroy(jpegencoder->output[0], pool_jpegencoder);
            pool_jpegencoder = NULL;
        }
        mmal_component_destroy(jpegencoder);
        jpegencoder = NULL;
    }
    if (jpegencoder2 != NULL) {
        check_disable_port(jpegencoder2->output[0]);
        mmal_component_disable(jpegencoder2);
        if (pool_jpegencoder2 != NULL) {
            mmal_port_pool_destroy(jpegencoder2->output[0], pool_jpegencoder2);
            pool_jpegencoder2 = NULL;
        }
        mmal_component_destroy(jpegencoder2);
        jpegencoder2 = NULL;
    }

    if (h264encoder != NULL) {
        check_disable_port(h264encoder->output[0]);
        mmal_component_disable(h264encoder);
        if (pool_h264encoder != NULL) {
            mmal_port_pool_destroy(h264encoder->output[0], pool_h264encoder);
            pool_h264encoder = NULL;
        }
        mmal_component_destroy(h264encoder);
        h264encoder = NULL;
    }
    if (null_sink != NULL) {
        mmal_component_disable(null_sink);
        mmal_component_destroy(null_sink);
        null_sink = NULL;
    }
    if (splitter != NULL) {
        mmal_component_disable(splitter);
        mmal_component_destroy(splitter);
        splitter = NULL;
    }

    if (pool_jpegencoder_in != NULL) {
        mmal_port_pool_destroy(jpegencoder->input[0], pool_jpegencoder_in);
        pool_jpegencoder_in = NULL;
    }

    // destroy connections
    if (con_cam_res != NULL) {
        mmal_connection_destroy(con_cam_res);
        con_cam_res = NULL;
    }
    if (con_res_jpeg != NULL) {
        mmal_connection_destroy(con_res_jpeg);
        con_res_jpeg = NULL;
    }
    if (con_cam_jpeg != NULL) {
        mmal_connection_destroy(con_cam_jpeg);
        con_cam_jpeg = NULL;
    }
    if (con_cam_h264 != NULL) {
        mmal_connection_destroy(con_cam_h264);
        con_cam_h264 = NULL
    }

    // cleanup semaphores
    vcos_semaphore_delete(&callback_data.complete_semaphore);
}

void capt_img(void) {
    char *filename_temp;
    struct statvfs buf;
    long limit = atoi(space_limit);

    currTime = time(NULL);
    gmTime = gmtime(&currTime);
    asprintf(&filename_temp, jpeg2_filename, gmTime->tm_year + 1900,
        gmTime->tm_mon + 1, gmTime->tm_mday, gmTime->tm_hour,
        gmTime->tm_min, gmTime->tm_sec, image2_cnt);
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

int findNextCount(char* folder, char* source) {
    char* search;
    char *s, *e;
    unsigned int current_count, max_count = 0;
    int found = 0;
    DIR *dp;
    struct dirent *fp;

    // get working copy of a path
    asprintf(&search,"%s", folder);
    // find base path by searching forward for first %sub then back for /
    s = strchr(search, '%');
    if (s != NULL) {
        *s = 0;
        s = strrchr(search, '/');
        if (s != NULL) {
            //truncate off to get base path and open it
            *s = 0;
            dp = opendir(search);
            if (dp != NULL) {
                //scan the contents
                while ((fp = readdir(dp))) {
                    s = fp->d_name;
                    // check if name is a thumbnail
                    e = s + strlen(s) - 7;
                    if (e > s && strcmp(e, ".th.jpg") == 0) {
                        // truncate where number should end
                        *e = 0;
                        //search to find beginning of field
                        s = strrchr(s, '.');
                        if (s != NULL) {
                            //set start to beginning
                            s++;
                            //see if it a comparison type
                            if (strchr(source, *s) != NULL) {
                                //extract number and set maximum
                                found = 1;
                                current_count = strtoul(s+1, &e, 10);
                                if (current_count > max_count) { 
                                    max_count = current_count;
                                }  
                            }  
                        }  
                    }  
                }  
                closedir(dp);
            }  
        }  
    }  
    free(search);
    return max_count + found;
}  

int main(int argc, char *argv[]) {
    int i, max, /* fd, */ length;
    /* char readbuf[60]; */
    char *filename_temp, /* *filename_recording, */ *cmd_temp;
    struct timeval now, delta, interval;
    char *bpath;
    FILE *fp;
    struct sigaction action;
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
            cfg_val[c_motion_detection] = 1;
        } else {
            fprintf(stderr, "Invalid argument: %s\n", argv[i]);
            return EX_USAGE;
        }
    }

    // default base media path
    asprintf(&cfg_stru[c_media_path], "%s", "/var/www/media");

    // read configs and init
    read_config(MJPG_DEF_CFG_FILE, 1);
    if (cfg_stru[c_user_config] != 0)
        read_config(cfg_stru[c_user_config], 0);

    createPath(cfg_stru[c_log_file], cfg_stru[c_base_path]);
    if (cfg_stru[c_boxing_path] != NULL) {
        asprintf(&bpath, "%s/temp", cfg_stru[c_boxing_path]);
        createPath(bpath, cfg_stru[c_base_path]);
        free(bpath);
    }

    puts("RaspiMJPEG Version " VERSION);
    exec_macro(cfg_stru[c_startstop], "start");

    if (cfg_val[c_motion_detection]) {
        TESTERR(system("motion") < 0, "Could not start Motion");
    }
    //
    // init
    if (cfg_val[c_autostart]) {
        start_all(0);
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

    memset(&action, 0, sizeof (struct sigaction));
    action.sa_handler = term;
    sigaction(SIGTERM, &action, NULL);
    sigaction(SIGINT, &action, NULL);

    if (status_filename != 0) {
        status_file = fopen(status_filename, "w");
        TESTERR(status_file == NULL, "Could not open/create status-file");
        if (cfg_val[c_autostart]) {
            if (!cfg_val[c_motion_detection]) {
                fputs("ready", status_file);
            } else {
                fputs("md_ready", status_file);
            }
        } else {
            fputs("halted", status_file);
        }
        fclose(status_file);
    }

    // Set up FIFO names
    if (cfg_stru[c_control_file] == 0) {
        error("No PIPE defined", 1);
    }
    for (i = 0; i < FIFO_MAX; i++) {
        if (i == 0) {
            sprintf(fdName[i], "%s", cfg_stru[c_control_file]);
        } else {
            sprintf(fdName[i], "%s%d", cfg_stru[c_control_file], i+10);
        }
    }

    // Clear out anything in FIFO(s) first
    for (i = 0; i < FIFO_MAX; i++) {
        do {
            fd[i] = open(fdName[i], O_RDONLY | O_NONBLOCK);
            if (fd[i] >= 0) {
                fcntl(fd[i], F_SETFL, 0);
                length = read(fd[i], readbuf[0], 60);
                close(fd[i]);
            } else {
                TESTERR(!i, "Could not open main PIPE");
                // apparently the others aren't as important
            }
        } while ((fd[i] >= 0) && length);
    }

    for (i = 0; i < FIFO_MAX; i++) {
        fd[i] = open(fdName[i], O_RDONLY | O_NONBLOCK);
        if (fd[i] >= 0) {
            DPRINTF(1, "Opening FIFO %i %s %i\n", i, fdName[i], fd[i]);
            fcntl(fd[i], F_SETFL, 0); 
        } 
    }

    if (cfg_val[c_autostart]) {
        DPRINTF(1, "MJPEG streaming, ready to receive commands\n");
        // Kick off motion detection at start if required.
        if (cfg_val[c_motion_detection] && (cfg_val[c_motion_external] == 1)) {
            DPUTS(1, "Autostart external motion kill any runnng motion");
            if (system("pkill motion 2> /dev/null") < 0) {
                DPERROR(1, "Could not stop external motion");
                exit(EX_OSERR);
            }
            sleep(1);
            DPUTS(1, "Autostart external motion start external motion");
            if (system("motion") < 0) {
                DPERROR(1, "Could not start external motion");
                exit(EX_OSERR);
            }
        }
    } else {
        if (cfg_stru[c_control_file] != 0) {
            DPUTS(1, "MJPEG idle, ready to receive commands");
        }
        else DPUTS(1, "MJPEG idle");
    }

    // Send restart signal to scheduler
    send_schedulecmd("9");

    while (running) {
        for (i = 0; i < FIFO_MAX; i++) {
            checkPipe(i);
        }

        /* Start of old all-in-one processing */
        if (pipe_filename != 0) {
            fd = open(pipe_filename, O_RDONLY | O_NONBLOCK);
            TESTERR(fd < 0, "Could not open PIPE");
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
                            TESTERR(pool_h264encoder == NULL,
                                "Could not create pool");
                            status = mmal_connection_create(&con_cam_h264,
                                camera->output[VIDEO_PORT],
                                h264encoder->input[0],
                                MMAL_CONNECTION_FLAG_TUNNELLING |
                                MMAL_CONNECTION_FLAG_ALLOCATION_ON_INPUT);
                            MMAL_STATUS("Could not create connecton camera -> video converter");
                            status = mmal_connection_enable(con_cam_h264);
                            MMAL_STATUS("Could not enable connection camera -> video converter");
                            currTime = time(NULL);
                            gmTime = gmtime(&currTime);
                            if (mp4box) {
                                asprintf(&filename_recording, h264_filename,
                                    gmTime->tm_year + 1900,
                                    gmTime->tm_mon + 1,
                                    gmTime->tm_mday, gmTime->tm_hour,
                                    gmTime->tm_min, gmTime->tm_sec,
                                    video_cnt);
                                asprintf(&filename_temp, "%s.h264",
                                    filename_recording);
                            } else {
                                asprintf(&filename_temp, h264_filename,
                                    video_cnt, gmTime->tm_year + 1900,
                                    gmTime->tm_mon + 1,
                                    gmTime->tm_mday, gmTime->tm_hour,
                                    gmTime->tm_min, gmTime->tm_sec);
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
                            TESTERR(system(cmd_temp) < 0,
                                "Could not start MP4Box");
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
                        TESTERR(system("pkill motion") < 0,
                            "Could not stop Motion");
                        }
                        puts("Motion detection stopped");
                        if (status_filename != 0) {
                            status_file = fopen(status_filename, "w");
                            fputs("ready", status_file);
                            fclose(status_file);
                        }
                    } else {
                        motion_detection = 1;
                        TESTERR(system("motion") < 0,
                            "Could not start Motion");
                        puts("Motion detection started");
                        if (status_filename != 0) {
                            status_file = fopen(status_filename, "w");
                            fputs("md_ready", status_file);
                            fclose(status_file);
                        }
                    }
                }
            }
        }
        /* End of old all-in-one processing */

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

        /* Start of new broken-out processing */
        // check to see if image preview changing
        if (!idle && cfg_val[c_watchdog_interval] > 0) {
            if (watchdog++ > cfg_val[c_watchdog_interval]) {
                watchdog = 0;
                pv_time = get_mtime(cfg_stru[c_preview_path]);
                if (pv_time == 0) {
                    watchdog_errors++;
                } else {
                    if (pv_time > last_pv_time) {
                        watchdog_errors = 0;
                    } else {
                        watchdog_errors++;
                    }
                    last_pv_time = pv_time;
                }
                if (watchdog_errors >= cfg_val[c_watchdog_errors]) {
                    DPUTS(1, "Watchdog detected problem. Stopping");
                    running = 0;
                }
            }
        } else {
            watchdog_errors = 0;
        }
        if (++onesec_check >= 10) {
            // run check on background boxing every 10 ticks and check for video
            // timer if capturing
            onesec_check = 0;
            // 4.9 compiler seems to want a print after the box finish to get
            // input FIFO working again
            if (check_box_files()) {
                DPUTS(1, "Removed item from Box Queue");
            }
            // Check to make sure image operation not stuck (no callback) if
            // enabled
            if ((cfg_val[c_callback_timeout] > 0) && i_capturing) {
                i_capturing--;
                if (i_capturing == 0) {
                    DPRINTF(1, "Image capture timed out %s\n", filename_image);
                    close_img(0);
                }
            }
            if (v_capturing && (video_stoptime > 0)) {
                if (time(NULL) >= video_stoptime) {
                    printLog("Stopping video from timer\n");
                    stop_video(0);
                    if (cfg_val[c_video_split] > 0) {
                        video_stoptime = time(NULL) + cfg_val[c_video_split];
                        DPRINTF(1, "Restarting next split of %d seconds\n",
                            cfg_val[c_video_split]);
                        start_video(0);
                    }
                }
            }
        }
        /* End of new broken-out processing */

        usleep(100000);
    }

    close(fd);
    if (system("pkill motion 2> /dev/null") < 0) {
        DPERROR(1, "Could not stop external motion");
        exit(EX_OSERR);
    }

    puts("SIGINT/SIGTERM received, stopping");

    // tidy up
    if (!idle) {
        stop_all();
    }

    exec_macro(cfg_stru[c_startstop], "stop");
    return 0;
}

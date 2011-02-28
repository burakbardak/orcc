/*
* Copyright (c) 2009, IETR/INSA of Rennes
* All rights reserved.
* 
* Redistribution and use in source and binary forms, with or without
* modification, are permitted provided that the following conditions are met:
* 
*   * Redistributions of source code must retain the above copyright notice,
*     this list of conditions and the following disclaimer.
*   * Redistributions in binary form must reproduce the above copyright notice,
*     this list of conditions and the following disclaimer in the documentation
*     and/or other materials provided with the distribution.
*   * Neither the name of the IETR/INSA of Rennes nor the names of its
*     contributors may be used to endorse or promote products derived from this
*     software without specific prior written permission.
* 
* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
* AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
* IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
* ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
* LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
* CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
* SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
* INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
* STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY
* WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
* SUCH DAMAGE.
*/
#include "SDL.h"

#include "orcc.h"
#include "orcc_fifo.h"

//#define NO_DISPLAY

#ifdef BENCHMARK
#include <locale.h>
#include <time.h>
FILE * pFile;
static Uint32 tInit = 0;
#endif


extern struct fifo_i8_s *display_B;
extern struct fifo_i16_s *display_WIDTH;
extern struct fifo_i16_s *display_HEIGHT;

static unsigned int fifo_display_B_id;
static unsigned int fifo_display_WIDTH_id;
static unsigned int fifo_display_HEIGHT_id;

static SDL_Surface *m_screen;
static SDL_Overlay *m_overlay;

#define MAX_WIDTH 720
#define MAX_HEIGHT 576


static int m_x;
static int m_y;
static int m_width;
static int m_height;

static unsigned char img_buf_y[MAX_WIDTH * MAX_HEIGHT];
static unsigned char img_buf_u[MAX_WIDTH * MAX_HEIGHT / 4];
static unsigned char img_buf_v[MAX_WIDTH * MAX_HEIGHT / 4];

static void press_a_key(int code) {
	char buf[2];
	printf("Press enter to continue\n");
	fgets(buf, 2, stdin);
	exit(code);
}

static Uint32 start_time;
static int num_images_start;
static int num_images_end;

void print_fps_avg(void) {
	Uint32 t = SDL_GetTicks();

	printf("%i images in %f seconds: %f FPS\n",
		num_images_end, (float) t / 1000.0f,
		1000.0f * (float)num_images_end / (float)t);
}

static Uint32 partial_start_time;
static Uint32 partial_end_time;
static int partial_num_images_start;
static int partial_num_images_end;

float compute_partial_fps(){
	return 1000.0f * (float)(partial_num_images_end - partial_num_images_start) / (float)(partial_end_time - partial_start_time);
}

void backup_partial_start_info(){
	partial_start_time = SDL_GetTicks();
	partial_num_images_start = num_images_end;
}

void backup_partial_end_info(){
	partial_end_time = SDL_GetTicks();
	partial_num_images_end = num_images_end;
}

static int show_fps = 1;

void remove_fps_printing(){
	show_fps = 0;
}

void active_fps_printing(){
	show_fps = 1;
}

static Uint32 t;

void display_show_image(void) {
	SDL_Rect rect = { 0, 0, m_width, m_height };

	int t2;
	SDL_Event event;

	///////////////////////////////////////////////////////////////////////////////////////////////
#ifndef NO_DISPLAY
	if (SDL_LockYUVOverlay(m_overlay) < 0) {
		fprintf(stderr, "Can't lock screen: %s\n", SDL_GetError());
		press_a_key(-1);
	}

	memcpy(m_overlay->pixels[0], img_buf_y, m_width * m_height );
	memcpy(m_overlay->pixels[1], img_buf_u, m_width * m_height / 4 );
	memcpy(m_overlay->pixels[2], img_buf_v, m_width * m_height / 4 );

	SDL_UnlockYUVOverlay(m_overlay);
	SDL_DisplayYUVOverlay(m_overlay, &rect);
#endif

	///////////////////////////////////////////////////////////////////////////////////////////////
	num_images_end++;
	t2 = SDL_GetTicks();
	if (show_fps && t2 - t > 3000) {
		printf("%f images/sec\n",
			1000.0f * (float)(num_images_end - num_images_start) / (float)(t2 - t));

#ifdef BENCHMARK
		if (tInit == 0)
			tInit = t2;

		fprintf (pFile, "%d \t %f \n",(t2-tInit),1000.0f * (float)(num_images_end - num_images_start) / (float)(t2 - t));

#endif
		t = t2;
		num_images_start = num_images_end;
	}

	/* Grab all the events off the queue. */
	while (SDL_PollEvent(&event)) {
		switch (event.type) {
			case SDL_QUIT:
				exit(0);
				break;
			default:
				break;
		}
	}
}

void display_write_mb(unsigned char tokens[384]) {
	int i, j, cnt, base;

	//printf("display_write_mb (%i, %i)\n", m_x, m_y);

	cnt = 0;
	base = m_y * m_width + m_x;

	for (i = 0; i < 16; i++) {
		for (j = 0; j < 16; j++) {
			int tok = tokens[cnt];
			int idx = base + i * m_width + j;
			cnt++;
			img_buf_y[idx] = tok;
		}
	}

	base = m_y / 2 * m_width / 2 + m_x / 2;
	for (i = 0; i < 8; i++) {
		for (j = 0; j < 8; j++) {
			int tok = tokens[cnt];
			int idx = base + i * m_width / 2 + j;
			cnt++;
			img_buf_u[idx] = tok;
		}
	}

	for (i = 0; i < 8; i++) {
		for (j = 0; j < 8; j++) {
			int tok = tokens[cnt];
			int idx = base + i * m_width / 2 + j;
			cnt++;
			img_buf_v[idx] = tok;
		}
	}

	m_x += 16;
	if (m_x == m_width) {
		m_x = 0;
		m_y += 16;
	}

	if (m_y == m_height) {
		m_x = 0;
		m_y = 0;
		display_show_image();
	}
}

static int init = 0;
static int sizeinit = 0;

static void display_init() {
		
#ifdef NO_DISPLAY
	// First, initialize SDL's subsystem.
	if (SDL_Init( SDL_INIT_TIMER ) < 0) {
		fprintf(stderr, "Timer initialization failed: %s\n", SDL_GetError());
		press_a_key(-1);
	}
#else
	// First, initialize SDL's video subsystem.
	if (SDL_Init( SDL_INIT_VIDEO ) < 0) {
		fprintf(stderr, "Video initialization failed: %s\n", SDL_GetError());
		press_a_key(-1);
	}

	SDL_WM_SetCaption("display", NULL);
#endif

	start_time = SDL_GetTicks();
	t = start_time;
	partial_start_time = start_time;
	partial_num_images_start = 0;

#ifdef BENCHMARK
	{
		char sFile [80];	
		time_t rawtime;
		struct tm * timeinfo;

		time ( &rawtime );
		timeinfo = localtime ( &rawtime );

		strftime (sFile,80,".//Bench/bench_%d-%m-%y_%H-%M-%S.log",timeinfo);

		pFile = fopen (sFile,"w");
		if (pFile== NULL)
		{
			fprintf(stderr, "Can't create log file, try to disable BENCHMARK preprocessor\n");
			exit(1);
		}
		setlocale(LC_NUMERIC, "");
		fprintf (pFile, "Time (in ms) \t fps \n");
	}
#endif

	atexit(SDL_Quit);
	atexit(print_fps_avg);

	init = 1;
}

void display_initialize(unsigned int fifo_B_id, unsigned int fifo_WIDTH_id, unsigned int fifo_HEIGHT_id) {
	m_x = 0;
	m_y = 0;
	fifo_display_B_id = fifo_B_id; 
	fifo_display_WIDTH_id = fifo_WIDTH_id; 
	fifo_display_HEIGHT_id = fifo_HEIGHT_id;

	if (!init) {
		display_init();
	}
}


static void display_set_video(int width, int height) {
	if (width == m_width && height == m_height) {
		// video mode is already good
		return;
	}

	m_width = width;
	m_height = height;
	
#ifndef NO_DISPLAY
	printf("set display to %ix%i\n", width, height);

	m_screen = SDL_SetVideoMode(m_width, m_height, 24, SDL_HWSURFACE | SDL_DOUBLEBUF);
	if (m_screen == NULL) {
		fprintf(stderr, "Couldn't set %ix%ix24 video mode: %s\n", m_width, m_height,
			SDL_GetError());
		press_a_key(-1);
	}

	if (m_overlay != NULL) {
		SDL_FreeYUVOverlay(m_overlay);
	}

	m_overlay = SDL_CreateYUVOverlay(m_width, m_height, SDL_IYUV_OVERLAY, m_screen);
	if (m_overlay == NULL) {
		fprintf(stderr, "Couldn't create overlay: %s\n", SDL_GetError());
		press_a_key(-1);
	}
#endif

	sizeinit = 1;
}

void display_scheduler(struct schedinfo_s *si) {
	int i = 0;

	while (1) {
		if (fifo_i16_has_tokens(display_WIDTH, fifo_display_WIDTH_id, 1) && fifo_i16_has_tokens(display_HEIGHT, fifo_display_HEIGHT_id, 1)) {
			short *ptr, width, height;
			i16 display_WIDTH_buf[1], display_HEIGHT_buf[1];

			ptr = fifo_i16_read(display_WIDTH, display_WIDTH_buf, fifo_display_WIDTH_id, 1);
			width = ptr[0] * 16;
			fifo_i16_read_end(display_WIDTH, fifo_display_WIDTH_id, 1);

			ptr = fifo_i16_read(display_HEIGHT, display_HEIGHT_buf, fifo_display_HEIGHT_id, 1);
			height = ptr[0] * 16;
			fifo_i16_read_end(display_HEIGHT, fifo_display_HEIGHT_id, 1);

			display_set_video(width, height);
			i++;
		}

		if (fifo_i8_has_tokens(display_B, fifo_display_B_id, 384) && sizeinit) {
			i8 display_B_buf[384];
			if (!init) {
				display_init();
			}

			display_write_mb(fifo_i8_read(display_B, display_B_buf, fifo_display_B_id, 384));
			fifo_i8_read_end(display_B, fifo_display_B_id, 384);
			i++;
		} else {
			break;
		}
	}

	si->num_firings = i;
	si->reason = starved;
	si->ports = 0x07; // FIFOs connected to first three input ports are empty
}

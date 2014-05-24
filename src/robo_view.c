
#include <glib.h>
#include <gtk/gtk.h>
#include <gdk/gdkkeysyms.h>

#include <gtk/gtkgl.h>
#include <GL/gl.h>
#include <GL/glu.h>

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <math.h>

#include "imu_view.h"
#include "imu_calcs.h"
#include "decimate.h"
#include "import_stl_file.h"
#include <jbplot.h>

struct zero_data_t {
	float x0;
	float y0;
	float dir_x;
	float dir_y;
	double a_x_sum;
	double a_y_sum;
	double a_z_sum;
	double w_x_sum; 
	double w_y_sum; 
	double w_z_sum; 
	int avg_count;
};	

struct axes_t {
	GLUquadric *origin;
	GLUquadric *x_cyl;
	GLUquadric *y_cyl;
	GLUquadric *z_cyl;
	GLUquadric *x_arrow;
	GLUquadric *y_arrow;
	GLUquadric *z_arrow;
};

static int load_count = -1;
static float north_angle_deg = 0.0;
static struct axes_t body_axes;	
static struct axes_t ref_axes;	
static GLUquadric *zero_dir_axis;
static gboolean body_axes_visible;
static gboolean ref_axes_visible;
static gboolean model_visible;
static gboolean ref_model_visible;
static gboolean path_visible;

static int playback_state = IDLE;
static gboolean real_time_load;
static gboolean abort_rt_load = FALSE;
static GTimeVal t_start, t_now, t_redraw;

static int zero_state = ZERO_IDLE;
static struct zero_data_t zero_data;
static int zero_direction = 3;
static float w_body_offsets[3] = { 0.0f, 0.0f, 0.0f};

static GMutex *mutex;

static GtkWidget *h_pane;
static GtkWidget *zero_dir_combo;
static GtkWidget *status_bar;
static gboolean first_config = TRUE;
static GtkWidget *window;
static GtkWidget *da;
static GtkWidget *slider;
static GtkWidget *play_btn;
static GtkWidget *pause_btn;
#ifndef LINE2LINE
static GtkWidget *raw_accel_plot, *raw_w_plot;
static GtkWidget *accel_comp_plot;
static trace_handle ax_trace[MAX_LOADS], ay_trace[MAX_LOADS], az_trace[MAX_LOADS];
static trace_handle axc_trace[MAX_LOADS], ayc_trace[MAX_LOADS], azc_trace[MAX_LOADS];
static trace_handle wx_trace[MAX_LOADS], wy_trace[MAX_LOADS], wz_trace[MAX_LOADS];
#endif
static GtkWidget *speed_plot;
static GtkWidget *g_plot;
static GtkWidget *dist_plot;
static trace_handle dist_trace[MAX_LOADS];
#ifdef IMU_VIEW_DIAGNOSTIC
static GtkWidget *dcm_labels[3][3];
static GtkWidget *euler_labels[3];
static GtkWidget *temp_plot;
static trace_handle temp_trace[MAX_LOADS];
static GtkWidget *raw_mag_plot;
static trace_handle mx_trace[MAX_LOADS], my_trace[MAX_LOADS], mz_trace[MAX_LOADS];
static GtkWidget *only_translation_cb;
#endif
static GtkWidget *show_model_cb;
static GtkWidget *show_ref_model_cb;
static GtkWidget *show_body_axes_cb;
static GtkWidget *show_ref_axes_cb;
static GtkWidget *show_path_cb;
static GtkWidget *only_orientation_cb;
static GtkWidget *ax_offset_entry;
static GtkWidget *ay_offset_entry;
static GtkWidget *az_offset_entry;
static GtkWidget *accel_deadband;
static GtkWidget *gyro_deadband;
static GtkWidget *g_thresh_entry;
static float g_thresh_val; 
static char *init_g_thresh_str = "3.5";
static float accel_deadband_value = 0.0f;
static float gyro_deadband_value = 0.0f;
static gboolean orient_only;
static gboolean translate_only;
static trace_handle speed_trace[MAX_LOADS];
static trace_handle g_trace[MAX_LOADS];
static GLuint motion_display_list = 0;
static GLuint ref_display_list = 0;
static gboolean dragging = FALSE;
static struct float_xy drag_start;
static float drag_start_tm[16];
static float motion_bound_coords[6];
static float ref_bound_coords[6];
static GLfloat light_position[] = { 1000, 1000, 0, 1 };
static float rot_matrix[16] =   {1, 0, 0, 0, 
                                 0, 1, 0, 0, 
                                 0, 0, 1, 0, 
                                 0, 0, 0, 1};
static float trans_matrix[16] = {1, 0, 0, 0, 
                                 0, 1, 0, 0, 
                                 0, 0, 1, 0, 
                                 0, 0, 0, 1};
static float dcm_matrix[16] =   {1, 0, 0, 0, 
                                 0, 1, 0, 0, 
                                 0, 0, 1, 0, 
                                 0, 0, 0, 1};
static float position[3] = {0, 0, 0};

static float accel_offsets[3] = {0., 0., 0.};

// These variables set the dimensions of the rectanglar region we wish to view.
static float x_range = 16.0f;
static float y_range = 16.0f;

static gboolean do_load_file = FALSE;

struct hist_t hist[MAX_LOADS];


static int init_axes(struct axes_t *a) {
	a->origin  = gluNewQuadric();
	a->x_cyl = gluNewQuadric();
	a->y_cyl = gluNewQuadric();
	a->z_cyl = gluNewQuadric();
	a->x_arrow = gluNewQuadric();
	a->y_arrow = gluNewQuadric();
	a->z_arrow = gluNewQuadric();
	return 0;
}

static inline void
set_trace_data_center(trace_handle trace, float *x, float *y, int start, int end, int center, int max_length) 
{
	int length = end - start + 1;
	int s = center - max_length / 2;
	int e  = center + max_length / 2;
	/* can't plot past end of data */
	if(e > end) {
		e = end;
		s = end - max_length + 1;
	}
	/* can't plot before start of data */
	if(s < 0) {
		s = 0;
		if(length > max_length) {
			e = s + max_length -1;
		}
		else {
			e = end;
		}
	}
	length = e - s + 1;
		
	jbplot_trace_set_data(trace, x+s, y+s, length);
}


static inline void
set_trace_data_end(trace_handle trace, float *x, float *y, int start, int end, int max_length) 
{
	int length = end - start + 1;
	if(length > max_length) {
		start = end - max_length + 1;
		length = max_length;
	}
	jbplot_trace_set_data(trace, x+start, y+start, length);
}

static inline void
set_trace_data_start(trace_handle trace, float *x, float *y, int start, int end, int max_length) 
{
	int length = end - start + 1;
	if(length > max_length) {
		end = start + max_length - 1;
		length = max_length;
	}
	jbplot_trace_set_data(trace, x+start, y+start, length);
}


#ifdef IMU_VIEW_DIAGNOSTIC
static void update_dcm_labels2(struct hist_t *hp, int index) {
	char str[100];
	int i,j;
	for(i=0; i<3; i++) {
		for(j=0; j<3; j++) {
			sprintf(str, "%.3f", hp->dcm[3*i + j][index]);
			gtk_label_set_text(GTK_LABEL(dcm_labels[i][j]), str);
		}
	}
	/* xyz convention */
	float euler_1 = atan2(hp->dcm[7][index],hp->dcm[8][index]);
	//printf("euler_1 = %g\n", euler_1);
	sprintf(str, "%.3f", euler_1);
	gtk_label_set_text(GTK_LABEL(euler_labels[0]), str);
	float euler_2 = -acos(hp->dcm[6][index]);
	sprintf(str, "%.3f", euler_2);
	gtk_label_set_text(GTK_LABEL(euler_labels[1]), str);
	float euler_3 = atan2(hp->dcm[3][index],hp->dcm[0][index]);
	sprintf(str, "%.3f", euler_3);
	gtk_label_set_text(GTK_LABEL(euler_labels[2]), str);
	
}
#endif

static void push_status(char *status_str, int context_id) {
		gtk_statusbar_push(GTK_STATUSBAR(status_bar), context_id, status_str);
}

static void pop_status(int context_id) {
		gtk_statusbar_pop(GTK_STATUSBAR(status_bar), context_id);
}

static int draw_axis(float x_start, float y_start, float x_end, float y_end) {
	float dx = x_end - x_start;
	float dy = y_end - y_start;
	float length = sqrt(dx*dx + dy*dy);
	float diam = length / AXIS_DIAM_DIV;
	float arrow_length = 0.1*length;

	glPushMatrix();
	glTranslatef(x_start, y_start, 100); /* translate to start point */
	glRotatef(90, 0.0, 1.0, 0.0); /* makes z-axis point in x-direction */
	glRotatef(atan2(dy, dx)*180/M_PI, -1, 0, 0);
	gluCylinder(zero_dir_axis, diam/2., diam/2., length - arrow_length, 5, 5);
	glTranslatef(0, 0, length - arrow_length);
	gluCylinder(zero_dir_axis, diam, 0.0, arrow_length, 5, 5);
	glPopMatrix();
	
}

static int draw_axes(struct axes_t *a) {
	float min_dim = (x_range > y_range) ? y_range : x_range;
	float length = AXIS_LENGTH_FACTOR * min_dim;
	float diam = length / AXIS_DIAM_DIV;

	/* draw z-axis */
	glColor3f(0, 0, 1);
	gluCylinder(a->z_cyl, diam/2., diam/2., length, 5, 5);
	glPushMatrix();
	glTranslatef(0, 0, length);
	gluCylinder(a->z_arrow, diam, 0.0, 0.1 * length, 5, 5);
	glPopMatrix();

	/* draw y-axis */
	glColor3f(0, 1, 0);
	glPushMatrix();
	glRotatef(-90, 1.0, 0.0, 0.0);
	gluCylinder(a->y_cyl, diam/2., diam/2., length, 5, 5);
	glPushMatrix();
	glTranslatef(0, 0, length);
	gluCylinder(a->y_arrow,diam, 0.0, 0.1 * length, 5, 5);
	glPopMatrix();
	glPopMatrix();

	/* draw x-axis */
	glColor3f(1, 0, 0);
	glPushMatrix();
	glRotatef(90, 0.0, 1.0, 0.0);
	gluCylinder(a->x_cyl, diam/2., diam/2., length, 5, 5);
	glPushMatrix();
	glTranslatef(0, 0, length);
	gluCylinder(a->x_arrow, diam, 0.0, 0.1 * length, 5, 5);
	glPopMatrix();
	glPopMatrix();

	/* draw origin */
	glColor3f(1, 1, 0);
	gluSphere(a->origin, diam * 1.5, 8, 8);

	return 0;
}


void gl_draw_bounding_box(float *bounds) {
	glPolygonMode(GL_FRONT_AND_BACK, GL_LINE);
	glBegin(GL_QUADS);
		glVertex3f(bounds[0],bounds[2],bounds[4]);
		glVertex3f(bounds[1],bounds[2],bounds[4]);
		glVertex3f(bounds[1],bounds[3],bounds[4]);
		glVertex3f(bounds[0],bounds[3],bounds[4]);

		glVertex3f(bounds[0],bounds[2],bounds[5]);
		glVertex3f(bounds[1],bounds[2],bounds[5]);
		glVertex3f(bounds[1],bounds[3],bounds[5]);
		glVertex3f(bounds[0],bounds[3],bounds[5]);

		glVertex3f(bounds[0],bounds[2],bounds[4]);
		glVertex3f(bounds[0],bounds[3],bounds[4]);
		glVertex3f(bounds[0],bounds[3],bounds[5]);
		glVertex3f(bounds[0],bounds[2],bounds[5]);

		glVertex3f(bounds[1],bounds[2],bounds[4]);
		glVertex3f(bounds[1],bounds[3],bounds[4]);
		glVertex3f(bounds[1],bounds[3],bounds[5]);
		glVertex3f(bounds[1],bounds[2],bounds[5]);

		glVertex3f(bounds[0],bounds[2],bounds[4]);
		glVertex3f(bounds[1],bounds[2],bounds[4]);
		glVertex3f(bounds[1],bounds[2],bounds[5]);
		glVertex3f(bounds[0],bounds[2],bounds[5]);

		glVertex3f(bounds[0],bounds[3],bounds[4]);
		glVertex3f(bounds[1],bounds[3],bounds[4]);
		glVertex3f(bounds[1],bounds[3],bounds[5]);
		glVertex3f(bounds[0],bounds[3],bounds[5]);
	glEnd();
	glPolygonMode(GL_FRONT_AND_BACK, GL_FILL);
}


void do_view_transform() {
	glMultMatrixf(trans_matrix);
	glMultMatrixf(rot_matrix);
}

void do_body_transform() {
	if(!orient_only) {
		glTranslatef(position[0]*1000, position[1]*1000, position[2]*1000);
	}
	if(!translate_only) {
		glMultMatrixf(dcm_matrix);
	}
}

static gboolean 
da_expose(GtkWidget *da, GdkEventExpose *event, gpointer user_data)
{
	int i;
	GdkGLContext *glcontext = gtk_widget_get_gl_context (da);
	GdkGLDrawable *gldrawable = gtk_widget_get_gl_drawable (da);

	if (!gdk_gl_drawable_gl_begin (gldrawable, glcontext)) {
		g_assert_not_reached ();
	}

	/* draw in here */
	glClearColor(0.5,0.5,1,0);
	glClear(GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT);
	
	glMatrixMode(GL_MODELVIEW);
	glLoadIdentity();
	
	glPushMatrix();

		/* do the view transform */
		do_view_transform();

		/* set the light position each frame, so it will appear fixed
     * w.r.t. the scene */
		glLightfv(GL_LIGHT0, GL_POSITION, light_position);


		/****** Draw the reference object (fixed) *******/
		if(ref_model_visible) {
			glColor3f( 0.8, 0.8, 0.8 );
			glCallList(ref_display_list); 
			/* Draw a wireframe bounding box */
			//gl_draw_bounding_box(ref_bound_coords);
		}

		/* Draw reference axes */
		if(ref_axes_visible) {
			draw_axes(&ref_axes);
		}

		/* Draw the zero'ing direction vector if necessary */
		if(zero_state == ZERO_WAIT_FOR_DIR && zero_direction != 3) {
			glColor3f( 1, 1, 0 );	/* yellow */	
			draw_axis(zero_data.x0, zero_data.y0, zero_data.dir_x, zero_data.dir_y);
		}

		/******* Draw the moving object (IMU) *******/

		/* path tracing */
		if(path_visible) {
			glColor3f( 1, 0, 0 );	/* red */	
			glLineWidth(2);
			glBegin(GL_LINE_STRIP);
			g_mutex_lock(mutex);
				for(i=hist[load_count].zero_index; i<hist[load_count].current && i <=hist[load_count].last_crunched_index; i++) {
					glVertex3f(
						hist[load_count].pos[0][i]*1000,
						hist[load_count].pos[1][i]*1000,
						hist[load_count].pos[2][i]*1000
					);
				}
			g_mutex_unlock(mutex);
			glEnd();
		}

		/* transform to the position and orientation of the body */
		g_mutex_lock(mutex);
			do_body_transform();
		g_mutex_unlock(mutex);

		if(hist[load_count].playback_index >= hist[load_count].zero_index || zero_state == ZERO_WAIT_FOR_DIR) {
			/* draw the actual moving object */
			if(model_visible) {
				glColor3f( 0, 0, 1 );	/* blue */	
				glCallList(motion_display_list);
				/* Draw a wireframe bounding box */
				//gl_draw_bounding_box(motion_bound_coords);
			}

			/* Draw body axes */
			if(body_axes_visible) {
				draw_axes(&body_axes);
			}
		}

	glPopMatrix();

	if (gdk_gl_drawable_is_double_buffered (gldrawable)) {
		gdk_gl_drawable_swap_buffers (gldrawable);
	}
	else {
		glFlush();
	}

	gdk_gl_drawable_gl_end (gldrawable);

	return TRUE;
}

#define mindex(matrix, row, col) matrix[(row-1) + 4*(col-1)]

int matrix_mult(float *m1, float *m2, float *m_out) {
	float m[16];
	m[0]  = m1[0]*m2[0]  + m1[4]*m2[1]  + m1[8]*m2[2]  + m1[12]*m2[3];
	m[4]  = m1[0]*m2[4]  + m1[4]*m2[5]  + m1[8]*m2[6]  + m1[12]*m2[7];
	m[8]  = m1[0]*m2[8]  + m1[4]*m2[9]  + m1[8]*m2[10] + m1[12]*m2[11];
	m[12] = m1[0]*m2[12] + m1[4]*m2[13] + m1[8]*m2[14] + m1[12]*m2[15];

	m[1]  = m1[1]*m2[0]  + m1[5]*m2[1]  + m1[9]*m2[2]  + m1[13]*m2[3];
	m[5]  = m1[1]*m2[4]  + m1[5]*m2[5]  + m1[9]*m2[6]  + m1[13]*m2[7];
	m[9]  = m1[1]*m2[8]  + m1[5]*m2[9]  + m1[9]*m2[10] + m1[13]*m2[11];
	m[13] = m1[1]*m2[12] + m1[5]*m2[13] + m1[9]*m2[14] + m1[13]*m2[15];

	m[2]  = m1[2]*m2[0]  + m1[6]*m2[1]  + m1[10]*m2[2]  + m1[14]*m2[3];
	m[6]  = m1[2]*m2[4]  + m1[6]*m2[5]  + m1[10]*m2[6]  + m1[14]*m2[7];
	m[10] = m1[2]*m2[8]  + m1[6]*m2[9]  + m1[10]*m2[10] + m1[14]*m2[11];
	m[14] = m1[2]*m2[12] + m1[6]*m2[13] + m1[10]*m2[14] + m1[14]*m2[15];

	m[3]  = m1[3]*m2[0]  + m1[7]*m2[1]  + m1[11]*m2[2]  + m1[15]*m2[3];
	m[7]  = m1[3]*m2[4]  + m1[7]*m2[5]  + m1[11]*m2[6]  + m1[15]*m2[7];
	m[11] = m1[3]*m2[8]  + m1[7]*m2[9]  + m1[11]*m2[10] + m1[15]*m2[11];
	m[15] = m1[3]*m2[12] + m1[7]*m2[13] + m1[11]*m2[14] + m1[15]*m2[15];

	memcpy(m_out, m, sizeof(m));
	return 0;
}


int matrix_mult33(float *m1, float *m2, float *m_out) {
	float m[9];
	m[0]  = m1[0]*m2[0]  + m1[1]*m2[3]  + m1[2]*m2[6];
	m[1]  = m1[0]*m2[1]  + m1[1]*m2[4]  + m1[2]*m2[7];
	m[2]  = m1[0]*m2[2]  + m1[1]*m2[5]  + m1[2]*m2[8];

	m[3]  = m1[3]*m2[0]  + m1[4]*m2[3]  + m1[5]*m2[6];
	m[4]  = m1[3]*m2[1]  + m1[4]*m2[4]  + m1[5]*m2[7];
	m[5]  = m1[3]*m2[2]  + m1[4]*m2[5]  + m1[5]*m2[8];

	m[6]  = m1[6]*m2[0]  + m1[7]*m2[3]  + m1[8]*m2[6];
	m[7]  = m1[6]*m2[1]  + m1[7]*m2[4]  + m1[8]*m2[7];
	m[8]  = m1[6]*m2[2]  + m1[7]*m2[5]  + m1[8]*m2[8];

	memcpy(m_out, m, sizeof(m));
	return 0;
}

static void set_top_view() {
	int i;
	for(i=0; i<16; i++) {
		rot_matrix[i]=0.0;
	}
	rot_matrix[0]  = 1; 
	rot_matrix[5]  = 1; 
	rot_matrix[10] = 1;
	rot_matrix[15] = 1;			
	gtk_widget_queue_draw(da);
}

static gboolean
key_press (GtkWidget *w, GdkEventKey *event, gpointer user_data) {
	float m[16] = {1, 0, 0, 0, 
                 0, 1, 0, 0, 
                 0, 0, 1, 0, 
                 0, 0, 0, 1};
	int rotate = 0;
	int translate = 0;
	int i;
	gboolean propagate = FALSE;

	/* Pass L/R key strokes to slider if slider is focused */
	GtkWidget *fw = gtk_window_get_focus(GTK_WINDOW(w));
	if(fw == slider && (event->keyval==GDK_Left || event->keyval==GDK_Right)) {
		return FALSE;
	}
#ifndef LINE2LINE
	else if(fw == ax_offset_entry || fw == ay_offset_entry || fw == az_offset_entry) { 
		return FALSE;
	}
#endif

	switch(event->keyval) {
		case GDK_Escape:
			stop_zero_operation(TRUE);
			break;

		case GDK_Tab:
			return FALSE;
			break;

		case GDK_Up:
			/* pan upwards */
			if(event->state & GDK_CONTROL_MASK) {
				mindex(m,2,4) = y_range * 0.1;
				translate = 1;	
			}
			/* rotate about negative x-axis */
			else {
				mindex(m,2,2) = cos(ROTATE_DELTA);
				mindex(m,2,3) = sin(ROTATE_DELTA);
				mindex(m,3,2) = -sin(ROTATE_DELTA);
				mindex(m,3,3) = cos(ROTATE_DELTA);
				rotate = 1;
			}
			break;

		case GDK_Down:
			/* pan downwards */
			if(event->state & GDK_CONTROL_MASK) {
				mindex(m,2,4) = -y_range * 0.1;
				translate = 1;	
			}
			/* rotate about positive x-axis */
			else {
				mindex(m,2,2) = cos(ROTATE_DELTA);
				mindex(m,2,3) = -sin(ROTATE_DELTA);
				mindex(m,3,2) = sin(ROTATE_DELTA);
				mindex(m,3,3) = cos(ROTATE_DELTA);
				rotate = 1;
			}
			break;

		case GDK_Left:
			/* pan leftwards */
			if(event->state & GDK_CONTROL_MASK) {
				mindex(m,1,4) = -x_range * 0.1;
				translate = 1;	
			}
			/* rotate about negative y-axis */
			else {
				mindex(m,1,1) = cos(ROTATE_DELTA);
				mindex(m,1,3) = -sin(ROTATE_DELTA);
				mindex(m,3,1) = sin(ROTATE_DELTA);
				mindex(m,3,3) = cos(ROTATE_DELTA);
				rotate = 1;
			}
			break;

		case GDK_Right:
			/* pan rightwards */
			if(event->state & GDK_CONTROL_MASK) {
				mindex(m,1,4) = x_range * 0.1;
				translate = 1;	
			}
			/* rotate about positive y-axis */
			else {
				mindex(m,1,1) = cos(ROTATE_DELTA);
				mindex(m,1,3) = sin(ROTATE_DELTA);
				mindex(m,3,1) = -sin(ROTATE_DELTA);
				mindex(m,3,3) = cos(ROTATE_DELTA);
				rotate = 1;
			}
			break;

		/* reset to original orientation (top view) */
		case ' ':
			set_top_view();
			break;

		/* zoom in */
		case 'z':
			x_range *= 0.8;
			y_range *= 0.8;
			configure(da, NULL, NULL);
			gtk_widget_queue_draw(da);
			break;

		/* zoom out */
		case 'Z':
			x_range *= 1.2;
			y_range *= 1.2;
			configure(da, NULL, NULL);
			gtk_widget_queue_draw(da);
			break;

		/* zoom all */
		case 'a':
			zoom_all();
			break;

		default:
			propagate = TRUE;
	}

	if(translate) {
		matrix_mult(m, trans_matrix, trans_matrix);
		gtk_widget_queue_draw(da);
	}

	if(rotate && zero_state==ZERO_IDLE) {
		matrix_mult(m, rot_matrix, rot_matrix);
		gtk_widget_queue_draw(da);
	}

	return (!propagate);
}

static gboolean configure_win (GtkWidget *w, GdkEventConfigure *event, gpointer user_data) {
	if(first_config && w->allocation.width > 300) {
		gtk_paned_set_position(GTK_PANED(h_pane), w->allocation.width/2);
		first_config = FALSE;
		printf("setting h_pane to %g\n", w->allocation.width/2.);
	}
	return FALSE;
}


static gboolean configure (GtkWidget *da, GdkEventConfigure *event, gpointer user_data) {
	GdkGLContext *glcontext = gtk_widget_get_gl_context (da);
	GdkGLDrawable *gldrawable = gtk_widget_get_gl_drawable (da);

	if (!gdk_gl_drawable_gl_begin (gldrawable, glcontext)) {
		g_assert_not_reached ();
	}

	int w = da->allocation.width;
	int h = da->allocation.height;
	glViewport (0, 0, w, h);

	// The complication is that the aspect ratio of the window may not match the
	//		aspect ratio of the scene we want to view.
	double scale;
	double windowXmin, windowXmax, windowYmin, windowYmax;
	w = (w==0) ? 1 : w;
	h = (h==0) ? 1 : h;
	if ( x_range/w < y_range/h ) {
		scale = (y_range/h)/(x_range/w);
		windowXmin = -x_range/2.0*scale;
		windowXmax = x_range/2.0*scale;
		windowYmin = -y_range/2.0;
		windowYmax = y_range/2.0;
	}
	else {
		scale = (x_range/w)/(y_range/h);
		windowYmin = -y_range/2.0*scale;
		windowYmax = y_range/2.0*scale;
		windowXmin = -x_range/2.0;
		windowXmax = x_range/2.0;
	}
	
	// Now that we know the max & min values for x & y that should be visible in the window,
	//		we set up the orthographic projection.
	glMatrixMode( GL_PROJECTION );
	glLoadIdentity();
	glOrtho( windowXmin, windowXmax, windowYmin, windowYmax, -1e5, 1e5 );

	glEnable (GL_BLEND);
	glBlendFunc (GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);
	
	gdk_gl_drawable_gl_end (gldrawable);

	return TRUE;
}

static gboolean
rotate (gpointer user_data)
{
	GtkWidget *da = GTK_WIDGET (user_data);

	gdk_window_invalidate_rect (da->window, &da->allocation, FALSE);
	gdk_window_process_updates (da->window, FALSE);

	return TRUE;
}

int load_model(const char *fname, GtkWidget *w, GLuint *display_list, float *bound_coords) {
	int stl_ret;
	GdkGLContext *glcontext = gtk_widget_get_gl_context (w);
	GdkGLDrawable *gldrawable = gtk_widget_get_gl_drawable (w);
	if (!gdk_gl_drawable_gl_begin (gldrawable, glcontext)) {
		g_assert_not_reached ();
	}
	stl_ret = import_stl_file(fname, display_list, bound_coords);
	gdk_gl_drawable_gl_end (gldrawable);

	return stl_ret;
}

void init_gl_props(GtkWidget *w) {
	GdkGLContext *glcontext = gtk_widget_get_gl_context (w);
	GdkGLDrawable *gldrawable = gtk_widget_get_gl_drawable (w);
	if (!gdk_gl_drawable_gl_begin (gldrawable, glcontext)) {
		g_assert_not_reached ();
	}

	glEnable ( GL_DEPTH_TEST );
	glEnable ( GL_CCW );
	glEnable ( GL_CULL_FACE );

	GLfloat mat_specular[] = { 0.5, 0.5, 0.5, 1.0 };
	GLfloat grey[] = { 0.5, 0.5, 0.5, 1.0 };
	GLfloat white[] = { 1, 1, 1, 1.0 };
	GLfloat black[] = { 0, 0, 0, 1.0 };
	GLfloat mat_shininess[] = { 5.0 };
	//GLfloat light_position[] = { 1000.0, 1000.0, 100.0, 1.0 };
	//GLfloat light_ambient[] = { 0.5, 0.5, 0.5, 1.0 };
	GLfloat light_ambient[] = { 0.4, 0.4, 0.4, 1.0 };
	//GLfloat light_diffuse[] = { 0.1, 0.1, 0.1, 1 };
	GLfloat light_diffuse[] = { 1, 1, 1, 1 };
	//GLfloat light_spec[] = { 0, 0, 0, 0 };
	GLfloat light_spec[] = { 0.1, 0.1, 0.1, 1 };

	//glMaterialfv(GL_FRONT, GL_AMBIENT_AND_DIFFUSE, grey);
	glMaterialfv(GL_FRONT, GL_SPECULAR, white);
	glMaterialfv(GL_FRONT, GL_EMISSION, black);
	glLightfv(GL_LIGHT0, GL_POSITION, light_position);
	glLightfv(GL_LIGHT0, GL_AMBIENT, light_ambient);
	glLightfv(GL_LIGHT0, GL_DIFFUSE, light_diffuse);
	glLightfv(GL_LIGHT0, GL_SPECULAR, light_spec);
	glEnable(GL_LIGHTING);
	glEnable(GL_LIGHT0);

	glEnable ( GL_COLOR_MATERIAL );
	glColorMaterial(GL_FRONT, GL_AMBIENT_AND_DIFFUSE);

	glMatrixMode(GL_MODELVIEW);
	glLoadIdentity();

	gdk_gl_drawable_gl_end (gldrawable);
}

void set_current_state2(struct hist_t *hp, int index) {
	dcm_matrix[0] = hp->dcm[0][index];
	dcm_matrix[1] = hp->dcm[1][index];
	dcm_matrix[2] = hp->dcm[2][index];
	dcm_matrix[4] = hp->dcm[3][index];
	dcm_matrix[5] = hp->dcm[4][index];
	dcm_matrix[6] = hp->dcm[5][index];
	dcm_matrix[8] = hp->dcm[6][index];
	dcm_matrix[9] = hp->dcm[7][index];
	dcm_matrix[10] = hp->dcm[8][index];

	position[0] = hp->pos[0][index];
	position[1] = hp->pos[1][index];
	position[2] = hp->pos[2][index];
	return;
}
	
int do_imu_calcs(int index) {
	static struct imu_state state;
	int i;

	/* calculate compensated accel values */
	float accel_comp[3];
	accel_comp[0] = hist[load_count].accel_body_raw[0][index] - accel_offsets[0];
	accel_comp[1] = hist[load_count].accel_body_raw[1][index] - accel_offsets[1];
	accel_comp[2] = hist[load_count].accel_body_raw[2][index] - accel_offsets[2];

	/* calculate magnitude of the vector formed by the compensated accel values */
	float accel_mag = sqrt(accel_comp[0]*accel_comp[0] + accel_comp[1]*accel_comp[1] + accel_comp[2]*accel_comp[2]);

	#define ALPHA_X state.dcm[0]
	#define ALPHA_Y state.dcm[1]
	#define ALPHA_Z state.dcm[2]
	#define BETA_X state.dcm[3]
	#define BETA_Y state.dcm[4]
	#define BETA_Z state.dcm[5]
	#define GAMMA_X state.dcm[6]
	#define GAMMA_Y state.dcm[7]
	#define GAMMA_Z state.dcm[8]

	/* perform accel deadband compensation */
	if(zero_state == ZERO_IDLE && fabs(accel_mag - state.gravity) < accel_deadband_value) {
		accel_comp[0] = ALPHA_Z * state.gravity;
		accel_comp[1] = BETA_Z * state.gravity;
		accel_comp[2] = GAMMA_Z * state.gravity;
	}

	/* first data point: initialize with hardcoded values */
	if(index <= 1) {
		state.dcm[0] =1.0;
		state.dcm[1] =0.0;
		state.dcm[2] =0.0;
		state.dcm[3] =0.0;
		state.dcm[4] =0.0;
		state.dcm[5] =1.0;
		state.dcm[6] =0.0;
		state.dcm[7] =-1.0;
		state.dcm[8] =0.0;
		for(i=0; i<3; i++) {
			state.vel[i] = 0.0f;
		}
		state.pos[0] = 0.0f;
		state.pos[1] = 0.0f;
		state.pos[2] = 1.2f;
		state.time = hist[load_count].time[index];
		state.gravity = 9.81;
		state.init = 1;
		printf("initializing imu_calcs()\n");
	}

	if(zero_state == ZERO_WAIT_FOR_DIR) {
		zero_data.a_x_sum += 	accel_comp[0];
		zero_data.a_y_sum += 	accel_comp[1];
		zero_data.a_z_sum += 	accel_comp[2];
		zero_data.w_x_sum += 	hist[load_count].w_body_raw[0][index];
		zero_data.w_y_sum += 	hist[load_count].w_body_raw[1][index];
		zero_data.w_z_sum += 	hist[load_count].w_body_raw[2][index];
		zero_data.avg_count++;
	}

	if (zero_state == ZERO_GO || zero_state == ZERO_WAIT_FOR_DIR) {

		/* Calculate average acceleration vector in body coords */
    /* during zero'ing, this vector must point in +z direction */
		float a_x_avg, a_y_avg, a_z_avg;
		float w_x_avg, w_y_avg, w_z_avg;
		//printf("samples to average during zero: %d\n", zero_data.avg_count);
		if(zero_data.avg_count > 0) {
			a_x_avg = zero_data.a_x_sum / zero_data.avg_count;
			a_y_avg = zero_data.a_y_sum / zero_data.avg_count;
			a_z_avg = zero_data.a_z_sum / zero_data.avg_count;
			w_x_avg = zero_data.w_x_sum / zero_data.avg_count;
			w_y_avg = zero_data.w_y_sum / zero_data.avg_count;
			w_z_avg = zero_data.w_z_sum / zero_data.avg_count;
		}
		else {
			a_x_avg = accel_comp[0];
			a_y_avg = accel_comp[1];
			a_z_avg = accel_comp[2];
			w_x_avg = hist[load_count].w_body_raw[0][index];
			w_y_avg = hist[load_count].w_body_raw[1][index];
			w_z_avg = hist[load_count].w_body_raw[2][index];
		}

		/* normalize the average accel vector to get the k unit vector */
		float accel_avg_length = 
			sqrt(a_x_avg*a_x_avg + a_y_avg*a_y_avg + a_z_avg*a_z_avg);
		float accel_avg_dir_x = a_x_avg / accel_avg_length;
		float accel_avg_dir_y = a_y_avg / accel_avg_length;
		float accel_avg_dir_z = a_z_avg / accel_avg_length;
		state.gravity = accel_avg_length;


		/* using the user-supplied direction vector, calculate the reference */
		/* frame coords of the i primed unit vector */	
		float dir_x = zero_data.dir_x - zero_data.x0;
		float dir_y = zero_data.dir_y - zero_data.y0;
		float dir_length = sqrt(dir_x*dir_x + dir_y*dir_y);
		
		ALPHA_Z = accel_avg_dir_x;
		BETA_Z  = accel_avg_dir_y;
		GAMMA_Z = accel_avg_dir_z;

		float sr_x = sqrt(1 - ALPHA_Z * ALPHA_Z);
		float sr_y = sqrt(1 - BETA_Z * BETA_Z);
		float sr_z = sqrt(1 - GAMMA_Z * GAMMA_Z);

		switch(zero_direction) {
			case 0: /* x direction */
				ALPHA_X = dir_x/dir_length * sr_x;
				ALPHA_Y = dir_y/dir_length * sr_x;

				BETA_X = (-ALPHA_Y*GAMMA_Z-ALPHA_X*ALPHA_Z*BETA_Z)/(ALPHA_X*ALPHA_X+ALPHA_Y*ALPHA_Y);
				BETA_Y = (ALPHA_X*GAMMA_Z-ALPHA_Y*ALPHA_Z*BETA_Z)/(ALPHA_X*ALPHA_X+ALPHA_Y*ALPHA_Y);

				/* k_prime = i_prime x j_prime */
				GAMMA_X = ALPHA_Y*BETA_Z - ALPHA_Z*BETA_Y;
				GAMMA_Y = ALPHA_Z*BETA_X - ALPHA_X*BETA_Z;
				break;

			case 1: /* y direction */
				BETA_X = dir_x/dir_length * sr_y;
				BETA_Y = dir_y/dir_length * sr_y;

				GAMMA_X = (-BETA_Y*ALPHA_Z-BETA_X*BETA_Z*GAMMA_Z)/(BETA_X*BETA_X+BETA_Y*BETA_Y);
				GAMMA_Y = (BETA_X*ALPHA_Z-BETA_Y*BETA_Z*GAMMA_Z)/(BETA_X*BETA_X+BETA_Y*BETA_Y);

				/* i_prime = j_prime x k_prime */
				ALPHA_X = BETA_Y*GAMMA_Z - BETA_Z*GAMMA_Y;
				ALPHA_Y = BETA_Z*GAMMA_X - BETA_X*GAMMA_Z;
				break;

			case 2: /* z direction */
				GAMMA_X = dir_x/dir_length * sr_z;
				GAMMA_Y = dir_y/dir_length * sr_z;

				ALPHA_X = (-GAMMA_Y*BETA_Z-GAMMA_X*GAMMA_Z*ALPHA_Z)/(GAMMA_X*GAMMA_X+GAMMA_Y*GAMMA_Y);
				ALPHA_Y = (GAMMA_X*BETA_Z-GAMMA_Y*GAMMA_Z*ALPHA_Z)/(GAMMA_X*GAMMA_X+GAMMA_Y*GAMMA_Y);

				/* j_prime = k_prime x i_prime */
				BETA_X = GAMMA_Y*ALPHA_Z - GAMMA_Z*ALPHA_Y;
				BETA_Y = GAMMA_Z*ALPHA_X - GAMMA_X*ALPHA_Z;
				break;

			case 3: { /* Use magnetometer instead */
				double m_x = hist[load_count].mag_body_raw[0][index];
				double m_y = hist[load_count].mag_body_raw[1][index];
				double m_z = hist[load_count].mag_body_raw[2][index];
				double a1 = m_z * BETA_Z - m_y * GAMMA_Z;
				double a2 = m_z * ALPHA_Z - m_x * GAMMA_Z;
				double a3 = m_y * ALPHA_Z - m_x * BETA_Z;

				ALPHA_Y = sqrt(a1*a1/(a1*a1 + a2*a2 + a3*a3));
				BETA_Y = -a2 / a1 * ALPHA_Y;
				GAMMA_Y = a3 / a1 * ALPHA_Y;

				ALPHA_X = BETA_Y*GAMMA_Z - BETA_Z*GAMMA_Y;
				BETA_X = GAMMA_Y*ALPHA_Z - GAMMA_Z*ALPHA_Y;
				GAMMA_X = ALPHA_Y*BETA_Z - ALPHA_Z*BETA_Y;

				/* check if need to change signs */
				if((m_x*ALPHA_X + m_y*BETA_X + m_z*GAMMA_X) < 0) {
					ALPHA_X = -ALPHA_X;
					ALPHA_Y = -ALPHA_Y;
					BETA_X = -BETA_X;
					BETA_Y = -BETA_Y;
					GAMMA_X = -GAMMA_X;
					GAMMA_Y = -GAMMA_Y;
				}
		
				/* now do after-the-fact rotation if an inertial orientation angle was spec'd*/
				if(north_angle_deg != 0.0f) {
					float rm[9];
					float angle_rad = north_angle_deg / 180. * M_PI;
					rm[0] = ALPHA_Z*ALPHA_Z + (1-ALPHA_Z*ALPHA_Z)*cos(angle_rad);
					rm[3] = ALPHA_Z*BETA_Z*(1-cos(angle_rad)) + GAMMA_Z*sin(angle_rad);
					rm[6] = ALPHA_Z*GAMMA_Z*(1-cos(angle_rad)) - BETA_Z*sin(angle_rad);

					rm[1] = ALPHA_Z*BETA_Z*(1-cos(angle_rad)) - GAMMA_Z*sin(angle_rad);
					rm[4] = BETA_Z*BETA_Z + (1-BETA_Z*BETA_Z)*cos(angle_rad);
					rm[7] = BETA_Z*GAMMA_Z*(1-cos(angle_rad)) + ALPHA_Z*sin(angle_rad);

					rm[2] = ALPHA_Z*GAMMA_Z*(1-cos(angle_rad)) + BETA_Z*sin(angle_rad);
					rm[5] = BETA_Z*GAMMA_Z*(1-cos(angle_rad)) - ALPHA_Z*sin(angle_rad);
					rm[8] = GAMMA_Z*GAMMA_Z + (1-GAMMA_Z*GAMMA_Z)*cos(angle_rad);

					matrix_mult33(rm, state.dcm, state.dcm);
				}
		
#if 0
				/* DEBUG */
				printf("RSS alphas: %g\n", sqrt(ALPHA_X*ALPHA_X+ALPHA_Y*ALPHA_Y+ALPHA_Z*ALPHA_Z));
				printf("RSS betas: %g\n", sqrt(BETA_X*BETA_X+BETA_Y*BETA_Y+BETA_Z*BETA_Z));
				printf("RSS gammas: %g\n", sqrt(GAMMA_X*GAMMA_X+GAMMA_Y*GAMMA_Y+GAMMA_Z*GAMMA_Z));
				printf("RSS X's: %g\n", sqrt(ALPHA_X*ALPHA_X+BETA_X*BETA_X+GAMMA_X*GAMMA_X));
				printf("RSS Y's: %g\n", sqrt(ALPHA_Y*ALPHA_Y+BETA_Y*BETA_Y+GAMMA_Y*GAMMA_Y));
				printf("RSS Z's: %g\n", sqrt(ALPHA_Z*ALPHA_Z+BETA_Z*BETA_Z+GAMMA_Z*GAMMA_Z));
#endif

				break;
			}

		}


		/* set gyro offsets */
		w_body_offsets[0] = w_x_avg;
		w_body_offsets[1] = w_y_avg;
		w_body_offsets[2] = w_z_avg;
		if (zero_state == ZERO_GO) {
			printf("gyro offsets: %g, %g, %g\n", w_x_avg, w_y_avg, w_z_avg);
		}

		state.time = hist[load_count].time[index];
		state.init = 1;
	}

	/* during at and the end of the zeroing process, set the velocity
	 * to zero and the position to whatever the user selected */
	if (zero_state == ZERO_GO || zero_state == ZERO_WAIT_FOR_DIR) {
		for(i=0; i<3; i++) {
			state.vel[i] = 0.0f;
		}
		state.pos[0] = zero_data.x0/1000.;
		state.pos[1] = zero_data.y0/1000.;
		state.pos[2] = 1.2f;
	}

	if (zero_state == ZERO_GO) {
		zero_state = ZERO_IDLE;

		printf("Zero'd DCM:\n");
		for(i=0; i<3; i++) {
			int j;
			for(j=0; j<3; j++) {
				printf("%12g", state.dcm[j + 3*i]);
			}
			printf("\n");
		}
		printf("\n");
		printf(" row 1 check: %g\n", ALPHA_X*ALPHA_X+ALPHA_Y*ALPHA_Y+ALPHA_Z*ALPHA_Z);
		printf(" row 2 check: %g\n", BETA_X*BETA_X+BETA_Y*BETA_Y+BETA_Z*BETA_Z);
		printf(" row 3 check: %g\n", GAMMA_X*GAMMA_X+GAMMA_Y*GAMMA_Y+GAMMA_Z*GAMMA_Z);
		printf(" col 1 check: %g\n", ALPHA_X*ALPHA_X+BETA_X*BETA_X+GAMMA_X*GAMMA_X);
		printf(" col 2 check: %g\n", ALPHA_Y*ALPHA_Y+BETA_Y*BETA_Y+GAMMA_Y*GAMMA_Y);
		printf(" col 3 check: %g\n", ALPHA_Z*ALPHA_Z+BETA_Z*BETA_Z+GAMMA_Z*GAMMA_Z);

		printf("zero'd gravity magnitude: %g m/sec^2\n", state.gravity);
	}

	float corrected_w[3];
	corrected_w[0] = hist[load_count].w_body_raw[0][index] - w_body_offsets[0];
	corrected_w[1] = hist[load_count].w_body_raw[1][index] - w_body_offsets[1];
	corrected_w[2] = hist[load_count].w_body_raw[2][index] - w_body_offsets[2];

	/* perform gyro deadband compensation */
	float gyro_mag = sqrt(pow(corrected_w[0],2)+pow(corrected_w[1],2)+pow(corrected_w[2],2));
	if(zero_state == ZERO_IDLE && gyro_mag < gyro_deadband_value) {
		corrected_w[0] = 0.0;
		corrected_w[1] = 0.0;
		corrected_w[2] = 0.0;
	}

	/* is rotation diabled? */
	if(translate_only) {
		corrected_w[0] = 0.0;
		corrected_w[1] = 0.0;
		corrected_w[2] = 0.0;
	}

	//printf("accel_raw: x=%g, y=%g, z=%g\n", hist.accel_body_raw[0][index], hist.accel_body_raw[1][index], hist.accel_body_raw[2][index]);
	//printf("accel_comp: x=%g, y=%g, z=%g\n", accel_comp[0], accel_comp[1], accel_comp[2]);

	imu_calc(
		corrected_w, 
		accel_comp, 
		hist[load_count].time[index], 
		&state
	);

	for(i=0; i<9; i++) {
		hist[load_count].dcm[i][index] = state.dcm[i];
	}
	for(i=0; i<3; i++) {
		hist[load_count].vel[i][index] = state.vel[i];
		hist[load_count].pos[i][index] = state.pos[i];
	}

	hist[load_count].accel_ref[0][index] =
		accel_comp[0]*ALPHA_X + accel_comp[1]*BETA_X + accel_comp[2]*GAMMA_X;
	hist[load_count].accel_ref[1][index] =
		accel_comp[0]*ALPHA_Y + accel_comp[1]*BETA_Y + accel_comp[2]*GAMMA_Y;
	hist[load_count].accel_ref[2][index] =
		accel_comp[0]*ALPHA_Z + accel_comp[1]*BETA_Z + accel_comp[2]*GAMMA_Z - state.gravity;

	#undef ALPHA_X
	#undef ALPHA_Y
	#undef ALPHA_Z
	#undef BETA_X
	#undef BETA_Y
	#undef BETA_Z
	#undef GAMMA_X
	#undef GAMMA_Y
	#undef GAMMA_Z

	//printf("pos: %g, %g, %g\n", state.pos[0],state.pos[1],state.pos[2]);

	return 0;
}

static int trip_count = 0;
static gboolean g_tripped = FALSE;

#ifndef LINE2LINE
static gboolean blink(gpointer data) {
	rgb_color_t white = {1,1,1};
	rgb_color_t red   = {1,0,0};
	if((trip_count % 2) == 0) {
		GDK_THREADS_ENTER();
			jbplot_set_plot_area_color(JBPLOT(g_plot), &red);
		GDK_THREADS_LEAVE();
	}
	else {
		GDK_THREADS_ENTER();
			jbplot_set_plot_area_color(JBPLOT(g_plot), &white);
		GDK_THREADS_LEAVE();
	}
	trip_count++;
	if(trip_count > 5) {
		trip_count = 0;
		g_tripped = FALSE;
		return FALSE;
	}
	else {
		return TRUE;
	}
}
#endif

static gpointer playback(gpointer data) {
	float t;
	static float start_ts;
	int status_context = gtk_statusbar_get_context_id(GTK_STATUSBAR(status_bar), "playback");

	while(1) {
		g_mutex_lock(mutex);
			gboolean loading = do_load_file;
		g_mutex_unlock(mutex);
		switch(playback_state) {
			case START_PLAYING:
				printf("Start Playing\n");
				GDK_THREADS_ENTER();
					pop_status(status_context);
					push_status("Playing...", status_context);
				GDK_THREADS_LEAVE();
				g_mutex_lock(mutex);
					if(hist[load_count].current == 0) {
						playback_state = GOTO_IDLE;
						break;
					}
					start_ts = hist[load_count].time[hist[load_count].playback_index];
				g_mutex_unlock(mutex);
				g_get_current_time(&t_start);
				t_redraw = t_start;
				playback_state = PLAYING;
				break;
			case PLAYING:
				g_mutex_lock(mutex);
					int playback_index = hist[load_count].playback_index;
					t = hist[load_count].time[hist[load_count].playback_index];
					int last_crunched_index = hist[load_count].last_crunched_index;
				g_mutex_unlock(mutex);
				g_get_current_time(&t_now);
				double run_time = (t_now.tv_sec - t_start.tv_sec) + 
													1.e-6*(t_now.tv_usec-t_start.tv_usec);
				if(!real_time_load && (t-start_ts > run_time) ) {
					g_usleep(1.0e6*(t-start_ts - run_time));
				}

				if(!loading) {
					GDK_THREADS_ENTER();
					gtk_range_set_value(GTK_RANGE(slider), t);
					GDK_THREADS_LEAVE();
				}

				/* crunch the data if necessary */
				if(playback_index > last_crunched_index || zero_state > ZERO_WAIT_FOR_POS) {
					g_mutex_lock(mutex);
						do_imu_calcs(playback_index);
						hist[load_count].last_crunched_index = playback_index;
					g_mutex_unlock(mutex);

					/* FIXME plot the crunched speed and G data (don't like where this is done!) */
					float g_load = 1/9.81 * sqrt( 
						pow(hist[load_count].accel_body_raw[0][playback_index],2) + 
						pow(hist[load_count].accel_body_raw[1][playback_index],2) + 
						pow(hist[load_count].accel_body_raw[2][playback_index],2) 
					); 
					float mph = 2.2369 * sqrt( 
						pow(hist[load_count].vel[0][playback_index],2) + 
						pow(hist[load_count].vel[1][playback_index],2) + 
						pow(hist[load_count].vel[2][playback_index],2) 
					); 
					float dist = sqrt(
						pow(hist[load_count].pos[0][playback_index]-zero_data.x0/1000. , 2) + 
						pow(hist[load_count].pos[1][playback_index]-zero_data.y0/1000. , 2) + 
						pow(hist[load_count].pos[2][playback_index]-1.2f , 2) 
					); 
					if(playback_index < hist[load_count].zero_index) {
						mph = 0.0;
						dist = 0.0;
					}
					g_mutex_lock(mutex);
						hist[load_count].g_load[playback_index] = g_load;
						hist[load_count].mph[playback_index] = mph;
						hist[load_count].dist[playback_index] = dist;
					g_mutex_unlock(mutex);

				}

				/* update plots */
				int i;
				for(i=0; i<=load_count; i++) {
					set_trace_data_center(speed_trace[i], hist[i].time, hist[i].mph, hist[i].zero_index, hist[i].last_crunched_index, playback_index, MAX_TRACE_LENGTH);	
					set_trace_data_center(g_trace[i], hist[i].time, hist[i].g_load, hist[i].zero_index, hist[i].last_crunched_index, playback_index, MAX_TRACE_LENGTH);	

#ifndef LINE2LINE
					set_trace_data_center(axc_trace[i], hist[i].time, hist[i].accel_ref[0], hist[i].zero_index, hist[i].last_crunched_index, playback_index, MAX_TRACE_LENGTH);	
					set_trace_data_center(ayc_trace[i], hist[i].time, hist[i].accel_ref[1], hist[i].zero_index, hist[i].last_crunched_index, playback_index, MAX_TRACE_LENGTH);	
					set_trace_data_center(azc_trace[i], hist[i].time, hist[i].accel_ref[2], hist[i].zero_index, hist[i].last_crunched_index, playback_index, MAX_TRACE_LENGTH);	

					set_trace_data_center(ax_trace[i], hist[i].time, hist[i].accel_body_raw[0], 0, hist[i].current-1, playback_index, MAX_TRACE_LENGTH);	
					set_trace_data_center(ay_trace[i], hist[i].time, hist[i].accel_body_raw[1], 0, hist[i].current-1, playback_index, MAX_TRACE_LENGTH);	
					set_trace_data_center(az_trace[i], hist[i].time, hist[i].accel_body_raw[2], 0, hist[i].current-1, playback_index, MAX_TRACE_LENGTH);	

					set_trace_data_center(wx_trace[i], hist[i].time, hist[i].w_body_raw[0], 0, hist[i].current-1, playback_index, MAX_TRACE_LENGTH);	
					set_trace_data_center(wy_trace[i], hist[i].time, hist[i].w_body_raw[1], 0, hist[i].current-1, playback_index, MAX_TRACE_LENGTH);	
					set_trace_data_center(wz_trace[i], hist[i].time, hist[i].w_body_raw[2], 0, hist[i].current-1, playback_index, MAX_TRACE_LENGTH);	
#endif

					set_trace_data_center(dist_trace[i], hist[i].time, hist[i].dist, hist[i].zero_index, hist[i].last_crunched_index, playback_index, MAX_TRACE_LENGTH);	

#ifdef IMU_VIEW_DIAGNOSTIC
					set_trace_data_center(mx_trace[i],   hist[i].time, hist[i].mag_body_raw[0], 0, hist[i].current-1, playback_index, MAX_TRACE_LENGTH);	
					set_trace_data_center(my_trace[i],   hist[i].time, hist[i].mag_body_raw[1], 0, hist[i].current-1, playback_index, MAX_TRACE_LENGTH);	
					set_trace_data_center(mz_trace[i],   hist[i].time, hist[i].mag_body_raw[2], 0, hist[i].current-1, playback_index, MAX_TRACE_LENGTH);	
					set_trace_data_center(temp_trace[i], hist[i].time, hist[i].temp,            0, hist[i].current-1, playback_index, MAX_TRACE_LENGTH);	
#endif
				}

				/* check for g_load trip */
#ifndef LINE2LINE
				if(fabs(hist[load_count].g_load[playback_index]) > g_thresh_val) {
					if(!g_tripped) {
						g_tripped = TRUE;
						g_timeout_add(200, blink, NULL);
					}
				}
#endif

				g_mutex_lock(mutex);
					set_current_state2(&hist[load_count], hist[load_count].playback_index);

					hist[load_count].playback_index++;
					if(hist[load_count].playback_index >= hist[load_count].current) {
						if(do_load_file) {
							playback_state = WAITING_TO_PLAY;
						}
						else {
							playback_state = GOTO_IDLE;
							hist[load_count].playback_index = 0;
						}
					}
				g_mutex_unlock(mutex);

				/* only redraw screen and plots ever so often */
				double redraw_time = (t_now.tv_sec - t_redraw.tv_sec) + 
													1.e-6*(t_now.tv_usec-t_redraw.tv_usec);
				if(redraw_time > 0.2) {
					GDK_THREADS_ENTER();
						jbplot_refresh(JBPLOT(speed_plot));
						jbplot_refresh(JBPLOT(g_plot));
						jbplot_refresh(JBPLOT(dist_plot));
						jbplot_set_cursor_pos(JBPLOT(speed_plot), t, 0);
						jbplot_set_cursor_pos(JBPLOT(g_plot), t, 0);
						jbplot_set_cursor_pos(JBPLOT(dist_plot), t, 0);
					#ifndef LINE2LINE
						jbplot_refresh(JBPLOT(accel_comp_plot));
						jbplot_refresh(JBPLOT(raw_accel_plot));
						jbplot_refresh(JBPLOT(raw_w_plot));
						jbplot_set_cursor_pos(JBPLOT(accel_comp_plot), t, 0);
						jbplot_set_cursor_pos(JBPLOT(raw_accel_plot), t, 0);
						jbplot_set_cursor_pos(JBPLOT(raw_w_plot), t, 0);
					#endif
					#ifdef IMU_VIEW_DIAGNOSTIC
						update_dcm_labels2(&hist[load_count], hist[load_count].playback_index-1);
						jbplot_refresh(JBPLOT(temp_plot));
						jbplot_refresh(JBPLOT(raw_mag_plot));
						jbplot_set_cursor_pos(JBPLOT(temp_plot), t, 0);
						jbplot_set_cursor_pos(JBPLOT(raw_mag_plot), t, 0);
					#endif
						gtk_widget_queue_draw(da);
					GDK_THREADS_LEAVE();
					t_redraw = t_now;
				}

				break;
			case WAITING_TO_PLAY:
				g_mutex_lock(mutex);
				if(hist[load_count].current > hist[load_count].playback_index) {
					playback_state = PLAYING;
					g_mutex_unlock(mutex);
				}
				else {
					g_mutex_unlock(mutex);
					g_usleep(500);
				}	
				break;
			case GOTO_PAUSE:
				printf("Goto Pause\n");
				GDK_THREADS_ENTER();
					pop_status(status_context);
					push_status("Paused.", status_context);
				GDK_THREADS_LEAVE();
				g_mutex_lock(mutex);
					playback_state = PAUSED;
				g_mutex_unlock(mutex);
				break;
			case PAUSED:
				g_usleep(5000);
				break;
			case GOTO_IDLE:
				printf("Goto Idle\n");
				GDK_THREADS_ENTER();
					pop_status(status_context);
					gtk_widget_set_sensitive(pause_btn, FALSE);
					gtk_widget_set_sensitive(play_btn, TRUE);
				GDK_THREADS_LEAVE();
				g_mutex_lock(mutex);
					playback_state = IDLE;
				g_mutex_unlock(mutex);
				break;
			case IDLE:
				g_usleep(5000);
				break;
			}
	}
	return NULL;
}

static char data_fname[1000];

static gpointer file_loader(gpointer data) {
	FILE *fp;
	static char line[1000];
	int i;
	int ret;
	int first_line;

	int status_context = gtk_statusbar_get_context_id(GTK_STATUSBAR(status_bar), "file_loader");

	while(1) {
		int eof_count = 0;
		gboolean do_load;
		g_mutex_lock(mutex);
			do_load = do_load_file;
		g_mutex_unlock(mutex);
		/* freewheel waiting to load a file */
		if(!do_load) {
			g_usleep(10000);
			continue;
		}

		first_line = 1;
		char status_str[1000] = "Loading file: ";
		strncat(status_str, data_fname, sizeof(status_str) - strlen(status_str) - 5);
		strcat(status_str, "...");
		GDK_THREADS_ENTER();
			pop_status(status_context);
			push_status(status_str, status_context);
		GDK_THREADS_LEAVE();

		g_mutex_lock(mutex);
			/* increment the load counter */
			load_count++;

			/* clear previous state histroy */
			hist[load_count].current = 0;
			hist[load_count].playback_index = 0;
			hist[load_count].last_crunched_index = -1;

			/* open the file (if not stdin) */
			if(!real_time_load) {
				fp = fopen(data_fname, "r");
				if(fp == NULL) {
					GDK_THREADS_ENTER();
						pop_status(status_context);
						push_status("Error opening file!", status_context);
					GDK_THREADS_LEAVE();
					//perror("Error opening file");
					//exit(1);
				}
			}
			else {
				fp = stdin;
			}
		g_mutex_unlock(mutex);

		/* suck in the file contents */
		while(1) {
			double t;
			float w[3];
			float accel[3];
			float mag[3];
			float temp;

			if(fgets(line, sizeof(line), fp) == NULL) {
				eof_count++;
				clearerr(fp);
				g_usleep(2000);
				/* in case file is being created in RT, allow 1.5 sec of EOF */
				if(eof_count > 750) {
					break;
				}
			}
			else {
				eof_count = 0;
				/* check for comment line (starts with '#') */
				if(line[0] == '#') {
					continue;
				}
				/* parse out the data */
				ret = sscanf(
					line, 
					"%lf %f %f %f %f %f %f %f %f %f %f",
					&t, w, w+1, w+2, accel, accel+1, accel+2, mag, mag+1, mag+2, &temp
				);
				if(ret != 7 && ret != 10 && ret != 11) {
					GDK_THREADS_ENTER();
						pop_status(status_context);
						push_status("Error parsing file!", status_context);
					GDK_THREADS_LEAVE();
					break;
				}

				g_mutex_lock(mutex);
					for(i=0; i<3; i++) {
						hist[load_count].w_body_raw[i][hist[load_count].current] = w[i];
						hist[load_count].accel_body_raw[i][hist[load_count].current] = accel[i];
						hist[load_count].mag_body_raw[i][hist[load_count].current] = mag[i];
					}
					hist[load_count].time[hist[load_count].current] = t;
					hist[load_count].temp[hist[load_count].current] = temp;
				g_mutex_unlock(mutex);
			
				if(first_line) {
					first_line = 0;
					GDK_THREADS_ENTER();
					gtk_widget_activate(play_btn);
					GDK_THREADS_LEAVE();
				}

				g_mutex_lock(mutex);
					hist[load_count].current++;
					if(hist[load_count].current >= hist[load_count].size) {
						printf("Allocating more memory for state_history...\n");
						expand_hist(&hist[load_count]);
					}
#ifdef LINE2LINE
					if(abort_rt_load || 
						(hist[load_count].current > hist[load_count].zero_index && 
						 hist[load_count].time[hist[load_count].current-1] - hist[load_count].time[hist[load_count].zero_index] > RUN_TIME)) 
#else
					if(abort_rt_load)
#endif
					{
						abort_rt_load = FALSE;
						g_mutex_unlock(mutex);
						break;
					}
				g_mutex_unlock(mutex);

			}
		}
		fclose(fp);
		if(!real_time_load) {
			printf("Done loading file\n");
		}
		else {
			real_time_load = FALSE;
			printf("Real-time data stream stopped\n");
		}
		GDK_THREADS_ENTER();
			pop_status(status_context);
		GDK_THREADS_LEAVE();

		g_mutex_lock(mutex);
			float t0 = hist[load_count].time[0];
			float tf = hist[load_count].time[hist[load_count].current-1];
		g_mutex_unlock(mutex);

		GDK_THREADS_ENTER();
			gtk_range_set_range(GTK_RANGE(slider), t0, tf);
			gtk_widget_set_sensitive(GTK_WIDGET(data), TRUE);
		GDK_THREADS_LEAVE();

		g_mutex_lock(mutex);
			do_load_file = FALSE;
		g_mutex_unlock(mutex);

	}
	return NULL;
}

void config_plots(void) {
	rgb_color_t black = {0,0,0};
	rgb_color_t red   = {1,0,0};
	rgb_color_t green = {0,1,0};
	rgb_color_t blue  = {0,0,1};
	rgb_color_t yellow  = {1,1,0};
	rgb_color_t grey  = {0.5,0.5,0.5};
	rgb_color_t colors[] = {black, red, green, blue, yellow};
	int i;

	/* specify the minimum size of all the plots */
	int min_width  = 200;
	int min_height = 200;

	/* g plot */
	gtk_widget_set_size_request(g_plot, min_width, min_height);
#ifdef LINE2LINE
	jbplot_set_plot_title(JBPLOT(g_plot), "G Load", 1);
#else
	jbplot_set_plot_title(JBPLOT(g_plot), "ATH G-index", 1);
#endif
	jbplot_set_plot_title_visible(JBPLOT(g_plot), 1);
	jbplot_set_x_axis_label(JBPLOT(g_plot), "Time (sec)", 1);
	jbplot_set_y_axis_label(JBPLOT(g_plot), "G-Force (g's)", 1);
	jbplot_set_cursor_props(JBPLOT(g_plot), CURSOR_VERT, grey, 2.0, LINETYPE_SOLID);
	for(i=0; i<MAX_LOADS; i++) {
		g_trace[i] = jbplot_create_trace(0);	
		if(g_trace[i]==NULL) {
			printf("Error creating plot traces!\n");
			exit(1);
		}
		char str[10];
		sprintf(str, "G's (%d)", i);
		jbplot_trace_set_name(g_trace[i], str);
		jbplot_add_trace(JBPLOT(g_plot), g_trace[i]);
		jbplot_trace_set_line_props(g_trace[i], LINETYPE_SOLID, 1.0, &colors[i]);
		jbplot_trace_set_decimation(g_trace[i], 0);
	}
	jbplot_set_legend_props(JBPLOT(g_plot), 1.0, NULL, NULL, LEGEND_POS_NONE);
	jbplot_legend_refresh(JBPLOT(g_plot));

	/* Speed plot */
	gtk_widget_set_size_request(speed_plot, min_width, min_height);
	jbplot_set_plot_title(JBPLOT(speed_plot), "Speed", 1);
	jbplot_set_plot_title_visible(JBPLOT(speed_plot), 1);
	jbplot_set_x_axis_label(JBPLOT(speed_plot), "Time (sec)", 1);
	//jbplot_set_x_axis_label_visible(JBPLOT(speed_plot), FALSE);
	jbplot_set_y_axis_label(JBPLOT(speed_plot), "Speed (MPH)", 1);
	jbplot_set_cursor_props(JBPLOT(speed_plot), CURSOR_VERT, grey, 2.0, LINETYPE_SOLID);
	for(i=0; i<MAX_LOADS; i++) {
		speed_trace[i] = jbplot_create_trace(0);	
		if(speed_trace[i]==NULL) {
			printf("Error creating plot traces!\n");
			exit(1);
		}
		char str[10];
		sprintf(str, "Speed (%d)", i);
		jbplot_trace_set_name(speed_trace[i], str);
		jbplot_add_trace(JBPLOT(speed_plot), speed_trace[i]);
		jbplot_trace_set_line_props(speed_trace[i], LINETYPE_SOLID, 1.0, &colors[i]);
		jbplot_trace_set_decimation(speed_trace[i], 0);
	}
	jbplot_set_legend_props(JBPLOT(speed_plot), 1.0, NULL, NULL, LEGEND_POS_NONE);
	jbplot_legend_refresh(JBPLOT(speed_plot));

#ifndef LINE2LINE
	/* reference frame accel plot */
	gtk_widget_set_size_request(accel_comp_plot,   min_width, min_height);
	jbplot_set_plot_title(JBPLOT(accel_comp_plot), "Reference Frame Acceleration", 1);
	jbplot_set_plot_title_visible(JBPLOT(accel_comp_plot), 1);
	jbplot_set_x_axis_label(JBPLOT(accel_comp_plot), "Time (sec)", 1);
	jbplot_set_y_axis_label(JBPLOT(accel_comp_plot), "Acceleration (m/s^2)", 1);
	jbplot_set_cursor_props(JBPLOT(accel_comp_plot), CURSOR_VERT, grey, 2.0, LINETYPE_SOLID);
	for(i=0; i<MAX_LOADS; i++) {
		axc_trace[i] = jbplot_create_trace(0);	
		ayc_trace[i] = jbplot_create_trace(0);	
		azc_trace[i] = jbplot_create_trace(0);	
		if(axc_trace[i]==NULL || ayc_trace[i]==NULL | azc_trace[i]==NULL) {
			printf("Error creating plot traces!\n");
			exit(1);
		}
		char str[10];
		sprintf(str, "x_ref (%d)", i);
		jbplot_trace_set_name(axc_trace[i], str);
		sprintf(str, "y_ref (%d)", i);
		jbplot_trace_set_name(ayc_trace[i], str);
		sprintf(str, "z_ref (%d)", i);
		jbplot_trace_set_name(azc_trace[i], str);
		jbplot_add_trace(JBPLOT(accel_comp_plot), axc_trace[i]);
		jbplot_add_trace(JBPLOT(accel_comp_plot), ayc_trace[i]);
		jbplot_add_trace(JBPLOT(accel_comp_plot), azc_trace[i]);
		jbplot_trace_set_line_props(axc_trace[i], LINETYPE_SOLID, 1.0, &red);
		jbplot_trace_set_decimation(axc_trace[i], 0);
		jbplot_trace_set_line_props(ayc_trace[i], LINETYPE_SOLID, 1.0, &green);
		jbplot_trace_set_decimation(ayc_trace[i], 0);
		jbplot_trace_set_line_props(azc_trace[i], LINETYPE_SOLID, 1.0, &blue);
		jbplot_trace_set_decimation(azc_trace[i], 0);
	}
	jbplot_set_legend_props(JBPLOT(accel_comp_plot), 1.0, NULL, NULL, LEGEND_POS_RIGHT);
	jbplot_legend_refresh(JBPLOT(accel_comp_plot));


	/* raw accel plot */
	gtk_widget_set_size_request(raw_accel_plot,    min_width, min_height);
	jbplot_set_plot_title(JBPLOT(raw_accel_plot), "Raw Accelerometer Data", 1);
	jbplot_set_plot_title_visible(JBPLOT(raw_accel_plot), 1);
	jbplot_set_x_axis_label(JBPLOT(raw_accel_plot), "Time (sec)", 1);
	//jbplot_set_x_axis_label_visible(JBPLOT(raw_accel_plot), FALSE);
	jbplot_set_y_axis_label(JBPLOT(raw_accel_plot), "Acceleration (m/s^2)", 1);
	jbplot_set_cursor_props(JBPLOT(raw_accel_plot), CURSOR_VERT, grey, 2.0, LINETYPE_SOLID);
	for(i=0; i<MAX_LOADS; i++) {
		ax_trace[i] = jbplot_create_trace(0);	
		ay_trace[i] = jbplot_create_trace(0);	
		az_trace[i] = jbplot_create_trace(0);	
		if(ax_trace[i]==NULL || ay_trace[i]==NULL | az_trace[i]==NULL) {
			printf("Error creating plot traces!\n");
			exit(1);
		}
		char str[10];
		sprintf(str, "x_body (%d)", i);
		jbplot_trace_set_name(ax_trace[i], str);
		sprintf(str, "y_body (%d)", i);
		jbplot_trace_set_name(ay_trace[i], str);
		sprintf(str, "z_body (%d)", i);
		jbplot_trace_set_name(az_trace[i], str);
		jbplot_add_trace(JBPLOT(raw_accel_plot), ax_trace[i]);
		jbplot_add_trace(JBPLOT(raw_accel_plot), ay_trace[i]);
		jbplot_add_trace(JBPLOT(raw_accel_plot), az_trace[i]);
		jbplot_trace_set_line_props(ax_trace[i], LINETYPE_SOLID, 1.0, &red);
		jbplot_trace_set_decimation(ax_trace[i], 0);
		jbplot_trace_set_line_props(ay_trace[i], LINETYPE_SOLID, 1.0, &green);
		jbplot_trace_set_decimation(ay_trace[i], 0);
		jbplot_trace_set_line_props(az_trace[i], LINETYPE_SOLID, 1.0, &blue);
		jbplot_trace_set_decimation(az_trace[i], 0);
	}
	jbplot_set_legend_props(JBPLOT(raw_accel_plot), 1.0, NULL, NULL, LEGEND_POS_RIGHT);
	jbplot_legend_refresh(JBPLOT(raw_accel_plot));

	/* rate gyro plot */
	gtk_widget_set_size_request(raw_w_plot,        min_width, min_height);
	jbplot_set_plot_title(JBPLOT(raw_w_plot), "Rate Gyro Data", 1);
	jbplot_set_plot_title_visible(JBPLOT(raw_w_plot), 1);
	jbplot_set_x_axis_label(JBPLOT(raw_w_plot), "Time (sec)", 1);
	jbplot_set_y_axis_label(JBPLOT(raw_w_plot), "Angular Velocity  (rads/s)", 1);
	jbplot_set_cursor_props(JBPLOT(raw_w_plot), CURSOR_VERT, grey, 2.0, LINETYPE_SOLID);
	for(i=0; i<MAX_LOADS; i++) {
		wx_trace[i] = jbplot_create_trace(0);	
		wy_trace[i] = jbplot_create_trace(0);	
		wz_trace[i] = jbplot_create_trace(0);	
		if(wx_trace[i]==NULL || wy_trace[i]==NULL | wz_trace[i]==NULL) {
			printf("Error creating plot traces!\n");
			exit(1);
		}
		char str[10];
		sprintf(str, "x_body (%d)", i);
		jbplot_trace_set_name(wx_trace[i], "x_body");
		sprintf(str, "y_body (%d)", i);
		jbplot_trace_set_name(wy_trace[i], "y_body");
		sprintf(str, "z_body (%d)", i);
		jbplot_trace_set_name(wz_trace[i], "z_body");
		jbplot_add_trace(JBPLOT(raw_w_plot), wx_trace[i]);
		jbplot_add_trace(JBPLOT(raw_w_plot), wy_trace[i]);
		jbplot_add_trace(JBPLOT(raw_w_plot), wz_trace[i]);
		jbplot_trace_set_line_props(wx_trace[i], LINETYPE_SOLID, 1.0, &red);
		jbplot_trace_set_decimation(wx_trace[i], 0);
		jbplot_trace_set_line_props(wy_trace[i], LINETYPE_SOLID, 1.0, &green);
		jbplot_trace_set_decimation(wy_trace[i], 0);
		jbplot_trace_set_line_props(wz_trace[i], LINETYPE_SOLID, 1.0, &blue);
		jbplot_trace_set_decimation(wz_trace[i], 0);
	}
	jbplot_set_legend_props(JBPLOT(raw_w_plot), 1.0, NULL, NULL, LEGEND_POS_RIGHT);
	jbplot_legend_refresh(JBPLOT(raw_w_plot));
#endif

	/* Distance from origin plot */
	gtk_widget_set_size_request(dist_plot,    min_width, min_height);
	jbplot_set_plot_title(JBPLOT(dist_plot), "Distance from Origin Plot", 1);
	jbplot_set_plot_title_visible(JBPLOT(dist_plot), 1);
	jbplot_set_x_axis_label(JBPLOT(dist_plot), "Time (sec)", 1);
	jbplot_set_y_axis_label(JBPLOT(dist_plot), "Distance (meters)", 1);
	jbplot_set_cursor_props(JBPLOT(dist_plot), CURSOR_VERT, grey, 2.0, LINETYPE_SOLID);
	for(i=0; i<MAX_LOADS; i++) {
		dist_trace[i] = jbplot_create_trace(0);	
		if(dist_trace[i]==NULL) {
			printf("Error creating plot traces!\n");
			exit(1);
		}
		char str[10];
		sprintf(str, "dist (%d)", i);
		jbplot_trace_set_name(dist_trace[i], str);
		jbplot_add_trace(JBPLOT(dist_plot), dist_trace[i]);
		jbplot_trace_set_line_props(dist_trace[i], LINETYPE_SOLID, 1.0, &colors[i]);
		jbplot_trace_set_decimation(dist_trace[i], 0);
	}
	jbplot_set_legend_props(JBPLOT(dist_plot), 1.0, NULL, NULL, LEGEND_POS_NONE);


#ifdef IMU_VIEW_DIAGNOSTIC
	/* magnetometer plot */
	gtk_widget_set_size_request(raw_mag_plot,      min_width, min_height);
	jbplot_set_plot_title(JBPLOT(raw_mag_plot), "Magnetometer Data", 1);
	jbplot_set_plot_title_visible(JBPLOT(raw_mag_plot), 1);
	jbplot_set_x_axis_label(JBPLOT(raw_mag_plot), "Time (sec)", 1);
	jbplot_set_y_axis_label(JBPLOT(raw_mag_plot), "Field Strength  (gauss)", 1);
	jbplot_set_cursor_props(JBPLOT(raw_mag_plot), CURSOR_VERT, grey, 2.0, LINETYPE_SOLID);
	for(i=0; i<MAX_LOADS; i++) {
		mx_trace[i] = jbplot_create_trace(0);	
		my_trace[i] = jbplot_create_trace(0);	
		mz_trace[i] = jbplot_create_trace(0);	
		if(mx_trace[i]==NULL || my_trace[i]==NULL | mz_trace[i]==NULL) {
			printf("Error creating plot traces!\n");
			exit(1);
		}
		char str[10];
		sprintf(str, "x_body (%d)", i);
		jbplot_trace_set_name(mx_trace[i], str);
		sprintf(str, "y_body (%d)", i);
		jbplot_trace_set_name(my_trace[i], str);
		sprintf(str, "z_body (%d)", i);
		jbplot_trace_set_name(mz_trace[i], str);
		jbplot_add_trace(JBPLOT(raw_mag_plot), mx_trace[i]);
		jbplot_add_trace(JBPLOT(raw_mag_plot), my_trace[i]);
		jbplot_add_trace(JBPLOT(raw_mag_plot), mz_trace[i]);
		jbplot_trace_set_line_props(mx_trace[i], LINETYPE_SOLID, 1.0, &red);
		jbplot_trace_set_decimation(mx_trace[i], 0);
		jbplot_trace_set_line_props(my_trace[i], LINETYPE_SOLID, 1.0, &green);
		jbplot_trace_set_decimation(my_trace[i], 0);
		jbplot_trace_set_line_props(mz_trace[i], LINETYPE_SOLID, 1.0, &blue);
		jbplot_trace_set_decimation(mz_trace[i], 0);
	}
	jbplot_set_legend_props(JBPLOT(raw_mag_plot), 1.0, NULL, NULL, LEGEND_POS_RIGHT);
	jbplot_legend_refresh(JBPLOT(raw_mag_plot));

	/* Temperature plot */
	gtk_widget_set_size_request(temp_plot,    min_width, min_height);
	jbplot_set_plot_title(JBPLOT(temp_plot), "Temperature Data", 1);
	jbplot_set_plot_title_visible(JBPLOT(temp_plot), 1);
	jbplot_set_x_axis_label(JBPLOT(temp_plot), "Time (sec)", 1);
	jbplot_set_y_axis_label(JBPLOT(temp_plot), "Temperature  (deg. C)", 1);
	jbplot_set_cursor_props(JBPLOT(temp_plot), CURSOR_VERT, grey, 2.0, LINETYPE_SOLID);
	for(i=0; i<MAX_LOADS; i++) {
		temp_trace[i] = jbplot_create_trace(0);	
		if(temp_trace[i]==NULL) {
			printf("Error creating plot traces!\n");
			exit(1);
		}
		char str[10];
		sprintf(str, "temp (%d)", i);
		jbplot_trace_set_name(temp_trace[i], str);
		jbplot_add_trace(JBPLOT(temp_plot), temp_trace[i]);
		jbplot_trace_set_line_props(temp_trace[i], LINETYPE_SOLID, 1.0, &colors[i]);
		jbplot_trace_set_decimation(temp_trace[i], 0);
	}
	jbplot_set_legend_props(JBPLOT(temp_plot), 1.0, NULL, NULL, LEGEND_POS_NONE);

#endif
}

void load_file(GtkButton *b, gpointer user_data) {
	GtkWidget *dialog;
	dialog = gtk_file_chooser_dialog_new("Load file from...",
	                                     NULL,
	                                     GTK_FILE_CHOOSER_ACTION_OPEN,
	                                     GTK_STOCK_CANCEL, GTK_RESPONSE_CANCEL,
	                                     GTK_STOCK_OPEN, GTK_RESPONSE_ACCEPT,
	                                     NULL);
	if(gtk_dialog_run(GTK_DIALOG(dialog)) == GTK_RESPONSE_ACCEPT) {
		char *filename;
		filename = gtk_file_chooser_get_filename(GTK_FILE_CHOOSER(dialog));
		strcpy(data_fname, filename);
		printf("selected file: %s\n", data_fname);
		gtk_widget_set_sensitive(GTK_WIDGET(b), FALSE);
		gtk_widget_set_sensitive(GTK_WIDGET(play_btn), FALSE);
		g_mutex_lock(mutex);
			do_load_file = TRUE;
		g_mutex_unlock(mutex);
		g_free(filename);
	}
	gtk_widget_destroy(dialog);

	return;
}

static void stop_zero_operation(gboolean cancel) {
	int status_context = gtk_statusbar_get_context_id(GTK_STATUSBAR(status_bar), "zero");
	pop_status(status_context);
	gdk_window_set_cursor(da->window, NULL);

	if(cancel) {
		g_mutex_lock(mutex);
			if(zero_state == ZERO_WAIT_FOR_POS || zero_state == ZERO_WAIT_FOR_DIR) {
				zero_state = ZERO_IDLE;
			}
		g_mutex_unlock(mutex);
	}
}


void zero_btn_clicked(GtkButton *b, gpointer user_data) {
	static GdkCursor *c1 = NULL;
	if(c1 == NULL) {
		c1 = gdk_cursor_new(GDK_CROSSHAIR);
	}
	gdk_window_set_cursor(da->window, c1);

	set_top_view();

	int status_context = gtk_statusbar_get_context_id(GTK_STATUSBAR(status_bar), "zero");
	pop_status(status_context);
	push_status(
		"Click on screen to set zero position (press escape to cancel)...",
		status_context
	);
	g_mutex_lock(mutex);
		zero_state = ZERO_WAIT_FOR_POS;
	g_mutex_unlock(mutex);
}

void play(GtkButton *b, gpointer user_data) {
	gtk_widget_set_sensitive(GTK_WIDGET(play_btn), FALSE);
	gtk_widget_set_sensitive(GTK_WIDGET(pause_btn), TRUE);
	playback_state = START_PLAYING;
}

void pause_cb(GtkButton *b, gpointer user_data) {
	gtk_widget_set_sensitive(GTK_WIDGET(play_btn), TRUE);
	gtk_widget_set_sensitive(GTK_WIDGET(pause_btn), FALSE);
	playback_state = GOTO_PAUSE;
	if(real_time_load) {
		abort_rt_load = TRUE;
	}
}

void slider_changed(GtkRange *r, gpointer user_data) {
	if(playback_state == PLAYING || 
		playback_state == START_PLAYING || 
		playback_state == WAITING_TO_PLAY) {
	}
	else {
		float val = gtk_range_get_value(r);
		int i;
		for(i=0; i<hist[load_count].current; i++) {
			if(hist[load_count].time[i] >= val) break;
		}
		if(i==hist[load_count].current) {
			i--;
		}
		if(i <= hist[load_count].last_crunched_index) {
			hist[load_count].playback_index = i;
			set_current_state2(&hist[load_count], i);
			jbplot_set_cursor_pos(JBPLOT(speed_plot), hist[load_count].time[i], 0);
			jbplot_set_cursor_pos(JBPLOT(g_plot), hist[load_count].time[i], 0);
		#ifndef LINE2LINE
			jbplot_set_cursor_pos(JBPLOT(accel_comp_plot), hist[load_count].time[i], 0);
			jbplot_set_cursor_pos(JBPLOT(raw_accel_plot), hist[load_count].time[i], 0);
			jbplot_set_cursor_pos(JBPLOT(raw_w_plot), hist[load_count].time[i], 0);
		#endif
			jbplot_set_cursor_pos(JBPLOT(dist_plot), hist[load_count].time[i], 0);
		#ifdef IMU_VIEW_DIAGNOSTIC
			update_dcm_labels2(&hist[load_count], i);
			jbplot_set_cursor_pos(JBPLOT(temp_plot), hist[load_count].time[i], 0);
			jbplot_set_cursor_pos(JBPLOT(raw_mag_plot), hist[load_count].time[i], 0);
		#endif
			gtk_widget_queue_draw(da);

			/* update plots */
			int playback_index = hist[load_count].playback_index;
			for(i=0; i<=load_count; i++) {
				set_trace_data_center(speed_trace[i], hist[i].time, hist[i].mph, hist[i].zero_index, hist[i].last_crunched_index, playback_index, MAX_TRACE_LENGTH);	
				set_trace_data_center(g_trace[i], hist[i].time, hist[i].g_load, hist[i].zero_index, hist[i].last_crunched_index, playback_index, MAX_TRACE_LENGTH);	

		#ifndef LINE2LINE
				set_trace_data_center(axc_trace[i], hist[i].time, hist[i].accel_ref[0], hist[i].zero_index, hist[i].last_crunched_index, playback_index, MAX_TRACE_LENGTH);	
				set_trace_data_center(ayc_trace[i], hist[i].time, hist[i].accel_ref[1], hist[i].zero_index, hist[i].last_crunched_index, playback_index, MAX_TRACE_LENGTH);	
				set_trace_data_center(azc_trace[i], hist[i].time, hist[i].accel_ref[2], hist[i].zero_index, hist[i].last_crunched_index, playback_index, MAX_TRACE_LENGTH);	

				set_trace_data_center(ax_trace[i], hist[i].time, hist[i].accel_body_raw[0], 0, hist[i].current-1, playback_index, MAX_TRACE_LENGTH);	
				set_trace_data_center(ay_trace[i], hist[i].time, hist[i].accel_body_raw[1], 0, hist[i].current-1, playback_index, MAX_TRACE_LENGTH);	
				set_trace_data_center(az_trace[i], hist[i].time, hist[i].accel_body_raw[2], 0, hist[i].current-1, playback_index, MAX_TRACE_LENGTH);	

				set_trace_data_center(wx_trace[i], hist[i].time, hist[i].w_body_raw[0], 0, hist[i].current-1, playback_index, MAX_TRACE_LENGTH);	
				set_trace_data_center(wy_trace[i], hist[i].time, hist[i].w_body_raw[1], 0, hist[i].current-1, playback_index, MAX_TRACE_LENGTH);	
				set_trace_data_center(wz_trace[i], hist[i].time, hist[i].w_body_raw[2], 0, hist[i].current-1, playback_index, MAX_TRACE_LENGTH);	
		#endif

				set_trace_data_center(dist_trace[i], hist[i].time, hist[i].dist, hist[i].zero_index, hist[i].last_crunched_index, playback_index, MAX_TRACE_LENGTH);	

#ifdef IMU_VIEW_DIAGNOSTIC
				set_trace_data_center(mx_trace[i],   hist[i].time, hist[i].mag_body_raw[0], 0, hist[i].current-1, playback_index, MAX_TRACE_LENGTH);	
				set_trace_data_center(my_trace[i],   hist[i].time, hist[i].mag_body_raw[1], 0, hist[i].current-1, playback_index, MAX_TRACE_LENGTH);	
				set_trace_data_center(mz_trace[i],   hist[i].time, hist[i].mag_body_raw[2], 0, hist[i].current-1, playback_index, MAX_TRACE_LENGTH);	
				set_trace_data_center(temp_trace[i], hist[i].time, hist[i].temp,            0, hist[i].current-1, playback_index, MAX_TRACE_LENGTH);	
#endif
			}

			jbplot_refresh(JBPLOT(speed_plot));
			jbplot_refresh(JBPLOT(g_plot));
		#ifndef LINE2LINE
			jbplot_refresh(JBPLOT(accel_comp_plot));
			jbplot_refresh(JBPLOT(raw_accel_plot));
			jbplot_refresh(JBPLOT(raw_w_plot));
		#endif
			jbplot_refresh(JBPLOT(dist_plot));
		#ifdef IMU_VIEW_DIAGNOSTIC
			jbplot_refresh(JBPLOT(temp_plot));
			jbplot_refresh(JBPLOT(raw_mag_plot));
		#endif

		}
		else {
			gtk_range_set_value(r, hist[load_count].time[hist[load_count].last_crunched_index]);
		}
	}
	return;
}

void xy_bounds(
	float *bounds,
	GLdouble *model, 
	GLdouble *proj, 
	GLint *view,
	float *min_x, float *max_x,
	float *min_y, float *max_y, int init) 
{
	GLdouble x,y,z;

	if(init) {
		*min_x = FLT_MAX; 
		*max_x = -FLT_MAX; 
		*min_y = FLT_MAX; 
		*max_y = -FLT_MAX;
	} 

	gluProject(bounds[0],bounds[2],bounds[4],model, proj, view, &x, &y, &z);
	if(x < *min_x) *min_x = x;	
	if(x > *max_x) *max_x = x;	
	if(y < *min_y) *min_y = y;	
	if(y > *max_y) *max_y = y;	
	gluProject(bounds[0],bounds[2],bounds[5],model, proj, view, &x, &y, &z);
	if(x < *min_x) *min_x = x;	
	if(x > *max_x) *max_x = x;	
	if(y < *min_y) *min_y = y;	
	if(y > *max_y) *max_y = y;	
	gluProject(bounds[0],bounds[3],bounds[4],model, proj, view, &x, &y, &z);
	if(x < *min_x) *min_x = x;	
	if(x > *max_x) *max_x = x;	
	if(y < *min_y) *min_y = y;	
	if(y > *max_y) *max_y = y;	
	gluProject(bounds[0],bounds[3],bounds[5],model, proj, view, &x, &y, &z);
	if(x < *min_x) *min_x = x;	
	if(x > *max_x) *max_x = x;	
	if(y < *min_y) *min_y = y;	
	if(y > *max_y) *max_y = y;	
	gluProject(bounds[1],bounds[2],bounds[4],model, proj, view, &x, &y, &z);
	if(x < *min_x) *min_x = x;	
	if(x > *max_x) *max_x = x;	
	if(y < *min_y) *min_y = y;	
	if(y > *max_y) *max_y = y;	
	gluProject(bounds[1],bounds[2],bounds[5],model, proj, view, &x, &y, &z);
	if(x < *min_x) *min_x = x;	
	if(x > *max_x) *max_x = x;	
	if(y < *min_y) *min_y = y;	
	if(y > *max_y) *max_y = y;	
	gluProject(bounds[1],bounds[3],bounds[4],model, proj, view, &x, &y, &z);
	if(x < *min_x) *min_x = x;	
	if(x > *max_x) *max_x = x;	
	if(y < *min_y) *min_y = y;	
	if(y > *max_y) *max_y = y;	
	gluProject(bounds[1],bounds[3],bounds[5],model, proj, view, &x, &y, &z);
	if(x < *min_x) *min_x = x;	
	if(x > *max_x) *max_x = x;	
	if(y < *min_y) *min_y = y;	
	if(y > *max_y) *max_y = y;	
}

void zoom_all() {
	GLdouble model[16];
	GLdouble proj[16];
	GLint    view[4];
	GLdouble x,y,z;
	float min_x, max_x;
	float min_y, max_y;
	int i;

	//printf("zoom_all() -----------------------\n");

	for(i=0; i<5; i++) {
		float m[16] = {1, 0, 0, 0, 
									 0, 1, 0, 0, 
									 0, 0, 1, 0, 
									 0, 0, 0, 1};

		glMatrixMode(GL_MODELVIEW);
		glLoadIdentity();
		do_view_transform();

		glGetDoublev(GL_MODELVIEW_MATRIX, model);

		glGetDoublev(GL_PROJECTION_MATRIX, proj);
		glGetIntegerv(GL_VIEWPORT, view);

		min_x = FLT_MAX; 
		max_x = -FLT_MAX; 
		min_y = FLT_MAX; 
		max_y = -FLT_MAX;

		if(ref_model_visible) {
			//printf("calling xy_bounds for reference body\n");
			xy_bounds(ref_bound_coords,model,proj,view,&min_x, &max_x,&min_y,&max_y,0); 
		}

		g_mutex_lock(mutex);
			do_body_transform();
		g_mutex_unlock(mutex);
		glGetDoublev(GL_MODELVIEW_MATRIX, model);

		if((model_visible && (hist[load_count].playback_index >= hist[load_count].zero_index || zero_state == ZERO_WAIT_FOR_DIR)) || !ref_model_visible) {
			//printf("calling xy_bounds for moving body\n");
			xy_bounds(motion_bound_coords,model,proj,view,&min_x, &max_x,&min_y,&max_y,0); 
		}

		float xy_ratio = x_range/y_range;	
		x_range = x_range * (max_x - min_x) / da->allocation.width;
		y_range = y_range * (max_y - min_y) / da->allocation.height;

		if(x_range/y_range > xy_ratio) {
			y_range = x_range / xy_ratio;
		}
		else {
			x_range = y_range * xy_ratio;
		}

		mindex(m,1,4) = -((min_x+max_x)-da->allocation.width)/2. * x_range/da->allocation.width;
		mindex(m,2,4) = -((min_y+max_y)-da->allocation.height)/2. * y_range/da->allocation.height;
		matrix_mult(m, trans_matrix, trans_matrix);

		configure(da, NULL, NULL);
	}

	gtk_widget_queue_draw(da);
}


void mouse_to_xy(float mx, float my, float *x, float *y) {
	GLdouble model[16];
	GLdouble proj[16];
	GLint    view[4];
	GLdouble xt, yt, zt;

	//printf("mouse_2_xy() -----------------------\n");

	float m[16] = {1, 0, 0, 0, 
								 0, 1, 0, 0, 
								 0, 0, 1, 0, 
								 0, 0, 0, 1};

	glMatrixMode(GL_MODELVIEW);
	glLoadIdentity();
	do_view_transform();

	glGetDoublev(GL_MODELVIEW_MATRIX, model);

	glGetDoublev(GL_PROJECTION_MATRIX, proj);
	glGetIntegerv(GL_VIEWPORT, view);

	gluUnProject(mx, my, 0.0, model, proj, view, &xt, &yt, &zt);

	//printf("clicked at (%g, %g, %g)\n", xt, yt, zt);
	*x = xt;
	*y = yt;
}


void screen_click(GtkWidget *w, GdkEventButton *event, gpointer user_data) {
	int status_context = gtk_statusbar_get_context_id(GTK_STATUSBAR(status_bar), "zero");

	gtk_window_set_focus(GTK_WINDOW(window), NULL);

	if(event->type == GDK_BUTTON_PRESS) {
		if(event->button == 1) {
			if(zero_state == ZERO_WAIT_FOR_POS) {
				float x, y;
				mouse_to_xy(event->x, w->allocation.height - event->y, &x, &y);
				g_mutex_lock(mutex);
					zero_data.x0 = x;
					zero_data.y0 = y;
					zero_data.dir_x = x;
					zero_data.dir_y = y;
					zero_state = ZERO_WAIT_FOR_DIR;
					zero_data.a_x_sum = 0.0;
					zero_data.a_y_sum = 0.0;
					zero_data.a_z_sum = 0.0;
					zero_data.w_x_sum = 0.0;
					zero_data.w_y_sum = 0.0;
					zero_data.w_z_sum = 0.0;
					zero_data.avg_count = 0;
					//hist.zero_index = hist.playback_index;
				g_mutex_unlock(mutex);
				pop_status(status_context);
				if(zero_direction == 3) {
					push_status(
						"Click on screen again to finalize zero operation."
						"  Down direction will be averaged until then"
						" (press escape to cancel)...",
						status_context
					);
				}
				else {
					push_status(
						"Click on screen to set forward direction."
						"  Down direction will be averaged until direction is"
						" selected (press escape to cancel)...",
						status_context
					);
				}
			}
			else if(zero_state == ZERO_WAIT_FOR_DIR) {
				float x, y;
				mouse_to_xy(event->x, w->allocation.height - event->y, &x, &y);
				gtk_toggle_button_set_active((GtkToggleButton *)show_model_cb, TRUE);
				g_mutex_lock(mutex);
					zero_data.dir_x = x;
					zero_data.dir_y = y;
					hist[load_count].zero_index = hist[load_count].playback_index;
					zero_state = ZERO_GO;
				g_mutex_unlock(mutex);
				stop_zero_operation(FALSE);
			}
			else {
				int i;
				drag_start.x = event->x;
				drag_start.y = event->y;
				for(i=0; i<16; i++) {
					drag_start_tm[i] = trans_matrix[i];
				}
				dragging = TRUE;
			}
		}
	}
	else if(event->type == GDK_BUTTON_RELEASE) {
		if(event->button == 1) {
			dragging = FALSE;
		}
	}
}

void screen_motion(GtkWidget *w, GdkEventMotion *event, gpointer user_data) {
	float m[16] = {1, 0, 0, 0, 
                 0, 1, 0, 0, 
                 0, 0, 1, 0, 
                 0, 0, 0, 1};

	if(zero_state == ZERO_WAIT_FOR_DIR) {
		float x, y;
		mouse_to_xy(event->x, w->allocation.height - event->y, &x, &y);
		g_mutex_lock(mutex);
			zero_data.dir_x = x;
			zero_data.dir_y = y;
		g_mutex_unlock(mutex);
		gtk_widget_queue_draw(da);
	}

	if(dragging) {
		mindex(trans_matrix,1,4) = mindex(drag_start_tm,1,4) + 
		                    (event->x - drag_start.x)*x_range / da->allocation.width;	
		mindex(trans_matrix,2,4) = mindex(drag_start_tm,2,4) - 
		                    (event->y - drag_start.y)*y_range / da->allocation.height;	

		gtk_widget_queue_draw(da);
	}
}

void checkbox_handler(GtkToggleButton *button, gpointer user_data) {
	gboolean state = gtk_toggle_button_get_active(button);
	if(GTK_WIDGET(button) == show_model_cb) {
		model_visible = state;
		gtk_widget_queue_draw(da);
	}
	else if (GTK_WIDGET(button) == show_ref_model_cb) {
		ref_model_visible = state;
		gtk_widget_queue_draw(da);
	}
	else if (GTK_WIDGET(button) == show_body_axes_cb) {
		body_axes_visible = state;
		gtk_widget_queue_draw(da);
	}
	else if (GTK_WIDGET(button) == show_ref_axes_cb) {
		ref_axes_visible = state;
		gtk_widget_queue_draw(da);
	}
	else if (GTK_WIDGET(button) == show_path_cb) {
		path_visible = state;
		gtk_widget_queue_draw(da);
	}
	else if (GTK_WIDGET(button) == only_orientation_cb) {
#ifdef IMU_VIEW_DIAGNOSTIC
		if(state && translate_only) {
			gtk_toggle_button_set_active(button, FALSE);
		}
		else {
#endif
			orient_only = state;
#ifdef IMU_VIEW_DIAGNOSTIC
		}
#endif
	}
#ifdef IMU_VIEW_DIAGNOSTIC
	else if (GTK_WIDGET(button) == only_translation_cb) {
		if(state && orient_only) {
			gtk_toggle_button_set_active(button, FALSE);
		}
		else {
			translate_only = state;
		}
	}
#endif
}

void display_usage(char *argv0) {
	char *cp = argv0;
	char * i = strrchr(argv0, '/');
	if( i >= argv0 && i < (argv0 + strlen(argv0) - 1) ) {
		cp = i+1;
	}
	printf("\n");	
	printf("Usage: %s [options] <motion_model> <reference_model> [<data_file>]\n", cp);
	printf("\n");	
	printf(
		" <motion_model> - path to STL file containing 3D geometry of moving body\n"
		"\n"
		" <reference_model> - path to STL file containing 3D geometry of stationary\n"
		"               reference object\n"	
		"\n"
		" <data_file> - (optional) path to data file containing IMU data in whitespace\n"
		"               delimited ascii format with the following column ordering\n"
		"               (or \"-\" to read data in same format from STDIN):\n\n"
		"                 time - in seconds\n"
		"                 w_x  - angular velocity in body x-direction (rate gyro)\n"
		"                 w_y  - angular velocity in body y-direction (rate gyro)\n"
		"                 w_z  - angular velocity in body z-direction (rate gyro)\n"
		"                 a_x  - acceleration in body x-direction (accel)\n"
		"                 a_y  - acceleration in body y-direction (accel)\n"
		"                 a_z  - acceleration in body z-direction (accel)\n"
		"\n\n"
		"Options:\n"
		" --angle <value_deg> : specify the angle between magnetic North direction and the x-axis\n"
		"                       direction in the inertial axis.  The value of this angle must be\n"
		"                       specified in degrees.\n"
		"\n"
	);	
	printf("\n");	
}

#ifndef LINE2LINE
gboolean g_thresh_handler(GtkWidget *w, GdkEventFocus *event, gpointer user_data) {
	float f;
	if(sscanf(gtk_entry_get_text(GTK_ENTRY(w)), "%f", &f) != 1) {
		f = 0.0;
	}
	char f_str[100];
	sprintf(f_str, "%g", f);
	gtk_entry_set_text(GTK_ENTRY(w), f_str);
	if(w == g_thresh_entry) {
		g_thresh_val = f;
		printf("setting g_threshold to %g\n", f);
	}
	return FALSE;
}
#endif

gboolean deadband_handler(GtkWidget *w, GdkEventFocus *event, gpointer user_data) {
	float f;
	if(sscanf(gtk_entry_get_text(GTK_ENTRY(w)), "%f", &f) != 1) {
		f = 0.0;
	}
	char f_str[100];
	sprintf(f_str, "%g", f);
	gtk_entry_set_text(GTK_ENTRY(w), f_str);
	if(w == accel_deadband) {
		accel_deadband_value = f;
		printf("setting accel_deadband to %g\n", f);
	}
	else if(w == gyro_deadband) {
		gyro_deadband_value = f;
		printf("setting gyro_deadband to %g\n", f);
	}
	return FALSE;
}

#ifndef LINE2LINE
gboolean offset_handler(GtkWidget *w, GdkEventFocus *event, gpointer user_data) {
	float f;
	if(sscanf(gtk_entry_get_text(GTK_ENTRY(w)), "%f", &f) != 1) {
		f = 0.0;
	}
	char f_str[100];
	sprintf(f_str, "%g", f);
	gtk_entry_set_text(GTK_ENTRY(w), f_str);
	if(w == ax_offset_entry) {
		accel_offsets[0] = f;
		printf("setting x_axis accel offset to %g\n", f);
	}
	else if(w == ay_offset_entry) {
		accel_offsets[1] = f;
		printf("setting y_axis accel offset to %g\n", f);
	}
	else if(w == az_offset_entry) {
		accel_offsets[2] = f;
		printf("setting z_axis accel offset to %g\n", f);
	}
	return FALSE;
}
#endif

void zero_dir_combo_handler(GtkComboBox *cb, gpointer user_data) {
	zero_direction = gtk_combo_box_get_active(cb);
	if(zero_direction < 0) {
		zero_direction = 0;
	}
}

void init_hist(struct hist_t *hp) {
	int i;
	int new_size = HIST_CHUNK_SIZE;
	for(i=0; i<3; i++) {
		hp->w_body_raw[i] = g_realloc(NULL, new_size * sizeof(*hp->w_body_raw[i]));
		hp->accel_body_raw[i] = g_realloc(NULL, new_size * sizeof(*hp->accel_body_raw[i]));
		hp->mag_body_raw[i] = g_realloc(NULL, new_size * sizeof(*hp->mag_body_raw[i]));
		hp->vel[i] = g_realloc(NULL, new_size * sizeof(*hp->vel[i]));
		hp->pos[i] = g_realloc(NULL, new_size * sizeof(*hp->pos[i]));
		hp->accel_ref[i] = g_realloc(NULL, new_size * sizeof(*hp->accel_ref[i]));
	}
	for(i=0; i<9; i++) {
		hp->dcm[i] = g_realloc(NULL, new_size * sizeof(*hp->dcm[i]));
	}
	hp->g_load = g_realloc(NULL, new_size * sizeof(*hp->g_load));
	hp->temp = g_realloc(NULL, new_size * sizeof(*hp->temp));
	hp->dist = g_realloc(NULL, new_size * sizeof(*hp->dist));
	hp->mph = g_realloc(NULL, new_size * sizeof(*hp->mph));
	hp->time = g_realloc(NULL, new_size * sizeof(*hp->time));
	hp->size = new_size;
	hp->current = 0;
	hp->zero_index = 3000000;
}

static int get_hist_size(struct hist_t *h) {
	int byte_count = 0;
	byte_count += 3 * h->size * sizeof(*h->w_body_raw[0]);
	byte_count += 3 * h->size * sizeof(*h->accel_body_raw[0]);
	byte_count += 3 * h->size * sizeof(*h->mag_body_raw[0]);
	byte_count += 9 * h->size * sizeof(*h->dcm[0]);
	byte_count += 3 * h->size * sizeof(*h->vel[0]);
	byte_count += 3 * h->size * sizeof(*h->pos[0]);
	byte_count += h->size * sizeof(*h->g_load);
	byte_count += h->size * sizeof(*h->temp);
	byte_count += h->size * sizeof(*h->dist);
	byte_count += h->size * sizeof(*h->mph);
	byte_count += h->size * sizeof(*h->accel_ref[0]);
	byte_count += h->size * sizeof(*h->time);
	return byte_count;
}


static void expand_hist(struct hist_t *hp) {
	int i;
	int new_size = hp->size + HIST_CHUNK_SIZE;
	for(i=0; i<3; i++) {
		hp->w_body_raw[i] = g_realloc(hp->w_body_raw[i], new_size * sizeof(*hp->w_body_raw[i]));
		hp->accel_body_raw[i] = g_realloc(hp->accel_body_raw[i], new_size * sizeof(*hp->accel_body_raw[i]));
		hp->mag_body_raw[i] = g_realloc(hp->mag_body_raw[i], new_size * sizeof(*hp->mag_body_raw[i]));
		hp->vel[i] = g_realloc(hp->vel[i], new_size * sizeof(*hp->vel[i]));
		hp->pos[i] = g_realloc(hp->pos[i], new_size * sizeof(*hp->pos[i]));
		hp->accel_ref[i] = g_realloc(hp->accel_ref[i], new_size * sizeof(*hp->accel_ref[i]));
	}
	for(i=0; i<9; i++) {
		hp->dcm[i] = g_realloc(hp->dcm[i], new_size * sizeof(*hp->dcm[i]));
	}
	hp->g_load = g_realloc(hp->g_load, new_size * sizeof(*hp->g_load));
	hp->temp = g_realloc(hp->temp, new_size * sizeof(*hp->temp));
	hp->dist = g_realloc(hp->dist, new_size * sizeof(*hp->dist));
	hp->mph = g_realloc(hp->mph, new_size * sizeof(*hp->mph));
	hp->time = g_realloc(hp->time, new_size * sizeof(*hp->time));
	hp->size = new_size;
	GTimeVal tv;
	g_get_current_time(&tv);
	printf("time: %ld sec, hist size: %d bytes\n", tv.tv_sec, get_hist_size(hp));
}


int main(int argc, char *argv[]) {
	int i,j;
	GtkWidget *top_level_vbox;
	GtkWidget *button_bar;
	GtkWidget *button_bar2;
	GtkWidget *button_bar3;
	GtkWidget *zero_btn;
	GtkWidget *load_file_btn;
	GtkWidget *plot_scroll_win;
	GtkWidget *plot_v_box;
	GtkWidget *dcm_table;
	GdkGLConfig *glconfig;
	GThread *file_loader_thread;
	GThread *playback_thread;

	gtk_init (&argc, &argv);
	gtk_gl_init (&argc, &argv);

	/* initialize history data structure */
	for(i=0; i<MAX_LOADS; i++) {
		init_hist(&hist[i]);
	}

	if(!g_thread_get_initialized()) {
		g_thread_init(NULL);
	}
	gdk_threads_init();
	mutex = g_mutex_new();	

	char *model_fname;
	char *reference_fname;

	/* parse cmd line args */
	int num_parsed = 0;
	int data_file_specified = 0;
	for(i=1; i<argc; i++) {
		if(argv[i][0] == '-' && strlen(argv[i])>1) {
			/* it's a cmd line option */
			if(!strcmp(argv[i], "--angle")) {
				/* angle */
				if(i < (argc-1)) {
					north_angle_deg = atof(argv[i+1]);
					printf("Got optional argument: angle = %f\n", north_angle_deg);
					i++;
				}
			}
		}
		else {
			/* it's a standard argument */
			switch(num_parsed) {
				case 0:
					model_fname = argv[i];
					break;
				case 1:
					reference_fname = argv[i];
					break;
				case 2:
					data_file_specified = 1;
					if(strlen(argv[i])==1 && argv[i][0]=='-') {
						printf("reading from stdin (real-time mode)...\n");
						real_time_load = TRUE;
						data_fname[0] = '\0'; /* empty string */
					}
					else {
						real_time_load = FALSE;
						if(strlen(argv[i]) >= sizeof(data_fname)) {
							perror("filename too long!");
							exit(1);
						}
						strcpy(data_fname, argv[i]);
					}
					break;
				default:
					;
			}
			num_parsed++;
		}
	}
	if(num_parsed < 2) {
		display_usage(argv[0]);
		exit(1);
	}
	
	window = gtk_window_new (GTK_WINDOW_TOPLEVEL);
	//gtk_window_set_default_size (GTK_WINDOW (window), 600, 600);
	gtk_window_maximize(GTK_WINDOW(window));

	top_level_vbox = gtk_vbox_new(FALSE, 2);
	gtk_container_add(GTK_CONTAINER (window), top_level_vbox);

	button_bar = gtk_hbox_new(FALSE, 4);
	gtk_box_pack_start(GTK_BOX(top_level_vbox), button_bar, FALSE, FALSE, 0);

	load_file_btn = gtk_button_new_with_label("Load File");
	gtk_box_pack_start(GTK_BOX(button_bar), load_file_btn, FALSE, FALSE, 0);
	g_signal_connect(load_file_btn, "clicked", G_CALLBACK(load_file), NULL);

	play_btn = gtk_button_new_from_stock(GTK_STOCK_MEDIA_PLAY);	
	gtk_box_pack_start(GTK_BOX(button_bar), play_btn, FALSE, FALSE, 0);
	g_signal_connect(play_btn, "clicked", G_CALLBACK(play), NULL);

	pause_btn = gtk_button_new_from_stock(GTK_STOCK_MEDIA_PAUSE);	
	gtk_box_pack_start(GTK_BOX(button_bar), pause_btn, FALSE, FALSE, 0);
	gtk_widget_set_sensitive(pause_btn, FALSE);
	g_signal_connect(pause_btn, "clicked", G_CALLBACK(pause_cb), NULL);

	slider = gtk_hscale_new_with_range(0, 1.0, 0.01);
	gtk_box_pack_start(GTK_BOX(button_bar), slider, TRUE, TRUE, 0);
	//gtk_range_set_fill_level(GTK_RANGE(slider), 0.4);
	//gtk_range_set_show_fill_level(GTK_RANGE(slider), TRUE);
	g_signal_connect(slider, "value-changed", G_CALLBACK(slider_changed), NULL);

	button_bar2 = gtk_hbox_new(FALSE, 4);
	gtk_box_pack_start(GTK_BOX(top_level_vbox), button_bar2, FALSE, FALSE, 0);

	show_model_cb = gtk_check_button_new_with_label("Show Moving Model");
	gtk_box_pack_start(GTK_BOX(button_bar2), show_model_cb, FALSE, FALSE, 0);
	g_signal_connect(show_model_cb, "toggled", G_CALLBACK(checkbox_handler), NULL);

	show_ref_model_cb = gtk_check_button_new_with_label("Show Reference Frame Model");
	gtk_box_pack_start(GTK_BOX(button_bar2), show_ref_model_cb, FALSE, FALSE, 0);
	g_signal_connect(show_ref_model_cb, "toggled", G_CALLBACK(checkbox_handler), NULL);

	show_body_axes_cb = gtk_check_button_new_with_label("Show Body Axes");
	gtk_box_pack_start(GTK_BOX(button_bar2), show_body_axes_cb, FALSE, FALSE, 0);
	g_signal_connect(show_body_axes_cb, "toggled", G_CALLBACK(checkbox_handler), NULL);

	show_ref_axes_cb = gtk_check_button_new_with_label("Show Reference Axes");
	gtk_box_pack_start(GTK_BOX(button_bar2), show_ref_axes_cb, FALSE, FALSE, 0);
	g_signal_connect(show_ref_axes_cb, "toggled", G_CALLBACK(checkbox_handler), NULL);

	show_path_cb = gtk_check_button_new_with_label("Show Motion Path");
	gtk_box_pack_start(GTK_BOX(button_bar2), show_path_cb, FALSE, FALSE, 0);
	g_signal_connect(show_path_cb, "toggled", G_CALLBACK(checkbox_handler), NULL);

	button_bar3 = gtk_hbox_new(FALSE, 4);
	gtk_box_pack_start(GTK_BOX(top_level_vbox), button_bar3, FALSE, FALSE, 0);

	zero_btn = gtk_button_new_with_label("Zero");	
	gtk_box_pack_start(GTK_BOX(button_bar3), zero_btn, FALSE, FALSE, 0);
	g_signal_connect(zero_btn, "clicked", G_CALLBACK(zero_btn_clicked), NULL);

	zero_dir_combo = gtk_combo_box_new_text();
	gtk_combo_box_append_text(GTK_COMBO_BOX(zero_dir_combo), "X");
	gtk_combo_box_append_text(GTK_COMBO_BOX(zero_dir_combo), "Y");
	gtk_combo_box_append_text(GTK_COMBO_BOX(zero_dir_combo), "Z");
	gtk_combo_box_append_text(GTK_COMBO_BOX(zero_dir_combo), "Mag");
	gtk_combo_box_set_active(GTK_COMBO_BOX(zero_dir_combo), 3);
	gtk_widget_set_tooltip_text(
		zero_dir_combo, 
		"Designates which body-axis is specified during the zeroing process (or to use Magnetometer instead)"
	);
	g_signal_connect(zero_dir_combo, "changed", G_CALLBACK(zero_dir_combo_handler), NULL);
	gtk_box_pack_start(GTK_BOX(button_bar3), zero_dir_combo, FALSE, FALSE, 0);

	gtk_box_pack_start(GTK_BOX(button_bar3), gtk_vseparator_new(), FALSE, FALSE, 0);

	only_orientation_cb = gtk_check_button_new_with_label("Only Track Orientiation");
	gtk_box_pack_start(GTK_BOX(button_bar3), only_orientation_cb, FALSE, FALSE, 0);
	g_signal_connect(only_orientation_cb, "toggled", G_CALLBACK(checkbox_handler), NULL);

#ifdef IMU_VIEW_DIAGNOSTIC
	only_translation_cb = gtk_check_button_new_with_label("Only Track Translation");
	gtk_box_pack_start(GTK_BOX(button_bar3), only_translation_cb, FALSE, FALSE, 0);
	g_signal_connect(only_translation_cb, "toggled", G_CALLBACK(checkbox_handler), NULL);
#endif

#ifndef LINE2LINE
	gtk_box_pack_start(GTK_BOX(button_bar3), gtk_vseparator_new(), FALSE, FALSE, 0);
	
	gtk_box_pack_start(GTK_BOX(button_bar3), gtk_label_new("a_x_offset"), FALSE, FALSE, 0);
	
	ax_offset_entry = gtk_entry_new();
	gtk_box_pack_start(GTK_BOX(button_bar3), ax_offset_entry, FALSE, FALSE, 0);
	g_signal_connect(ax_offset_entry, "focus-out-event", G_CALLBACK(offset_handler), NULL);
	gtk_entry_set_width_chars(GTK_ENTRY(ax_offset_entry), 5);
	gtk_entry_set_text(GTK_ENTRY(ax_offset_entry), "0.0");

	gtk_box_pack_start(GTK_BOX(button_bar3), gtk_label_new("a_y_offset"), FALSE, FALSE, 0);

	ay_offset_entry = gtk_entry_new();
	gtk_box_pack_start(GTK_BOX(button_bar3), ay_offset_entry, FALSE, FALSE, 0);
	g_signal_connect(ay_offset_entry, "focus-out-event", G_CALLBACK(offset_handler), NULL);
	gtk_entry_set_width_chars(GTK_ENTRY(ay_offset_entry), 5);
	gtk_entry_set_text(GTK_ENTRY(ay_offset_entry), "0.0");

	gtk_box_pack_start(GTK_BOX(button_bar3), gtk_label_new("a_z_offset"), FALSE, FALSE, 0);

	az_offset_entry = gtk_entry_new();
	gtk_box_pack_start(GTK_BOX(button_bar3), az_offset_entry, FALSE, FALSE, 0);
	g_signal_connect(az_offset_entry, "focus-out-event", G_CALLBACK(offset_handler), NULL);
	gtk_entry_set_width_chars(GTK_ENTRY(az_offset_entry), 5);
	gtk_entry_set_text(GTK_ENTRY(az_offset_entry), "0.0");
#endif

	gtk_box_pack_start(GTK_BOX(button_bar3), gtk_vseparator_new(), FALSE, FALSE, 0);

	gtk_box_pack_start(GTK_BOX(button_bar3), gtk_label_new("accel deadband"), FALSE, FALSE, 0);
	accel_deadband = gtk_entry_new();
	gtk_box_pack_start(GTK_BOX(button_bar3), accel_deadband, FALSE, FALSE, 0);
	g_signal_connect(accel_deadband, "focus-out-event", G_CALLBACK(deadband_handler), NULL);
	gtk_entry_set_width_chars(GTK_ENTRY(accel_deadband), 5);
	gtk_entry_set_text(GTK_ENTRY(accel_deadband), "0.0");
	gtk_box_pack_start(GTK_BOX(button_bar3), gtk_label_new("gyro deadband"), FALSE, FALSE, 0);
	gyro_deadband = gtk_entry_new();
	gtk_box_pack_start(GTK_BOX(button_bar3), gyro_deadband, FALSE, FALSE, 0);
	g_signal_connect(gyro_deadband, "focus-out-event", G_CALLBACK(deadband_handler), NULL);
	gtk_entry_set_width_chars(GTK_ENTRY(gyro_deadband), 5);
	gtk_entry_set_text(GTK_ENTRY(gyro_deadband), "0.0");

#ifndef LINE2LINE
	gtk_box_pack_start(GTK_BOX(button_bar3), gtk_vseparator_new(), FALSE, FALSE, 0);

	gtk_box_pack_start(GTK_BOX(button_bar3), gtk_label_new("ATH G-Index Threshold"), FALSE, FALSE, 0);
	g_thresh_entry = gtk_entry_new();
	gtk_box_pack_start(GTK_BOX(button_bar3), g_thresh_entry, FALSE, FALSE, 0);
	g_signal_connect(g_thresh_entry, "focus-out-event", G_CALLBACK(g_thresh_handler), NULL);
	gtk_entry_set_width_chars(GTK_ENTRY(g_thresh_entry), 5);
	gtk_entry_set_text(GTK_ENTRY(g_thresh_entry), init_g_thresh_str);
	sscanf(init_g_thresh_str, "%f", &g_thresh_val);
#endif

	h_pane = gtk_hpaned_new();
	gtk_box_pack_start(GTK_BOX(top_level_vbox), h_pane, TRUE, TRUE, 0);

	status_bar = gtk_statusbar_new();
	gtk_box_pack_start(GTK_BOX(top_level_vbox), status_bar, FALSE, FALSE, 0);

	da = gtk_drawing_area_new ();
	gtk_paned_pack1(GTK_PANED(h_pane), da, TRUE, TRUE);
	gtk_widget_set_events (da, GDK_EXPOSURE_MASK);
	gtk_widget_add_events(da, GDK_BUTTON_PRESS_MASK);
	gtk_widget_add_events(da, GDK_BUTTON_RELEASE_MASK);
	gtk_widget_add_events(da, GDK_POINTER_MOTION_MASK);
	g_signal_connect(da, "button-press-event", G_CALLBACK(screen_click), NULL);
	g_signal_connect(da, "button-release-event", G_CALLBACK(screen_click), NULL);
	g_signal_connect(da, "motion-notify-event", G_CALLBACK(screen_motion), NULL);

	plot_scroll_win = gtk_scrolled_window_new(NULL, NULL);
	gtk_scrolled_window_set_policy(
		GTK_SCROLLED_WINDOW(plot_scroll_win), 
		GTK_POLICY_NEVER,
		GTK_POLICY_AUTOMATIC
	);
	gtk_paned_pack2(GTK_PANED(h_pane), plot_scroll_win, TRUE, TRUE);

	plot_v_box = gtk_vbox_new(FALSE, 4);
	gtk_scrolled_window_add_with_viewport(GTK_SCROLLED_WINDOW(plot_scroll_win), plot_v_box);

	g_plot = jbplot_new();
	gtk_box_pack_start(GTK_BOX(plot_v_box), g_plot, TRUE, TRUE, 0);
	speed_plot = jbplot_new();
	gtk_box_pack_start(GTK_BOX(plot_v_box), speed_plot, TRUE, TRUE, 0);

#ifndef LINE2LINE
	accel_comp_plot = jbplot_new();
	gtk_box_pack_start(GTK_BOX(plot_v_box), accel_comp_plot, TRUE, TRUE, 0);
	raw_accel_plot = jbplot_new();
	gtk_box_pack_start(GTK_BOX(plot_v_box), raw_accel_plot, TRUE, TRUE, 0);
	raw_w_plot = jbplot_new();
	gtk_box_pack_start(GTK_BOX(plot_v_box), raw_w_plot, TRUE, TRUE, 0);
#endif

#ifdef IMU_VIEW_DIAGNOSTIC
	raw_mag_plot = jbplot_new();
	gtk_box_pack_start(GTK_BOX(plot_v_box), raw_mag_plot, TRUE, TRUE, 0);
	temp_plot = jbplot_new();
	gtk_box_pack_start(GTK_BOX(plot_v_box), temp_plot, TRUE, TRUE, 0);
#endif

	dist_plot = jbplot_new();
	gtk_box_pack_start(GTK_BOX(plot_v_box), dist_plot, TRUE, TRUE, 0);

	config_plots();

#ifdef IMU_VIEW_DIAGNOSTIC
	gtk_box_pack_start(GTK_BOX(plot_v_box), gtk_label_new("Direction Cosine Matrix"), FALSE, FALSE, 0);
	dcm_table = gtk_table_new(3,3,TRUE);
	gtk_box_pack_start(GTK_BOX(plot_v_box), dcm_table, TRUE, TRUE, 0);

	for(i=0; i<3; i++) {	
		for(j=0; j<3; j++) {	
			dcm_labels[i][j] = gtk_label_new("a");
			gtk_label_set_width_chars(GTK_LABEL(dcm_labels[i][j]), 10);
			gtk_label_set_justify(GTK_LABEL(dcm_labels[i][j]), GTK_JUSTIFY_CENTER);
			gtk_table_attach(GTK_TABLE(dcm_table), dcm_labels[i][j], j,j+1, i,i+1, GTK_SHRINK, GTK_SHRINK, 5,5);
		}
	}
	
	gtk_box_pack_start(GTK_BOX(plot_v_box), gtk_label_new("Euler Angles"), FALSE, FALSE, 0);
	for(i=0; i<3; i++) {	
		euler_labels[i] = gtk_label_new("a");
		gtk_box_pack_start(GTK_BOX(plot_v_box), euler_labels[i], FALSE, FALSE, 0);
	}
#endif

	g_signal_connect_swapped(window,"destroy",G_CALLBACK(gtk_main_quit),NULL);

	gtk_widget_show(window);


	init_axes(&body_axes);
	init_axes(&ref_axes);
	gtk_toggle_button_set_active((GtkToggleButton *)show_model_cb, TRUE);
	gtk_toggle_button_set_active((GtkToggleButton *)show_ref_model_cb, TRUE);
	gtk_toggle_button_set_active((GtkToggleButton *)show_body_axes_cb, FALSE);
	gtk_toggle_button_set_active((GtkToggleButton *)show_ref_axes_cb, FALSE);
	gtk_toggle_button_set_active((GtkToggleButton *)show_path_cb, FALSE);
	gtk_toggle_button_set_active((GtkToggleButton *)only_orientation_cb, FALSE);
#ifdef IMU_VIEW_DIAGNOSTIC
	gtk_toggle_button_set_active((GtkToggleButton *)only_translation_cb, FALSE);
#endif
	orient_only = FALSE;
	translate_only = FALSE;

	zero_dir_axis = gluNewQuadric();

	/* prepare GL */
	glconfig = gdk_gl_config_new_by_mode (
			GDK_GL_MODE_RGB |
			GDK_GL_MODE_DEPTH |
			GDK_GL_MODE_DOUBLE);

	if (!glconfig) {
		g_assert_not_reached ();
	}

	if (!gtk_widget_set_gl_capability (da, glconfig, NULL, TRUE, GDK_GL_RGBA_TYPE)) {
		g_assert_not_reached ();
	}

	g_signal_connect (window, "key-press-event",G_CALLBACK (key_press), NULL);
	g_signal_connect (window, "configure-event", G_CALLBACK (configure_win), NULL);
	g_signal_connect (da, "configure-event", G_CALLBACK (configure), NULL);
	g_signal_connect (da, "expose-event", G_CALLBACK (da_expose), NULL);

	gtk_widget_show_all (window);

	int status_context = gtk_statusbar_get_context_id(GTK_STATUSBAR(status_bar), "main");
	push_status("Idle", status_context);

	int ret;
	printf("loading reference model file...\n");
	ret = load_model(reference_fname, da, &ref_display_list, ref_bound_coords);
	printf("import_stl_file() returned %d\n", ret);

	printf("loading motion model file...\n");
	ret = load_model(model_fname, da, &motion_display_list, motion_bound_coords);
	printf("import_stl_file() returned %d\n", ret);

	init_gl_props(da);

	file_loader_thread = g_thread_create(file_loader, (gpointer)load_file_btn, TRUE, NULL);
	if(file_loader_thread == NULL) {
		printf("Error creating file loader thread!\n");
	}
	playback_thread = g_thread_create(playback, NULL, TRUE, NULL);
	if(playback_thread == NULL) {
		printf("Error creating playback thread!\n");
	}

	/* check if a data file was passed on cmd line */
	if(data_file_specified) {
		gtk_widget_set_sensitive(load_file_btn, FALSE);
		gtk_widget_set_sensitive(play_btn, FALSE);
		g_mutex_lock(mutex);
			do_load_file = TRUE;
		g_mutex_unlock(mutex);
	}


	zoom_all();

	gtk_main ();
}

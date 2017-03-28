/* Copyright (C) 2000  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

BEGINEXTERN
typedef struct dblPointList{
  double *d;                   /* data */
  long nb;                     /* number of elements */
  double xsml,xbig,ysml,ybig;  /* extrema */
} dblPointList;

typedef struct RectObj {
  struct RectObj *next;
  long code,color;
} RectObj;

typedef struct PariRect {
  RectObj *head,*tail;
  long sizex,sizey;
  double cursorx,cursory;
  double xscale,yscale;
  double xshift,yshift;
} PariRect;

/* The structures below are "subclasses" of RectObj. */

typedef struct RectObj1P {
  struct RectObj *next;
  long code,color;
  double x,y;
} RectObj1P;

typedef struct RectObj2P {
  struct RectObj *next;
  long code,color;
  double x1,y1;
  double x2,y2;
} RectObj2P;

typedef struct RectObjMP {
  struct RectObj *next;
  long code,color;
  long count;
  double *xs,*ys;
} RectObjMP;

typedef struct RectObjST {
  struct RectObj *next;
  long code,color;
  long length;
  char *s;
  double x,y;
  long dir;
} RectObjST;

typedef struct RectObjPN {
  struct RectObj *next;
  long code,color;
  long pen;
} RectObjPN;

typedef struct RectObjPS {
  struct RectObj *next;
  long code,color;
  double size;
} RectObjPS;

struct plot_points { long x, y; };
struct plot_eng {
  PARI_plot *pl;
  void *data;
  void (*sc)(void *data, long col);
  void (*pt)(void *data, long x, long y);
  void (*ln)(void *data, long x1, long y1, long x2, long y2);
  void (*bx)(void *data, long x, long y, long w, long h);
  void (*mp)(void *data, long n, struct plot_points *points);
  void (*ml)(void *data, long n, struct plot_points *points);
  void (*st)(void *data, long x, long y, char *s, long l);
};

/* Pointer conversion. */
#define RoMV(rop) ((RectObj1P*)rop)
#define RoPT(rop) ((RectObj1P*)rop)
#define RoLN(rop) ((RectObj2P*)rop)
#define RoBX(rop) ((RectObj2P*)rop)
#define RoMP(rop) ((RectObjMP*)rop)
#define RoML(rop) ((RectObjMP*)rop)
#define RoST(rop) ((RectObjST*)rop)
#define RoPTT(rop) ((RectObjPN*)rop)
#define RoPTS(rop) ((RectObjPS*)rop)
#define RoLNT(rop) ((RectObjPN*)rop)

/* All the access to the rectangle data go via these macros! */
#define RHead(rp) ((rp)->head)
#define RTail(rp) ((rp)->tail)
#define RXsize(rp) ((rp)->sizex)
#define RYsize(rp) ((rp)->sizey)
#define RXcursor(rp) ((rp)->cursorx)
#define RYcursor(rp) ((rp)->cursory)
#define RXshift(rp) ((rp)->xshift)
#define RYshift(rp) ((rp)->yshift)
#define RXscale(rp) ((rp)->xscale)
#define RYscale(rp) ((rp)->yscale)

#define RoNext(rop) ((rop)->next)
#define RoType(rop) ((rop)->code)
#define RoCol(rop) ((rop)->color)
#define RoMVx(rop) (RoMV(rop)->x)
#define RoMVy(rop) (RoMV(rop)->y)
#define RoPTx(rop) (RoPT(rop)->x)
#define RoPTy(rop) (RoPT(rop)->y)
#define RoLNx1(rop) (RoLN(rop)->x1)
#define RoLNy1(rop) (RoLN(rop)->y1)
#define RoLNx2(rop) (RoLN(rop)->x2)
#define RoLNy2(rop) (RoLN(rop)->y2)
#define RoBXx1(rop) (RoBX(rop)->x1)
#define RoBXy1(rop) (RoBX(rop)->y1)
#define RoBXx2(rop) (RoBX(rop)->x2)
#define RoBXy2(rop) (RoBX(rop)->y2)

#define RoMPcnt(rop) (RoMP(rop)->count)
#define RoMPxs(rop) (RoMP(rop)->xs)
#define RoMPys(rop) (RoMP(rop)->ys)

#define RoMLcnt(rop) (RoML(rop)->count)
#define RoMLxs(rop) (RoML(rop)->xs)
#define RoMLys(rop) (RoML(rop)->ys)

#define RoSTs(rop) (RoST(rop)->s)
#define RoSTl(rop) (RoST(rop)->length)
#define RoSTx(rop) (RoST(rop)->x)
#define RoSTy(rop) (RoST(rop)->y)
#define RoSTdir(rop) (RoST(rop)->dir)

#define RoPTTpen(rop) (RoPTT(rop)->pen)
#define RoLNTpen(rop) (RoLNT(rop)->pen)
#define RoPTSsize(rop) (RoPTS(rop)->size)

#define RoSTdirLEFT       0x00
#define RoSTdirCENTER     0x01
#define RoSTdirRIGHT      0x02
#define RoSTdirHPOS_mask  0x03

#define RoSTdirBOTTOM     0x00
#define RoSTdirVCENTER    0x04
#define RoSTdirTOP        0x08
#define RoSTdirVPOS_mask  0x0c

#define RoSTdirHGAP       0x10
#define RoSTdirVGAP       0x20

#define PLOT_PARAMETRIC   0x00001
#define PLOT_RECURSIVE    0x00002
#define PLOT_NO_RESCALE   0x00004
#define PLOT_NO_AXE_X     0x00008
#define PLOT_NO_AXE_Y     0x00010
#define PLOT_NO_FRAME     0x00020
#define PLOT_POINTS       0x00040
#define PLOT_POINTS_LINES 0x00080
#define PLOT_SPLINES      0x00100
#define PLOT_NO_TICK_X    0x00200
#define PLOT_NO_TICK_Y    0x00400
#define PLOT_NODOUBLETICK 0x00800
#define PLOT_COMPLEX      0x01000

#define RECT_CP_RELATIVE  0x1
#define RECT_CP_NW        0x0
#define RECT_CP_SW        0x2
#define RECT_CP_SE        0x4
#define RECT_CP_NE        0x6

void gen_draw(struct plot_eng *eng, long *w, long *x, long *y, long lw, double xs, double ys);

void gp_get_plot(PARI_plot *T);
ENDEXTERN

/* Copyright (C) 2016  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

#include <emscripten/emscripten.h>
#include "pari.h"

void
pari_emscripten_wget(const char *s)
{
  const char *name = stack_sprintf("/gpjs/root/%s",s);
  emscripten_async_wget(name,s,NULL,NULL);
  pari_err(e_MISC,"retry");
}

void
pari_emscripten_help(const char *s)
{
  pari_err(e_MISC,"Help: http://pari.math.u-bordeaux.fr/dochtml/help/%s",s);
}

static void
emscripten_draw(PARI_plot *T, long *w, long *x, long *y, long lw)
{
  pari_sp av = avma;
  EM_ASM(rawPrint=true);
  pari_printf("%s\n", rect2svg(w,x,y,lw,T));
  EM_ASM(rawPrint=false);
  avma = av;
}

static void
pari_emscripten_get_plot(PARI_plot *T)
{
  T->width   = 480; // width and
  T->height  = 320; //  height of plot window
  T->hunit   = 3;   //
  T->vunit   = 3;   //
  T->fwidth  = 9;   // font width
  T->fheight = 12;  //   and height
  T->draw = &emscripten_draw;
}

void
pari_emscripten_plot_init(void)
{
  pari_set_plot_engine(pari_emscripten_get_plot);
}

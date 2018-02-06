/* Copyright (C) 2016  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

#include "pari.h"
#include "../src/graph/rect.h"
#include <emscripten/emscripten.h>

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
emscripten_draw(PARI_plot *T, GEN w, GEN x, GEN y)
{
  pari_sp av = avma;
  EM_ASM(rawPrint=true);(void)T;
  pari_printf("%s\n", rect2svg(w,x,y,NULL));
  EM_ASM(rawPrint=false);
  avma = av;
}

static long plot_width, plot_height;

static void
pari_emscripten_get_plot(PARI_plot *T)
{
  T->width   = plot_width;
  T->height  = plot_height;
  T->hunit   = 3;   //
  T->vunit   = 3;   //
  T->fwidth  = 9;   // font width
  T->fheight = 12;  //   and height
  gp_get_ploth_default_sizes(T);
  T->dwidth  = 0;   // display width
  T->dheight = 0;   //   and height
  T->draw = &emscripten_draw;
}

void
pari_emscripten_plot_init(long width, long height)
{
  plot_width  = width;
  plot_height = height;
  pari_set_plot_engine(pari_emscripten_get_plot);
}

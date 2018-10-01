/* Copyright (C) 2018  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

#include "pari.h"
#include "paripriv.h"

/********************************************************************/
/**                                                                **/
/**                       CHARACTER STRINGS                        **/
/**                                                                **/
/********************************************************************/

/* Utillity functions */
char *
stack_strdup(const char *s)
{
  long n = strlen(s)+1;
  char *t = stack_malloc(n);
  memcpy(t,s,n); return t;
}
char *
stack_strcat(const char *s, const char *t)
{
  long ls = strlen(s), lt = strlen(t);
  long n = ls + lt + 1;
  char *u = stack_malloc(n);
  memcpy(u,     s, ls);
  memcpy(u + ls,t, lt+1); return u;
}

char *
pari_strdup(const char *s)
{
  long n = strlen(s)+1;
  char *t = (char*)pari_malloc(n);
  memcpy(t,s,n); return t;
}
char *
pari_strndup(const char *s, long n)
{
  char *t = (char*)pari_malloc(n+1);
  memcpy(t,s,n); t[n] = 0; return t;
}

/* return the first n0 chars of s as a GEN [s may not be 0-terminated] */
GEN
strntoGENstr(const char *s, long n0)
{
  long n = nchar2nlong(n0+1);
  GEN x = cgetg(n+1, t_STR);
  char *t = GSTR(x);
  x[n] = 0;
  strncpy(t, s, n0); t[n0] = 0; return x;
}

GEN
strtoGENstr(const char *s) { return strntoGENstr(s, strlen(s)); }

GEN
chartoGENstr(char c)
{
  GEN x = cgetg(2, t_STR);
  char *t = GSTR(x);
  t[0] = c; t[1] = 0; return x;
}

static char
ltoc(long n) {
  if (n <= 0 || n > 255)
    pari_err(e_MISC, "out of range in integer -> character conversion (%ld)", n);
  return (char)n;
}
static char
itoc(GEN x) { return ltoc(gtos(x)); }

GEN
Strchr(GEN g)
{
  long i, l, len, t = typ(g);
  char *s;
  GEN x;
  if (is_vec_t(t)) {
    l = lg(g); len = nchar2nlong(l);
    x = cgetg(len+1, t_STR); s = GSTR(x);
    for (i=1; i<l; i++) *s++ = itoc(gel(g,i));
  }
  else if (t == t_VECSMALL)
  {
    l = lg(g); len = nchar2nlong(l);
    x = cgetg(len+1, t_STR); s = GSTR(x);
    for (i=1; i<l; i++) *s++ = ltoc(g[i]);
  }
  else
    return chartoGENstr(itoc(g));
  *s = 0; return x;
}

GEN
strsplit(GEN x, GEN p)
{
  long i0, i, iv, ls, lt;
  char *s, *t;
  GEN v;
  if (typ(x) != t_STR) pari_err_TYPE("strsplit",x);
  if (typ(p) != t_STR) pari_err_TYPE("strsplit",p);
  s = GSTR(x); ls = strlen(s); v = cgetg(ls, t_VEC);
  t = GSTR(p); lt = strlen(t); iv = 1;
  for (i = i0 = 0; i < ls; i++)
    while (!strncmp(s + i, t, lt))
    {
      gel(v, iv++) = strntoGENstr(s + i0, i - i0);
      i += lt; i0 = i;
    }
  gel(v, iv++) = strntoGENstr(s + i0, i - i0);
  stackdummy((pari_sp)(v + iv), (pari_sp)(v + ls));
  setlg(v, iv); return v;
}

GEN
strjoin(GEN v, GEN p)
{
  pari_sp av = avma;
  long i, l;
  GEN w;
  if (!is_vec_t(typ(v))) pari_err_TYPE("strjoin",v);
  if (typ(p) != t_STR) pari_err_TYPE("strjoin",p);
  l = lg(v); if (l == 1) return strtoGENstr("");
  w = cgetg(2*l - 2, t_VEC);
  gel(w, 1) = gel(v, 1);
  for (i = 2; i < l; i++)
  {
    gel(w, 2*i-2) = p;
    gel(w, 2*i-1) = gel(v, i);
  }
  return gerepileuptoleaf(av, shallowconcat1(w));
}

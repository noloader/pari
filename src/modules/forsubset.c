/* Copyright (C) 2017  The PARI group.

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

void
forksubset_init(forsubset_t *T, long n, long k)
{
  long i;
  T->n = n;
  T->k = k;
  T->v = cgetg(k + 1, t_VECSMALL);
  setlg(T->v, k + 1);
  for (i = 1; i <= k; i++) (T->v)[i] = i;
}

void forallsubset_init(forsubset_t *T, long n)
{
  T->n = n;
  T->k = 0;
  T->v = cgetg(n + 1, t_VECSMALL);
  setlg(T->v, 1);
}

int
forksubset_next(forsubset_t *T)
{
  GEN v = T->v;
  long n = T->n;
  long k = T->k;
  long i;

  if (k == 0 || k == n) return 0;

  if (v[k] < n)
  {
    v[k]++;
    return 1;
  }
  for (i = k - 1; i >= 1 && v[i+1] == v[i] + 1; i--);
  if (i == 0) return 0;

  v[i]++;
  for (; i < k; i++) v[i+1] = v[i] + 1;
  return 1;
}

int
forallsubset_next(forsubset_t *T)
{
  long i;

  if (forksubset_next(T)) return 1;
  else if (T->k < T->n)
  {
    (T->k)++;
    setlg(T->v, T->k+1);
    for (i = 1; i <= T->k; i++) (T->v)[i] = i;
    return 1;
  }

  return 0;
}

void
forksubset(void *E, long call(void *, GEN), long n, long k)
{
  forsubset_t T;
  pari_sp av = avma;

  if (k < 0 || k > n) return;

  forksubset_init(&T, n, k);
  do
  {
    if (call(E, T.v)) break;
  } while (forksubset_next(&T));

  avma = av;
}

void
forallsubset(void *E, long call(void *, GEN), long n)
{
  forsubset_t T;
  pari_sp av = avma;

  forallsubset_init(&T, n);
  do
  {
    if (call(E, T.v)) break;
  } while (forallsubset_next(&T));

  avma = av;
}

static void
forksubset0(long n, long k, GEN code)
{
  push_lex(gen_0, code);
  forksubset((void *)code, &gp_evalvoid, n, k);
  pop_lex(1);
}
static void
forallsubset0(long n, GEN code)
{
  push_lex(gen_0, code);
  forallsubset((void *)code, &gp_evalvoid, n);
  pop_lex(1);
}
void
forsubset0(GEN nk, GEN code)
{
  switch(typ(nk))
  {
    case t_INT: return forallsubset0(itos(nk), code);
    case t_VEC:
      if (lg(nk) == 3)
      {
        GEN n = gel(nk,1), k = gel(nk,2);
        if (typ(n) == t_INT && typ(k) == t_INT)
          return forksubset0(itos(n),itos(k), code);
      }
    default:
      pari_err_TYPE("forsubset", nk);
  }
}

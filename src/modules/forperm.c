/* Copyright (C) 2017  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/* for loop over permutations in lexicographic order
 * This implements the algorithm L in D. Knuth "The Art Of Computer Programming"
 * Fascicle 2b */

#include "pari.h"
#include "paripriv.h"

void
forperm_init(forperm_t *T, long k)
{
  T->k = k;
  T->v = identity_perm(k);
}

int
forperm_next(forperm_t *T)
{
  GEN v = T->v;
  long k = T->k;
  long t, m1, m2;
  long *p, *q;

  for (m1 = k - 1; m1 > 0 && v[m1] >= v[m1 + 1]; m1--);
  if (m1 <= 0) return 0;

  for (m2 = k; v[m1] >= v[m2]; m2--);

  t = v[m1];
  v[m1] = v[m2];
  v[m2] = t;

  p = v + m1 + 1;
  q = v + k;
  while (p < q)
  {
    t = *p;
    *p = *q;
    *q = t;
    p++;
    q--;
  }
  return 1;
}

void
forperm(void *E, long call(void *, GEN), GEN k)
{
  forperm_t T;
  pari_sp av = avma;

  switch (typ(k))
  {
    case t_INT:
      if (signe(k) < 0) pari_err_DOMAIN("forperm", "a", "<", gen_0, k);
      forperm_init(&T, itos(k));
      break;
    case t_VEC:
      k = vec_to_vecsmall(k);
      T.v = vecsmall_copy(k);
      T.k = lg(k) - 1;
      break;
    case t_VECSMALL:
      T.v = vecsmall_copy(k);
      T.k = lg(k) - 1;
      break;
    default:
      pari_err_TYPE("forperm", k);
      return; /* LCOV_EXCL_LINE */
  }

  do
  {
    if (call(E, T.v)) break;
  } while (forperm_next(&T));

  avma = av;
}

void
forperm0(GEN k, GEN code)
{
  push_lex(gen_0, code);
  forperm((void *)code, &gp_evalvoid, k);
  pop_lex(1);
}


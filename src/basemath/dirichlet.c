/* Copyright (C) 2015  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/********************************************************************/
/**                                                                **/
/**           Dirichlet series through Euler product               **/
/**                                                                **/
/********************************************************************/
#include "pari.h"
#include "paripriv.h"

static void
err_direuler(GEN x)
{ pari_err_DOMAIN("direuler","constant term","!=", gen_1,x); }

/* Multiply x in place by Euler factor s at prime p, using temporary space y
 * (for numerator) */
static void
dirmuleuler(GEN x, ulong p, GEN s, GEN y)
{
  ulong i, k, n = lg(x) - 1;
  GEN c, N = numer(s), D = denom(s);
  long j, tx, lx;

  tx = typ(N);
  if (is_scalar_t(tx))
  {
    if (!gequal1(N))
    {
      if (!gequalm1(N)) err_direuler(N);
      D = gneg(D);
    }
  }
  else
  {
    ulong k1, q, qlim;
    if (tx != t_POL) pari_err_TYPE("direuler",N);
    lx = degpol(N);
    if (lx < 0) err_direuler(N);
    c = gel(N,2);
    if (!gequal1(c))
    {
      if (!gequalm1(c)) err_direuler(N);
      N = gneg(N);
      D = gneg(D);
    }
    for (i=1; i<=n; i++) gel(y,i) = gel(x,i);
    q = p; qlim = n/p;
    for (j = 1; q<=n && j<=lx; j++)
    {
      c = gel(N,j+2);
      if (!gequal0(c))
        for (k=1,k1=q; k1<=n; k1+=q,k++)
          gel(x,k1) = gadd(gel(x,k1), gmul(c,gel(y,k)));
      if (q > qlim) break;
      q *= p;
    }
  }
  tx = typ(D);
  if (is_scalar_t(tx))
  {
    if (!gequal1(D)) err_direuler(D);
  }
  else
  {
    if (tx != t_POL) pari_err_TYPE("direuler",D);
    c = gel(D,2);
    if (!gequal1(c)) err_direuler(D);
    lx = degpol(D);
    for (i=p; i<=n; i+=p)
    {
      s = gen_0; k = i;
      for (j = 1; !(k%p) && j<=lx; j++)
      {
        c = gel(D,j+2); k /= p;
        if (!gequal0(c)) s = gadd(s, gmul(c,gel(x,k)));
      }
      gel(x,i) = gsub(gel(x,i),s);
    }
  }
}

/* Euler product on primes coprime to Sbad */
static GEN
direuler_bad(void *E, GEN (*eval)(void *, GEN), GEN a, GEN b, GEN c, GEN Sbad)
{
  ulong n;
  pari_sp av0 = avma, av;
  GEN x, y, prime;
  forprime_t T;

  if (typ(b) != t_INT)
  { b = gfloor(b); if (typ(b) != t_INT) pari_err_TYPE("direuler",b); }
  if (typ(a) != t_INT)
  { a = gceil(a); if (typ(a) != t_INT) pari_err_TYPE("direuler",a); }
  if (c)
  {
    if (typ(c) != t_INT)
    { c = gfloor(c); if (typ(c) != t_INT) pari_err_TYPE("direuler", c); }
    if (signe(c) <= 0) { avma = av0; return cgetg(1,t_VEC); }
    if (cmpii(c, b) < 0) b = c;
  }
  if (lgefint(b) > 3) pari_err_OVERFLOW("direuler");
  if (!forprime_init(&T, a,b)) { avma = av0; return mkvec(gen_1); }
  n = itou(b);
  y = cgetg(n+1,t_VEC); av = avma;
  x = zerovec(n); gel(x,1) = gen_1;
  while ( (prime = forprime_next(&T)) )
  {
    ulong p = prime[2];
    if (Sbad && !umodiu(Sbad, p)) continue;
    dirmuleuler(x, p, eval(E,prime), y);
    if (gc_needed(av,1))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"direuler");
      x = gerepilecopy(av, x);
    }
  }
  return gerepilecopy(av0,x);
}

/* in place */
static void
dirseteuler(GEN v, ulong p, GEN s, GEN y)
{
  ulong lv = lg(v), k;
  for (k = p; k < lv; k += p) gel(v,k) = gen_0;
  dirmuleuler(v, p, s, y);
}

static GEN
localfactor(void *E, GEN p)
{
  GEN v = (GEN)E, L = gel(v,1), a = gel(v,2);
  return ginv(closure_callgen2(a, p, stoi(logint(L, p, NULL))));
}
static GEN
direxpand_bad(GEN a, long L, GEN Sbad)
{
  pari_sp ltop = avma;
  long ta = typ(a), la, tv, i;
  GEN an, v, y;

  if (ta == t_CLOSURE) switch(closure_arity(a))
  {
    GEN gL;
    case 2:
      gL = stoi(L);
      return direuler_bad((void*)mkvec2(gL,a), localfactor, gen_2, gL,gL, Sbad);
    case 1:
      a = closure_callgen1(a, stoi(L));
      if (typ(a) != t_VEC) pari_err_TYPE("direxpand", a);
      return a;
    default: pari_err_TYPE("direxpand [wrong arity]", a);
  }
  if (ta != t_VEC) pari_err_TYPE("direxpand", a);
  la = lg(a); if (la == 1) pari_err_TYPE("direxpand", a);
  v = gel(a,1); tv = typ(v);
  if (tv != t_CLOSURE && tv != t_VEC)
  { /* regular vector, return it */
    if (la-1 < L) L = la-1;
    an = cgetg(L+1, t_VEC);
    for (i = 1; i <= L; i++) gel(an,i) = gcopy(gel(a,i));
    return an;
  }
  /* vector [an, [p1, 1/L_{p1}], ..., [pk, 1/L_{pk}}]]: exceptional primes */
  if (!Sbad) Sbad = gen_1;
  for (i = 2; i < la; i++)
  {
    GEN ai = gel(a,i), p;
    if (typ(ai) != t_VEC || lg(ai) != 3)
      pari_err_TYPE("direxpand [exceptional prime]", ai);
    p = gel(ai,1);
    if (!isprime(p)) pari_err_TYPE("direxpand [exceptional prime]", ai);
    Sbad = mulii(Sbad, p);
  }
  an = direxpand_bad(v, L, Sbad);
  y = cgetg(L+1, t_VEC); /* scratch space */
  for (i = 2; i < la; i++)
  {
    GEN ai = gel(a,i), s = ginv(gel(ai,2));
    ulong p = itou(gel(ai,1));
    dirseteuler(an, p, s, y);
  }
  return gerepilecopy(ltop, an);
}
GEN
direxpand(GEN a, long L) { return direxpand_bad(a, L, NULL); }

GEN
direuler(void *E, GEN (*eval)(void *, GEN), GEN a, GEN b, GEN c)
{ return direuler_bad(E, eval, a, b, c, NULL); }

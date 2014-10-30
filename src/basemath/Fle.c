/* Copyright (C) 2014  The PARI group.

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

/* Not so fast arithmetic with points over elliptic curves over Fl */

/***********************************************************************/
/**                                                                   **/
/**                              Fle                                  **/
/**                                                                   **/
/***********************************************************************/
GEN
Fle_changepoint(GEN x, GEN ch, ulong p)
{
  ulong p1,u,r,s,t,v,v2,v3;
  GEN z;
  if (ell_is_inf(x)) return x;
  u = ch[1]; r = ch[2];
  s = ch[3]; t = ch[4];
  v = Fl_inv(u, p); v2 = Fl_sqr(v,p); v3 = Fl_mul(v,v2,p);
  p1 = Fl_sub(x[1],r,p);
  z = cgetg(3,t_VECSMALL);
  z[1] = Fl_mul(v2, p1, p);
  z[2] = Fl_mul(v3, Fl_sub(x[2], Fl_add(Fl_mul(s,p1, p),t, p),p),p);
  return z;
}

GEN
Fle_changepointinv(GEN x, GEN ch, ulong p)
{
  ulong u, r, s, t, X, Y, u2, u3, u2X;
  GEN z;
  if (ell_is_inf(x)) return x;
  X = x[1]; Y = x[2];
  u = ch[1]; r = ch[2];
  s = ch[3]; t = ch[4];
  u2 = Fl_sqr(u, p); u3 = Fl_mul(u,u2,p);
  u2X = Fl_mul(u2,X, p);
  z = cgetg(3, t_VECSMALL);
  z[1] = Fl_add(u2X,r,p);
  z[2] = Fl_add(Fl_mul(u3,Y,p), Fl_add(Fl_mul(s,u2X,p), t, p), p);
  return z;
}
static GEN
Fle_dbl_slope(GEN P, ulong a4, ulong p, ulong *slope)
{
  ulong x, y, Qx, Qy;
  if (ell_is_inf(P) || !P[2]) return ellinf();
  x = P[1]; y = P[2];
  *slope = Fl_div(Fl_add(Fl_triple(Fl_sqr(x,p), p), a4, p),
                  Fl_double(y, p), p);
  Qx = Fl_sub(Fl_sqr(*slope, p), Fl_double(x, p), p);
  Qy = Fl_sub(Fl_mul(*slope, Fl_sub(x, Qx, p), p), y, p);
  return mkvecsmall2(Qx, Qy);
}

GEN
Fle_dbl(GEN P, ulong a4, ulong p)
{
  ulong slope;
  return Fle_dbl_slope(P,a4,p,&slope);
}

static GEN
Fle_add_slope(GEN P, GEN Q, ulong a4, ulong p, ulong *slope)
{
  ulong Px, Py, Qx, Qy, Rx, Ry;
  if (ell_is_inf(P)) return Q;
  if (ell_is_inf(Q)) return P;
  Px = P[1]; Py = P[2];
  Qx = Q[1]; Qy = Q[2];
  if (Px==Qx)
    return Py==Qy ? Fle_dbl_slope(P, a4, p, slope): ellinf();
  *slope = Fl_div(Fl_sub(Py, Qy, p), Fl_sub(Px, Qx, p), p);
  Rx = Fl_sub(Fl_sub(Fl_sqr(*slope, p), Px, p), Qx, p);
  Ry = Fl_sub(Fl_mul(*slope, Fl_sub(Px, Rx, p), p), Py, p);
  return mkvecsmall2(Rx, Ry);
}

GEN
Fle_add(GEN P, GEN Q, ulong a4, ulong p)
{
  ulong slope;
  return Fle_add_slope(P,Q,a4,p,&slope);
}

static GEN
Fle_neg(GEN P, ulong p)
{
  if (ell_is_inf(P)) return P;
  return mkvecsmall2(P[1], Fl_neg(P[2], p));
}

GEN
Fle_sub(GEN P, GEN Q, ulong a4, ulong p)
{
  pari_sp av = avma;
  ulong slope;
  return gerepileupto(av, Fle_add_slope(P, Fle_neg(Q, p), a4, p, &slope));
}

struct _Fle
{
  ulong a4,a6;
  ulong p;
};

static GEN
_Fle_dbl(void *E, GEN P)
{
  struct _Fle *ell = (struct _Fle *) E;
  return Fle_dbl(P, ell->a4, ell->p);
}

static GEN
_Fle_add(void *E, GEN P, GEN Q)
{
  struct _Fle *ell=(struct _Fle *) E;
  return Fle_add(P, Q, ell->a4, ell->p);
}

static GEN
_Fle_mulu(void *E, GEN P, ulong n)
{
  pari_sp av = avma;
  struct _Fle *e=(struct _Fle *) E;
  if (!n || ell_is_inf(P)) return ellinf();
  if (n==1) return zv_copy(P);
  if (n==2) return Fle_dbl(P,e->a4, e->p);
  return gerepileupto(av, gen_powu(P, n, (void*)e, &_Fle_dbl, &_Fle_add));
}

GEN
Fle_mulu(GEN P, ulong n, ulong a4, ulong p)
{
  struct _Fle E;
  E.a4= a4; E.p = p;
  return _Fle_mulu(&E, P, n);
}

static GEN
_Fle_mul(void *E, GEN P, GEN n)
{
  pari_sp av = avma;
  struct _Fle *e=(struct _Fle *) E;
  long s = signe(n);
  if (!s || ell_is_inf(P)) return ellinf();
  if (s<0) P = Fle_neg(P, e->p);
  if (is_pm1(n)) return s>0? zv_copy(P): P;
  return gerepileupto(av, gen_pow(P, n, (void*)e, &_Fle_dbl, &_Fle_add));
}

GEN
Fle_mul(GEN P, GEN n, ulong a4, ulong p)
{
  struct _Fle E;
  E.a4 = a4; E.p = p;
  return _Fle_mul(&E, P, n);
}

/* Finds a random non-singular point on E */

GEN
random_Fle(ulong a4, ulong a6, ulong p)
{
  ulong x, x2, y, rhs;
  do
  {
    x   = random_Fl(p); /*  x^3+a4*x+a6 = x*(x^2+a4)+a6  */
    x2  = Fl_sqr(x, p);
    rhs = Fl_add(Fl_mul(x, Fl_add(x2, a4, p), p), a6, p);
  } while ((!rhs && !Fl_add(Fl_triple(x2,p),a4,p))
          || krouu(rhs, p) < 0);
  y = Fl_sqrt(rhs, p);
  return mkvecsmall2(x, y);
}

static GEN
_Fle_rand(void *E)
{
  struct _Fle *e=(struct _Fle *) E;
  return random_Fle(e->a4, e->a6, e->p);
}

static const struct bb_group Fle_group={_Fle_add,_Fle_mul,_Fle_rand,hash_GEN,zv_equal,ell_is_inf,NULL};

GEN
Fle_order(GEN z, GEN o, ulong a4, ulong p)
{
  pari_sp av = avma;
  struct _Fle e;
  e.a4=a4;
  e.p=p;
  return gerepileuptoint(av, gen_order(z, o, (void*)&e, &Fle_group));
}

ulong
Fl_ellj(ulong a4, ulong a6, ulong p)
{
  if (SMALL_ULONG(p))
  {
    /* a43 = 4 a4^3 */
    ulong a43 = Fl_double(Fl_double(Fl_mul(a4, Fl_sqr(a4, p), p), p), p);
    /* a62 = 27 a6^2 */
    ulong a62 = Fl_mul(Fl_sqr(a6, p), 27 % p, p);
    ulong z1 = Fl_mul(a43, 1728 % p, p);
    ulong z2 = Fl_add(a43, a62, p);
    return Fl_div(z1, z2, p);
  } else
    return Fl_ellj_pre(a4, a6, p, get_Fl_red(p));
}

void
Fl_ellj_to_a4a6(ulong j, ulong p, ulong *pt_a4, ulong *pt_a6)
{
  ulong zagier = 1728 % p;
  if (j == 0)           { *pt_a4 = 0; *pt_a6 =1; }
  else if (j == zagier) { *pt_a4 = 1; *pt_a6 =0; }
  else
  {
    ulong k = Fl_sub(zagier, j, p);
    ulong kj = Fl_mul(k, j, p);
    ulong k2j = Fl_mul(kj, k, p);
    *pt_a4 = Fl_triple(kj, p);
    *pt_a6 = Fl_double(k2j, p);
  }
}

void
Fl_elltwist(ulong a4, ulong a6, ulong D, ulong p, ulong *pt_a4, ulong *pt_a6)
{
  ulong D2 = Fl_sqr(D, p);
  *pt_a4 = Fl_mul(a4, D2, p);
  *pt_a6 = Fl_mul(a6, Fl_mul(D, D2, p), p);
}

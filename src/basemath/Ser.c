/* Copyright (C) 2000, 2012  The PARI group.

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
/*******************************************************************/
/*                                                                 */
/*                     Conversion --> t_SER                        */
/*                                                                 */
/*******************************************************************/
static GEN
RgX_to_ser_i(GEN x, long l, long lx, long v, int copy)
{
  GEN y;
  long i;
  if (lx == 2) return zeroser(varn(x), l-2);
  if (l <= 2) pari_err_BUG("RgX_to_ser (l <= 2)");
  y = cgetg(l,t_SER); y[1] = x[1]; setvalp(y, v);
  x += v; lx = minss(lx-v, l);
  if (copy)
    for (i = 2; i <lx; i++) gel(y,i) = gcopy(gel(x,i));
  else
    for (i = 2; i <lx; i++) gel(y,i) = gel(x,i);
  for (     ; i < l; i++) gel(y,i) = gen_0;
  return normalize(y);
}
/* enlarge/truncate t_POL x to a t_SER with lg l */
GEN
RgX_to_ser(GEN x, long l) { return RgX_to_ser_i(x, l, lg(x), RgX_val(x), 0); }
GEN
RgX_to_ser_inexact(GEN x, long l)
{
  long i, lx = lg(x);
  int first = 1;
  for (i = 2; i < lx && gequal0(gel(x,i)); i++) /* ~ RgX_valrem + normalize */
    if (first && !isexactzero(gel(x,i)))
    {
      pari_warn(warner,"normalizing a series with 0 leading term");
      first = 0;
    }
  return RgX_to_ser_i(x, l, lx, i - 2, 0);
}
GEN
rfrac_to_ser(GEN x, long l)
{ return gdiv(gel(x,1), RgX_to_ser(gel(x,2), l)); }

/* R(1/x) + O(x^N) */
GEN
rfracrecip_to_ser_absolute(GEN R, long N)
{
  GEN n = gel(R,1), d = gel(R,2);
  long vx = varn(d), vn, v, dn;

  if (typ(n) != t_POL || varn(n) != vx) { vn = 0; dn = 0; }
  else
  {
    vn = RgX_valrem(n, &n);
    n = RgX_recip(n);
    dn = degpol(n);
  }
  v = vn - RgX_valrem(d, &d);
  d = RgX_recip(d);
  R = gdiv(n, RgX_to_ser(d, N+2));
  setvalp(R, valp(R) + degpol(d)-dn-v);
  return R;
}

/* assume prec >= 0 */
GEN
scalarser(GEN x, long v, long prec)
{
  long i, l;
  GEN y;

  if (gequal0(x))
  {
    if (isrationalzero(x)) return zeroser(v, prec);
    if (!isexactzero(x)) prec--;
    y = cgetg(3, t_SER);
    y[1] = evalsigne(0) | _evalvalp(prec) | evalvarn(v);
    gel(y,2) = gcopy(x); return y;
  }
  l = prec + 2; y = cgetg(l, t_SER);
  y[1] = evalsigne(1) | _evalvalp(0) | evalvarn(v);
  gel(y,2) = gcopy(x); for (i=3; i<l; i++) gel(y,i) = gen_0;
  return y;
}

/* assume x a t_[SER|POL], apply gtoser to all coeffs */
static GEN
coefstoser(GEN x, long v, long prec)
{
  long i, lx;
  GEN y = cgetg_copy(x, &lx); y[1] = x[1];
  for (i=2; i<lx; i++) gel(y,i) = gtoser(gel(x,i), v, prec);
  return y;
}

static void
err_ser_priority(GEN x, long v) { pari_err_PRIORITY("gtoser", x, "<", v); }
/* x a t_POL */
static GEN
poltoser(GEN x, long v, long prec)
{
  long s = varncmp(varn(x), v);
  if (s < 0) err_ser_priority(x,v);
  if (s > 0) return scalarser(x, v, prec);
  return RgX_to_ser_i(x, prec+2, lg(x), RgX_val(x), 1);
}
/* x a t_RFRAC */
static GEN
rfractoser(GEN x, long v, long prec)
{
  long s = varncmp(varn(gel(x,2)), v);
  pari_sp av;
  if (s < 0) err_ser_priority(x,v);
  if (s > 0) return scalarser(x, v, prec);
  av = avma; return gerepileupto(av, rfrac_to_ser(x, prec+2));
}
GEN
toser_i(GEN x)
{
  switch(typ(x))
  {
    case t_SER: return x;
    case t_POL: return RgX_to_ser(x, precdl+2);
    case t_RFRAC: return rfrac_to_ser(x, precdl+2);
  }
  return NULL;
}

GEN
gtoser(GEN x, long v, long prec)
{
  long tx = typ(x), j;
  GEN y;

  if (v < 0) v = 0;
  if (prec < 0)
    pari_err_DOMAIN("gtoser", "precision", "<", gen_0, stoi(prec));
  if (tx == t_SER)
  {
    long s = varncmp(varn(x), v);
    if      (s < 0) y = coefstoser(x, v, prec);
    else if (s > 0) y = scalarser(x, v, prec);
    else y = gcopy(x);
    return y;
  }
  if (is_scalar_t(tx)) return scalarser(x,v,prec);
  switch(tx)
  {
    case t_POL: return poltoser(x, v, prec);
    case t_RFRAC: return rfractoser(x, v, prec);
    case t_VECSMALL: x = zv_to_ZV(x);/*fall through*/
    case t_QFR: case t_QFI: case t_VEC: case t_COL:
    {
      GEN z;
      long lx = lg(x); if (tx == t_QFR) lx--;
      if (varncmp(gvar(x), v) <= 0) pari_err_PRIORITY("gtoser", x, "<=", v);
      y = cgetg(lx+1, t_SER);
      y[1] = evalvarn(v)|evalvalp(0);
      x--;
      for (j=2; j<=lx; j++) gel(y,j) = gel(x,j);
      z = gcopy(normalize(y));
      settyp(y, t_VECSMALL);/* left on stack */
      return z;
    }

    default: pari_err_TYPE("gtoser",x);
      return NULL; /* LCOV_EXCL_LINE */
  }
  return y;
}

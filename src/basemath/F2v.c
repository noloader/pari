/* Copyright (C) 2012-2019 The PARI group.


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

/***********************************************************************/
/**                                                                   **/
/**                             F2v                                   **/
/**                                                                   **/
/***********************************************************************/
/* F2v objects are defined as follows:
   An F2v is a t_VECSMALL:
   v[0] = codeword
   v[1] = number of components
   x[2] = a_0...a_31 x[3] = a_32..a_63, etc.  on 32bit
   x[2] = a_0...a_63 x[3] = a_64..a_127, etc. on 64bit

   where the a_i are bits.
*/

int
F2v_equal0(GEN V)
{
  long l = lg(V);
  while (--l > 1)
    if (V[l]) return 0;
  return 1;
}

GEN
F2c_to_ZC(GEN x)
{
  long l = x[1]+1, lx = lg(x);
  GEN  z = cgetg(l, t_COL);
  long i, j, k;
  for (i=2, k=1; i<lx; i++)
    for (j=0; j<BITS_IN_LONG && k<l; j++,k++)
      gel(z,k) = (x[i]&(1UL<<j))? gen_1: gen_0;
  return z;
}
GEN
F2c_to_mod(GEN x)
{
  long l = x[1]+1, lx = lg(x);
  GEN  z = cgetg(l, t_COL);
  GEN _0 = mkintmod(gen_0,gen_2);
  GEN _1 = mkintmod(gen_1,gen_2);
  long i, j, k;
  for (i=2, k=1; i<lx; i++)
    for (j=0; j<BITS_IN_LONG && k<l; j++,k++)
      gel(z,k) = (x[i]&(1UL<<j))? _1: _0;
  return z;
}

/* x[a..b], a <= b */
GEN
F2v_slice(GEN x, long a, long b)
{
  long i,j,k, l = b-a+1;
  GEN z = cgetg(nbits2lg(l), t_VECSMALL);
  z[1] = l;
  for(i=a,k=1,j=BITS_IN_LONG; i<=b; i++,j++)
  {
    if (j==BITS_IN_LONG) { j=0; z[++k]=0; }
    if (F2v_coeff(x,i)) z[k] |= 1UL<<j;
  }
  return z;
}
/* x[a..b,], a <= b */
GEN
F2m_rowslice(GEN x, long a, long b)
{
  long i, l;
  GEN y = cgetg_copy(x, &l);
  for (i = 1; i < l; i++) gel(y,i) = F2v_slice(gel(x,i),a,b);
  return y;
}

GEN
F2m_to_ZM(GEN z)
{
  long i, l = lg(z);
  GEN x = cgetg(l,t_MAT);
  for (i=1; i<l; i++) gel(x,i) = F2c_to_ZC(gel(z,i));
  return x;
}
GEN
F2m_to_mod(GEN z)
{
  long i, l = lg(z);
  GEN x = cgetg(l,t_MAT);
  for (i=1; i<l; i++) gel(x,i) = F2c_to_mod(gel(z,i));
  return x;
}

GEN
F2v_to_Flv(GEN x)
{
  long l = x[1]+1, lx = lg(x);
  GEN  z = cgetg(l, t_VECSMALL);
  long i,j,k;
  for (i=2, k=1; i<lx; i++)
    for (j=0; j<BITS_IN_LONG && k<l; j++,k++)
      z[k] = (x[i]>>j)&1UL;
  return z;
}

GEN
F2m_to_Flm(GEN z)
{
  long i, l = lg(z);
  GEN x = cgetg(l,t_MAT);
  for (i=1; i<l; i++) gel(x,i) = F2v_to_Flv(gel(z,i));
  return x;
}

GEN
ZV_to_F2v(GEN x)
{
  long l = lg(x)-1;
  GEN z = cgetg(nbits2lg(l), t_VECSMALL);
  long i,j,k;
  z[1] = l;
  for(i=1,k=1,j=BITS_IN_LONG; i<=l; i++,j++)
  {
    if (j==BITS_IN_LONG) { j=0; z[++k]=0; }
    if (mpodd(gel(x,i))) z[k] |= 1UL<<j;
  }
  return z;
}

GEN
RgV_to_F2v(GEN x)
{
  long l = lg(x)-1;
  GEN z = cgetg(nbits2lg(l), t_VECSMALL);
  long i,j,k;
  z[1] = l;
  for(i=1,k=1,j=BITS_IN_LONG; i<=l; i++,j++)
  {
    if (j==BITS_IN_LONG) { j=0; z[++k]=0; }
    if (Rg_to_F2(gel(x,i))) z[k] |= 1UL<<j;
  }
  return z;
}

GEN
Flv_to_F2v(GEN x)
{
  long l = lg(x)-1;
  GEN z = cgetg(nbits2lg(l), t_VECSMALL);
  long i,j,k;
  z[1] = l;
  for(i=1,k=1,j=BITS_IN_LONG; i<=l; i++,j++)
  {
    if (j==BITS_IN_LONG) { j=0; z[++k]=0; }
    if (x[i]&1L) z[k] |= 1UL<<j;
  }
  return z;
}

GEN
ZM_to_F2m(GEN x) { pari_APPLY_same(ZV_to_F2v(gel(x,i))) }
GEN
RgM_to_F2m(GEN x) { pari_APPLY_same(RgV_to_F2v(gel(x,i))) }
GEN
Flm_to_F2m(GEN x) { pari_APPLY_same(Flv_to_F2v(gel(x,i))) }

GEN
const_F2v(long m)
{
  long i, l = nbits2lg(m);
  GEN c = cgetg(l, t_VECSMALL);
  c[1] = m;
  for (i = 2; i < l; i++) uel(c,i) = -1UL;
  if (remsBIL(m)) uel(c,l-1) = (1UL<<remsBIL(m))-1UL;
  return c;
}

/* Allow lg(y)<lg(x) */
void
F2v_add_inplace(GEN x, GEN y)
{
  long n = lg(y);
  long r = (n-2)&7L, q = n-r, i;
  for (i = 2; i < q; i += 8)
  {
    x[  i] ^= y[  i]; x[1+i] ^= y[1+i]; x[2+i] ^= y[2+i]; x[3+i] ^= y[3+i];
    x[4+i] ^= y[4+i]; x[5+i] ^= y[5+i]; x[6+i] ^= y[6+i]; x[7+i] ^= y[7+i];
  }
  switch (r)
  {
    case 7: x[i] ^= y[i]; i++; case 6: x[i] ^= y[i]; i++;
    case 5: x[i] ^= y[i]; i++; case 4: x[i] ^= y[i]; i++;
    case 3: x[i] ^= y[i]; i++; case 2: x[i] ^= y[i]; i++;
    case 1: x[i] ^= y[i]; i++;
  }
}

/* Allow lg(y)<lg(x) */
void
F2v_and_inplace(GEN x, GEN y)
{
  long n = lg(y);
  long r = (n-2)&7L, q = n-r, i;
  for (i = 2; i < q; i += 8)
  {
    x[  i] &= y[  i]; x[1+i] &= y[1+i]; x[2+i] &= y[2+i]; x[3+i] &= y[3+i];
    x[4+i] &= y[4+i]; x[5+i] &= y[5+i]; x[6+i] &= y[6+i]; x[7+i] &= y[7+i];
  }
  switch (r)
  {
    case 7: x[i] &= y[i]; i++; case 6: x[i] &= y[i]; i++;
    case 5: x[i] &= y[i]; i++; case 4: x[i] &= y[i]; i++;
    case 3: x[i] &= y[i]; i++; case 2: x[i] &= y[i]; i++;
    case 1: x[i] &= y[i]; i++;
  }
}

/* Allow lg(y)<lg(x) */
void
F2v_negimply_inplace(GEN x, GEN y)
{
  long n = lg(y);
  long r = (n-2)&7L, q = n-r, i;
  for (i = 2; i < q; i += 8)
  {
    x[  i] &= ~y[  i]; x[1+i] &= ~y[1+i]; x[2+i] &= ~y[2+i]; x[3+i] &= ~y[3+i];
    x[4+i] &= ~y[4+i]; x[5+i] &= ~y[5+i]; x[6+i] &= ~y[6+i]; x[7+i] &= ~y[7+i];
  }
  switch (r)
  {
    case 7: x[i] &= ~y[i]; i++; case 6: x[i] &= ~y[i]; i++;
    case 5: x[i] &= ~y[i]; i++; case 4: x[i] &= ~y[i]; i++;
    case 3: x[i] &= ~y[i]; i++; case 2: x[i] &= ~y[i]; i++;
    case 1: x[i] &= ~y[i]; i++;
  }
}

ulong
F2v_dotproduct(GEN x, GEN y)
{
  long i, lx = lg(x);
  ulong c;
  if (lx <= 2) return 0;
  c = uel(x,2) & uel(y,2);
  for (i=3; i<lx; i++) c ^= uel(x,i) & uel(y,i);
#ifdef LONG_IS_64BIT
  c ^= c >> 32;
#endif
  c ^= c >> 16;
  c ^= c >>  8;
  c ^= c >>  4;
  c ^= c >>  2;
  c ^= c >>  1;
  return c & 1;
}

ulong
F2v_hamming(GEN H)
{
  long i, n=0, l=lg(H);
  for (i=2; i<l; i++) n += hammingl(uel(H,i));
  return n;
}

GEN
matid_F2m(long n)
{
  GEN y = cgetg(n+1,t_MAT);
  long i;
  if (n < 0) pari_err_DOMAIN("matid_F2m", "dimension","<",gen_0,stoi(n));
  for (i=1; i<=n; i++) { gel(y,i) = zero_F2v(n); F2v_set(gel(y,i),i); }
  return y;
}

INLINE GEN
F2m_F2c_mul_i(GEN x, GEN y, long lx, long l)
{
  long j;
  GEN z = NULL;

  for (j=1; j<lx; j++)
  {
    if (!F2v_coeff(y,j)) continue;
    if (!z) z = vecsmall_copy(gel(x,j));
    else F2v_add_inplace(z,gel(x,j));
  }
  if (!z) z = zero_F2v(l);
  return z;
}

GEN
F2m_mul(GEN x, GEN y)
{
  long i,j,l,lx=lg(x), ly=lg(y);
  GEN z;
  if (ly==1) return cgetg(1,t_MAT);
  z = cgetg(ly,t_MAT);
  if (lx==1)
  {
    for (i=1; i<ly; i++) gel(z,i) = mkvecsmall(0);
    return z;
  }
  l = coeff(x,1,1);
  for (j=1; j<ly; j++) gel(z,j) = F2m_F2c_mul_i(x, gel(y,j), lx, l);
  return z;
}

GEN
F2m_F2c_mul(GEN x, GEN y)
{
  long l, lx = lg(x);
  if (lx==1) return cgetg(1,t_VECSMALL);
  l = coeff(x,1,1);
  return F2m_F2c_mul_i(x, y, lx, l);
}

static GEN
_F2m_mul(void *data, GEN x, GEN y) { (void) data; return F2m_mul(x,y); }
static GEN
_F2m_sqr(void *data, GEN x) { (void) data; return F2m_mul(x,x); }
GEN
F2m_powu(GEN x, ulong n)
{
  if (!n) return matid(lg(x)-1);
  return gen_powu(x, n,NULL, &_F2m_sqr, &_F2m_mul);
}

static long
F2v_find_nonzero(GEN x0, GEN mask0, long m)
{
  ulong *x = (ulong *)x0+2, *mask = (ulong *)mask0+2, e;
  long i, l = lg(x0)-2;
  for (i = 0; i < l; i++)
  {
    e = *x++ & *mask++;
    if (e) return i*BITS_IN_LONG+vals(e)+1;
  }
  return m+1;
}

/* in place, destroy x */
GEN
F2m_ker_sp(GEN x, long deplin)
{
  GEN y, c, d;
  long i, j, k, r, m, n;

  n = lg(x)-1;
  m = mael(x,1,1); r=0;

  d = cgetg(n+1, t_VECSMALL);
  c = const_F2v(m);
  for (k=1; k<=n; k++)
  {
    GEN xk = gel(x,k);
    j = F2v_find_nonzero(xk, c, m);
    if (j>m)
    {
      if (deplin) {
        GEN c = zero_F2v(n);
        for (i=1; i<k; i++)
          if (F2v_coeff(xk, d[i]))
            F2v_set(c, i);
        F2v_set(c, k);
        return c;
      }
      r++; d[k] = 0;
    }
    else
    {
      F2v_clear(c,j); d[k] = j;
      F2v_clear(xk, j);
      for (i=k+1; i<=n; i++)
      {
        GEN xi = gel(x,i);
        if (F2v_coeff(xi,j)) F2v_add_inplace(xi, xk);
      }
      F2v_set(xk, j);
    }
  }
  if (deplin) return NULL;

  y = zero_F2m_copy(n,r);
  for (j=k=1; j<=r; j++,k++)
  {
    GEN C = gel(y,j); while (d[k]) k++;
    for (i=1; i<k; i++)
      if (d[i] && F2m_coeff(x,d[i],k))
        F2v_set(C,i);
    F2v_set(C, k);
  }
  return y;
}

/* not memory clean */
GEN
F2m_ker(GEN x) { return F2m_ker_sp(F2m_copy(x), 0); }
GEN
F2m_deplin(GEN x) { return F2m_ker_sp(F2m_copy(x), 1); }

ulong
F2m_det_sp(GEN x) { return !F2m_ker_sp(x, 1); }

ulong
F2m_det(GEN x)
{
  pari_sp av = avma;
  ulong d = F2m_det_sp(F2m_copy(x));
  return gc_ulong(av, d);
}

/* Destroy x */
GEN
F2m_gauss_pivot(GEN x, long *rr)
{
  GEN c, d;
  long i, j, k, r, m, n;

  n = lg(x)-1; if (!n) { *rr=0; return NULL; }
  m = mael(x,1,1); r=0;

  d = cgetg(n+1, t_VECSMALL);
  c = const_F2v(m);
  for (k=1; k<=n; k++)
  {
    GEN xk = gel(x,k);
    j = F2v_find_nonzero(xk, c, m);
    if (j>m) { r++; d[k] = 0; }
    else
    {
      F2v_clear(c,j); d[k] = j;
      for (i=k+1; i<=n; i++)
      {
        GEN xi = gel(x,i);
        if (F2v_coeff(xi,j)) F2v_add_inplace(xi, xk);
      }
    }
  }

  *rr = r; set_avma((pari_sp)d); return d;
}

long
F2m_rank(GEN x)
{
  pari_sp av = avma;
  long r;
  (void)F2m_gauss_pivot(F2m_copy(x),&r);
  return gc_long(av, lg(x)-1 - r);
}

static GEN
F2m_inv_upper_1_ind(GEN A, long index)
{
  pari_sp av = avma;
  long n = lg(A)-1, i = index, j;
  GEN u = const_vecsmall(n, 0);
  u[i] = 1;
  for (i--; i>0; i--)
  {
    ulong m = F2m_coeff(A,i,i+1) & uel(u,i+1); /* j = i+1 */
    for (j=i+2; j<=n; j++) m ^= F2m_coeff(A,i,j) & uel(u,j);
    u[i] = m & 1;
  }
  return gerepileuptoleaf(av, Flv_to_F2v(u));
}
static GEN
F2m_inv_upper_1(GEN A)
{
  long i, l;
  GEN B = cgetg_copy(A, &l);
  for (i = 1; i < l; i++) gel(B,i) = F2m_inv_upper_1_ind(A, i);
  return B;
}

static GEN
F2_get_col(GEN b, GEN d, long li, long aco)
{
  long i, l = nbits2lg(aco);
  GEN u = cgetg(l, t_VECSMALL);
  u[1] = aco;
  for (i = 1; i <= li; i++)
    if (d[i]) /* d[i] can still be 0 if li > aco */
    {
      if (F2v_coeff(b, i))
        F2v_set(u, d[i]);
      else
        F2v_clear(u, d[i]);
    }
  return u;
}

/* destroy a, b */
GEN
F2m_gauss_sp(GEN a, GEN b)
{
  long i, j, k, l, li, bco, aco = lg(a)-1;
  GEN u, d;

  if (!aco) return cgetg(1,t_MAT);
  li = gel(a,1)[1];
  d = zero_Flv(li);
  bco = lg(b)-1;
  for (i=1; i<=aco; i++)
  {
    GEN ai = vecsmall_copy(gel(a,i));
    if (!d[i] && F2v_coeff(ai, i))
      k = i;
    else
      for (k = 1; k <= li; k++) if (!d[k] && F2v_coeff(ai,k)) break;
    /* found a pivot on row k */
    if (k > li) return NULL;
    d[k] = i;

    /* Clear k-th row but column-wise instead of line-wise */
    /*  a_ij -= a_i1*a1j/a_11
       line-wise grouping:  L_j -= a_1j/a_11*L_1
       column-wise:         C_i -= a_i1/a_11*C_1
    */
    F2v_clear(ai,k);
    for (l=1; l<=aco; l++)
    {
      GEN al = gel(a,l);
      if (F2v_coeff(al,k)) F2v_add_inplace(al,ai);
    }
    for (l=1; l<=bco; l++)
    {
      GEN bl = gel(b,l);
      if (F2v_coeff(bl,k)) F2v_add_inplace(bl,ai);
    }
  }
  u = cgetg(bco+1,t_MAT);
  for (j = 1; j <= bco; j++) gel(u,j) = F2_get_col(gel(b,j), d, li, aco);
  return u;
}

GEN
F2m_gauss(GEN a, GEN b)
{
  pari_sp av = avma;
  if (lg(a) == 1) return cgetg(1,t_MAT);
  return gerepileupto(av, F2m_gauss_sp(F2m_copy(a), F2m_copy(b)));
}
GEN
F2m_F2c_gauss(GEN a, GEN b)
{
  pari_sp av = avma;
  GEN z = F2m_gauss(a, mkmat(b));
  if (!z) return gc_NULL(av);
  if (lg(z) == 1) { set_avma(av); return cgetg(1,t_VECSMALL); }
  return gerepileuptoleaf(av, gel(z,1));
}

GEN
F2m_inv(GEN a)
{
  pari_sp av = avma;
  if (lg(a) == 1) return cgetg(1,t_MAT);
  return gerepileupto(av, F2m_gauss_sp(F2m_copy(a), matid_F2m(gel(a,1)[1])));
}

GEN
F2m_invimage_i(GEN A, GEN B)
{
  GEN d, x, X, Y;
  long i, j, nY, nA = lg(A)-1, nB = lg(B)-1;
  x = F2m_ker_sp(shallowconcat(A, B), 0);
  /* AX = BY, Y in strict upper echelon form with pivots = 1.
   * We must find T such that Y T = Id_nB then X T = Z. This exists iff
   * Y has at least nB columns and full rank */
  nY = lg(x)-1;
  if (nY < nB) return NULL;

  /* implicitly: Y = rowslice(x, nA+1, nA+nB), nB rows */
  d = cgetg(nB+1, t_VECSMALL);
  for (i = nB, j = nY; i >= 1; i--, j--)
  {
    for (; j>=1; j--)
      if (F2m_coeff(x,nA+i,j)) { d[i] = j; break; } /* Y[i,j] */
    if (!j) return NULL;
  }
  x = vecpermute(x, d);

  X = F2m_rowslice(x, 1, nA);
  Y = F2m_rowslice(x, nA+1, nA+nB);
  return F2m_mul(X, F2m_inv_upper_1(Y));
}
GEN
F2m_invimage(GEN A, GEN B)
{
  pari_sp av = avma;
  GEN X = F2m_invimage_i(A,B);
  if (!X) return gc_NULL(av);
  return gerepileupto(av, X);
}

GEN
F2m_F2c_invimage(GEN A, GEN y)
{
  pari_sp av = avma;
  long i, l = lg(A);
  GEN M, x;

  if (l==1) return NULL;
  if (lg(y) != lgcols(A)) pari_err_DIM("F2m_F2c_invimage");
  M = cgetg(l+1,t_MAT);
  for (i=1; i<l; i++) gel(M,i) = gel(A,i);
  gel(M,l) = y; M = F2m_ker(M);
  i = lg(M)-1; if (!i) return gc_NULL(av);

  x = gel(M,i);
  if (!F2v_coeff(x,l)) return gc_NULL(av);
  F2v_clear(x, x[1]); x[1]--; /* remove last coord */
  return gerepileuptoleaf(av, x);
}

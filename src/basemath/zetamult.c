/* Copyright (C) 2000  The PARI group.
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
/**             MULTIPLE ZETA VALUES (AKHILESH ALGORITHM)          **/
/**                                                                **/
/********************************************************************/
#include "pari.h"
#include "paripriv.h"

static GEN
la(long e, long f, GEN s)
{
  if (e == f) return gmul2n(s,1);
  return (e > f)? s: gmulgs(s,3);
}

/* dual of evec[1..l-1] */
static GEN
revslice(GEN evec, long l)
{
  GEN res = cgetg(l, t_VECSMALL);
  long i;
  for (i = 1; i < l; ++i) res[i] = 1 - evec[l-i];
  return res;
}

/* N.B. evec[ne] = 1 */
static GEN
etoa(GEN evec)
{
  long ct = 0, ctold = 0, i = 1, le = lg(evec);
  GEN avec = cgetg(le, t_VECSMALL);
  while (++ct < le)
    if (evec[ct] == 1) { avec[i++] = ct - ctold; ctold = ct; }
  setlg(avec, i); return avec;
}

static GEN
atoe(GEN avec)
{
  long i, l = lg(avec);
  GEN evec = cgetg(l, t_VEC);
  for (i = 1; i < l; i++) { long a = avec[i]; gel(evec,i) = vecsmall_ei(a,a); }
  return shallowconcat1(evec);
}

/* phivec[i] contains phip(j,avec[i..r]) for 1<=j<=N > 2 */
static GEN
phip(long N, GEN avec, long prec)
{
  long i, j, ar, r = lg(avec) - 1;
  GEN u, r1, phivec = cgetg(r+1, t_VEC);

  ar = avec[r]; r1 = real_1(prec);
  gel(phivec, r) = u = cgetg(N, t_VEC); gel(u,1) = r1;
  for (j = 2; j < N; j++) gel(u,j) = divri(r1, powuu(j,ar));
  for (i = r-1; i >= 1; i--)
  {
    GEN t, phi = gel(phivec,i+1);
    ar = avec[i];
    gel(phivec, i) = u = cgetg(N, t_VEC);
    gel(u,1) = gen_0; t = gel(phi,1);
    gel(u,2) = gmul2n(t, -ar);
    for (j = 3; j < N; j++)
    {
      t = mpadd(t, gel(phi,j-1));
      gel(u,j) = mpdiv(t, powuu(j,ar));
    }
  }
  return phivec;
}

/* Return 1 if vec2 RHS of vec1, -1 if vec1 RHS of vec2, 0 else */
static long
isrhs(GEN v1, GEN v2)
{
  long s = 1, i, l1 = lg(v1), l2 = lg(v2);
  if (l1 < l2) { s = -1; swap(v1,v2); lswap(l1,l2); }
  for (i = l2-1; i >= 1; --i)
    if (v2[i] != v1[l1-l2+i]) return 0;
  return s;
}

static long
istruerhs(GEN v1, GEN v2)
{
  long i, l1 = lg(v1), l2 = lg(v2);
  if (l1 < l2) return 0;
  for (i = l2-1; i >= 1; --i)
    if (v2[i] != v1[l1-l2+i]) return 0;
  return l1-l2+1;
}

static GEN
isinphi(GEN v, GEN a, GEN phivec)
{
  long m, l = lg(v);
  for (m = 1; m < l; m++)
  {
    long s = istruerhs(gel(v,m), a);
    if (s) return gmael(phivec,m,s);
  }
  return NULL;
}

/* If v RHS of LR[i] for some i, return LR. If LR[i] RHS (strict) of v, replace
 * LR[i] by v. If none, add v to LR. */
static GEN
addevec(GEN LR, GEN v)
{
  long s, i, l1 = lg(LR);
  for (i = 1; i < l1; i++)
  {
    s = isrhs(gel(LR,i), v);
    if (s == 1) return LR;
    if (s ==-1) { gel(LR,i) = v; return LR; }
  }
  return vec_append(LR,v);
}

GEN
zetamult(GEN avec, long prec)
{
  pari_sp ltop = avma;
  long k, n, i, j, N, l, bitprec, prec2;
  GEN binvec, S, LR, phiall, MA, MR, evec = gen_0;

  avec = zetamultconvert(avec, 1);
  if (lg(avec) == 1) return gen_1;
  evec = atoe(avec);
  k = lg(evec)-1; /* weight */
  bitprec = prec2nbits(prec) + 64*(1+(k>>5));
  prec2 = nbits2prec(bitprec);
  N = 5 + bitprec/2;
  binvec = cgetg(N+1, t_VEC); gel(binvec, 1) = gen_2;
  for (n = 2; n <= N; ++n)
    gel(binvec, n) = diviuexact(mului(4*n-2, gel(binvec, n-1)), n);
  LR = cgetg(1, t_VEC);
  MA = cgetg(k, t_VEC);
  MR = cgetg(k, t_VEC);
  for (i = 1; i < k; ++i)
  {
    gel(MA,i) = etoa(revslice(evec, i+1));
    gel(MR,i) = etoa(vecslice(evec, i+1, k));
    LR = addevec(addevec(LR, gel(MA,i)), gel(MR,i));
  }
  l = lg(LR);
  phiall = cgetg(l, t_VEC);
  for (j = 1; j < l; j++) gel(phiall,j) = phip(N+1, gel(LR,j), prec2);
  S = real_0(prec2);
  for (i = 1; i < k; i++)
  {
    GEN phi1 = isinphi(LR, gel(MA,i), phiall);
    GEN phi2 = isinphi(LR, gel(MR,i), phiall);
    GEN s = gmul2n(mpmul(gel(phi1,1), gel(phi2,1)), -1);
    for (n = 2; n <= N; ++n)
      s = mpadd(s, mpdiv(mpmul(gel(phi1,n), gel(phi2,n)), gel(binvec,n)));
    S = mpadd(S, la(evec[i], evec[i+1], s));
  }
  return gerepileuptoleaf(ltop, rtor(S,prec));
}

/**************************************************************/
/*                         ALL MZV's                          */
/**************************************************************/

/* vecsmall to binary */
static long
myfd(GEN evec, long ini, long fin)
{
  long i, s = 0;
  for (i = ini; i <= fin; ++i) s = evec[i] | (s << 1);
  return s;
}

/* Given admissible evec w = 0e_2....e_{k-1}1, compute a,b,v such that
 * w=0{1}_{b-1}v{0}_{a-1}1 with v empty or admissible.
 * Input: binary vector evec */
static void
findabv(GEN w, long *pa, long *pb, long *pminit, long *pmmid, long *pmfin)
{
  long le = lg(w) - 2;
  if (le == 0)
  {
    *pa = 1;
    *pb = 1;
    *pminit = 2;
    *pmfin = 2;
    *pmmid = 1;
  }
  else
  {
    long a, b, j, lv;
    for (j = 1; j <= le; ++j)
      if (!w[j+1]) break;
    b = j;
    for (j = le; j >= 1; --j)
      if (w[j+1]) break;
    a = le + 1 - j;
    lv = le + 2 - a - b;
    if (lv > 0)
    {
      long v = myfd(w, b + 1, le - a + 2);
      *pa = a;
      *pb = b;
      *pminit = (((1 << b) - 1) << (lv - 1)) + (v/2) + 2;
      *pmfin = (((1 << (lv - 1)) + v) << (a - 1)) + 2;
      *pmmid = (1 << (lv - 2)) + (v/2) + 2;
    }
    else
    {
      *pa = a;
      *pb = b;
      *pminit = (1 << (b - 1)) + 1;
      *pmfin = (a == 1) ? 2 : (1 << (a - 2)) + 2;
      *pmmid = 1;
    }
  }
}

/* Returns 'all':
* all[1] contains zeta(emptyset)_{n-1,n-1},
* all[2] contains zeta({0})_{n-1,n-1}=zeta({1})_{n-1,n-1} for n >= 2,
* all[m+2][n] : 1 <= m < 2^{k-2}, 1 <= n <= N + 1
* contains zeta(w)_{n-1,n-1}, w corresponding to m,n
* all[m+2] : 2^{k-2} <= m < 2^{k-1} contains zeta(w), w corresponding to m
(code: w=0y1 iff m=1y). */
static GEN
fillall(long k, long bitprec)
{
  long N = bitprec / 2, prec = nbits2prec(bitprec);
  long k1, j, n, m, mbar = 0, K = 1 << (k - 1), K2 = K/2;
  GEN all, binvec, p1, p2, r1, pab, S;
  r1 = real_1(prec);
  pab = cgetg(N + 2, t_VEC); gel(pab, 1) = gen_0; /* not needed */
  for (n = 2; n <= N+1; n++) gel(pab, n) = powersr(divru(r1, n), k);
  /* 1/n^a = gmael(pab, n, a + 1) */
  binvec = cgetg(N + 2, t_VEC); gel(binvec, 1) = gen_1;
  for (n = 1; n <= N; n++)
    gel(binvec, n+1) = diviuexact(mului(4*n-2, gel(binvec, n)), n);
  all = cgetg(K + 2, t_VEC);
  gel(all, 1) = p1 = cgetg(N + 2, t_VEC); gel(p1, 1) = r1;
  for (j = 2; j <= N+1; j++) gel(p1, j) = divri(r1, gel(binvec, j));
  gel(all, 2) = p2 = cgetg(N + 2, t_VEC); gel(p2, 1) = gen_0;
  for (j = 2; j <= N+1; j++) gel(p2, j) = gdivgs(gel(p1, j), j - 1);
  for (m = 1; m < K2; m++)
  {
    gel(all, m+2) = p1 = cgetg(N + 2, t_VEC);
    for (n = 1; n <= N; n++) gel(p1, n) = cgetr(prec);
    gel(p1, n) = gen_0;
  }
  for (m = K2; m < K; m++)
  {
    gel(all, m+2) = p1 = cgetr(prec);
    mpaff(gen_0, p1);
  }
  for (k1 = 2; k1 <= k; ++k1)
  { /* Assume length evec < k1 filled */
    /* If evec = 0e_2...e_{k_1-1}1 then m = (1e_2...e_{k_1-1})_2 */
    GEN w = cgetg(k1, t_VECSMALL);
    long M = 1 << (k1 - 2);
    pari_sp av = avma;
    for (m = M; m < 2*M; ++m)
    {
      GEN pinit, pfin, pmid;
      long comp, a, b, minit, mfin, mmid, mc = m, ii = 0;
      p1 = gel(all, m + 2);
      for (j = k1 - 1; j >= 2; --j)
      {
        w[j] = mc & 1;
        ii = (1 - w[j]) | (ii<<1);
        mc >>= 1;
      }
      mbar = M + ii;
      comp = mbar - m;
      if (comp < 0) continue;
      p2 = gel(all, mbar + 2);
      findabv(w, &a,&b,&minit,&mmid,&mfin);
      pinit= gel(all, minit);
      pfin = gel(all, mfin);
      pmid = gel(all, mmid);
      for (n = N; n > 1; n--, avma = av)
      {
        GEN t = mpmul(gel(pinit,n+1), gmael(pab, n, a + 1));
        GEN u = mpmul(gel(pfin, n+1), gmael(pab, n, b + 1));
        GEN v = mpmul(gel(pmid, n+1), gmael(pab, n, a + b + 1));
        S = mpadd(k1 < k ? gel(p1, n+1) : p1, mpadd(mpadd(t, u), v));
        if (!signe(S)) S = gen_0;
        mpaff(S, k1 < k ? gel(p1, n) : p1);
        if (comp > 0 && k1 < k) mpaff(S, gel(p2, n));
      }
      { /* n = 1: same formula simplifies */
        GEN t = gel(pinit,2), u = gel(pfin,2), v = gel(pmid,2);
        S = mpadd(k1 < k ? gel(p1,2) : p1, mpadd(mpadd(t, u), v));
        if (!signe(S)) S = gen_0;
        mpaff(S, k1 < k ? gel(p1,1) : p1);
        if (comp > 0 && k1 < k) mpaff(S, gel(p2, 1));
        avma = av;
      }
      if (comp > 0 && k1 == k) mpaff(p1, p2);
    }
  }
  for (j = 1; j < K; j++)
    gel(all, j) = j < K2 ? gmael(all, j+2, 1) : gel(all, j+2);
  setlg(all, K); return all;
}

GEN
zetamultall(long k, long prec)
{
  pari_sp av = avma;
  if (k < 1) pari_err_DOMAIN("zetamultall", "k", "<", gen_1, stoi(k));
  if (k >= 64) pari_err_OVERFLOW("zetamultall");
  return gerepilecopy(av, fillall(k, prec2nbits(prec) + 32));
}

/* m > 0 */
static GEN
mtoevec(GEN m)
{
  GEN e = vecsmall_append(binary_zv(m), 1);
  e[1] = 0; return e;
}

static GEN
etoindex(GEN evec)
{
  long k = lg(evec) - 1;
  return utoipos((1 << (k-2)) + myfd(evec, 2, k-1));
}

/* Conversions: types are evec, avec, m (if evec=0y1, m=(1y)_2).
   fl is respectively 0, 1, 2. Type of a is autodetected. */
GEN
zetamultconvert(GEN a, long fl)
{
  pari_sp av = avma;
  long i, l;
  if (fl < 0 || fl > 2) pari_err_FLAG("zetamultconvert");
  switch(typ(a))
  {
    case t_INT:
      if (signe(a) <= 0) pari_err_TYPE("zetamultconvert",a);
      switch (fl)
      {
        case 0: a = mtoevec(a); break;
        case 1: a = etoa(mtoevec(a)); break;
        case 2: a = icopy(a); break;
      }
      break;
    case t_VEC: case t_COL: case t_VECSMALL:
      a = gtovecsmall(a);
      l = lg(a);
      if (a[1] == 0)
      {
        if (!a[l-1]) pari_err_TYPE("zetamultconvert", a);
        for (i = 1; i < l; i++)
          if (a[i] & ~1UL) pari_err_TYPE("zetamultconvert", a);
        switch (fl)
        {
          case 1: a = etoa(a); break;
          case 2: a = etoindex(a);
        }
      }
      else
      {
        if (a[1] < 2) pari_err_TYPE("zetamultconvert", a);
        for (i = 2; i < l; i++)
          if (a[i] <= 0) pari_err_TYPE("zetamultconvert", a);
        switch (fl)
        {
          case 0: a = atoe(a); break;
          case 2: a = etoindex(atoe(a));
        }
      }
      break;
    default: pari_err_TYPE("zetamultconvert", a);
  }
  return gerepileuptoleaf(av, a);
}

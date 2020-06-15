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
/**                         MULTIPLE ZETA VALUES                   **/
/**                                                                **/
/********************************************************************/
#include "pari.h"
#include "paripriv.h"

/********************************************************************/
/**                           CONVERSIONS                          **/
/********************************************************************/
/* vecsmall to binary */
static long
fd(GEN evec, long a, long b)
{
  long i, s = 0;
  for (i = a; i <= b; i++) s = evec[i] | (s << 1);
  return s;
}
/* 2^(b-a+1) + fd(evec) */
static long
fd1(GEN evec, long a, long b)
{
  long i, s = 1;
  for (i = a; i <= b; i++) s = evec[i] | (s << 1);
  return s;
}
static GEN
vfd(GEN evec, long a, long b)
{
  GEN e = cgetg(b - a + 2, t_VECSMALL);
  long i;
  for (i = a; i <= b; i++) e[i - a + 1] = evec[i];
  return e;
}

/* m > 0 */
static GEN
mtoevec(GEN m)
{
  GEN e = vecsmall_append(binary_zv(m), 1);
  e[1] = 0; return e;
}
static GEN
etoindex(GEN evec) { return utoipos(fd1(evec, 2, lg(evec)-2)); }

/* dual of evec[1..l-1] */
static GEN
revslice(GEN evec, long l)
{
  GEN res = cgetg(l, t_VECSMALL);
  long i;
  for (i = 1; i < l; i++) res[i] = 1 - evec[l-i];
  return res;
}

/* N.B. evec[ne] = 1 */
static GEN
etoa(GEN evec)
{
  long c = 0, cold = 0, i = 1, l = lg(evec);
  GEN avec = cgetg(l, t_VECSMALL);
  while (++c < l)
    if (evec[c] == 1) { avec[i++] = c - cold; cold = c; }
  setlg(avec, i); return avec;
}

static GEN
atoe(GEN avec)
{
  long i, j, l = lg(avec), n = zv_sum(avec);
  GEN evec = zero_zv(n);
  for (i = 1, j = 0; i < l; i++) { long a = avec[i]; j += a; evec[j] = 1; }
  return evec;
}


/* Conversions: types are evec, avec, m (if evec=0y1, m=(1y)_2).
   fl is respectively 0, 1, 2. Type of a is autodetected. */
static GEN
zetamultconvert_i(GEN a, long fl)
{
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
  return a;
}
GEN
zetamultconvert(GEN a, long fl)
{
  pari_sp av = avma;
  return gerepileuptoleaf(av, zetamultconvert_i(a, fl));
}

GEN
zetamultdual(GEN s)
{
  pari_sp av = avma;
  GEN e = zetamultconvert_i(s, 0);
  return gerepileuptoleaf(av, etoa(revslice(e, lg(e))));
}

/********************************************************************/
/**                      AKHILESH ALGORITHM                        **/
/********************************************************************/
static long
la(long e, long f) { return (e == f)? 2: (e? 1: 3); }
static GEN
lamul(long la, GEN s)
{
  switch(la)
  {
    case 2: return gmul2n(s,1);
    case 3: return gmulgs(s,3);
    default: return s;
  }
}

/* vpow[s][j] = j^-s as a t_INT or t_REAL; j < L
 * return vphi s.t. vphi[i] = phi_j(a[i..r]) for 0 < j < L */
static GEN
get_vphi(GEN a, GEN vpow)
{
  long i, r = lg(a) - 1;
  GEN vphi = cgetg(r+1, t_VEC);
  gel(vphi, r) = gel(vpow, a[r]);
  for (i = r-1; i >= 1; i--)
  {
    GEN t, u, phi = gel(vphi,i+1), pow = gel(vpow, a[i]);
    long j, L = lg(pow), J = minss(L, r-i), prec = realprec(gel(pow,L-1));
    pari_sp av;
    gel(vphi, i) = u = cgetg(L, t_VEC);
    for (j = 1; j <= J; j++) gel(u,j) = gen_0;
    t = gel(phi,j-1); /* 1 if j == 2 */
    gel(u,j) = j == 2? gel(pow,2): mpmul(t, gel(pow,j));
    for (j = J+2; j < L; j++) gel(u,j) = cgetr(prec);
    av = avma;
    for (j = J+2; j < L; j++)
    {
      t = mpadd(t, gel(phi,j-1));
      affrr(mpmul(t, gel(pow,j)), gel(u,j)); /* t / j^a[i] */
      if (!(j & 0xff)) t = gerepileuptoleaf(av, t);
    }
    set_avma(av);
  }
  return vphi;
}

/* Return 1 if vec2 RHS of vec1, -1 if vec1 RHS of vec2, 0 else */
static long
isrhs(GEN v1, GEN v2)
{
  long s = 1, i, l1 = lg(v1), l2 = lg(v2);
  if (l1 < l2) { s = -1; swap(v1,v2); lswap(l1,l2); }
  for (i = l2-1; i >= 1; i--)
    if (v2[i] != v1[l1-l2+i]) return 0;
  return s;
}

static long
istruerhs(GEN v1, GEN v2)
{
  long i, l1 = lg(v1), l2 = lg(v2);
  if (l1 < l2) return 0;
  for (i = l2-1; i >= 1; i--)
    if (v2[i] != v1[l1-l2+i]) return 0;
  return l1-l2+1;
}

/* a is a rhs of a unique v[m] */
static GEN
isinphi(GEN v, GEN a, GEN vphi)
{
  long m, l = lg(v);
  for (m = 1; m < l; m++)
  {
    long s = istruerhs(gel(v,m), a);
    if (s) return gmael(vphi,m,s);
  }
  return NULL; /* LCOV_EXCL_LINE */
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

/* N > 1, v[n] = 1 / binom(2n, n) as a t_REAL */
static GEN
get_vbin(long N, long prec)
{
  GEN v = cgetg(N+1, t_VEC);
  long n;
  gel(v,1) = gen_0; /* unused */
  gel(v,2) = invr(utor(6,prec));
  for (n = 3; n <= N; n++) gel(v,n) = divru(mulru(gel(v,n-1), n), 4*n-2);
  return v;
}
/* length k */
static GEN
zetamultinit_i(long k, long m, long bitprec)
{
  long i, N, prec;
  GEN vpow = cgetg(m+1, t_VEC);

  bitprec += 64*(1+(k>>5));
  prec = nbits2prec(bitprec);
  N = 5 + bitprec/2;
  gel(vpow,1) = vecpowug(N, gen_m1, prec);
  for (i = 2; i <= m; i++)
  {
    GEN pow = cgetg(N+1, t_VEC), powm = gel(vpow,i-1);
    long j;
    gel(pow,1) = gen_1;
    gel(pow,2) = real2n(-i, prec);
    for (j = 3; j <= N; j++) gel(pow,j) = divru(gel(powm,j), j);
    gel(vpow,i) = pow;
  }
  return mkvec2(vpow, get_vbin(N, prec));
}
GEN
zetamultinit(long n, long prec)
{
  pari_sp av = avma;
  if (n <= 2) pari_err_DOMAIN("zetamultinit", "weight", "<=", gen_2, stoi(n));
  return gerepilecopy(av, zetamultinit_i(n-1, n-1, prec2nbits(prec)));
}
/* a a t_VECSMALL */
static GEN
zetamult_i(GEN a, GEN T, long prec)
{
  pari_sp av = avma;
  long k, m, n, i, j, l, L;
  GEN vpow, vphi, vbin, LR, MA, MR, e, vLA, v1, v2, S = NULL;

  if (lg(a) == 1) return gen_1;
  if (lg(a) == 2) return szeta(a[1], prec);
  e = atoe(a); k = lg(e)-1; /* weight */
  LR = cgetg(1, t_VEC);
  MA = cgetg(k, t_VEC);
  MR = cgetg(k, t_VEC);
  for (i = 1; i < k; i++)
  {
    gel(MA,i) = etoa(revslice(e, i+1));
    gel(MR,i) = etoa(vecslice(e, i+1, k));
    LR = addevec(addevec(LR, gel(MA,i)), gel(MR,i));
  }
  m = vecvecsmall_max(LR);
  if (!T) T = zetamultinit_i(k, m, prec2nbits(prec));
  else
  {
    if (typ(T) != t_VEC || lg(T) != 3) pari_err_TYPE("zetamult", T);
    n = lg(gel(T,1));
    if (n <= m) pari_err_DOMAIN("zetamult", "weight", ">", utoi(n), utoi(k));
  }
  vpow = gel(T,1);
  vbin = gel(T,2);
  l = lg(LR); vphi = cgetg(l, t_VEC);
  for (j = 1; j < l; j++) gel(vphi,j) = get_vphi(gel(LR,j), vpow);
  vLA = cgetg(k, t_VECSMALL);
  v1 = cgetg(k, t_VEC);
  v2 = cgetg(k, t_VEC);
  for (i = 1; i < k; i++)
  {
    vLA[i] = la(e[i],e[i+1]);
    gel(v1,i) = isinphi(LR, gel(MA,i), vphi);
    gel(v2,i) = isinphi(LR, gel(MR,i), vphi);
  }
  L = lg(vbin); av = avma;
  for (n = 1; n < L; n++)
  {
    GEN s = lamul(vLA[1], mpmul(gmael(v1,1,n), gmael(v2,1,n)));
    for (i = 2; i < k; i++)
      s = mpadd(s, lamul(vLA[i], mpmul(gmael(v1,i,n), gmael(v2,i,n))));
    if (n == 1)
      S = gmul2n(s,-1);
    else
      S = gerepileupto(av, gadd(S, mpmul(s, gel(vbin,n))));
  }
  return S;
}
GEN
zetamult0(GEN s, GEN T, long prec)
{
  pari_sp av0 = avma, av;
  GEN z, avec, r = cgetr(prec);

  av = avma; avec = zetamultconvert_i(s,1);
  if (lg(avec) == 1) return gc_const(av0, gen_1);
  z = zetamult_i(avec, T, prec); affrr(z, r); return gc_const(av, r);
}
GEN
zetamult(GEN s, long prec) { return zetamult0(s, NULL, prec); }

static GEN allstar(GEN avec);
/* If star = NULL, ordinary MZV, otherwise Yamamoto interpolation (MZSV for t = 1).
 * The latter has complexity O~(2^|s|). */
GEN
zetamult_interpolate(GEN s, GEN t, GEN T, long prec)
{
  pari_sp av = avma, av2;
  long i, l, la;
  GEN avec, v, V;
  if (!t) return zetamult0(s, T, prec);

  avec = zetamultconvert_i(s, 1);
  v = allstar(avec); l = lg(v); la = lg(avec);
  if (!T) T = zetamultinit_i(la-1, zv_sum(avec)-1, prec2nbits(prec));
  V = cgetg(la, t_VEC);
  for (i = 1; i < la; i++)
  { gel(V,i) = cgetr(prec + EXTRAPRECWORD); affur(0, gel(V,i)); }
  av2 = avma;
  for (i = 1; i < l; i++, set_avma(av2))
  {
    GEN a = gel(v,i); /* avec */
    long n = lg(a)-1; /* > 0 */
    affrr(addrr(gel(V,n), zetamult_i(a, T, prec)), gel(V,n));
  }
  return gerepileupto(av, poleval(vecreverse(V),t));
}

/**************************************************************/
/*                         ALL MZV's                          */
/**************************************************************/
/* Find all star avecs corresponding to given t_VECSMALL avec */
static GEN
allstar(GEN avec)
{
  long i, la = lg(avec), K = 1 << (la - 2);
  GEN w = cgetg(K + 1, t_VEC);

  gel(w, 1) = avec;
  for (i = 2; i < la; i++)
  {
    long L = 1 << (i - 2), j;
    for (j = 1; j <= L; j++)
    {
      GEN u = gel(w,j), v;
      long k, l = lg(u) - 1, ind = l - la + i;
      gel(w, L + j) = v = cgetg(l, t_VECSMALL);
      for (k = 1; k < ind; k++) v[k] = u[k];
      v[ind] = u[ind] + u[ind + 1];
      for (k = ind + 1; k < l; k++) v[k] = u[k+1];
    }
  }
  return w;
}

static GEN
allstar2(GEN avec, GEN zvec)
{
  long la = lg(avec), i, K = 1 << (la - 2);
  GEN W = cgetg(K + 1, t_VEC), Z = cgetg(K + 1, t_VEC);

  gel(W, 1) = avec = gtovecsmall(avec);
  gel(Z, 1) = zvec = gtovec(zvec);
  for (i = 2; i < la; i++)
  {
    long L = 1 << (i - 2), j;
    for (j = 1; j <= L; j++)
    {
      GEN u = gel(W, j), w, y = gel(Z, j), z;
      long l = lg(u) - 1, ind = l - la + i, k;
      w = cgetg(l, t_VECSMALL);
      z = cgetg(l, t_VEC);
      for (k = 1; k < ind; k++) { w[k] = u[k]; gel(z, k) = gel(y, k); }
      w[ind] = u[ind] + u[ind + 1];
      gel(z, ind) = gmul(gel(y, ind), gel(y, ind + 1));
      for (k = ind + 1; k < l; k++) { w[k] = u[k + 1]; gel(z, k) = gel(y, k + 1); }
      gel(W, L + j) = w;
      gel(Z, L + j) = z;
    }
  }
  return mkvec2(W, Z);
}

/* Generalization to Multiple Polylogarithms.
The basic function is polylogmult which takes two arguments
avec, as above, and zvec, the vector of z_j, and the result
is $\sum_{n_1>n_2>...>n_r>0}z_1^{n_1}...z_r^{n_r}/(n_1^a_1...n_r^{a_r})$. */

/* Given admissible evec = xe_2....e_{k-1}y, (k>=2), compute a,b,v such that
evec = x{1}_{a-1}v{0}_{b-1}y with v empty or admissible.
Input: vector w=evec
Output: v=wmid, winit, wfin
Difference with findabv: winit, wfin, and wmid are computed here. */
static void
findabvgen(GEN evec, GEN *wmid, GEN *winit, GEN *wfin)
{
  long le = lg(evec) - 1, a, b, j;
  GEN x = gel(evec, 1), y = gel(evec, le);
  if (le <= 2)
  {
    *wmid = cgetg(1, t_VEC);
    *winit = mkvec(x);
    *wfin = mkvec(y); return;
  }
  a = le - 1;
  for (j = 1; j <= le - 2; j++)
    if (!gequal1(gel(evec, j + 1))) { a = j; break; }
  b = le - 1;
  for (j = le - 2; j >= 1; j--)
    if (!gequal0(gel(evec, j + 1))) { b = le - 1 - j; break; }
  *wmid = a + b <= le - 1 ? vecslice(evec, a + 1, le - b) : cgetg(1, t_VEC);
  *winit = shallowconcat(shallowconcat(x, const_vec(a-1, gen_1)), *wmid);
  *wfin = shallowconcat(shallowconcat(*wmid, const_vec(b-1,gen_0)), y);
}

static long
acros(GEN evec)
{
  pari_sp av = avma;
  long l = lg(evec);
  GEN u, v, wmid, winit, wfin;
  if (l <= 2) return 0;
  findabvgen(evec, &wmid, &winit, &wfin);
  u = gel(evec,1); v = gel(evec,l-1);
  return gc_long(av, maxss(-gexpo(gmul(gsubsg(1, u), v)), 0)
                     + maxss(acros(wmid), maxss(acros(winit), acros(wfin))));
}

static GEN
mk(GEN p) { return (lg(p) > 2)? mkvec2(p, NULL): mkvec(p); }
static GEN
findabvgenrec(GEN evec, void(*find)(GEN,GEN*,GEN*,GEN*))
{
  long j, wlen = 4096, lw = 1, fl = 1;
  GEN w = cgetg(wlen + 1, t_VEC);
  gel(w, lw++) = mkvec2(evec, NULL);
  while (fl)
  {
    fl = 0;
    for (j = 1; j < lw; j++)
    {
      GEN wj = gel(w, j);
      if (lg(wj) == 3 && !gel(wj,2))
      {
        GEN wmid, winit, wfin;
        find(gel(wj,1), &wmid, &winit, &wfin);
        gel(wj, 2) = mkvecsmall(lw);
        if (lw + 3 >= wlen) { wlen <<= 2; w = vec_lengthen(w, wlen); }
        gel(w, lw++) = mk(wmid);
        gel(w, lw++) = mk(winit);
        gel(w, lw++) = mk(wfin); fl = 1;
      }
    }
  }
  setlg(w, lw); return w;
}

/* y != 0,1 */
static GEN
filllg1(GEN ibin1, GEN r1, GEN y, long N, long prec)
{
  GEN v, y1 = gsubgs(gmulsg(2, y), 1), y3 = gmul(y, gsubsg(1, y));
  long n;

  v = cgetg(N + 2, t_VEC); gel(v, N + 1) = gen_0;
  if (gcmpgs(gnorm(y3),1) > 0)
  {
    GEN y2 = gdiv(r1, y3);
    for (n = N; n >= 1; n--)
    {
      pari_sp av2 = avma;
      GEN z = gmul(y2, gsub(gel(v, n+1), gmul(y1, gel(ibin1, n+1))));
      gel(v, n) = gerepileupto(av2, z);
    }
  }
  else
  {
    pari_sp av0 = avma;
    gel(v, 1) = gerepileupto(av0, glog(gdiv(y, gsubgs(y, 1)), prec));
    for (n = 1; n < N; n++)
    {
      pari_sp av2 = avma;
      GEN z = gadd(gmul(y3, gel(v, n)), gmul(y1, gel(ibin1, n+1)));
      gel(v, n + 1) = gerepileupto(av2, z);
    }
  }
  return v;
}

/* k > 1 */
static GEN
filltabM(GEN ibin, GEN ibin1, GEN evecinit, long prec)
{
  GEN r1 = real_1(prec), tabevec = findabvgenrec(evecinit, &findabvgen);
  long j, j1, k1, k = lg(evecinit)-1, N = lg(ibin)-2, ltab = lg(tabevec);

  for (j = 1; j < ltab; j++)
  {
    GEN e = gel(tabevec,j);
    if (lg(e) == 2)
    {
      GEN evec = gel(e,1);
      if (lg(evec) == 1) gel(e,1) = ibin;
      if (lg(evec) == 2)
      {
        GEN y = gel(evec, 1);
        if (isintzero(y) || isint1(y)) gel(e,1) = ibin1;
        else
        {
          GEN res = filllg1(ibin1, r1, y, N, prec);
          gel(e,1) = res;
          for (j1 = j + 1; j1 < ltab; j1++)
          {
            GEN ev = gel(tabevec, j1);
            if (lg(ev) == 2 && lg(gel(ev,1)) == 2 && gequal(gmael(ev,1,1), y))
              gel(ev,1) = res;
          }
        }
      }
    }
  }
  for (k1 = 2; k1 <= k; k1++)
    for (j = 1; j < ltab; j++)
    {
      GEN e0 = gel(tabevec, j);
      if (lg(e0) == 3 && lg(gel(e0, 1)) == k1 + 1)
      {
        GEN evec = gel(e0, 1), tmp, tabfin, tabini, tabmid;
        GEN xy1, x = gel(evec, 1), y = gel(evec, k1);
        long n, a, b, j2, s, ct = gel(e0,2)[1];
        tabmid = gmael(tabevec, ct, 1);
        tabini = gmael(tabevec, ct + 1, 1);
        tabfin = gmael(tabevec, ct + 2, 1);
        if (gequal0(x)) { s = -1; xy1 = gdiv(r1, y); }
        else { s = 1; xy1 = gdiv(r1, gmul(gsubsg(1, x), y)); }
        a = k1 - 1;
        for (j2 = 1; j2 <= k1 - 2; j2++)
          if (!isint1(gel(evec, j2 + 1))) { a = j2; break;}
        b = k1 - 1;
        for (j2 = k1 - 2; j2 >= 1; j2--)
          if (!isintzero(gel(evec, j2 + 1))) { b = k1 - 1 - j2; break; }
        gel(e0,1) = tmp = cgetg(N+2, t_VEC); gel(tmp, N+1) = gen_0;
        for (n = N; n >= 1; n--)
        {
          pari_sp av = avma;
          GEN z,p1,p2,p3, na = powuu(n,a), nb = powuu(n,b), nab = mulii(na,nb);
          p1 = gmul(gel(tabini, n+1), na);
          p2 = gadd(gmul(gel(tabfin, n+1), nb), gel(tabmid, n+1));
          p3 = s > 0 ? gsub(p1, p2) : gadd(p1, p2);
          z = gmul(xy1, gadd(gel(tmp, n+1), gdiv(p3, nab)));
          gel(tmp, n) = gerepileupto(av, z);
        }
        for (j1 = j + 1; j1 < ltab; j1++)
        {
          GEN e = gel(tabevec, j1);
          if (lg(e) == 3 && gequal(gel(e,1), evec)) gel(e,1) = tmp;
        }
      }
    }
  return gmael(tabevec, 1, 1);
}

static GEN
aztoe(GEN avec, GEN zvec, long prec)
{
  GEN y, E, u = subsr(1, real2n(10-prec2nbits(prec), LOWDEFAULTPREC));
  long i, l = lg(avec);

  E = cgetg(l, t_VEC); if (l == 1) return E;
  y = gen_1;
  for (i = 1; i < l; i++)
  {
    long a = avec[i];
    GEN e, zi = gel(zvec, i);
    if (a <= 0 || (a == 1 && i == 1 && gequal1(zi)))
      pari_err_TYPE("polylogmult [divergent]", avec);
    if (gequal0(zi)) return NULL;
    gel(E, i) = e = zerovec(a);
    gel(e, a) = y = gdiv(y, zi);
    if (gcmp(gnorm(y), u) < 0) pari_err_TYPE("polylogmult [divergent]", zvec);
  }
  return shallowconcat1(E);
}

/***********************************************************/
/* Special case of zvec = [1,1,...], i.e., zetamult.       */
/***********************************************************/
static void
findabvgens(GEN evec, GEN *pwmid, GEN *pwinit, GEN *pwfin)
{
  GEN wmid, winit, wfin;
  long le = lg(evec) - 1, a, b, j, lw;
  if (le <= 2)
  {
    *pwmid = cgetg(1, t_VECSMALL);
    *pwinit = mkvecsmall(0);
    *pwfin = mkvecsmall(1); return;
  }
  a = le - 1;
  for (j = 1; j <= le - 2; j++) if (!evec[j + 1]) { a = j; break; }
  b = le - 1;
  for (j = le - 2; j >= 1; j--) if (evec[j + 1]) { b = le - 1 - j; break; }

  *pwmid = wmid = a+b <= le-1? vfd(evec, a+1, le-b): cgetg(1, t_VECSMALL);
  lw = lg(wmid) - 1;
  *pwinit = winit = cgetg(a + lw + 1, t_VECSMALL);
  winit[1] = 0; for (j = 2; j <= a; j++) winit[j] = 1;
  for (j = a + 1; j <= a + lw; j++) winit[j] = wmid[j - a];
  *pwfin = wfin = cgetg(b + lw + 1, t_VECSMALL);
  for (j = 1; j <= lw; j++) wfin[j] = wmid[j];
  for (j = lw + 1; j < b + lw; j++) wfin[j] = 0;
  wfin[b + lw] = 1;
}
/* k > 1 */
static GEN
filltabMs(GEN ibin, GEN ibin1, GEN evecinit, long prec)
{
  GEN tabevec = findabvgenrec(evecinit,&findabvgens);
  long j, k1, k = lg(evecinit)-1, N = lg(ibin)-2, ltab = lg(tabevec);

  for (j = 1; j < ltab; j++)
    if (lg(gel(tabevec, j)) == 2)
    {
      GEN evec = gmael(tabevec, j, 1);
      if (lg(evec) == 1) gmael(tabevec, j, 1) = ibin;
      if (lg(evec) == 2) gmael(tabevec, j, 1) = ibin1;
    }
  for (k1 = 2; k1 <= k; k1++)
    for (j = 1; j < ltab; j++)
    {
      GEN e0 = gel(tabevec, j);
      if (lg(e0) == 3 && lg(gel(e0, 1)) == k1 + 1)
      {
        GEN evec = gel(e0, 1), tmp, tabfin, tabini, tabmid;
        long n, a, b, j1, j2, ct = gel(e0,2)[1];
        tabmid = gmael(tabevec, ct, 1);
        tabini = gmael(tabevec, ct + 1, 1);
        tabfin = gmael(tabevec, ct + 2, 1);
        a = k1 - 1;
        for (j2 = 1; j2 <= k1 - 2; j2++)
          if (!evec[j2 + 1]) { a = j2; break;}
        b = k1 - 1;
        for (j2 = k1 - 2; j2 >= 1; j2--)
          if (evec[j2 + 1]) { b = k1 - 1 - j2; break; }
        gel(e0,1) = tmp = cgetg(N + 2, t_VEC); gel(tmp, N+1) = gen_0;
        for (n = N; n >= 1; n--)
        {
          GEN z = cgetr(prec);
          pari_sp av = avma;
          GEN na = powuu(n, a), nb = powuu(n, b), nab = mulii(na, nb);
          GEN p1, p2, p3;
          p1 = gmul(gel(tabini, n+1), na);
          p2 = gadd(gmul(gel(tabfin, n+1), nb), gel(tabmid, n+1));
          p3 = gadd(gel(tmp, n+1), gdiv(gadd(p1, p2), nab));
          mpaff(p3, z); set_avma(av); gel(tmp,n) = z;
        }
        for (j1 = j + 1; j1 < ltab; j1++)
        {
          GEN e = gel(tabevec, j1);
          if (lg(e) == 3 && gequal(gel(e,1), evec)) gel(e,1) = tmp;
        }
      }
    }
  return gmael(tabevec, 1, 1);
}

/* evec t_VECSMALL: mult. polylog with z = [1,...,1] => MZV; else t_VEC */
static GEN
zetamultevec(GEN evec, long prec)
{
  long log, n, bitprec, prec2, N, k = lg(evec) - 1;
  GEN all, ibin, ibin1;

  if (k == 0) return gen_1;
  log = typ(evec) == t_VEC;
  bitprec = prec2nbits(prec) + 64*(1 + (k >> 5));
  N = 5 + bitprec/2;
  prec2 = nbits2prec(log? bitprec + acros(evec) * N: bitprec);
  ibin = cgetg(N + 2, t_VEC);
  ibin1= cgetg(N + 2, t_VEC);
  gel(ibin,1) = gel(ibin1,1) = gen_0; /* unused */
  gel(ibin,2) = gel(ibin1,2) = real2n(-1,prec2);
  /* cf get_vbin: shifted by 1 :-( */
  for (n = 2; n <= N; n++)
  {
    gel(ibin, n+1) = divru(mulru(gel(ibin, n), n), 4*n-2);
    gel(ibin1, n+1) = divru(gel(ibin, n+1), n);
  }
  all = log? filltabM(ibin, ibin1, evec, prec2)
           : filltabMs(ibin, ibin1, evec, prec2);
  return gprec_wtrunc(gel(all,1), prec);
}

static GEN
zetamultrec_i(GEN avec, long prec)
{
  pari_sp av = avma;
  if (lg(avec) == 1) return gen_1;
  if (lg(avec) == 2) return szeta(avec[1], prec);
  return gerepilecopy(av, zetamultevec(atoe(avec), prec));
}

GEN
polylogmult(GEN s, GEN zvec, long prec)
{
  pari_sp av = avma;
  GEN avec = zetamultconvert_i(s, 1);

  if (!zvec) return gerepileupto(av, zetamultrec_i(avec, prec));
  switch (typ(zvec))
  {
    case t_INT: case t_FRAC: case t_REAL: case t_COMPLEX:
      zvec = mkvec(zvec); break;
    case t_VEC: case t_COL: break;
    case t_VECSMALL: zvec = zv_to_ZV(zvec); break;
    default: pari_err_TYPE("polylogmult [zvec]", zvec);
  }
  if (lg(zvec) != lg(avec))
    pari_err_TYPE("polylogmult [#avec != #zvec]", mkvec2(avec,zvec));
  return gerepilecopy(av, zetamultevec(aztoe(avec,zvec,prec), prec));
}

GEN
polylogmult_interpolate(GEN s, GEN zvec, GEN t, long prec)
{
  pari_sp av = avma;
  GEN V, avec, A, AZ, Z;
  long i, la, l;

  if (!t) return polylogmult(s, zvec, prec);
  if (!zvec) return zetamult_interpolate(s, t, NULL, prec);
  avec = zetamultconvert_i(s, 1); la = lg(avec);
  AZ = allstar2(avec, zvec);
  A = gel(AZ, 1); l = lg(A);
  Z = gel(AZ, 2); V = zerovec(la-1);
  for (i = 1; i < l; i++)
  {
    pari_sp av2 = avma;
    GEN a = gel(A,i), e = aztoe(a, gel(Z,i), prec);
    long n = lg(a)-1; /* > 0 */
    gel(V,n) = gerepileupto(av2, gadd(gel(V,n), zetamultevec(e, prec)));
  }
  return gerepileupto(av, poleval(vecreverse(V),t));
}

/**************************************************************/
/*                           ALL MZV's                        */
/**************************************************************/

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
    for (j = 1; j <= le; j++)
      if (!w[j+1]) break;
    *pb = b = j;
    for (j = le; j >= 1; j--)
      if (w[j+1]) break;
    *pa = a = le + 1 - j;
    lv = le + 2 - a - b;
    if (lv > 0)
    {
      long v = fd(w, b + 1, le - a + 2), u = v + (1 << (lv-1));
      *pminit = (((1 << b) - 1) << (lv - 1)) + (v/2) + 2;
      *pmfin = (u << (a - 1)) + 2;
      *pmmid = (u >> 1) + 2;
    }
    else
    {
      *pminit = (1 << (b - 1)) + 1;
      *pmfin = (a == 1) ? 2 : (1 << (a - 2)) + 2;
      *pmmid = 1;
    }
  }
}

/* Returns L:
* L[1] contains zeta(emptyset)_{n-1,n-1},
* L[2] contains zeta({0})_{n-1,n-1}=zeta({1})_{n-1,n-1} for n >= 2,
* L[m+2][n] : 1 <= m < 2^{k-2}, 1 <= n <= N + 1
* contains zeta(w)_{n-1,n-1}, w corresponding to m,n
* L[m+2] : 2^{k-2} <= m < 2^{k-1} contains zeta(w), w corresponding to m
(code: w=0y1 iff m=1y). */
static GEN
fillL(long k, long bitprec)
{
  long N = 1 + bitprec/2, prec = nbits2prec(bitprec);
  long k1, j, n, m, mbar = 0, K = 1 << (k - 1), K2 = K/2;
  GEN L, v, p1, p2, r1, pab, S;

  r1 = real_1(prec);
  pab = cgetg(N+1, t_VEC); gel(pab, 1) = gen_0; /* not needed */
  for (n = 2; n <= N; n++) gel(pab, n) = powersr(divru(r1, n), k);
  /* 1/n^a = gmael(pab, n, a + 1) */
  L = cgetg(K + 2, t_VEC);
  gel(L,1) = v = cgetg(N+1, t_VEC);
  gel(v,1) = gen_0; /* unused */
  gel(v,2) = real2n(-1,prec);
  gel(v,3) = invr(utor(6,prec)); /* cf get_vbin: shifted by 1 :-( */
  for (n = 3; n < N; n++) gel(v,n+1) = divru(mulru(gel(v,n), n), 4*n-2);

  gel(L,2) = p1 = cgetg(N+1, t_VEC);
  gel(p1,1) = gen_0; /* unused */
  for (j = 2; j <= N; j++) gel(p1,j) = divru(gel(v,j), j-1);

  for (m = 1; m < K2; m++)
  {
    gel(L, m+2) = p1 = cgetg(N+1, t_VEC);
    for (n = 1; n < N; n++) gel(p1, n) = cgetr(prec);
    gel(p1, n) = gen_0;
  }
  for (m = K2; m < K; m++) gel(L, m+2) = utor(0, prec);
  for (k1 = 2; k1 <= k; k1++)
  { /* Assume length evec < k1 filled */
    /* If evec = 0e_2...e_{k_1-1}1 then m = (1e_2...e_{k_1-1})_2 */
    GEN w = cgetg(k1, t_VECSMALL);
    long M = 1 << (k1 - 2);
    pari_sp av = avma;
    for (m = M; m < 2*M; m++)
    {
      GEN pinit, pfin, pmid;
      long comp, a, b, minit, mfin, mmid, mc = m, ii = 0;
      p1 = gel(L, m + 2);
      for (j = k1 - 1; j >= 2; j--)
      {
        w[j] = mc & 1;
        ii = (1 - w[j]) | (ii<<1);
        mc >>= 1;
      }
      mbar = M + ii;
      comp = mbar - m;
      if (comp < 0) continue;
      p2 = gel(L, mbar + 2);
      findabv(w, &a,&b,&minit,&mmid,&mfin);
      pinit= gel(L, minit);
      pfin = gel(L, mfin);
      pmid = gel(L, mmid);
      for (n = N-1; n > 1; n--, set_avma(av))
      {
        GEN t = mpmul(gel(pinit,n+1), gmael(pab, n, a+1));
        GEN u = mpmul(gel(pfin, n+1), gmael(pab, n, b+1));
        GEN v = mpmul(gel(pmid, n+1), gmael(pab, n, a+b+1));
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
        set_avma(av);
      }
      if (comp > 0 && k1 == k) mpaff(p1, p2);
    }
  }
  return L;
}

/* bit 0 of flag set: full, otherwise only half
 * bit 1 of flag set: all <= k, otherwise only k
 * half: 2^(k-3)+ delta_{k even} * 2^(k/2-2), sum = 2^(k-2)+2^(floor(k/2)-1)-1
 * full: 2^(k-2); sum = 2^(k-1)-1 */
static GEN
zetamultall_i(long k, long flag, long prec)
{
  GEN res, ind, L = fillL(k, prec2nbits(prec) + 32);
  long m, minit, K2 = 1 << (k-2), n = lg(L) - 1;

  minit = (flag & 2L) ? 1 : K2;
  if (flag & 1L)
  {
    res = cgetg(n - minit, t_VEC);
    ind = cgetg(n - minit, t_VECSMALL);
    for (m = minit; m < n - 1; m++)
    {
      gel(res, m - minit + 1) = m < K2 ? gmael(L, m + 2, 1) : gel(L, m + 2);
      ind[m - minit + 1] = m;
    }
  }
  else
  {
    long nres, c = 0;
    if (k == 2) nres = 1;
    else if (flag & 1L)
      nres = (1 << (k - 2)) + (1 << ((k/2) - 1)) - 1;
    else
      nres = (1 << (k - 1));
    res = cgetg(nres + 1, t_VEC);
    ind = cgetg(nres + 1, t_VECSMALL);
    for (m = minit; m < n - 1; m++)
    {
      GEN z = m < K2 ? gmael(L, m + 2, 1) : gel(L, m + 2);
      c++; gel(res, c) = z; ind[c] = m;
    }
    setlg(res, c);
  }
  return mkvec2(res, ind);
}

/* fd(e, 2, lg(e)-2), e = atoe(avec) */
static long
atom(GEN avec)
{
  long i, m, l = lg(avec);
  if (l < 3) return 0;
  m = 1; /* avec[1] != 0 */
  for (i = 2; i < l-1; i++) m = (m << avec[i]) + 1;
  return m << (avec[i]-1);
}
static long
atoind(GEN avec, long flag)
{ return atom(avec) + (flag? (1 << (zv_sum(avec) - 2)): 1); }
/* If flag is set, L has all k1 <= k, otherwise only k */
static GEN
zetamultstar_i(GEN L, GEN avec, long flag)
{
  GEN s = allstar(avec), S = gen_0;
  long i, l = lg(s);
  for (i = 1; i < l; i++) S = gadd(S, gel(L, atoind(gel(s,i), flag)));
  return S;
}

/* bit 0: notstar/star
 * bit 1: half/full (ignored if notstar, always full)
 * bit 2: only k/all <= k
 * bit 3: without/with avec index */
GEN
zetamultall0(long k, long flag, long prec)
{
  pari_sp av = avma;
  GEN Lind, L, res;
  long K, k1, ct, fl = flag >> 1;

  if (k < 1) pari_err_DOMAIN("zetamultall", "k", "<", gen_1, stoi(k));
  if (k >= 64) pari_err_OVERFLOW("zetamultall");
  if (!(flag & 1L))
  { /* not star */
    Lind = zetamultall_i(k, fl, prec);
    res = (flag & 8L)? Lind : gel(Lind, 1);
    return gerepilecopy(av, res);
  }
  /* star */
  fl = (flag >> 1) & 2L; /* 2 if all <= k, else k */
  Lind = gerepilecopy(av, zetamultall_i(k, fl | 1L, prec)); /* full */
  L = gel(Lind, 1);
  K = 1 << (k - 2);
  res = cgetg(fl? 2*K: K+1, t_VEC);
  for (ct = 1, k1 = fl? 2: k; k1 <= k; k1++)
  {
    GEN w = cgetg(k1 + 1, t_VECSMALL);
    long M = 1 << (k1 - 1), m;
    for (m = 1; m <= M; m += 2)
    {
      pari_sp av = avma;
      long j, mc = m;
      for (j = k1; j >= 1; j--) { w[j] = mc & 1; mc >>= 1; }
      gel(res, ct++) = gerepileupto(av, zetamultstar_i(L, etoa(w), fl >> 1));
    }
  }
  if (flag & 8L) res = mkvec2(res, gel(Lind, 2));
  return gerepilecopy(av, res);
}
GEN
zetamultall(long k, long prec) { return zetamultall0(k, 6, prec); }

/* Don Zagier and Danylo Radchenko's routines */
/* accuracy 2^(-b); s << (b/log b)^2, l << b/sqrt(log b) */
static void
zparams(long *s, long *l, long prec)
{
  double D = prec2nbits(prec)*LOG10_2, E = 3*D/2/log(3*D);
  *s = (long)floor(E*E);
  *l = (long)floor(sqrt(*s * log((double)*s)/2.));
}

static GEN
zetamult_zagier_i(GEN avec, long prec)
{
  pari_sp av;
  GEN ze, z = real_0(prec), b;
  long h, r, n, s, l, t = lg(avec) - 1, prec2 = prec + EXTRAPRECWORD;

  zparams(&s, &l, prec);
  ze= cgetg(s + 1, t_VEC);
  b = cgetg(l + 1, t_VEC);
  for (r = 1; r <= s; r++) gel(ze,r) = cgetr(prec2);
  for (r = 1; r <= l; r++) { gel(b,r) = cgetr(prec2); affur(0,gel(b,r)); }
  affur(1, gel(b,1)); av = avma;
  for (r = 1, h = -1; r <= t; r++)
  {
    long m, j = avec[t + 1 - r];
    GEN q;

    h += j - 1; z = gen_0;
    q = invr(itor(powuu(s,h), prec2));
    for (m = 1; m <= l; m++)
    {
      pari_sp av2;
      GEN S = gel(b, m), C;
      q = divru(q, s); av2 = avma;
      C = binomialuu(h + m, m);
      for (n = 1; n < m; n++)
      { /* C = binom(h+m, m-n+1) */
        S = gsub(S, mulir(C, gel(b, n)));
        C = diviuexact(muliu(C, m-n+1), h+n);
      }
      affrr(divru(S, h+m), gel(b,m)); set_avma(av2);
      z = gadd(z, gmul(gel(b, m), q));
    }
    for (m = s; m >= 1; m--)
    {
      GEN z1 = r == 1? ginv(powuu(m,j)): gdiv(gel(ze, m), powuu(m,j));
      z1 = gadd(z, z1);
      affrr(z, gel(ze, m)); z = z1;
    }
    set_avma(av);
  }
  return z;
}

GEN
zetamult_zagier(GEN avec, long prec)
{
  pari_sp av = avma;
  GEN a = vecsmall_reverse(gtovecsmall(avec));
  return gerepilecopy(av, zetamult_zagier_i(a, prec));
}

/* Compute t-mzvs; slower than Zagier's code for t=0 */
static GEN
zetamult_interpolate2_i(GEN avec, GEN t, long prec)
{
  pari_sp av;
  GEN a, b, ze, _1;
  long i, j, n, s, l;

  zparams(&s, &l, prec);
  n = lg(avec) - 1;
  a = zeromatcopy(n + 1, l);
  b = zerovec(l + 1);
  for (i = 1; i <= n; i++)
  {
    long h = avec[n + 1 - i];
    if (i == 1) gel(b, h) = gen_1;
    else
      for (j = l + 1; j >= 1; j--)
      {
        if (j <= h) gel(b, j) = gen_0;
        else gel(b, j) = gadd(gcoeff(a, i, j-h), gmul(t, gel(b, j-h)));
      }
    gcoeff(a, i+1, 1) = gel(b, 2); /* j = 1 */
    for (j = 2; j <= l; j++)
    { /* b[j+1] - \sum_{0 <= u < j-1 binom(j,u) a[i+1,u+1]*/
      pari_sp av = avma;
      GEN S = gel(b, j + 1);
      S = gsub(S, gcoeff(a, i+1, 1)); /* u = 0 */
      if (j > 2) S = gsub(S, gmulgs(gcoeff(a, i+1, 2), j)); /* u = 1 */
      if (j >= 4)
      {
        GEN C = utoipos(j*(j-1) / 2);
        long u, U = (j-1)/2;
        for (u = 2; u <= U; u++)
        { /* C = binom(j,u) */
          S = gsub(S, gmul(C, gadd(gcoeff(a, i+1, u+1), gcoeff(a, i+1, j-u+1))));
          C = diviuexact(muliu(C, j-u), u+1);
        }
        if (!odd(j)) S = gsub(S, gmul(C, gcoeff(a,i+1, j/2+1)));
      }
      gcoeff(a, i+1, j) = gerepileupto(av, gdivgs(S, j));
    }
  }
  _1 = real_1(prec); av = avma;
  ze = cgetg(n+1, t_VEC);
  for (i = 1; i <= n; i++)
  {
    GEN S = gdivgs(gcoeff(a, n+2-i, 1), s);
    for (j = 2; j <= l; j++)
      S = gadd(S, gdiv(gcoeff(a, n+2-i, j), powuu(s,j)));
    gel(ze, i) = S;
  }
  for (i = s; i >= 1; i--)
  {
    GEN b0 = divri(_1, powuu(i, avec[n])), z;
    z = gel(ze,n); gel(ze,n) = gadd(z, b0);
    for (j = n-1; j >= 1; j--)
    {
      b0 = gdiv(gadd(gmul(t, b0), z), powuu(i, avec[j]));
      z = gel(ze,j); gel(ze,j) = gadd(gel(ze,j), b0);
    }
    if (gc_needed(av, 1))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"zetamult: i = %ld", i);
      ze = gerepilecopy(av, ze);
    }
  }
  return gel(ze, 1);
}

GEN
zetamult_interpolate2(GEN avec, GEN t, long prec)
{
  pari_sp av = avma;
  GEN a = vecsmall_reverse(gtovecsmall(avec));
  return gerepilecopy(av, zetamult_interpolate2_i(a, t, prec));
}

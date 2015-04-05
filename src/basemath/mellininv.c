/* Copyright (C) 2015  The PARI group.

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
/*               Computation of inverse Mellin                     */
/*               transforms of gamma products.                     */
/*******************************************************************/

#ifndef M_E
#define M_E 2.7182818284590452354
#endif

static const double MELLININV_CUTOFF  =  11.; /* C */
static const double MELLININV_CUTOFF2 = 121.; /* C*C */

static GEN
MOD2(GEN x) { GEN q = gdivent(x,gen_2); return gsub(x,gmul2n(q,1)); }
static GEN
RgV_MOD2(GEN v)
{
  long i, l;
  GEN w = cgetg_copy(v,&l);
  for (i=1; i<l; i++) gel(w,i) = MOD2(gel(v,i));
  return w;
}

/* poles of the gamma factor */
static GEN
gammapoles(GEN Vga)
{
  long i, m, d = lg(Vga)-1;
  GEN P, V, B = RgV_MOD2(Vga);
  P = gen_indexsort(B, (void*)gcmp, cmp_nodata);
  V = cgetg(d+1, t_VEC);
  for (i = 1, m = 1; i <= d;)
  {
    GEN u = gel(B, P[i]);
    long k;
    for(k = i+1; k <= d; ++k)
      if (!gequal(gel(B, P[k]), u)) break;
    gel(V, m++) = vecpermute(Vga, vecslice(P,i,k-1));
    i = k;
  }
  setlg(V, m); return V;
}

/* coefficient matrix for power series expansion of inverse Mellin around x=0 */
static GEN
coeffall(GEN Vga, GEN mj, GEN lj, long limn, long prec)
{
  long i, j, n, N = lg(lj)-1, d = lg(Vga)-1;
  GEN call = cgetg(N+1, t_MAT);
  for (j=1; j <= N; j++)
  {
    GEN c, m = gel(mj,j), pr = gen_1, t = gen_1;
    long precdl = lj[j]+3;
    for (i=1; i <= d; ++i)
    {
      GEN a = gmul2n(gadd(m, gel(Vga,i)), -1);
      GEN u = deg1pol_shallow(ghalf, a, 0);
      pr = gmul(pr, ggamma(RgX_to_ser(u, precdl), prec));
      t = gmul(t, u);
    }
    c = cgetg(limn+2,t_COL);
    gel(c,1) = pr;
    for (n=1; n <= limn; n++)
      gel(c,n+1) = gdiv(gel(c,n), RgX_translate(t, stoi(-2*n)));
    gel(call,j) = c;
  }
  return call;
}

static GEN
mysercoeff(GEN x, long n)
{
  long N = n - valp(x);
  return (N < 0)? gen_0: gel(x, N+2);
}

/* generalized power series expansion of inverse Mellin around x = 0 */
static GEN
Ksmallinit(GEN Vga, long bitprec)
{
  pari_sp av = avma;
  long d = lg(Vga)-1, N, j, n, limn, prec;
  GEN LA, lj, mj, call, matvec;
  double C2 = MELLININV_CUTOFF2;

  if (!is_matvec_t(typ(Vga))) pari_err_TYPE("Ksmallinit",Vga);
  LA = gammapoles(Vga); N = lg(LA)-1;
  lj = cgetg(N+1, t_VECSMALL);
  for (j = 1; j <= N; ++j) lj[j] = lg(gel(LA,j))-1;
  mj = cgetg(N+1, t_VEC);
  for (j = 1; j <= N; ++j) gel(mj, j) = gsubsg(2,vecmin(gel(LA,j)));

  prec = nbits2prec((long)(1+bitprec*(1+M_PI*d/C2)));
  limn = ceil(2*LOG2*bitprec/(d*rtodbl(mplambertW(dbltor(C2/(M_PI*M_E))))));
  call = coeffall(Vga, mj, lj, limn, prec);
  matvec = cgetg(N+1, t_VEC);
  for (j = 1; j <= N; ++j)
  {
    long k, ljj = lj[j];
    gel(matvec, j) = cgetg(ljj+1, t_COL);
    for (k = 0; k < ljj; ++k)
    {
      GEN L = cgetg(limn+1, t_VEC);
      for (n = 1; n <= limn; ++n)
        gel(L, n) = gtofp(mysercoeff(gcoeff(call, n+1, j), -(k+1)), prec);
      gmael(matvec, j, k+1) = L;
    }
  }
  return gerepilecopy(av, mkvec3(lj, mj, matvec));
}

/* Same for m-th derivatives. */
static GEN
Kderivsmallinit(GEN Vga, long m, long bitprec)
{
  pari_sp av = avma;
  GEN vv, lj, mj, matvec, matpol;
  long N, j, i;
  if (!is_matvec_t(typ(Vga))) pari_err_TYPE("Kderivsmallinit",Vga);
  vv = Ksmallinit(Vga, bitprec);
  lj = gel(vv,1);
  mj = gel(vv,2);
  matvec = gel(vv,3);
  N = lg(lj)-1;
  matpol = cgetg(N + 1, t_VEC);
  for (j = 1; j <= N; ++j)
  {
    long k, ljj = lj[j];
    gel(matpol, j) = cgetg(ljj+1, t_COL);
    for (k = 0; k < ljj; ++k)
    {
      GEN p1 = RgV_to_RgX(gmael(matvec, j, k + 1), 0);
      gmael(matpol, j, k + 1) = RgX_shift(p1, 1);
    }
  }
  for (i = 1; i <= m; ++i)
    for (j = 1; j <= N; ++j)
    {
      long k, ljj = lj[j];
      for (k = 0; k < ljj; ++k)
      {
        GEN p1 = gmael(matpol, j, k+1), p3 = RgX_shift(RgX_deriv(p1), 1);
        GEN p2 = (k < ljj-1) ? gmael(matpol, j, k+2) : gen_0;
        gmael(matpol, j, k+1) = gsub(gmul2n(p3, 1), gadd(p2, gmul(gel(mj, j), p1)));
      }
      gel(mj, j) = gaddgs(gel(mj, j), 1);
    }
  for (j = 1; j <= N; ++j)
  {
    long k, ljj = lj[j];
    for (k = 0; k < ljj; ++k)
    {
      GEN p1 = RgX_shift(gmael(matpol, j, k+1), -1);
      gmael(matvec, j, k+1) = RgX_to_RgC(p1, lgpol(p1));
    }
  }
  return gerepilecopy(av, mkvec3(lj, mj, matvec));
}

/* Evaluate a vector considered as a polynomial using Horner's
   rule. Warning: unstable. */

static GEN
evalvec(GEN vec, long lim, GEN u, long prec)
{
  pari_sp ltop = avma;
  GEN S, ui;
  long n;
  if (!is_matvec_t(typ(vec))) pari_err_TYPE("evalvec",vec);
  lim = minss(lim, lg(vec)-1); S = gen_0;
  if (gcmp(gnorml2(u), gen_1) <= 0)
  {
    for (n = lim; n >= 1; --n)
      S = gmul(u, gadd(gel(vec, n), S));
    return gerepileupto(ltop, S);
  }
  ui = ginv(gtofp(u, prec));
  for (n = 1; n <= lim; ++n)
    S = gmul(ui, gadd(gel(vec, n), S));
  return gerepileupto(ltop, gmul(gpowgs(u, lim + 1), S));
}

/* x^k/k! for 0 <= k <= n. */
static GEN
gpowersdivfact(GEN x, long n)
{
  pari_sp av = avma;
  long j;
  GEN xp = cgetg(n+2, t_VEC);
  gel(xp, 1) = gen_1;
  for (j = 1; j <= n; ++j) gel(xp, j+1) = gdivgs(gmul(x, gel(xp, j)), j);
  return gerepilecopy(av, xp);
}

/* Compute m-th derivative of inverse Mellin at x by generalized
   power series around x = 0. */
static GEN
Kderivsmall(GEN K, GEN x, long bitprec)
{
  pari_sp ltop = avma, btop;
  long prec;
  GEN lj, mj, matvec, Vga = gel(K, 2);
  GEN Lx, Lxp, x2;
  GEN A, S, VS = gel(K, 4);
  long d, N, j, k, mlj, limn, m = itos(gel(K, 3));
  double Ed, xd, Wd, Wd0;
  GEN p1;
  lj = gel(VS, 1); mj = gel(VS, 2); matvec = gel(VS, 3);
  N = lg(lj)-1; d = lg(Vga)-1; A = vecsum(Vga);
  Ed = LOG2*bitprec/d;
  xd = maxdd(M_PI*gtodouble(gabs(x, LOWDEFAULTPREC)), 1E-13);
  if (xd > Ed)
    pari_err_DOMAIN("Kderivsmall (use Kderivlarge)","x",">=",dbltor(Ed),x);
  Wd0 = Ed/(M_E*xd);
  Wd = log(1.+Wd0);
  Wd *= (1.-log(Wd/Wd0))/(1.+Wd);
  Wd *= (1.-log(Wd/Wd0))/(1.+Wd);
  limn = (long) ceil(2*Ed/Wd);
  prec = nbits2prec((long) ceil(bitprec+d*xd/LOG2));
  if (!gequal0(imag_i(x)))
  {
    long j;
    for (j = 1; j <= d; ++j)
      if (typ(gel(Vga, j)) != t_INT)
        pari_err(e_MISC, "Complex argument in inversemellin with nonintegral Vga");
  }
  x = gmul(gtofp(x, prec), mppi(prec));
  x = odd(d) ? gsqrt(gpowgs(x, d), prec) : gpowgs(x, d/2);
  Lx = gneg(glog(x, prec)); x2 = gsqr(x);
  btop = avma;
  mlj = vecsmall_max(lj);
  Lxp = gpowersdivfact(Lx, mlj);
  p1 = gen_0;
  for (j = 1; j <= N; ++j)
  {
    GEN s = real_0(prec);
    long ljj = lj[j];
    for (k = 0; k < ljj; ++k)
      s = gadd(s, gmul(gel(Lxp, k+1), evalvec(gmael(matvec, j, k+1), limn, x2, prec)));
    p1 = gadd(p1, gmul(gpow(x, gneg(gel(mj, j)), prec), s));
    if (gc_needed(btop, 1))
      p1 = gerepilecopy(btop, p1);
  }
  A = gsubsg(m*d, A);
  S = gequal0(A) ? p1 : gmul(gsqrt(gpow(mppi(prec), A, prec), prec), p1);
  return gerepileupto(ltop, gtofp(S, nbits2prec(bitprec)));
}

static void
Kderivlarge_optim(GEN K, GEN t, long bitprec, long *pprec, long *pnlim)
{
  GEN Vga = gel(K,2), VL = gel(K,5), A2 = gel(VL,3);
  long prec, d = lg(Vga)-1;
  double td = gtodouble(gabs(t, LOWDEFAULTPREC));
  double a = BITS_IN_LONG + ceil((gtodouble(A2)*log(td)/2 - M_PI*d*td)/LOG2);
  double E = LOG2*bitprec;
  double CC = d <= 2 ? 81. : 101.; /* heuristic */

  if (a > 0) bitprec += a;
  prec = nbits2prec(bitprec);
  if (prec < LOWDEFAULTPREC) prec = LOWDEFAULTPREC;
  *pprec = prec;

  *pnlim = ceil(E*E / (CC*td));
}

/* Compute m-th derivative of inverse Mellin at t by
   continued fraction of asymptotic expansion. */
static GEN
Kderivlarge(GEN K, GEN t, long bitprec)
{
  pari_sp ltop = avma;
  GEN tdA, P, S, pi, pit, Vga = gel(K,2);
  const long d = lg(Vga)-1;
  GEN M, VL = gel(K,5), Ms = gel(VL,1), cd = gel(VL,2), A2 = gel(VL,3);
  long status, prec, nlim, m = itos(gel(K, 3));

  Kderivlarge_optim(K, t, bitprec, &prec, &nlim);
  t = gtofp(t, prec);
  if (typ(A2) == t_INT && !mpodd(A2))
    tdA = gpowgs(t, itos(A2)/2);
  else
    tdA = gsqrt(gpow(t, A2, prec), prec);
  tdA = gmul(tdA, cd);

  pi = mppi(prec);
  pit = gmul(pi, t);
  P = gmul(tdA, gexp(gmulsg(-d, pit), prec));
  if (m) P = gmul(P, gpowgs(mulsr(-2, pi), m));
  M = gel(Ms,1);
  status = itos(gel(Ms,2));
  if (status == 2)
    S = poleval(RgV_to_RgX(M, 0), ginv(pit));
  else
  {
    S = contfraceval(M, ginv(pit), nlim/2);
    if (status == 1) S = gmul(S, gsubsg(1, ginv(gmul(pit, pi))));
  }
  return gerepileupto(ltop, gmul(P, S));
}

/* Dokchitser's coefficients used for asymptotic expansion of inverse Mellin
 * 2 <= p <= min(n+1, d) */
static GEN
fun_vp(long p, long n, long d, GEN SM, GEN vsinh)
{
  pari_sp ltop = avma;
  long m, j, k;
  GEN s = gen_0;
  for (m = 0; m <= p; ++m)
  {
    GEN pr = gen_1, s2 = gen_0, sh = gel(vsinh, d-p+1);/* (sh(x)/x)^(d-p) */
    long pm = p-m;
    for (j = m; j < p; ++j) pr = muliu(pr, d-j);
    for (k = 0; k <= pm; k+=2)
    {
      GEN e = gdiv(powuu(2*n-p+1, pm-k), mpfact(pm-k));
      s2 = gadd(s2, gmul(e, RgX_coeff(sh, k)));
    }
    s = gadd(s, gmul(gmul(gel(SM, m+1), pr), s2));
    if (gc_needed(ltop, 1)) s = gerepilecopy(ltop, s);
  }
  return gerepileupto(ltop, gmul(gdivsg(-d, powuu(2*d, p)), s));
}

/* Asymptotic expansion of inverse Mellin, to length nlimmax. Set status = 0
 * (regular), 1 (one Hankel determinant vanishes => contfracinit will fail)
 * or 2 (same as 1, but asymptotic expansion is finite!)
 *
 * If status = 2, the asymptotic expansion is finite so return only
 * the necessary number of terms nlim <= nlimmax + d. */
static GEN
Klargeinit0(GEN Vga, long nlimmax, long *status)
{
  const long prec = LOWDEFAULTPREC;
  const long d = lg(Vga)-1;
  long k, n, m, cnt;
  GEN pol, SM, nS1, se, vsinh, M, dk;

  if (d==1 || (d==2 && gequal1(gabs(gsub(gel(Vga,1), gel(Vga,2)), prec))))
  { /* shortcut */
    *status = 2; return mkvec(gen_1);
  }
  /* d >= 2 */
  *status = 0;
  pol = roots_to_pol(gneg(Vga), 0); /* deg(pol) = d */
  nS1 = gpowers(gneg(RgX_coeff(pol, d-1)), d);
  dk = gpowers(utoi(d), d-1);
  SM = cgetg(d+3, t_VEC);
  for (m = 0; m <= d; ++m)
  {
    pari_sp btop = avma;
    GEN s = gmul(gdivgs(gel(nS1, m+1), d), binomialuu(d, m));
    for (k = 1; k <= m; ++k)
    {
      GEN e = gmul(gel(nS1, m-k+1), gel(dk, k));
      s = gadd(s, gmul(gmul(e, binomialuu(d-k, m-k)), RgX_coeff(pol, d-k)));
    }
    gel(SM, m+1) = gerepileupto(btop, s);
  }
  se = gdiv(gsinh(RgX_to_ser(pol_x(0), d+2), prec), pol_x(0));
  vsinh = gpowers(se, d);
  M = vectrunc_init(nlimmax + d);
  vectrunc_append(M, gen_1);
  for (n=2, cnt=0; (n <= nlimmax) || cnt; ++n)
  {
    pari_sp btop = avma;
    long p, ld = minss(d, n);
    GEN s = gen_0;
    for (p = 2; p <= ld; ++p)
      s = gadd(s, gmul(fun_vp(p, n-1, d, SM, vsinh), gel(M, n+1-p)));
    s = gerepileupto(btop, gdivgs(s, n-1));
    vectrunc_append(M, s);
    if (!isintzero(s))
    {
      if (n >= nlimmax) break;
      cnt = 0;
    }
    else
    {
      cnt++; *status = 1;
      if (cnt >= d-1) { *status = 2; setlg(M, lg(M) - (d-1)); break; }
    }
  }
  return M;
}

/* remove trailing zeros from vector. */
static void
stripzeros(GEN M)
{
  long i;
  for(i = lg(M)-1; i >= 1; --i)
    if (!gequal0(gel(M, i))) break;
  setlg(M, i+1);
}

/* Asymptotic expansion of the m-th derivative of inverse Mellin, to length
 * nlimmax. If status = 2, the asymptotic expansion is finite so return only
 * the necessary number of terms nlim <= nlimmax + d. */
static GEN
gammamellininvasymp_i(GEN Vga, long nlimmax, long m, long *status)
{
  pari_sp ltop = avma;
  GEN M, A, Aadd;
  long d, i, nlim, n;

  M = Klargeinit0(Vga, nlimmax, status);
  if (!m) return gerepilecopy(ltop, M);
  d = lg(Vga)-1;
  /* half the exponent of t in asymptotic expansion. */
  A = gdivgs(gaddsg(1-d, vecsum(Vga)), 2*d);
  if (*status == 2) M = shallowconcat(M, zerovec(m));
  nlim = lg(M)-1;
  Aadd = gdivgs(stoi(2-d), 2*d); /* (1/d) - (1/2) */
  for (i = 1; i <= m; i++, A = gadd(A,Aadd))
    for (n = nlim-1; n >= 1; --n)
      gel(M, n+1) = gsub(gel(M, n+1),
                         gmul(gel(M, n), gsub(A, gdivgs(stoi(n-1), d))));
  stripzeros(M);
  return gerepilecopy(ltop, M);
}
GEN
gammamellininvasymp(GEN Vga, long nlimmax, long m)
{ long status; return gammamellininvasymp_i(Vga, nlimmax, m, &status); }

/* Does the continued fraction of the asymptotic expansion M at oo of inverse
 * Mellin transform associated to Vga have zero Hankel determinants ? */
static long
ishankelspec(GEN Vga, GEN M)
{
  long status, i, d = lg(Vga)-1;

  if (d == 5 || d == 7)
  { /* known bad cases: a x 5 and a x 7 */
    GEN v1 = gel(Vga, 1);
    for (i = 2; i <= d; ++i)
      if (!gequal(gel(Vga,i), v1)) break;
    if (i > d) return 1;
  }
  status = 0;
  /* Heuristic: if 6 first terms in contfracinit don't fail, assume it's OK */
  pari_CATCH(e_INV) { status = 1; }
  pari_TRY { contfracinit(M, 6); }
  pari_ENDCATCH; return status;
}

/* Initialize data for computing m-th derivative of inverse Mellin */
GEN
gammamellininvinit_bitprec(GEN Vga, long m, long bitprec)
{
  pari_sp ltop = avma;
  GEN A2, M, VS, VL, cd;
  long d = lg(Vga)-1, status;
  double tmax = LOG2*bitprec / MELLININV_CUTOFF2;
  const double C2 = MELLININV_CUTOFF2, CC = d <= 2 ? 81. : 101.;
  const long nlimmax = ceil(bitprec*C2*LOG2/CC);

  if (!is_vec_t(typ(Vga))) pari_err_TYPE("gammamellininvinit",Vga);
  A2 = gaddsg(m*(2-d) + 1-d, vecsum(Vga));
  cd = (d <= 2)? gen_2: gsqrt(gdivgs(int2n(d+1), d), nbits2prec(bitprec));
  /* if in Klarge, we have |t| > tmax = LOG2*D/C2, thus nlim < LOG2*D*C2/CC. */
  M = gammamellininvasymp_i(Vga, nlimmax, m, &status);
  if (status == 2)
  {
    tmax = -1.; /* only use Klarge */
    VS = gen_0;
  }
  else
  {
    long prec = nbits2prec((4*bitprec)/3);
    VS = Kderivsmallinit(Vga, m, bitprec);
    if (status == 0 && ishankelspec(Vga, M)) status = 1;
    if (status == 1)
    { /* a Hankel determinant vanishes => contfracinit is undefined.
         So compute K(t) / (1 - 1/(pi^2*t)) instead of K(t)*/
      GEN t = ginv(mppi(prec));
      long i;
      for (i = 2; i < lg(M); ++i)
        gel(M, i) = gadd(gel(M, i), gmul(gel(M, i-1), t));
    }
    else
      M = RgC_gtofp(M, prec); /* convert from rationals to t_REAL: faster */
    M = contfracinit(M, lg(M)-2);
  }
  VL = mkvec3(mkvec2(M, stoi(status)), cd, A2);
  return gerepilecopy(ltop, mkvec5(dbltor(tmax), Vga, stoi(m), VS, VL));
}
GEN
gammamellininvinit(GEN Vga, long m, long prec)
{ return gammamellininvinit_bitprec(Vga, m, prec2nbits(prec)); }

/* Compute m-th derivative of inverse Mellin at x = s^(d/2) using
 * initialization data. Use Taylor expansion at 0 for |x| < tmax, and
 * asymptotic expansion at oo otherwise. WARNING: assume that accuracy
 * has been increased according to tmax by the CALLING program. */
GEN
gammamellininvrt_bitprec(GEN K, GEN x, long bitprec)
{
  GEN tmax = gel(K,1);
  if (gcmp(gabs(x, LOWDEFAULTPREC), tmax) < 0)
    return Kderivsmall(K, x, bitprec);
  else
    return Kderivlarge(K, x, bitprec);
}
GEN
gammamellininvrt(GEN K, GEN x, long prec)
{ return gammamellininvrt_bitprec(K, x, prec2nbits(prec)); }

/* Compute inverse Mellin at s. K from gammamellininv OR a Vga, in which
 * case the initialization data is computed. */
GEN
gammamellininv_bitprec(GEN K, GEN s, long m, long bitprec)
{
  pari_sp av = avma;
  GEN s2d;
  long d;
  if (!is_vec_t(typ(K))) pari_err_TYPE("gammamellininvinit",K);
  if (lg(K) != 6 || !is_vec_t(typ(gel(K,2))))
    K = gammamellininvinit_bitprec(K, m, bitprec);
  d = lg(gel(K,2))-1;
  s2d = gpow(s, gdivgs(gen_2, d), nbits2prec(bitprec));
  return gerepileupto(av, gammamellininvrt_bitprec(K, s2d, bitprec));
}
GEN
gammamellininv(GEN Vga, GEN s, long m, long prec)
{ return gammamellininv_bitprec(Vga, s, m, prec2nbits(prec)); }

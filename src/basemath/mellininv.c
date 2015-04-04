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

/* Poles of the gamma factor. */

static GEN
gammapoles(GEN Vga)
{
  long i, m, d = lg(Vga)-1;
  GEN P, V;
  GEN B = cgetg(d+1,t_VEC);
  for (i = 1; i <= d; ++i)
    gel(B, i) = gel(gdiventres(gel(Vga, i), gen_2), 2);
  P = gen_indexsort(B, (void*)gcmp, cmp_nodata);
  V = cgetg(d+1, t_VEC);
  for (i = 1, m = 1; i <= d;)
  {
    long n, k, j;
    GEN Vm;
    GEN u = gel(B, P[i]);
    for(k = i + 1; k <= d; ++k)
      if (gcmp(gel(B, P[k]), u))
        break;
    n = k - i;
    if (n == 0) break;
    Vm = cgetg(n+1, t_VEC);
    for(j = 1; j <= n; ++j)
      gel(Vm, j) = gel(Vga, P[j+i-1]);
    gel(V, m++) = Vm;
    i = k;
  }
  setlg(V, m);
  return V;
}

/* Compute coefficient matrix for generalized power series expansion
   of inverse Mellin around x = 0. */

static GEN
coeffall(GEN Vga, GEN mj, GEN lj, long limn, long prec)
{
  long i, j, n, N = lg(lj)-1, d = lg(Vga)-1;
  GEN call, p5;
  GEN pols = cgetg(N+1, t_MAT);
  for (j = 1; j <= N; ++j)
  {
    GEN polj = cgetg(d+1, t_COL);
    for (i = 1; i <= d; ++i)
      gel(polj, i) = deg1pol(ghalf, gdivgs(gadd(gel(mj, j), gel(Vga, i)), 2), 0);
    gel(pols, j) = polj;
  }
  call = cgetg(limn+2, t_MAT);
  p5 = cgetg(N+1, t_COL);
  for (j = 1; j <= N; ++j)
  {
    pari_sp btop = avma;
    GEN pr = gen_1;
    for (i = 1; i <= d; ++i)
      pr = gmul(pr, ggamma(RgX_to_ser(gmael(pols, j, i), lj[j]+3), prec));
    gel(p5, j) = gerepileupto(btop, pr);
  }
  gel(call, 1) = p5;
  for (n = 1; n <= limn; ++n)
  {
    GEN p16 = cgetg(N+1, t_COL);
    for (j = 1; j <= N; ++j)
    {
      pari_sp btop = avma;
      GEN pr = cgetg(d+1, t_COL);
      for (i = 1; i <= d; ++i)
        gel(pr, i) = gsubgs(gmael(pols, j, i), n);
      pr = divide_conquer_prod(pr, gmul);
      gel(p16, j) = gerepileupto(btop, gdiv(gcoeff(call, j, n), pr));
    }
    gel(call, n + 1) = p16;
  }
  return call;
}

static GEN
mysercoeff(GEN x, long n)
{
  long N = n - valp(x);
  return (N < 0)? gen_0: gel(x, N+2);
}

/* Initialization for generalized power series expansion of
   inverse Mellin around x = 0. */

static GEN
Ksmallinit(GEN Vga, long bitprec)
{
  pari_sp av = avma;
  long prec;
  long d = lg(Vga)-1, N, j, n;
  GEN LA, lj, mj;
  long limn;
  GEN call, matvec;
  double C2 = MELLININV_CUTOFF2;

  if (!is_matvec_t(typ(Vga))) pari_err_TYPE("Ksmallinit",Vga);
  LA = gammapoles(Vga); N = lg(LA)-1;
  lj = cgetg(N+1, t_VECSMALL);
  for (j = 1; j <= N; ++j) lj[j] = lg(gel(LA, j))-1;
  mj = cgetg(N+1, t_VEC);
  for (j = 1; j <= N; ++j) gel(mj, j) = gsubsg(2,vecmin(gel(LA, j)));
  prec = nbits2prec((long)(1+bitprec*(1+M_PI*d/C2)));
  limn = ceil(2*LOG2*bitprec/(d*rtodbl(mplambertW(dbltor(C2/(M_PI*M_E))))));
  call = coeffall(Vga, mj, lj, limn, prec);
  matvec = cgetg(N + 1, t_VEC);
  for (j = 1; j <= N; ++j)
  {
    long k, ljj = lj[j];
    gel(matvec, j) = cgetg(ljj+1, t_COL);
    for (k = 0; k < ljj; ++k)
    {
      GEN L = cgetg(limn+1, t_VEC);
      for (n = 1; n <= limn; ++n)
        gel(L, n) = gtofp(mysercoeff(gcoeff(call, j, n + 1), -(k + 1)), prec);
      gmael(matvec, j, k + 1) = L;
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
  lj = gel(vv, 1); mj = gel(vv, 2); matvec = gel(vv, 3);
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
        GEN p1 = gmael(matpol, j, k + 1), p3 = RgX_shift(RgX_deriv(p1), 1);
        GEN p2 = (k < ljj - 1) ? gmael(matpol, j, k + 2) : gen_0;
        gmael(matpol, j, k + 1) = gsub(gmul2n(p3, 1), gadd(p2, gmul(gel(mj, j), p1)));
      }
      gel(mj, j) = gaddgs(gel(mj, j), 1);
    }
  for (j = 1; j <= N; ++j)
  {
    long k, ljj = lj[j];
    for (k = 0; k < ljj; ++k)
    {
      GEN p1 = RgX_shift(gmael(matpol, j, k + 1), -1);
      gmael(matvec, j, k + 1) = RgX_to_RgC(p1, lgpol(p1));
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
  for (j = 1; j <= n; ++j)
    gel(xp, j+1) = gdivgs(gmul(x, gel(xp, j)), j);
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
  GEN A, S, VVS = gel(K, 4);
  long d, N, j, k, mlj, limn, m = itos(gel(K, 3));
  double Ed, xd, Wd, Wd0;
  GEN p1;
  lj = gel(VVS, 1); mj = gel(VVS, 2); matvec = gel(VVS, 3);
  N = lg(lj)-1; d = lg(Vga)-1; A = vecsum(Vga);
  Ed = LOG2*bitprec/d;
  xd = maxdd(M_PI*gtodouble(gabs(x, LOWDEFAULTPREC)), 1E-13);
  if (xd > Ed)
    pari_err_DOMAIN("Kderivsmall (use Kderivlarge)","x",">=",dbltor(Ed),x);
  Wd0 = Ed/(M_E*xd); Wd=log(1.+Wd0);
  Wd*=(1.-log(Wd/Wd0))/(1.+Wd); Wd*=(1.-log(Wd/Wd0))/(1.+Wd);
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
      s = gadd(s, gmul(gel(Lxp, k+1), evalvec(gmael(matvec, j, k + 1), limn, x2, prec)));
    p1 = gadd(p1, gmul(gpow(x, gneg(gel(mj, j)), prec), s));
    if (gc_needed(btop, 1))
      p1 = gerepilecopy(btop, p1);
  }
  A = gsubsg(m*d, A);
  S = gequal0(A) ? p1 : gmul(gsqrt(gpow(mppi(prec), A, prec), prec), p1);
  return gerepileupto(ltop, gtofp(S, nbits2prec(bitprec)));
}

/* Compute some coefficients necessary for computing
   asymptotic expansion of inverse Mellin. */

static GEN
fun_vp(long p, long n, long d, GEN SM, GEN vsinh)
{
  pari_sp ltop = avma;
  long m, j, k;
  GEN s = gen_0;
  for (m = 0; m <= p; ++m)
  {
    long pm2 = (p - m)/2;
    GEN pr = gen_1, s2 = gen_0;
    for (j = m; j < p; ++j)
      pr = gmulgs(pr, d - j);
    for (k = 0; k <= pm2; ++k)
    {
      GEN e = gdiv(gpowgs(stoi(2*n - p + 1), p - m - 2*k), mpfact(p - m - 2*k));
      s2 = gadd(s2, gmul(e, RgX_coeff(gel(vsinh, d - p + 1), 2*k)));
    }
    s = gadd(s, gmul(gmul(gel(SM, m + 1), pr), s2));
    if (gc_needed(ltop, 1))
      s = gerepilecopy(ltop, s);
  }
  return gerepileupto(ltop, gmul(gdivsg(-d, powuu(2*d, p)), s));
}

/* Reasonable test if Vga with zero Hankel determinants.
Return 1 if some Hankel vanishes, 2 if some coeff vanishes, 0
if no vanishing Hankel found. */

static GEN Klargeinit0(GEN Vga, long nlimmax, long *status);

static long
testhankelspec(GEN Vga)
{
  pari_sp av = avma;
  GEN M, e, q;
  long j, k, status;
  M = Klargeinit0(Vga, 7, &status);
  /* Here status = 0 */
  e = zerovec(6); q = cgetg(7, t_VEC);
  for (k = 1; k <= 6; ++k)
  {
    if (gequal0(gel(M, k))) {avma = av; return 2;}
    gel(q, k) = gdiv(gel(M, k+1), gel(M, k));
  }
  for (j = 1; j <= 3; ++j)
  {
    long l = 6 - 2*j;
    for (k = 0; k <= l; ++k)
      gel(e, k+1) = gsub(gadd(gel(e, k+2), gel(q, k+2)), gel(q, k+1));
    for (k = 0; k < l; ++k)
    {
      if (gequal0(gel(e, k+1))) {avma = av; return 1;}
      gel(q, k+1) = gdiv(gmul(gel(q, k+2), gel(e, k+2)), gel(e, k+1));
    }
  }
  avma = av; return 0;
}

/* Include here all the Vga you know with zero Hankel determinants.
   For the moment the only special cases encountered are Vga = [a,a,a,a,a].
   and [a,a,a,a,a,a,a]. Add more if more are found. */

static long
ishankelspec(GEN Vga)
{
  long i, d = lg(Vga)-1;
  GEN v1;
  if (d == 5 || d == 7)
  {
    v1 = gel(Vga, 1);
    for (i = 2; i <= d; ++i)
      if (!gequal(gel(Vga, i), v1)) break;
    if (i == d+1) return 1;
  }
  return testhankelspec(Vga) != 0;
}

/* Exponent of t in asymptotic expansion. */

static GEN
gammavec_expo(GEN Vga)
{
  long d = lg(Vga)-1;
  return gdivgs(gaddsg(1 - d, vecsum(Vga)), d);
}

/* Returns the asymptotic expansion of inverse Mellin, to
   length nlimmax. In the special cases d = 1 or
   d = 2 and Vga[2] - Vga[1] is odd, the asymptotic expansion
   is finite so return only the necessary number of terms. */

static GEN
Klargeinit0(GEN Vga, long nlimmax, long *status)
{
  long prec = LOWDEFAULTPREC;
  long k, n, m, cnt = 0;
  GEN pol, SM, nS1, se, vsinh, M, dk;
  long d = lg(Vga)-1;
  *status = 0;
  if (d == 1 || (d == 2 && gequal1(gabs(gsub(gel(Vga, 1), gel(Vga, 2)), prec))))
  {
    *status = 2; return mkvec(gen_1);
  }
  pol = roots_to_pol(gneg(Vga), 0);
  nS1 = gpowers(gneg(RgX_coeff(pol, d - 1)), d);
  dk = gpowers(utoi(d), d - 1);
  SM = cgetg(d+3, t_VEC);
  for (m = 0; m <= d; ++m)
  {
    pari_sp btop = avma;
    GEN s = gmul(gdivgs(gel(nS1, m + 1), d), binomialuu(d, m));
    for (k = 1; k <= m; ++k)
    {
      GEN e = gmul(gel(nS1, m - k + 1), gel(dk, k));
      s = gadd(s, gmul(gmul(e, binomialuu(d - k, m - k)), RgX_coeff(pol, d - k)));
    }
    gel(SM, m + 1) = gerepileupto(btop, s);
  }
  se = gdiv(gsinh(gadd(pol_x(0), zeroser(0, d + 2)), prec), pol_x(0));
  vsinh = gpowers(se, d);
  M = vectrunc_init(nlimmax + d);
  vectrunc_append(M, gen_1);
  for (n = 2; (n <= nlimmax) || cnt; ++n)
  {
    pari_sp btop = avma;
    long p, ld = minss(d, n);
    GEN s = gen_0;
    for (p = 2; p <= ld; ++p)
      s = gadd(s, gmul(fun_vp(p, n - 1, d, SM, vsinh), gel(M, n + 1 - p)));
    s = gerepileupto(btop, gdivgs(s, n - 1));
    vectrunc_append(M, s);
    if (!isintzero(s))
    {
      if (n >= nlimmax) break;
      cnt = 0;
    }
    else
    {
      cnt++; *status = 1;
      if (cnt >= d - 1) { *status = 2; setlg(M, lg(M) - (d - 1)); break; }
    }
  }
  return M;
}

/* Remove trailing zeros from vector. */

static GEN
remzeros(GEN M)
{
  pari_sp ltop = avma;
  GEN M0;
  long lm, i, j;
  lm = lg(M);
  for(i = lm - 1; i >= 1; --i)
    if (!gequal0(gel(M, i))) break;
  M0 = cgetg(i + 1, t_VEC);
  for (j = 1; j <= i; ++j) gel(M0, j) = gel(M, j);
  return gerepilecopy(ltop, M0);
}

/* Returns the asymptotic expansion of the m-th derivative of
   inverse Mellin, to length nlimmax. In the special cases d = 1 or
   d = 2 and Vga[2] - Vga[1] is odd, the asymptotic expansion
   is finite so return only the necessary number of terms. */

static GEN
gammamellininvasymp_i(GEN Vga, long nlimmax, long m, long *status)
{
  pari_sp ltop = avma;
  GEN M, A, Aadd;
  long d, i, nlim, n;
  M = Klargeinit0(Vga, nlimmax, status);
  if (m == 0) return gerepilecopy(ltop, M);
  d = lg(Vga)-1; A = gammavec_expo(Vga);
  if (*status == 2)
  {
    long lM = lg(M)-1;
    M = vec_lengthen(M, lM + m);
    for (i = 1; i <= m; ++i) gel(M, lM+i) = gen_0;
  }
  nlim = lg(M)-1; Aadd = gsubgs(gdivgs(gen_2, d), 1);
  for (i = 1; i <= m; ++i)
  {
    for (n = nlim - 1; n >= 1; --n)
      gel(M, n + 1) = gsub(gel(M, n + 1), gmul(gel(M, n),
                           gsub(gdivgs(A, 2), gdivgs(stoi(n - 1), d))));
    A = gadd(A, Aadd);
  }
  return gerepilecopy(ltop, remzeros(M));
}

GEN
gammamellininvasymp(GEN Vga, long nlimmax, long m)
{
  long status;
  return gammamellininvasymp_i(Vga, nlimmax, m, &status);
}

/* Compute m-th derivative of inverse Mellin at t by
   continued fraction of asymptotic expansion. */

static GEN
Kderivlarge(GEN K, GEN t, long bitprec)
{
  pari_sp ltop = avma;
  long d;
  GEN tdA, A2, P, P0, S, pi, pit, cd, Vga = gel(K, 2);
  GEN VVL = gel(K, 5), M;
  double E, CC, tdd;
  long nlim, m = itos(gel(K, 3)), status;
  long prec;
  d = lg(Vga)-1; A2 = gel(VVL, 3);
  tdd = gtodouble(gabs(t, LOWDEFAULTPREC));
  prec = nbits2prec(maxss(LOWDEFAULTPREC,
               ceil(bitprec+BITS_IN_LONG-(M_PI*d*tdd-gtodouble(A2)*log(tdd)/2)/LOG2)));
  t = gtofp(t, prec);
  cd = gel(VVL, 2);
  if (typ(A2) == t_INT && !mpodd(A2))
    tdA = gmul(gpowgs(t, itos(A2)/2), cd);
  else
    tdA = gmul(gsqrt(gpow(t, A2, prec), prec), cd);
  pi = mppi(prec); pit = gmul(pi, t);
  P0 = gmul(tdA, gexp(gmulsg(-d, pit), prec));
  P = m ? gmul(gpowgs(gmulsg(-2, pi), m), P0) : P0;
  M = gmael(VVL, 1, 1); status = itos(gmael(VVL, 1, 2));
  if (status == 2)
  {
    GEN z = poleval(RgV_to_RgX(M, 0), ginv(pit));
    return gerepileupto(ltop, gmul(P, z));
  }
  E = LOG2*bitprec;
  CC = d <= 2 ? 81. : 101.;
  nlim = ceil(E*E/(CC*tdd));
  S = contfraceval(M, ginv(pit), nlim/2);
  if (status == 1) S = gmul(S, gsubsg(1, ginv(gmul(pit, pi))));
  return gerepileupto(ltop, gmul(P, S));
}

/* Compute inverse Mellin at x using all precomputed data.
tmax is the largest value of $t$ for which we use Ksmall, In
principle, it is always set by the calling program.
WARNING: it is assumed that the accuracy has been increased according
to tmax by the CALLING program. */

/* When K(t) is an exponential, give the formula (if K(t)
is a Bessel function it is better to use the present program
because we only want absolute accuracy). Otherwise use the
power series for $t<tmax$, the continued fraction to at most nlimmax
terms if $t>tmax$, where $tmax$ is computed by the program. The output
is a COLUMN vector. */
/* Warning: we compute here K(x^(d/2)) instead of K(x) because
this is all that is needed in lfuninit. */

/* Initialize all necessary data for computing m-th
   derivative of inverse Mellin. */

GEN
gammamellininvinit_bitprec(GEN Vga, long m, long bitprec)
{
  pari_sp ltop = avma;
  GEN A2, M, VVS, VVL, cd;
  long nlimmax, d = lg(Vga)-1, status;
  double tmax = LOG2*bitprec / MELLININV_CUTOFF2;
  double C2 = MELLININV_CUTOFF2, CC = d <= 2 ? 81. : 101.;
  if (!is_vec_t(typ(Vga))) pari_err_TYPE("gammamellininvinit",Vga);
  A2 = gaddsg(m*(2 - d) + 1 - d, vecsum(Vga));
  cd = d <= 2 ? gen_2 : gsqrt(gdivgs(int2n(d + 1), d), nbits2prec(bitprec));
  nlimmax = ceil(bitprec*C2*LOG2/CC);
  /* Since we are in Klarge, we have tdd > tmax = LOG2*D/C2.
     Thus, nlim < LOG2*D*C2/CC. */
  M = gammamellininvasymp_i(Vga, nlimmax, m, &status);
  if (status == 2)
  {
    tmax = -1.; /* Only use Klarge */
    VVS = gen_0;
  }
  else
  {
    long prec = nbits2prec((4*bitprec)/3);
    VVS = Kderivsmallinit(Vga, m, bitprec);
    if (status == 0 && ishankelspec(Vga)) status = 1;
    if (status == 1)
    {
      GEN eps = ginv(mppi(prec));
      long i;
      for (i = 2; i < lg(M); ++i)
        gel(M, i) = gadd(gel(M, i), gmul(gel(M, i - 1), eps));
    }
    M = contfracinit(RgC_gtofp(M, prec), lg(M) - 2);
  }
  VVL = mkvec3(mkvec2(M, stoi(status)), cd, A2);
  return gerepilecopy(ltop, mkvec5(dbltor(tmax), Vga, stoi(m), VVS, VVL));
}

GEN
gammamellininvinit(GEN Vga, long m, long prec)
{
  return gammamellininvinit_bitprec(Vga, m, prec2nbits(prec));
}

/* Compute m-th derivative of inverse Mellin at x = s^(d/2)
   using initialization data, which contains m = gel(K, 3). */

GEN
gammamellininvrt_bitprec(GEN K, GEN x, long bitprec)
{
  GEN tmax = gel(K, 1);
  if (gcmp(gabs(x, LOWDEFAULTPREC), tmax) < 0)
    return Kderivsmall(K, x, bitprec);
  else
    return Kderivlarge(K, x, bitprec);
}

GEN
gammamellininvrt(GEN K, GEN x, long prec)
{
  return gammamellininvrt_bitprec(K, x, prec2nbits(prec));
}

/* Compute inverse Mellin at s. K can either be a Vga, in which
   case the initialization data is computed, or an initialization
   data itself. In application to lfuninit, this is not needed
   since only inverse Mellin at s^(d/2) is useful. */

/* Compute m-th derivative of inverse Mellin at s. K can either be a Vga,
   in which case the initialization data is computed, or an initialization
   data itself. */

GEN
gammamellininv_bitprec(GEN K, GEN s, long m, long bitprec)
{
  pari_sp ltop = avma;
  GEN s2d, p1;
  if (!is_vec_t(typ(K)))
    pari_err_TYPE("gammamellininvinit",K);
  if (!(lg(K) == 6 && is_vec_t(typ(gel(K,2)))))
    K = gammamellininvinit_bitprec(K, m, bitprec);
  s2d = gpow(s, gdivgs(gen_2, lg(gel(K, 2))-1), nbits2prec(bitprec));
  p1 = gammamellininvrt_bitprec(K, s2d, bitprec);
  return gerepileupto(ltop, p1);
}

GEN
gammamellininv(GEN Vga, GEN s, long m, long prec)
{
  return gammamellininv_bitprec(Vga, s, m, prec2nbits(prec));
}

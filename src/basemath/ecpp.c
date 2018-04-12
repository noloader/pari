/* Copyright (C) 2014 The PARI group.

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

#define dbg_mode() if (DEBUGLEVEL >= 2)

#define ANSI_COLOR_RED     "\x1b[31m"
#define ANSI_COLOR_GREEN   "\x1b[32m"
#define ANSI_COLOR_YELLOW  "\x1b[33m"
#define ANSI_COLOR_BLUE    "\x1b[34m"
#define ANSI_COLOR_MAGENTA "\x1b[35m"
#define ANSI_COLOR_CYAN    "\x1b[36m"
#define ANSI_COLOR_WHITE   "\x1b[37m"

#define ANSI_COLOR_BRIGHT_RED     "\x1b[31;1m"
#define ANSI_COLOR_BRIGHT_GREEN   "\x1b[32;1m"
#define ANSI_COLOR_BRIGHT_YELLOW  "\x1b[33;1m"
#define ANSI_COLOR_BRIGHT_BLUE    "\x1b[34;1m"
#define ANSI_COLOR_BRIGHT_MAGENTA "\x1b[35;1m"
#define ANSI_COLOR_BRIGHT_CYAN    "\x1b[36;1m"
#define ANSI_COLOR_BRIGHT_WHITE   "\x1b[37;1m"

#define ANSI_COLOR_RESET   "\x1b[0m"

/* THINGS THAT DON'T BELONG */

/* Assume that x is a vector such that
   f(x) = 1 for x <= k
   f(x) = 0 otherwise.
   Return k.
*/
static long
zv_binsearch0(void *E, long (*f)(void* E, GEN x), GEN x)
{
  long lo = 1;
  long hi = lg(x)-1;
  while (lo < hi) {
    long mi = lo + (hi - lo)/2 + 1;
    if (f(E,gel(x,mi))) lo = mi;
    else hi = mi - 1;
  }
  if (f(E,gel(x,lo))) return lo;
  return 0;
}

INLINE long
timer_record(GEN* X0, const char* Xx, pari_timer* ti)
{
  long t = 0;
  dbg_mode() {
    long i, j;
    t = timer_delay(ti);
    if (!X0) return t;
    i = Xx[0]-'A'+1;
    j = Xx[1]-'1'+1;
    umael3(*X0, 1, i, j) += t;
    umael3(*X0, 2, i, j) ++;
  }
  return t;
}

INLINE long
FpJ_is_inf(GEN P) { return signe(gel(P, 3)) == 0; }

/*****************************************************************/

/* Assuming D < 0,
   these return the number of units in Q(sqrt(D)). */
INLINE long
D_get_wD(long D)
{
  if (D == -4) return 4;
  if (D == -3) return 6;
  return 2;
}

/* Dinfo contains information related to the discirminant
      D: the discriminant (D < 0)
      h: the class number associated to D
     bi: the "best invariant" for computing polclass(D, bi)
         In particular, we choose this invariant to be the one
           in which D is compatible
           and the coefficients of polclass(D, bi) are minimized
     pd: the degree of polclass
         This is usually equal to h except when the invariant
           is a double eta-quotient w_p,q and p|D and q|D.
           In this special case, the degree is h/2.
   Dfac: the prime factorization of D
         Note that D can be factored as D = q0 q1* q2* ... qn*
           where q0* = 1, 4, -4, 8
             and qi* = 1 mod 4 and |qi| is a prime
         The prime factorization is implemented as a vecsmall
           listing the indices of the qi* as they appear in
           the primelist. If q0* = 1, the first component of
           this vecsmall contains the index of q1*. Otherwise,
           it contains the index of q0*.
*/
INLINE long
Dinfo_get_D(GEN Dinfo) { return gel(Dinfo, 1)[1]; }
INLINE long
Dinfo_get_h(GEN Dinfo) { return gel(Dinfo, 1)[2]; }
INLINE long
Dinfo_get_bi(GEN Dinfo) { return gel(Dinfo, 1)[3]; }
INLINE ulong
Dinfo_get_pd(GEN Dinfo) { return umael(Dinfo, 1, 4); }
INLINE GEN
Dinfo_get_Dfac(GEN Dinfo) { return gel(Dinfo, 2); }

/* primelist and indexlist

  primelist begins with 8, -4, -8, which we consider as "prime"
  the subsequent elements are the corresponding p^star of the
  odd primes below the indicated limit (maxsqrt) listed in
  increasing absolute value

  indexlist keeps the index of the odd primes. see tables below:

         i |   1 |   2 |   3 |   4 |   5 |   6 |   7 |   8 |   9 |  10 |  11 |
  ---------+-----+-----+-----+-----+-----+-----+-----+-----+-----+-----+-----+
         i |   1 |   2 |   3 |   4 |   5 |   6 |   7 |   8 |   9 |  10 |  11 |
  Plist[i] |   8 |  -4 |  -8 |  -3 |   5 |  -7 | -11 |  13 |  17 | -19 | -23 |
         p |   3 |   5 |   7 |   9 |  11 |  13 |  15 |  17 |  19 |  21 |  23 |
  ---------+-----+-----+-----+-----+-----+-----+-----+-----+-----+-----+-----+
  Ilist[i] |   4 |   5 |   6 | XXX |   7 |   8 | XXX |   9 |  10 | XXX |  11 |
  ---------+-----+-----+-----+-----+-----+-----+-----+-----+-----+-----+-----+
*/

/*  Input: maxsqrt
   Output: primelist containing primes whose absolute value is at most maxsqrt
*/
static GEN
ecpp_primelist_init(long maxsqrt)
{
  GEN P = cgetg(maxsqrt, t_VECSMALL);
  forprime_t T;
  long j;
  u_forprime_init(&T, 3, ULONG_MAX);
  P[1] =  8;
  P[2] = -4;
  P[3] = -8;
  for (j = 4;;j++)
  {
    long p = u_forprime_next(&T);
    if (!p || p > maxsqrt) break;
    if (p%4 == 3) p = -p;
    P[j] = p;
  }
  setlg(P,j); return P;
}

static GEN
Dfac_to_disc(GEN x, GEN P) { pari_APPLY_long(uel(P,x[i])); }
static GEN
Dfac_to_roots(GEN x, GEN P) { pari_APPLY_type(t_VEC, gel(P,x[i])); }

/*  Input: primelist
   Output: returns a vecsmall indicating at what index
           of primelist each odd prime occurs
*/
INLINE GEN
primelist_to_indexlist(GEN P)
{
  long i, lP = lg(P), maxprime = labs(P[lP-1]);
  GEN indexlist;

  if (maxprime < 8) maxprime = 8;
  indexlist = zero_zv(maxprime/2);
  for (i = 4; i < lP; i++)
  {
    long p = labs(P[i]);
    uel(indexlist, p/2) = i;
  }
  return indexlist;
}

INLINE ulong
ecpp_param_get_maxsqrt(GEN param) { return umael3(param, 1, 1, 1); }
INLINE ulong
ecpp_param_get_maxdisc(GEN param) { return umael3(param, 1, 1, 2); }
INLINE ulong
ecpp_param_get_maxpcdg(GEN param) { return umael3(param, 1, 1, 3); }
INLINE GEN
ecpp_param_get_primelist(GEN param) { return gmael3(param, 1, 2, 1); }
INLINE GEN
ecpp_param_get_disclist(GEN param) { return gmael(param, 1, 3); }
INLINE GEN
ecpp_param_get_primorial_vec(GEN param) { return gel(param, 2); }

/*  Input: x, 20 <= x <= 30
 * Output: a vector whose ith entry is the product of all primes below 2^x */
static GEN
primorial_vec(ulong x)
{
  pari_sp av = avma;
  long i, y = x-19;
  GEN v = primes_upto_zv(1UL << x), w = cgetg(y+1, t_VEC);
  /* ind[i]th prime number is the largest prime <= 2^(20+i) */
  long ind[] = { 0, 82025L, 155611L, 295947L, 564163L, 1077871L, 2063689L,
                 3957809L, 7603553L, 14630843L, 28192750L, 54400028L };
  gel(w,1) = zv_prod_Z(vecslice(v,1,ind[1]));
  for (i = 2; i <= y; i++)
  {
    pari_sp av2 = avma;
    GEN q = mulii(gel(w,i-1), zv_prod_Z(vecslice(v,ind[i-1]+1,ind[i])));
    gel(w,i) = gerepileuptoint(av2, q);
  }
  return gerepileupto(av, w);
}

INLINE GEN
ecpp_param_get_primorial(GEN param, long v)
{
  GEN primorial_vec = ecpp_param_get_primorial_vec(param);
  return gel(primorial_vec, v);
}
INLINE void
ecpp_param_set_maxdisc(GEN param, ulong x) { umael3(param, 1, 1, 2) = x; }
INLINE void
ecpp_param_set_maxpcdg(GEN param, ulong x) { umael3(param, 1, 1, 3) = x; }
INLINE void
ecpp_param_set_tdivexp(GEN param, ulong x) { gel(param, 2) = primorial_vec(x); }

static GEN ecpp_disclist_init( long maxsqrt, ulong maxdisc, GEN primelist);

INLINE void
ecpp_param_set_disclist(GEN param)
{
  long maxsqrt = ecpp_param_get_maxsqrt(param);
  ulong maxdisc = ecpp_param_get_maxdisc(param);
  GEN primelist = ecpp_param_get_primelist(param);
  gmael(param, 1, 3) = ecpp_disclist_init(maxsqrt, maxdisc, primelist);
}

/* NDinfomqg contains
   N, as in the theorem in ??ecpp
   Dinfo, as discussed in the comment about Dinfo
   m, as in the theorem in ??ecpp
   q, as in the theorem in ??ecpp
   g, a quadratic non-residue modulo N
   sqrt, a list of squareroots
*/
INLINE GEN
NDinfomqg_get_N(GEN x) { return gel(x,1); }
INLINE GEN
NDinfomqg_get_Dinfo(GEN x) { return gel(x,2); }
INLINE long
NDinfomqg_get_longD(GEN x) { return Dinfo_get_D(NDinfomqg_get_Dinfo(x)); }
INLINE GEN
NDinfomqg_get_D(GEN x) { return stoi(NDinfomqg_get_longD(x)); }
INLINE GEN
NDinfomqg_get_m(GEN x) { return gel(x,3); }
INLINE GEN
NDinfomqg_get_q(GEN x) { return gel(x,4); }
INLINE GEN
NDinfomqg_get_g(GEN x) { return gel(x,5); }
INLINE GEN
NDinfomqg_get_sqrt(GEN x) { return gel(x,6); }

/* COMPARATOR FUNCTIONS */

static int
sort_disclist(void *data, GEN x, GEN y)
{
  long d1, h1, g1, o1, bi1, pd1, hf1, wD1, d2, h2, g2, o2, bi2, pd2, hf2, wD2;
  (void)data;
  d1 = Dinfo_get_D(x); wD1 = D_get_wD(d1);
  d2 = Dinfo_get_D(y); wD2 = D_get_wD(d2);
  /* higher number of units means more elliptic curves to try */
  if (wD1 != wD2) return wD2 > wD1 ? 1 : -1;
  /* lower polclass degree is better: faster computation of roots modulo N */
  pd1 = Dinfo_get_pd(x); /* degree of polclass */
  pd2 = Dinfo_get_pd(y);
  if (pd1 != pd2) return pd1 > pd2 ? 1 : -1;
  g1 = lg(Dinfo_get_Dfac(x))-1; /* genus number */
  h1 = Dinfo_get_h(x); /* class number */
  o1 = h1 >> (g1-1); /* odd class number */
  g2 = lg(Dinfo_get_Dfac(y))-1;
  h2 = Dinfo_get_h(y);
  o2 = h2 >> (g2-1);
  if (o1 != o2) return g1 > g2 ? 1 : -1;
  /* lower class number is better: higher probability of succesful cornacchia */
  if (h1 != h2) return h1 > h2 ? 1 : -1;
  /* higher height factor is better: polclass would have lower coefficients */
  bi1 = Dinfo_get_bi(x); /* best invariant */
  hf1 = modinv_height_factor(bi1); /* height factor */
  bi2 = Dinfo_get_bi(y);
  hf2 = modinv_height_factor(bi2);
  if (hf1 != hf2) return hf2 > hf1 ? 1 : -1;
  /* "higher" discriminant is better since its absolute value is lower */
  if (d1 != d2) return d2 > d1 ? 1 : -1;
  return 0;
}

/* Dmq macros */
INLINE GEN
Dmq_get_Dinfo(GEN Dmq) { return gel(Dmq, 1); }
INLINE GEN
Dmq_get_m(GEN Dmq) { return gel(Dmq, 2); }
INLINE GEN
Dmq_get_q(GEN Dmq) { return gel(Dmq, 3); }
INLINE long
Dmq_get_cnum(GEN Dmq) { return gmael(Dmq, 1, 1)[2]; }

static int
sort_NDmq_by_D(void *data, GEN x, GEN y)
{
  long d1 = NDinfomqg_get_longD(x);
  long d2 = NDinfomqg_get_longD(y);
  (void)data; return d2 > d1 ? 1 : -1;
}

static int
sort_Dmq_by_q(void *data, GEN x, GEN y)
{ (void)data; return cmpii(gel(x,3), gel(y,3)); }

static int
sort_Dmq_by_cnum(void *data, GEN x, GEN y)
{
  ulong h1 = Dmq_get_cnum(x);
  ulong h2 = Dmq_get_cnum(y);
  if (h1 != h2) return h1 > h2 ? 1 : -1;
  return sort_Dmq_by_q(data, x, y);
}

static void
ecpp_param_set_maxsqrt(GEN param, long x)
{
  umael3(param, 1, 1, 1) = x;
  gmael3(param, 1, 2, 1) = ecpp_primelist_init(x);
}

/* return H s.t if -maxD <= D < 0 is fundamental then H[(-D)>>1] is the
 * ordinary class number of Q(sqrt(D)); junk at other entries. */
static GEN
allh(ulong maxD)
{
  ulong a, A = usqrt(maxD/3), maxD2 = maxD >> 1;
  GEN H = zero_zv(maxD2);
  for (a = 1; a <= A; a++)
  {
    ulong a2 = a << 1, aa = a*a, aa4 = aa << 2, b, c;
    { /* b = 0 */
      ulong D = aa << 1;
      for (c = a; D <= maxD2; c++) { H[D]++; D += a2; }
    }
    for (b = 1; b < a; b++)
    {
      ulong B = b*b, D = (aa4 - B) >> 1;
      if (D > maxD2) break;
      H[D]++; D += a2; /* c = a */
      for (c = a+1; D <= maxD2; c++) { H[D] += 2; D += a2; }
    }
    { /* b = a */
      ulong D = (aa4 - aa) >> 1;
      for (c = a; D <= maxD2; c++) { H[D]++; D += a2; }
    }
  }
  return H;
}

static GEN
ecpp_disclist_init( long maxsqrt, ulong maxdisc, GEN primelist)
{
  pari_sp av = avma;
  long i, p, u, lmerge;
  forprime_t T;
  GEN Harr = allh(maxdisc); /* table of class numbers*/
  GEN ev, od; /* ev: D = 0 mod 4; od: D = 1 mod 4 */
  GEN indexlist = primelist_to_indexlist(primelist); /* for making Dfac */
  GEN merge; /* return this */
  long lenv = maxdisc/4; /* max length of od/ev FIXME: ev can have length maxdisc/8 */
  long N; /* maximum number of positive prime factors */

  /* tuning paramaters blatantly copied from vecfactoru */
  if (maxdisc < 510510UL) N = 7;
  else if (maxdisc < 9699690UL) N = 8;
  #ifdef LONG_IS_64BIT
    else if (maxdisc < 223092870UL) N = 9;
    else if (maxdisc < 6469693230UL) N = 10;
    else if (maxdisc < 200560490130UL) N = 11;
    else if (maxdisc < 7420738134810UL) N = 12;
    else if (maxdisc < 304250263527210UL) N = 13;
    else N = 16; /* don't bother */
  #else
    else N = 9;
  #endif

  /* initialization */
  od = cgetg(lenv + 1, t_VEC);
  ev = cgetg(lenv + 1, t_VEC);

  /* od[i] holds Dinfo of -(4*i-1)
     ev[i] holds Dinfo of -(4*i)   */
  for (i = 1; i <= lenv; i++)
  {
    long h, x, id;
    h = Harr[2*i-1]; /* class number of -(4*i-1) */
    gel(od, i) = mkvec2(mkvecsmall4(1, h, 0, h), vecsmalltrunc_init(N));
    switch(i&7)
    {
      case 0:
      case 4: gel(ev,i) = NULL; continue;
      case 2: x =-8; id = 3; break;
      case 6: x = 8; id = 1; break;
      default:x =-4; id = 2; break;
    }
    h = Harr[2*i]; /* class number of -(4*i) */
    gel(ev, i) = mkvec2(mkvecsmall4(x, h, 0, h), vecsmalltrunc_init(N));
    vecsmalltrunc_append(gmael(ev, i, 2), id);
  }

  /* sieve part */
  u_forprime_init(&T, 3, maxsqrt);
  while ( (p = u_forprime_next(&T)) )
  {
    long s; /* sp = number we're looking at, detects nonsquarefree numbers */
    long t; /* points to which number we're looking at */
    long q; /* p^star */
    switch(p&3)
    {
      case 1: q =  p; s = 3; break;
      default:q = -p; s = 1; break; /* case 3 */
    }
    for (t = (s*p+1)>>2; t <= lenv; t += p, s += 4)
    {
      GEN c = gel(od,t); if (!c) continue;
      if (s%p == 0) gel(od,t) = NULL;
      else
      {
        umael(c,1,1) *= q;
        vecsmalltrunc_append(gel(c,2), uel(indexlist,p/2));
      }
    }
    s = 1;
    for (t = p; t <= lenv; t += p, s++)
    {
      GEN c = gel(ev,t); if (!c) continue;
      if (s%p == 0) gel(ev,t) = NULL;
      else
      {
        umael(c,1,1) *= q;
        vecsmalltrunc_append(gel(c,2), uel(indexlist,p/2));
      }
    }
  }

  u = 0;
  for (i = 1; i <= lenv; i++)
  {
    GEN c = gel(od,i);
    if (c && umael(c,1,1) != -4*i+1) gel(od,i) = NULL; else u++;
  }
  for (i = 1; i <= lenv; i++)
  {
    GEN c = gel(ev,i);
    if (c && umael(c,1,1) != -4*i) gel(ev,i) = NULL; else u++;
  }

  /* merging the two arrays */
  merge = cgetg(u+1, t_VEC); lmerge = 0;
  for (i = 1; i <= lenv; i++)
  {
    GEN c = gel(od,i);
    if (c) gel(merge, ++lmerge) = c;
  }
  for (i = 1; i <= lenv; i++)
  {
    GEN c = gel(ev,i);
    if (c) gel(merge, ++lmerge) = c;
  }
  setlg(merge, lmerge);
  for (i = 1; i < lmerge; i++)
  {
    GEN T = gmael(merge,i,1); /* fill in bestinv [3] and poldegree [4] */
    long p1 = 1, p2 = 1, D = T[1], h = T[2];
    T[3] = disc_best_modinv(D);
    if (modinv_degree(&p1,&p2,T[3]) && (-D)%p1==0 && (-D)%p2==0) T[4] = h/2;
  }
  merge = gen_sort(merge, NULL, &sort_disclist);
  return gerepileupto(av, merge);
}

/*  Input: a vector tune whose components are vectors of length 3
 * Output: vector param of precomputations
 *   let x = [maxsqrt, maxdisc, maxpcdg] be the last component of tune then
 *   param[1][1] = tune[#tune] = [maxsqrt, maxdisc, maxpcdg]
 *   param[1][2] =   primelist = [ Vecsmall with the list of primes ]
 *   param[1][3] =    disclist = vector of Dinfos, sorted by disclist
 *   param[2]    = primorial_vec
 *   param[3]    =          tune */
static GEN
ecpp_param_set(GEN tune, GEN x)
{
  pari_sp av = avma;
  GEN param1 = mkvec3(zero_zv(3), zerovec(1), zerovec(1));
  GEN param = mkvec3(param1, gen_1, tune);
  long  maxsqrt = uel(x,1);
  ulong maxpcdg = uel(x,2);
  ulong tdivexp = uel(x,3);
  ecpp_param_set_maxsqrt(param, maxsqrt);
  ecpp_param_set_maxdisc(param, maxsqrt*maxsqrt);
  ecpp_param_set_maxpcdg(param, maxpcdg);
  ecpp_param_set_disclist(param);
  ecpp_param_set_tdivexp(param, tdivexp);
  return gerepilecopy(av, param);
}

/* cert contains [N, t, s, a4, [x, y]] as documented in ??ecpp; the following
 * information can be obtained:
 * D = squarefreepart(t^2-4N)
 * m = (N+1-t), q = m/s, a6 = y^3 - x^2 - a4*x, J */
INLINE GEN
cert_get_N(GEN x) { return gel(x,1); }
INLINE GEN
cert_get_t(GEN x) { return gel(x,2); }
INLINE GEN
cert_get_D(GEN x)
{
  GEN N = cert_get_N(x), t = cert_get_t(x);
  return coredisc(subii(sqri(t), shifti(N, 2)));
}
INLINE GEN
cert_get_m(GEN x)
{
  GEN N = cert_get_N(x), t = cert_get_t(x);
  return subii(addiu(N, 1), t);
}
INLINE GEN
cert_get_s(GEN x) { return gel(x,3); }
INLINE GEN
cert_get_q(GEN x) { return diviiexact(cert_get_m(x), cert_get_s(x)); }
INLINE GEN
cert_get_a4(GEN x) { return gel(x,4); }
INLINE GEN
cert_get_P(GEN x) { return gel(x,5); }
INLINE GEN
cert_get_x(GEN x) { return gel(cert_get_P(x), 1); }
INLINE GEN
cert_get_a6(GEN z)
{
  GEN N = cert_get_N(z), a = cert_get_a4(z), P = cert_get_P(z);
  GEN x = gel(P,1), xx = Fp_sqr(x, N);
  GEN y = gel(P,2), yy = Fp_sqr(y, N);
  return Fp_sub(yy, Fp_mul(x, Fp_add(xx,a,N), N), N);
}
INLINE GEN
cert_get_E(GEN x) { return mkvec2(cert_get_a4(x), cert_get_a6(x)); }
INLINE GEN
cert_get_J(GEN x)
{
  GEN a = cert_get_a4(x), b = cert_get_a6(x), N = cert_get_N(x);
  return Fp_ellj(a, b, N);
}

/*  Input: J, N
 * Output: [a, b], a = 3*J*(1728-J) mod N, b = 2*J*(1728-J)^2 mod N */
static GEN
Fp_ellfromj(GEN j, GEN N)
{
  GEN k, jk, a, b;
  j = Fp_red(j, N);
  if (isintzero(j)) return mkvec2(gen_0, gen_1);
  if (absequalui(umodui(1728, N), j)) return mkvec2(gen_1, gen_0);
  k = Fp_sub(utoi(1728), j, N);
  jk = Fp_mul(j, k, N);
  a = Fp_mulu(jk, 3, N);
  b = Fp_mulu(Fp_mul(j, Fp_sqr(k,N), N), 2, N);
  return mkvec2(a, b);
}

/* "Twist factor". Does not cover J = 0, 1728 */
static GEN
cert_get_lambda(GEN z)
{
  GEN N, J, a, b, AB, aB, bA;
  J = cert_get_J(z);
  N = cert_get_N(z);
  a = cert_get_a4(z);
  b = cert_get_a6(z);
  AB = Fp_ellfromj(J, N);
  aB = Fp_mul(a, gel(AB,2), N);
  bA = Fp_mul(b, gel(AB,1), N); return Fp_div(aB, bA, N);
}

/* Solves for T such that if
   [A, B] = [3*J*(1728-J), 2*J*(1728-J)^2]
   and you let
   L = T^3 + A*T + B, A = A*L^2, B = B*L^3
   then
   x == TL and y == L^2
*/
static GEN
cert_get_T(GEN z)
{
  GEN N = cert_get_N(z), x = cert_get_x(z);
  GEN l = cert_get_lambda(z); /* l = 1/L */
  return Fp_mul(x, l, N);
}

/* database for all invariants
   stolen from Hamish's code
*/
static GEN
polmodular_db_init_allinv(void)
{
  GEN ret1, ret2 = cgetg(39+1, t_VEC);
  enum { DEFAULT_MODPOL_DB_LEN = 32 };
  long i;
  for (i = 1; i < lg(ret2); i++)
    gel(ret2, i) = zerovec_block(DEFAULT_MODPOL_DB_LEN);
  ret1 = zerovec_block(DEFAULT_MODPOL_DB_LEN);
  return mkvec2(ret1, ret2);
}

/*  Input: a discriminant D and a database of modular polynomials,
 * Output: polclass(D,disc_best_modinv(D)) */
static GEN
D_polclass(GEN D, GEN *db)
{
  long inv = disc_best_modinv(itos(D));
  GEN HD, t = mkvec2(gel(*db, 1), gmael(*db, 2, inv));
  if (inv == 0) t = mkvec2(gel(*db, 1), gen_0);
  HD = polclass0(itos(D), inv, 0, &t);
  gel(*db, 1) = gel(t,1);
  if (inv != 0) gmael(*db, 2, inv) = gel(t,2);
  return HD;
}

/*  Input: N, Dinfo, a root rt mod N of polclass(D,disc_best_modinv(D))
 * Output: a root J mod N of polclass(D) */
INLINE GEN
NDinfor_find_J(GEN N, GEN Dinfo, GEN rt)
{ return Fp_modinv_to_j(rt, Dinfo_get_bi(Dinfo), N); }

INLINE long
NmqEP_check(GEN N, GEN q, GEN E, GEN P, GEN s)
{
  GEN a = gel(E,1), mP, sP;
  sP = FpJ_mul(P, s, a, N); if (FpJ_is_inf(sP)) return 0;
  mP = FpJ_mul(sP,q, a, N); return FpJ_is_inf(mP);
}

/* Find an elliptic curve E modulo N and a point P on E which corresponds to
 * the ith element of the certificate; uses N, D, m, q, J from previous steps.
 * All computations are modulo N unless stated otherwise */

/* g is a quadratic and cubic non-residue modulo N */
static GEN
j0_find_g(GEN N)
{
  GEN n = diviuexact(subiu(N, 1), 3);
  for(;;)
  {
    GEN g = randomi(N);
    if (kronecker(g, N) == -1 && !equali1(Fp_pow(g, n, N))) return g;
  }
}

static GEN
random_FpJ(GEN A, GEN B, GEN N)
{
  GEN P = random_FpE(A, B, N);
  return FpE_to_FpJ(P);
}

static GEN
NDinfomqgJ_find_EP(GEN N, GEN Dinfo, GEN m, GEN q, GEN g, GEN J, GEN s)
{
  long i, D = Dinfo_get_D(Dinfo);
  GEN gg;
  GEN E = Fp_ellfromj(J, N), A = gel(E,1), B = gel(E,2);
  GEN P = random_FpJ(A, B, N);
  if (NmqEP_check(N, q, E, P, s)) return mkvec2(E, P);
  switch (D_get_wD(D))
  {
    case 2:
      gg = Fp_sqr(g, N);
      A = Fp_mul(A, gg, N); /* Ag^2 */
      B = Fp_mul(Fp_mul(B, gg, N), g, N); /* Bg^3 */
      E = mkvec2(A, B);
      P = random_FpJ(A, B, N);
      if (NmqEP_check(N, q, E, P, s)) return mkvec2(E, P);
      else return NDinfomqgJ_find_EP(N, Dinfo, m, q, g, J, s);
    case 4:
      for (i = 1; i < 4; i++)
      {
        A = Fp_mul(A, g, N); /* Ag */
        E = mkvec2(A, B);
        P = random_FpJ(A, B, N);
        if (NmqEP_check(N, q, E, P, s)) return mkvec2(E, P);
      }
      return NDinfomqgJ_find_EP(N, Dinfo, m, q, g, J, s);
    case 6:
      B = Fp_mul(B, g, N); /* Bg */
      E = mkvec2(A, B);
      P = random_FpJ(A, B, N);
      if (NmqEP_check(N, q, E, P, s)) return mkvec2(E, P);
      g = j0_find_g(N);
      for (i = 1; i < 6; i++)
      {
        B = Fp_mul(B, g, N); /* Bg */
        if (i % 3 == 0) continue;
        E = mkvec2(A, B);
        P = random_FpJ(A, B, N);
        if (NmqEP_check(N, q, E, P, s)) return mkvec2(E, P);
      }
      return NDinfomqgJ_find_EP(N, Dinfo, m, q, g, J, s);
  }
  pari_err(e_BUG, "NDinfomqgJ_find_EP");
  return NULL;
}

/* Convert the disc. factorisation of a genus field to the
 * disc. factorisation of its real part. */
static GEN
realgenusfield(GEN Dfac, GEN sq, GEN p)
{
  long i, j, l = lg(Dfac), dn, n = 0;
  GEN sn, s = gen_0, R = cgetg(l-1, t_VECSMALL);
  for (i = 1; i < l; i++)
    if (Dfac[i] < 0) { n = i; break; }
  if (n == 0) pari_err_BUG("realgenusfield");
  dn = Dfac[n]; sn = gel(sq, n);
  for (j = i = 1; i < l; i++)
    if (i != n)
    {
      long d = Dfac[i];
      GEN si = gel(sq,i);
      R[j++] = d > 0 ? d : d * dn;
      s = Fp_add(s, d > 0? si: Fp_mul(si, sn, p), p);
    }
  return mkvec2(R, s);
}

static GEN
FpX_classtower_oneroot(GEN P, GEN Dfac, GEN sq, GEN p)
{
  pari_timer ti;
  pari_sp av = avma;
  long i, l;
  GEN V, v, R, C, N = NULL;
  if (degpol(P)==1 || gcmp(gsupnorm(P,DEFAULTPREC), p) >= 0)
    return FpX_oneroot_split(P, p);
  V = realgenusfield(Dfac, sq, p);
  v = gel(V, 1); R = gel(V,2);
  l = lg(v)-1;
  dbg_mode() timer_start(&ti);
  for(i=1; i<=l; i++)
  {
    ulong d = uel(v,i);
    GEN Q = deg2pol_shallow(gen_1, gen_0, stoi(-(long)d), 1);
    N = N ? polcompositum0(N,Q,2): Q;
  }
  if (N)
  {
    P = liftpol_shallow(gmael(nffactor(N, P),1,1));
    P = FpXY_evalx(Q_primpart(P), R, p);
    dbg_mode() err_printf(ANSI_COLOR_BRIGHT_GREEN " %6ld" ANSI_COLOR_RESET
                         , timer_delay(&ti));
  } else
    dbg_mode() err_printf("       ");
  C = FpX_oneroot_split(P, p);
  dbg_mode() err_printf(" %6ld", timer_delay(&ti));
  return gerepileupto(av, C);
}

/* This uses [N, D, m, q] from step 1 to find the appropriate j-invariants
 * to be used in step 3. Step 2 is divided into substeps 2a, 2b, 2c */
static GEN
ecpp_step2(GEN step1, GEN *X0)
{
  long j;
  pari_timer ti;
  GEN perm = gen_indexsort(step1, NULL, &sort_NDmq_by_D);
  GEN step2 = cgetg(lg(step1), t_VEC);
  GEN HD = NULL, Dprev = gen_0, db = polmodular_db_init_allinv();

  for (j = 1; j < lg(step2); j++)
  {
    long i = uel(perm, j);
    GEN J, t, s, a4, P, EP, rt, S = gel(step1, i);
    GEN Dinfo = NDinfomqg_get_Dinfo(S);
    GEN Dfac = Dinfo_get_Dfac(Dinfo);
    GEN N = NDinfomqg_get_N(S), D = NDinfomqg_get_D(S);
    GEN m = NDinfomqg_get_m(S), q = NDinfomqg_get_q(S);
    GEN g = NDinfomqg_get_g(S), sq = NDinfomqg_get_sqrt(S);

    /* C1: Find the appropriate class polynomial modulo N */
    dbg_mode() timer_start(&ti);
    if (!equalii(D, Dprev)) HD = D_polclass(D, &db);
    dbg_mode() {
      long tt = timer_record(X0, "C1", &ti);
      err_printf(ANSI_COLOR_BRIGHT_GREEN "\n[ %3d | %4ld bits]" ANSI_COLOR_RESET, i, expi(N));
      err_printf(ANSI_COLOR_GREEN " D = %8Ps poldeg = %4ld" ANSI_COLOR_RESET, D, degpol(HD));
      if (equalii(D, Dprev)) err_printf(" %6ld", tt);
      else err_printf(ANSI_COLOR_BRIGHT_WHITE " %6ld" ANSI_COLOR_RESET, tt);
    }
    /* C2: Find a root modulo N of the polynomial obtained in previous step */
    dbg_mode() timer_start(&ti);
    rt = FpX_classtower_oneroot(HD, Dfac, sq, N);
    dbg_mode() err_printf(" %6ld", timer_record(X0, "C2", &ti));

    /* C3: Convert root from previous step into the appropriate j-invariant */
    dbg_mode() timer_start(&ti);
    J = NDinfor_find_J(N, Dinfo, rt);
    dbg_mode() err_printf(" %6ld", timer_record(X0, "C3", &ti));

    /* D1: Find an elliptic curve E with a point P satisfying the theorem */
    dbg_mode() timer_start(&ti);
    s = diviiexact(m, q);
    EP = NDinfomqgJ_find_EP(N, Dinfo, m, q, g, J, s);
    dbg_mode() err_printf(" %6ld", timer_record(X0, "D1", &ti));

    /* D2: Compute for t and s */
    dbg_mode() timer_start(&ti);
    t = subii(addiu(N, 1), m); /* t = N+1-m */
    a4 = gmael(EP, 1, 1);
    P = FpJ_to_FpE(gel(EP, 2), N);
    dbg_mode() err_printf(" %6ld", timer_record(X0, "D2", &ti));

    gel(step2, i) = mkvec5(N, t, s, a4, P);
    Dprev = D;
  }
  return step2;
}
/* end of functions for step 2 */

/* start of functions for step 1 */

/*  Input: vector whose components are [D, m]
   Output: vector whose components are m
*/
static GEN
Dmvec_to_mvec(GEN Dmvec)
{
  long lgmvec = lg(Dmvec);
  GEN mvec = cgetg(lgmvec, t_VEC);
  long i;
  for (i = 1; i < lgmvec; i++) gel(mvec, i) = gmael(Dmvec, i, 2);
  return mvec;
}

/*  Input: vector v whose components are [D, m], vector w whose components are q
   Output: vector whose components are [D, m, q]
*/
static GEN
Dmvec_qvec_to_Dmqvec(GEN Dmvec, GEN qvec)
{
  long i, l = lg(Dmvec);
  GEN Dmqvec = cgetg(l, t_VEC);
  for (i = 1; i < l; i++)
  {
    GEN D = gmael(Dmvec, i, 1);
    GEN m = gmael(Dmvec, i, 2);
    GEN q = gel(qvec, i);
    gel(Dmqvec, i) = mkvec3(D, m, q);
  }
  return Dmqvec;
}

/*  Input: vector whose components are [D, m, q]
   Output: vector whose components are q
*/
static GEN
Dmqvec_to_qvec(GEN Dmqvec)
{
  long i, l = lg(Dmqvec);
  GEN qvec = cgetg(l, t_VEC);
  for (i = 1; i < l; i++) gel(qvec, i) = gmael(Dmqvec, i, 3);
  return qvec;
}

/* This returns the square root modulo N of the ith entry of the primelist.
   If this square root is already in sqrtlist, simply return it.
   Otherwise, compute it, save it and return it.
   g is a quadratic non-residue that is needed
     somehow in the algorithm for taking square roots modulo N.
*/
static GEN
p_find_primesqrt(GEN N, GEN* X0, GEN primelist, GEN sqrtlist, long i, GEN g)
{
  if (!signe(gel(sqrtlist,i)))
  {
    long p = uel(primelist, i);
    dbg_mode() err_printf(ANSI_COLOR_MAGENTA "S" ANSI_COLOR_RESET);
    /* A4: Get the square root of a prime factor of D. */
    gel(sqrtlist, i) = Fp_sqrt_i(stoi(p), g, N); /* NULL if invalid. */
  }
  return gel(sqrtlist, i);
}

/* This finds the legit square root of D modulo N where D is the discriminant
 * in Dinfo: find the square root modulo N of each prime p dividing D; then
 * assemble the actual square root of D by multiplying the prime square roots */
static GEN
D_find_discsqrt(GEN N, GEN primelist, GEN *X0, GEN Dinfo, GEN sqrtlist, GEN g)
{
  GEN s = NULL, Dfac = Dinfo_get_Dfac(Dinfo);
  long i, lgDfac = lg(Dfac);
  for (i = 1; i < lgDfac; i++)
  {
    GEN sqrtfi = p_find_primesqrt(N, X0, primelist, sqrtlist, uel(Dfac, i), g);
    if (!sqrtfi) pari_err_BUG("D_find_discsqrt"); ; /* when N composite ? */
    s = s? Fp_mul(s, sqrtfi, N): sqrtfi;
  }
  return s? s: gen_1;
}

/* Given a solution U, V to U^2 + |D|V^2 = 4N, this find all the possible
     cardinalities of the elliptic curves over the finite field F_N
     whose endomorphism ring is isomorphic to the maximal order
     in the imaginary quadratic number field K = Q(sqrt(D)). ???
*/
static GEN
NUV_find_m(GEN Dinfo, GEN N, GEN U, GEN V, long wD)
{
  GEN m, Nplus1 = addiu(N, 1), u = U, mvec = cgetg(wD+1, t_VEC);
  long i;
  for (i = 0; i < wD; i++)
  {
    if (odd(i)) m = subii(Nplus1, u);
    else
    {
      if (wD == 4 && i==2) u = shifti(V, 1);
      if (wD == 6 && i==2) u = shifti(submuliu(U, V, 3), -1);
      if (wD == 6 && i==4) u = shifti(addmuliu(U, V, 3), -1);
      m = addii(Nplus1, u);
    }
    gel(mvec, i+1) = mkvec2(Dinfo, m);
  }
  return mvec;
}

/* Populates Dmbatch with Dmvec's -- whose components are of the form [D,m],
   where m is a cardinalities of an elliptic curve with endomorphism ring
   isomorphic to the maximal order of imaginary quadratic K = Q(sqrt(D)).
   It returns 0 if:
     * Any of the p* dividing D is not a quadratic residue mod N
     * Cornacchia cannot find a solution U^2 + |D|V^2 = 4N.
   Otherwise, it returns the number of cardinalities added to Dmbatch.
   Finally, sqrtlist and g help compute the square root modulo N of D.
*/
static long
D_collectcards(GEN N, GEN param, GEN* X0, GEN Dinfo, GEN sqrtlist, GEN g, GEN Dmbatch, GEN kroP)
{
  long i, l, corn_succ, wD, D = Dinfo_get_D(Dinfo);
  GEN U, V, sqrtofDmodN, Dfac = Dinfo_get_Dfac(Dinfo);
  GEN primelist = ecpp_param_get_primelist(param);
  pari_timer ti;

  /* A1: Check (p*|N) = 1 for all primes dividing D */
  dbg_mode() timer_start(&ti);
  l = lg(Dfac);
  for (i = 1; i < l; i++)
  {
    long j = Dfac[i], s = kroP[j];
    if (s > 1) kroP[j] = s = krosi(primelist[j], N); /* update cache */
    if (s == 0) return -1; /* N is composite */
    if (s < 0) return 0;
  }
  dbg_mode() timer_record(X0, "A1", &ti);

  /* A3: Get square root of D mod N */
  dbg_mode() timer_start(&ti);
  sqrtofDmodN = D_find_discsqrt(N, primelist, X0, Dinfo, sqrtlist, g);
  dbg_mode() {
    timer_record(X0, "A3", &ti);
    if (!equalii(Fp_sqr(sqrtofDmodN, N), addis(N, D)) /* D mod N, D < 0*/ )
      pari_err_BUG("D_find_discsqrt");
  }

  /* A5: Use square root with Cornacchia to solve U^2 + |D|V^2 = 4N */
  dbg_mode() timer_start(&ti);
  corn_succ = cornacchia2_sqrt( absi(stoi(D)), N, sqrtofDmodN, &U, &V);
  dbg_mode() timer_record(X0, "A5", &ti);
  if (!corn_succ) {
    dbg_mode() err_printf(ANSI_COLOR_YELLOW "c" ANSI_COLOR_RESET);
    return 0;
  }

  /* We're sticking with this D. */
  dbg_mode() err_printf(ANSI_COLOR_BRIGHT_YELLOW "D" ANSI_COLOR_RESET);

  /* A6: Collect the w(D) cardinalities of E/(F_N) with CM by D */
  dbg_mode() timer_start(&ti);
  wD = D_get_wD(D);
  vectrunc_append_batch(Dmbatch,  NUV_find_m(Dinfo,N,U,V,wD));
  dbg_mode() timer_record(X0, "A6", &ti);
  return wD;
}

/* Compute (S(16N, 2) + S(4096N, 4) + 4)\4 + 1,  where S is the nth root
 * rounded down. This is at most one more than (N^1/4 + 1)^2. */
static GEN
ecpp_qlo(GEN N)
{
  GEN a = sqrtnint(shifti(N, 4), 2);
  GEN b = sqrtnint(shifti(N, 12), 4);
  return addiu(shifti(addii(a, b), -2), 2);
}

static long
lessthan_qlo(void* E, GEN q) { return (cmpii(q, (GEN)E) < 0); }
static long
gained_bits(void* E, GEN q) { return (expi(q) <= (long)E); }

/*  Input: Dmqvec
 * Output: Dmqvec such that q satisfies (N^1/4 + 1)^2 < q < N/2 */
static GEN
Dmqvec_slice_Dmqvec(GEN N, GEN Dmqvec)
{
  long lo_ind, hi_ind, goal;
  GEN qlo, qvec;

  /* Dmqvec is sorted according to q */
  Dmqvec = gen_sort(Dmqvec, NULL, &sort_Dmq_by_q);
  qvec = Dmqvec_to_qvec(Dmqvec);

  qlo = ecpp_qlo(N);
  lo_ind = zv_binsearch0((void*)qlo, &lessthan_qlo, qvec); lo_ind++;
  if (lo_ind >= lg(qvec)) return NULL;

  goal = expi(N)-1;
  hi_ind = zv_binsearch0((void*)goal, &gained_bits, qvec);
  if (hi_ind == 0) return NULL;

  return vecslice(Dmqvec, lo_ind, hi_ind);
}

/* Given a vector mvec of mi's, simultaneously remove all prime factors of each
 * mi less then BOUND_PRIMORIAL. This implements Franke 2004: Proving the
 * Primality of Very Large Numbers with fastECPP */
static GEN
mvec_batchfactor_qvec(GEN mvec, GEN primorial)
{ /* Obtain the product tree of mvec. */
  GEN leaf = Z_ZV_mod_tree(primorial, mvec, ZV_producttree(mvec));
  long i;

  /* Go through each leaf and remove small factors. */
  for (i = 1; i < lg(mvec); i++)
  {
    GEN m = gel(mvec, i);
    while (!equali1(gel(leaf,i)) )
    {
      gel(leaf,i) = gcdii(m, gel(leaf,i));
      m = diviiexact(m, gel(leaf,i));
    }
    gel(mvec, i) = m;
  }
  return mvec;
}

/*  Input: Dmvec
   Output: Dmqvec
   Uses mvec_batchfactor_qvec to produce the output.
*/
static GEN
Dmvec_batchfactor_Dmqvec(GEN Dmvec, GEN primorial)
{
  GEN qvec = mvec_batchfactor_qvec(Dmvec_to_mvec(Dmvec), primorial);
  return Dmvec_qvec_to_Dmqvec(Dmvec, qvec);
}

/* tunevec = [maxsqrt, maxpcdg, tdivexp]
     and is a shorthand for specifying the parameters of ecpp
*/
static GEN
tunevec(GEN N, GEN param)
{
  GEN T = gel(param,3);
  long e = expi(N), i, l = lg(T)-1;
  for (i = 1; i < l; i++)
    if (mael(T,i,4) == 0 || e <= mael(T,i,4)) break;
  return gel(T,i);
}
static long
tunevec_tdivbd(GEN N, GEN param) { return uel(tunevec(N, param), 3); }
static long
tunevec_batchsize(GEN N, GEN param)
{ return (28-tunevec_tdivbd(N, param) < 0 ? 0 : 28-tunevec_tdivbd(N, param)); }

/*  Input: Dmbatch (from the downrun)
   Output: Dmqvec
*/
static GEN
Dmbatch_factor_Dmqvec(GEN N, GEN* X0, GEN Dmbatch, GEN param)
{
  pari_sp av = avma;
  pari_timer ti;
  GEN primorial = ecpp_param_get_primorial(param, tunevec_tdivbd(N, param)-19);
  GEN Dmqvec;

  /* B1: Factor by batch. */
  dbg_mode() timer_start(&ti);
  Dmqvec = Dmvec_batchfactor_Dmqvec(Dmbatch, primorial);
  dbg_mode() timer_record(X0, "B1", &ti);

  /* B2: For each batch, remove cardinalities lower than (N^(1/4)+1)^2
   *     and cardinalities in which we didn't win enough bits. */
  Dmqvec = Dmqvec_slice_Dmqvec(N, Dmqvec);
  if (!Dmqvec) { avma = av; return NULL; } /* nothing is left */
  return gerepilecopy(av, Dmqvec);
}

/* Dmq (where q does not have small prime factors); determine if q is
 * pseudoprime */
static long
Dmq_isgoodq(GEN Dmq, GEN* X0)
{
  pari_timer ti;
  GEN q = Dmq_get_q(Dmq);
  long s;

  /* B3: Check pseudoprimality of each q on the list. */
  dbg_mode() timer_start(&ti);
  s = BPSW_psp_nosmalldiv(q);
  dbg_mode() timer_record(X0, "B3", &ti);
  return s; /* did not find for this m */
}

/* If N is small, return [N], else [ NDmqg, therest ] after a recursive call:
 *   NDmqg is a vector of the form [N,D,m,q,g].
 *   therest is the output of a recursive call with N = q
 * For successive D, find a square root of D mod N (g is a quad. non-residue),
 * use it to solve U^2 + |D|V^2 = 4N, then find candidates for m. When
 * enough candidates m, factor the m's of the batch and produce the q's
 * If one of the q's is pseudoprime, recursive call with N = q */
static GEN
N_downrun_NDinfomq(GEN N, GEN param, GEN *X0, long *depth, long persevere)
{
  pari_sp ave = avma;
  pari_timer T, ti;
  long lgdisclist, lprimelist, t, i, j, expiN = expi(N);
  long persevere_next = 0, FAIL = 0;
  ulong maxpcdg;
  GEN primelist, disclist, sqrtlist, g, Dmbatch, kroP;

  if (expiN < 64) return mkvec(N);

  dbg_mode() timer_start(&T);
  (*depth)++; /* we're going down the tree. */
  maxpcdg = ecpp_param_get_maxpcdg(param);
  primelist = ecpp_param_get_primelist(param);
  disclist = ecpp_param_get_disclist(param);
  lgdisclist = lg(disclist);

  /* Precomputation for batch size t. */
  t = expiN >> tunevec_batchsize(N, param);
  if (t < 1) t = 1;

  /* Precomputation for taking square roots, g needed for Fp_sqrt_i */
  g = Fp_2gener(N); if (!g) return gen_0; /* Composite if this happens. */

  /* Initialize sqrtlist for this N. */
  lprimelist = lg(primelist);
  sqrtlist = zerovec(lprimelist-1);

  /* A2: Check (p*|N) = 1 for all p */
  dbg_mode() timer_start(&ti);
  /* kroP[i] will contain (primelist[i] | N) */
  kroP = const_vecsmall(lprimelist-1, 2/*sentinel*/);
  switch(mod8(N))
  { /* primelist[1,2,3] = [8,-4,-8]; N is odd */
    case 1: kroP[1] = kroP[2] = kroP[3] = 1; break;
    case 3: kroP[1] = -1; kroP[2] =-1; kroP[3] = 1; break;
    case 5: kroP[1] = -1; kroP[2] = 1; kroP[3] =-1; break;
    case 7: kroP[1] =  1; kroP[2] =-1; kroP[3] =-1; break;
  }
  dbg_mode() timer_record(X0, "A2", &ti);

  /* Print the start of this iteration. */
  dbg_mode() {
    char o = persevere? '<': '[';
    char c = persevere? '>': ']';
    err_printf(ANSI_COLOR_BRIGHT_CYAN "\n%c %3d | %4ld bits%c "
               ANSI_COLOR_RESET, o, *depth, expiN, c);
  }
  /* Initialize Dmbatch, populated with candidate cardinalities in Phase I
   * (until #Dmbatch >= t); its elements will be factored on Phase II */
  Dmbatch = vectrunc_init(t+7);

  /* Number of cardinalities so far; should always be equal to lg(Dmbatch)-1. */
  /* i determines which discriminant we are considering. */
  i = 1;
  while (!FAIL)
  {
    pari_timer F;
    long lgDmqlist, last_i = i, numcard = 0; /* #Dmbatch */
    GEN Dmqlist;

    /* Dmbatch begins "empty", but keep the allocated memory. */
    setlg(Dmbatch, 1);

    /* PHASE I: Go through the D's and search for candidate m's.
     * Fill up Dmbatch until there are at least t elements. */
    while (i < lgdisclist )
    {
      GEN Dinfo = gel(disclist, i);
      long n;
      if (!persevere && Dinfo_get_pd(Dinfo) > maxpcdg) { FAIL = 1; break; }
      n = D_collectcards(N,param, X0, Dinfo, sqrtlist, g, Dmbatch, kroP);
      if (n < 0) return gen_0;
      last_i = i++;
      numcard += n; if (numcard >= t) break;
    }

    /* We have exhausted disclist and there are no card. to be factored */
    if (numcard <= 0 && (FAIL || i >= lgdisclist)) break;

    /* PHASE II: Find the corresponding q's for the m's found. Use Dmbatch */
    /* Find coresponding q of the candidate m's. */
    dbg_mode() timer_start(&F);
    Dmqlist = Dmbatch_factor_Dmqvec(N, X0, Dmbatch, param);
    if (Dmqlist == NULL) continue; /* none left => next discriminant. */

    /* If we are cheating by adding class numbers, sort by class number */
    if (Dinfo_get_pd(gel(disclist, last_i)) > maxpcdg)
      gen_sort_inplace(Dmqlist, NULL, &sort_Dmq_by_cnum, NULL);

    /* Check pseudoprimality before going down. */
    lgDmqlist = lg(Dmqlist);
    for (j = 1; j < lgDmqlist; j++)
    {
      GEN ret, Dfac, NDinfomq, Dmq = gel(Dmqlist,j);
      GEN Dinfo = Dmq_get_Dinfo(Dmq);
      GEN m = Dmq_get_m(Dmq);
      GEN q = Dmq_get_q(Dmq);
      if (expiN <= expi(q))
      {
        dbg_mode() err_printf(ANSI_COLOR_BRIGHT_RED "  x" ANSI_COLOR_RESET);
        continue;
      }
      dbg_mode() err_printf(ANSI_COLOR_WHITE "." ANSI_COLOR_RESET);
      if (!Dmq_isgoodq(Dmq, X0)) continue;

      dbg_mode() {
        err_printf(ANSI_COLOR_BRIGHT_BLUE "  %ld" ANSI_COLOR_RESET,
                   Dmq_get_cnum(Dmq));
        err_printf(ANSI_COLOR_BRIGHT_RED "\n       %5ld bits " ANSI_COLOR_RESET,
                   expi(q)-expiN);
      }
      /* Cardinality is pseudoprime. Call the next downrun! */
      ret = N_downrun_NDinfomq(q, param, X0, depth, persevere_next);

      /* That downrun failed. */
      if (ret == NULL) {
        dbg_mode() {
          char o = persevere? '<': '[';
          char c = persevere? '>': ']';
          err_printf(ANSI_COLOR_CYAN "\n%c %3d | %4ld bits%c " ANSI_COLOR_RESET,
                     o, *depth, expiN, c);
        }
        continue;
      }
      /* That downrun succeeded. */
      Dfac = Dinfo_get_Dfac(Dinfo);
      gel(Dinfo, 2) = Dfac_to_disc(Dfac, primelist);
      NDinfomq = mkcol6(N, Dinfo, m, q, g, Dfac_to_roots(Dfac,sqrtlist));
      return gerepilecopy(ave, mkvec2(NDinfomq, ret));
    }
    /* We have exhausted all the discriminants. */
    if (i >= lgdisclist) FAIL = 1;
    if (Dinfo_get_pd(gel(disclist, last_i)) > maxpcdg)
    {
      dbg_mode() err_printf(ANSI_COLOR_BRIGHT_RED "  !" ANSI_COLOR_RESET);
      persevere_next = 1;
    }
  }
  /* FAILED: Out of discriminants. */
  if (X0) umael(*X0, 3, 1)++; /* FAILS++ */
  dbg_mode() err_printf(ANSI_COLOR_BRIGHT_RED "  X" ANSI_COLOR_RESET);
  (*depth)--; return NULL;
}

/* x: the output of the (recursive) downrun function; return a vector
 * whose components are [N, D, m, q, g] */
static GEN
ecpp_flattencert(GEN x, long depth)
{
  long i, l = depth+1;
  GEN ret = cgetg(l, t_VEC);
  if (typ(x) != t_VEC) return gen_0;
  for (i = 1; i < l; i++) { gel(ret, i) = gel(x,1); x = gel(x,2); }
  return ret;
}

/* This calls the first downrun.
 * Then unravels the skeleton of the certificate.
 * This returns one of the following:
 * - a vector of the form [N, D, m, q, y]
 * - gen_0 (if N is composite)
 * - NULL (if FAIL) */
static GEN
ecpp_step1(GEN N, GEN param, GEN* X0)
{
  long depth = 0;
  GEN downrun = N_downrun_NDinfomq(N, param, X0, &depth, 1);
  if (downrun == NULL) return NULL;
  return ecpp_flattencert(downrun, depth);
}

/* The input is an integer N.
   It uses the precomputation step0 done in ecpp_step0. */
static GEN
ecpp0(GEN N, GEN param)
{

  GEN step1, answer, Tv, Cv, X0;
  pari_sp av = avma;
  long i, j;

  /* Check if N is pseudoprime to begin with. */
  if (!BPSW_psp(N)) return gen_0;

  /* Check if we should even prove it. */
  if (expi(N) < 64) return N;

  /* Timers and Counters */
  Tv = mkvec4(zero_zv(6), zero_zv(3), zero_zv(3), zero_zv(2));
  Cv = mkvec4(zero_zv(6), zero_zv(3), zero_zv(3), zero_zv(2));
  X0 = mkvec3(Tv, Cv, zero_zv(1));

  step1 = ecpp_step1(N, param, &X0);
  if (step1 == NULL) { avma = av; return NULL; }
  if (typ(step1) != t_VEC) { avma = av; return gen_0; }

  answer = ecpp_step2(step1, &X0);

  dbg_mode() {
  for (i = 1; i < lg(Tv); i++)
  {
    GEN v = gel(Tv, i);
    long l = lg(v);
    for (j = 1; j < l; j++)
    {
      long t = umael3(X0,1, i,j), n = umael3(X0,2, i,j);
      if (!t) continue;
      err_printf("\n  %c%ld: %16ld %16ld %16.3f", 'A'+i-1,j, t,n, (double)t/n);
    }
  }
    err_printf("\n" ANSI_COLOR_BRIGHT_RED "\nFAILS: %16ld" ANSI_COLOR_RESET "\n", umael(X0, 3, 1));
  }
  return gerepilecopy(av, answer);
}

static const long ecpp_tune[][4]=
{
  {  100,  2,  20,   500 },
  {  350, 14,  21,  1000 },
  {  450, 18,  21,  1500 },
  {  750, 22,  22,  2000 },
  {  900, 26,  23,  2500 },
  { 1000, 32,  23,  3000 },
  { 1200, 38,  24,  3500 },
  { 1400, 44,  24,  4000 },
  { 1600, 50,  24,  4500 },
  { 1800, 56,  25,  5000 },
  { 2000, 62,  25,  5500 },
  { 2200, 68,  26,  6000 },
  { 2400, 74,  26,  6500 },
  { 2600, 80,  26,  7000 },
  { 2800, 86,  26,  7500 },
  { 3000, 92,  27,  8000 },
  { 3200, 98,  27,  8500 },
  { 3400, 104, 27,  9000 },
  { 3400, 110, 27,  9500 },
  { 3800, 116, 28,     0 }
};

/* assume N BPSW-pseudoprime */
GEN
ecpp(GEN N)
{
  long expiN, i, tunelen;
  GEN tune;

  /* Check if we should even prove it. */
  expiN = expi(N);
  if (expiN < 64) return N;

  tunelen = (expiN+499)/500;
  tune = cgetg(tunelen+1, t_VEC);
  for (i = 1; i <= tunelen && ecpp_tune[i-1][3]; i++)
    gel(tune,i) = mkvecsmall4(ecpp_tune[i-1][0], ecpp_tune[i-1][1],
                              ecpp_tune[i-1][2], ecpp_tune[i-1][3]);
  for (; i <= tunelen; i++) gel(tune,i) = mkvecsmall4(200*(i-1),6*i-4,28,500*i);
  for(;;)
  {
    GEN C, param, x = gel(tune, tunelen);
    pari_timer T;
    dbg_mode() timer_start(&T);
    param = ecpp_param_set(tune, x);
    dbg_mode() {
      err_printf(ANSI_COLOR_BRIGHT_WHITE "\n%Ps" ANSI_COLOR_RESET, x);
      err_printf(ANSI_COLOR_WHITE "  %8ld" ANSI_COLOR_RESET, timer_delay(&T));
    }
    if ((C = ecpp0(N, param))) return C;
    x[1] *= 2;
    x[2] *= 2;
    x[3] = minss(x[3]+1, 30);
  }
}
long
isprimeECPP(GEN N)
{
  pari_sp av = avma;
  GEN res;
  if (!BPSW_psp(N)) return 0;
  res = ecpp(N);
  avma = av; return !isintzero(res);
}

/* PARI ECPP Certificate -> Human-readable format */
static GEN
cert_out(GEN x)
{
  long i, l = lg(x);
  pari_str str;
  str_init(&str, 1);
  if (typ(x) == t_INT)
  {
    str_printf(&str, "%Ps is prime.\nIndeed, ispseudoprime(%Ps) = 1 and %Ps < 2^64.\n", x, x, x);
    return strtoGENstr(str.string);
  }
  for (i = 1; i < l; i++)
  {
    GEN xi = gel(x, i);
    str_printf(&str, "[%ld]\n", i);
    str_printf(&str, " N = %Ps\n", cert_get_N(xi));
    str_printf(&str, " t = %Ps\n", cert_get_t(xi));
    str_printf(&str, " s = %Ps\n", cert_get_s(xi));
    str_printf(&str, "a4 = %Ps\n", cert_get_a4(xi));
    str_printf(&str, "D = %Ps\n", cert_get_D(xi));
    str_printf(&str, "m = %Ps\n", cert_get_m(xi));
    str_printf(&str, "q = %Ps\n", cert_get_q(xi));
    str_printf(&str, "E = %Ps\n", cert_get_E(xi));
    str_printf(&str, "P = %Ps\n", cert_get_P(xi));
  }
  return strtoGENstr(str.string);
}

/* PARI ECPP Certificate -> Magma Certificate
 * [* [*
 *     N, |D|, -1, m,
 *     [* a, b *],
 *     [* x, y, 1 *],
 *     [* [* q, 1 *] *]
 *   *], ... *] */
static GEN
magma_out(GEN x)
{
  long i, n = lg(x)-1;
  pari_str ret;
  str_init(&ret, 1);
  if (typ(x) == t_INT)
  {
    str_printf(&ret, "Operation not supported.");
    return strtoGENstr(ret.string);
  }
  str_printf(&ret, "[* ");
  for (i = 1; i<=n; i++)
  {
    GEN xi = gel(x,i), E = cert_get_E(xi), P = cert_get_P(xi);
    str_printf(&ret, "[* %Ps, %Ps, -1, %Ps, ",
              cert_get_N(xi), negi(cert_get_D(xi)), cert_get_m(xi));
    str_printf(&ret, "[* %Ps, %Ps *], ", gel(E,1), gel(E,2));
    str_printf(&ret, "[* %Ps, %Ps, 1 *], ", gel(P,1), gel(P,2));
    str_printf(&ret, "[* [* %Ps, 1 *] *] *]", cert_get_q(xi));
    if (i != n) str_printf(&ret, ", ");
  }
  str_printf(&ret, " *]");
  return strtoGENstr(ret.string);
}

/* Prints: label=(sign)hexvalue\n
 *   where sign is + or -
 *   hexvalue is value in hex, of the form: 0xABC123 */
static void
primo_printval(pari_str *ret, const char* label, GEN value)
{
  str_printf(ret, label);
  if (signe(value) >= 0) str_printf(ret, "=0x%P0X\n", value);
  else str_printf(ret, "=-0x%P0X\n", negi(value));
}

/* Input: PARI ECPP Certificate / Output: PRIMO Certificate
 *
 * Let Y^2 = X^3 + aX + b be the elliptic curve over N with the point (x,y)
 * as described in the PARI certificate.
 *
 * If J != 0, 1728, PRIMO asks for [J,T], where T = a/A * B/b * x,
 * A = 3J(1728-J) and B = 2J(1728-J)^2.
 *
 * If J=0 or J=1728, PRIMO asks for [A,B,T]; we let A=a and B=b => T = x */
static GEN
primo_out(GEN x)
{
  long i, l = (typ(x) == t_INT) ? 1 : lg(x);
  pari_str ret;
  str_init(&ret, 1);
  str_printf(&ret, "[PRIMO - Primality Certificate]\nFormat=4\n");
  str_printf(&ret, "TestCount=%ld\n\n[Comments]\n", l-1);
  str_printf(&ret, "Generated by PARI/GP %s\n",paricfg_version);
  str_printf(&ret, "https://pari.math.u-bordeaux.fr/\n\n[Candidate]\n");
  if (typ(x) == t_INT)
  {
    str_printf(&ret, "N=0x%P0X\n", x);
    return strtoGENstr(ret.string);
  }
  str_printf(&ret, "N=0x%P0X\n\n", cert_get_N(gel(x,1)));
  for (i = 1; i < l; i++)
  {
    GEN a4, a6, N, Nover2, xi = gel(x,i);
    long Ais0, Bis0;
    str_printf(&ret, "[%ld]\n", i);
    N = cert_get_N(xi);
    Nover2 = shifti(N, -1);
    primo_printval(&ret, "S", cert_get_s(xi));
    primo_printval(&ret, "W", cert_get_t(xi));
    a4 = cert_get_a4(xi); Ais0 = isintzero(a4);
    a6 = cert_get_a6(xi); Bis0 = isintzero(a6);
    if (!Ais0 && !Bis0) { /* J != 0, 1728 */
      primo_printval(&ret, "J", Fp_center(cert_get_J(xi), N, Nover2));
      primo_printval(&ret, "T", cert_get_T(xi));
    } else {
      if (!Ais0) a4 = Fp_center(a4, N, Nover2);
      if (!Bis0) a6 = Fp_center(a6, N, Nover2);
      primo_printval(&ret, "A", a4);
      primo_printval(&ret, "B", a6);
      primo_printval(&ret, "T", cert_get_x(xi));
    }
    str_printf(&ret, "\n");
  }
  return strtoGENstr(ret.string);
}

/* return 1 if q > (N^1/4 + 1)^2, 0 otherwise */
static long
Nq_isvalid(GEN N, GEN q)
{
  GEN c = subii(sqri(subiu(q,1)), N);
  if (signe(c) <= 0) return 0;
  /* (q-1)^2 > N; check that (N - (q-1)^2)^2 > 16Nq */
  return (cmpii(sqri(c), shifti(mulii(N,q), 4)) > 0);
}

/* return 1 if 'cert' is a valid PARI ECPP certificate */
static long
ecppisvalid_i(GEN cert)
{
  const long trustbits = 64;/* a pseudoprime < 2^trustbits is prime */
  long i, lgcert = lg(cert);
  GEN ql, q = gen_0;

  if (typ(cert) == t_INT)
  {
    if (expi(cert) >= trustbits) return 0; /* >= 2^trustbits */
    return BPSW_psp(cert);
  }
  if (typ(cert) != t_VEC || lgcert <= 1) return 0;
  ql = gel(cert, lgcert-1); if (lg(ql)-1 != 5) return 0;
  ql = cert_get_q(ql);
  if (expi(ql) >= trustbits || !BPSW_psp(ql)) return 0;

  for (i = 1; i < lgcert; i++)
  {
    GEN N, W, mP, sP, r, m, s, a, P, certi = gel(cert, i);
    if (lg(certi)-1 != 5) return 0;

    N = cert_get_N(certi);
    if (typ(N) != t_INT || signe(N) <= 0) return 0;
    switch(umodiu(N,6))
    {
      case 1: case 5: break; /* Check if N is not divisible by 2 or 3 */
      default: return 0;
    }
    /* Check if N matches the q from the previous entry. */
    if (i > 1 && !equalii(N, q)) return 0;

    W = cert_get_t(certi);
    if (typ(W) != t_INT) return 0;
    /* Check if W^2 < 4N (Hasse interval) */
    if (!(cmpii(sqri(W), shifti(N,2)) < 0)) return 0;

    s = cert_get_s(certi);
    if (typ(s) != t_INT || signe(s) < 0) return 0;

    m = cert_get_m(certi);
    q = dvmdii(m, s, &r);
    /* Check m%s == 0 */
    if (!isintzero(r)) return 0;
    /* Check q > (N^(1/4) + 1)^2 */
    if (!Nq_isvalid(N, q)) return 0;

    a = cert_get_a4(certi);
    if (typ(a) != t_INT) return 0;

    P = cert_get_P(certi);
    if (typ(P) != t_VEC || lg(P) != 3) return 0;
    P = FpE_to_FpJ(P);

    /* Check mP == 0 */
    mP = FpJ_mul(P, m, a, N);
    if (!FpJ_is_inf(mP)) return 0;

    /* Check sP != 0 and third component is coprime to N */
    sP = FpJ_mul(P, s, a, N);
    if (!isint1(gcdii(gel(sP, 3), N))) return 0;
  }
  return 1;
}
long
ecppisvalid(GEN cert)
{
  pari_sp av = avma;
  long v = ecppisvalid_i(cert);
  avma = av; return v;
}

GEN
ecppexport(GEN cert, long flag)
{
  switch(flag)
  {
    case 0: return cert_out(cert);
    case 1: return magma_out(cert);
    case 2: return primo_out(cert);
  }
  pari_err_FLAG("primecertexport");
  return NULL;/*LCOV_EXCL_LINE*/
}

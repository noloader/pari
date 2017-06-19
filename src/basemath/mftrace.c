/* Copyright (C) 2016  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/*************************************************************************/
/*                                                                       */
/*              Modular forms package based on trace formulas            */
/*                                                                       */
/*************************************************************************/
#include "pari.h"
#include "paripriv.h"

enum {
  t_MF_CONST, t_MF_EISEN, t_MF_Ek, t_MF_DELTA, t_MF_ETAQUO, t_MF_ELL,
  t_MF_MUL, t_MF_MULRC, t_MF_DIV, t_MF_LINEAR, t_MF_LINEAR_BHN,
  t_MF_SHIFT, t_MF_HECKEU, t_MF_DERIV, t_MF_DERIVE2, t_MF_INTEG,
  t_MF_TWIST, t_MF_EMBED, t_MF_HECKE, t_MF_BD, t_MF_TRACE, t_MF_NEWTRACE,
  t_MF_CLOSURE, t_MF_DIHEDRAL, t_MF_EISENM1M2, t_MF_POW, t_MF_RELTOABS
};

typedef struct {
  GEN vnew, vfull, DATA, VCHIP;
  long newHIT, newTOTAL, cuspHIT, cuspTOTAL;
} cachenew_t;

static void init_cachenew(cachenew_t *c, long n, GEN D);
static long mfisinspace_i(GEN mf, GEN F);
static GEN mfinit_i(GEN NK, long space);
static GEN mfeisenbasis_i(long N, long k, GEN CHI);
static GEN mfwt1trace_i(long N, GEN CHI, long space);
static GEN myfactoru(long N);
static GEN mygmodulo_lift(long k, long ord, GEN C);
static GEN mfcoefs_i(GEN F, long n, long d);
static GEN c_deflate(long n, long d, GEN V);
static GEN mfparams_ii(GEN F);
static GEN bhnmat_extend(GEN M, long m,long l, GEN vtf, cachenew_t *cache);
static GEN initnewtrace(long N, GEN CHI);
static void dbg_cachenew(cachenew_t *C);
static GEN c_integ(long n, long d, GEN F, GEN gk);
static GEN hecke_i(long m, long l, GEN knN, GEN CHI, GEN F);
static GEN c_Ek(long n, long d, long k, GEN C);
static GEN mfcusptrace_i(long N, long k, long n, GEN TDATA);
static GEN mfnewtracecache(long N, long k, long n, cachenew_t *cache);
static GEN colnewtrace(long n0, long n, long d, long N, long k, cachenew_t *cache);
static GEN dihan(GEN bnr, GEN w, GEN Tinit, GEN k0j, ulong n);
static GEN sigchi(long k, GEN CHI, long n);
static GEN sigchi2(long k, GEN CHI1, GEN CHI2, long n, long ord);
static GEN GammaNsig(long N, long k, long m1, long m2, long n);
static GEN mfmatheckewt1(GEN mf, long n, GEN B);
static GEN wt1basiscols(GEN mf, long n);
static GEN mfmathecke_i(GEN mf, long n);
static GEN mfdihedralcusp(long N, GEN CHI);
static GEN mfwt1basisdiv(GEN D, GEN CHI);
static long mfdihedralcuspdim(long N, GEN CHI);
static GEN mfdihedralnew(long N, GEN CHI);
static GEN mfdihedralall(GEN LIM);
static GEN mfeval0(long N, long k, GEN F, GEN vtau, long bitprec);
static GEN mfparams_i(GEN F);
static GEN mfwt1newinit(long N, GEN CHI, GEN TMP);
static long mfwt1dim(long N, GEN CHI);

GEN
mf_get_CHI(GEN mf) { return gmael(mf,1,3); }
long
mf_get_N(GEN mf) { return itou(gmael(mf,1,1)); }
long
mf_get_k(GEN mf) { return itou(gmael(mf,1,2)); }
long
mf_get_space(GEN mf) { return itos(gmael(mf,1,4)); }
GEN
mf_get_eisen(GEN mf) { return gel(mf,2); }
GEN
mf_get_vtf(GEN mf) { return gel(mf,3); }
GEN
mf_get_basis(GEN mf) { return shallowconcat(gel(mf,2), gel(mf,3)); }
GEN
mfbasis(GEN mf) { checkmf(mf); return concat(gel(mf,2), gel(mf,3)); }
long
mf_get_dim(GEN mf)
{
  switch(mf_get_space(mf))
  {
    case mf_NEW: case mf_CUSP: case mf_OLD:
      return lg(mf_get_vtf(mf)) - 1;
    case mf_FULL:
      return lg(mf_get_vtf(mf)) - 1 + lg(mf_get_eisen(mf))-1;
    case mf_EISEN:
      return lg(mf_get_eisen(mf))-1;
    default: pari_err_FLAG("mf_get_dim");
  }
  return 0;
}
GEN
mf_get_listj(GEN mf) { return gel(mf,4); }
GEN
mfnew_get_vj(GEN mf) { return gel(mf,4); }
GEN
mfcusp_get_vMjd(GEN mf) { return gel(mf,4); }
GEN
mf_get_M(GEN mf) { return gmael(mf,5,3); }
GEN
mf_get_Minv(GEN mf) { return gmael(mf,5,2); }
GEN
mf_get_Mindex(GEN mf) { return gmael(mf,5,1); }
GEN
mf_get_newforms(GEN mf) { return gel(mf,6); }
GEN
mf_get_fields(GEN mf) { return gel(mf,7); }

enum { _CHIP = 1, _SQRTS, _MUP, _GCD, _VCHIP, _BEZ, _NEWLZ };

/* ordinary gtocol forgets about initial 0s */
GEN
sertocol(GEN S) { return gtocol0(S, -(lg(S) - 2 + valp(S))); }

/*******************************************************************/
/*     Linear algebra in cyclotomic fields (TODO: export this)     */
/*******************************************************************/
/* return r and split prime p giving projection Q(zeta_n) -> Fp, zeta -> r */
static ulong
QabM_init(long n, ulong *p)
{
  ulong pinit = 1000000007;
  forprime_t T;
  if (n <= 1) { *p = pinit; return 0; }
  u_forprime_arith_init(&T, pinit, ULONG_MAX, 1, n);
  *p = u_forprime_next(&T);
  return Flx_oneroot(ZX_to_Flx(polcyclo(n, 0), *p), *p);
}
static ulong
Qab_to_Fl(GEN P, ulong r, ulong p)
{
  ulong t;
  GEN den;
  P = Q_remove_denom(lift_shallow(P), &den);
  if (typ(P) == t_POL) { GEN Pp = ZX_to_Flx(P, p); t = Flx_eval(Pp, r, p); }
  else t = umodiu(P, p);
  if (den) t = Fl_div(t, umodiu(den, p), p);
  return t;
}
static GEN
QabC_to_Flc(GEN C, ulong r, ulong p)
{
  long i, l = lg(C);
  GEN A = cgetg(l, t_VECSMALL);
  for (i = 1; i < l; ++i) uel(A,i) = Qab_to_Fl(gel(C,i), r, p);
  return A;
}
static GEN
QabM_to_Flm(GEN M, ulong r, ulong p)
{
  long i, l;
  GEN A = cgetg_copy(M, &l);
  for (i = 1; i < l; ++i)
    gel(A, i) = QabC_to_Flc(gel(M, i), r, p);
  return A;
}
/* A a t_POL */
static GEN
QabX_to_Flx(GEN A, ulong r, ulong p)
{
  long i, l = lg(A);
  GEN a = cgetg(l, t_VECSMALL);
  a[1] = ((ulong)A[1])&VARNBITS;
  for (i = 2; i < l; i++) uel(a,i) = Qab_to_Fl(gel(A,i), r, p);
  return Flx_renormalize(a, l);
}

/* M matrix with coeff in Q(\chi)), where Q(\chi) = Q(X)/(P) for
 * P = cyclotomic Phi_n. Assume M rational if n <= 2 */
static GEN
QabM_ker(GEN M, GEN P, long n)
{
  GEN B;
  if (n <= 2)
    B = ZM_ker(Q_primpart(M));
  else
    B = ZabM_ker(Q_primpart(lift_shallow(M)), P, n);
  return vec_Q_primpart(B);
}
/* pseudo-inverse of M */
static GEN
QabM_pseudoinv(GEN M, GEN P, long n, GEN *pv, GEN *pden)
{
  GEN cM, Mi;
  if (n <= 2)
  {
    M = Q_primitive_part(M, &cM);
    Mi = ZM_pseudoinv(M, pv, pden); /* M^(-1) = Mi / (cM * den) */
  }
  else
  {
    M = Q_primitive_part(lift_shallow(M), &cM);
    Mi = ZabM_pseudoinv(M, P, n, pv, pden);
    Mi = gmodulo(Mi, P);
  }
  *pden = mul_content(*pden, cM);
  return Mi;
}

/*******************************************************************/
/*   Relative trace between cyclotomic fields (TODO: export this)  */
/*******************************************************************/
/* g * prod_{p | g, (p,q) = 1} (1-1/p) */
static long
phipart(long g, long q)
{
  long i, l;
  GEN P;
  if (g == 1) return 1;
  P = gel(myfactoru(g), 1);
  l = lg(P);
  for (i = 1; i < l; i++)
  {
    long p = P[i];
    if (q % p) g -= g / p;
  }
  return g;
}

/* Trace(zeta_n^k) from Q(\zeta_n) to Q; k > 0 */
static GEN
tracerelzQ(long n, long k)
{
  long s, g = cgcd(k, n), q = n/g, muq = moebiusu(q);
  if (!muq) return gen_0;
  s = phipart(g, q); if (muq < 0) s = -s;
  return stoi(s);
}
/* Trace(zeta_n^k) from Q(\zeta_n) to Q(\zeta_m) with m|n; k > 0 */
static GEN
tracerelz(long n, long m, long k, long vt)
{
  long s, d, g, q, muq, v;
  GEN S;

  if (m == 1) return tracerelzQ(n, k);
  d = n / m;
  g = cgcd(k, d);
  q = d / g; if (cgcd(q, m) > 1) return gen_0;
  muq = moebiusu(q); if (!muq) return gen_0;
  k /= g;
  /* (m,q) = 1 */
  s = phipart(g, m*q); if (muq < 0) s = -s;
  v = Fl_inv(q % m, m);
  v = (v*k) % m;
  S = mygmodulo_lift(v, m, stoi(s));
  if (typ(S) == t_POL) setvarn(S, vt);
  return S;
}
/* x a t_POL modulo Phi_n; n, m not 2 mod 4, degrel != 1*/
static GEN
tracerel_i(GEN T, GEN x)
{
  long k, l = lg(x);
  GEN S = gen_0;
  for (k = 2; k < l; k++) S = gadd(S, gmul(gel(T,k-1), gel(x,k)));
  return S;
}
/* m | n, both not 2 mod 4 */
static GEN
Qab_trace_init(long n, long m)
{
  GEN T, Pn, Pm;
  long i, d, vt = fetch_user_var("t");
  Pn = polcyclo(n, vt);
  if (m == n) return mkvec(Pn);
  d = degpol(Pn);
  Pm = polcyclo(m, vt);
  T = cgetg(d+1, t_VEC);
  gel(T,1) = utoipos(d / degpol(Pm)); /* Tr 1 */
  for (i = 1; i < d; i++) gel(T,i+1) = tracerelz(n, m, i, vt);
  return mkvec3(Pm, Pn, T);
}
/* v = Qab_trace_init(n,m); x is a t_VEC of polmodulo Phi_n
 * Tr_{Q(zeta_n)/Q(zeta_m)} (zeta_n^t * x) */
static GEN
QabV_tracerel(GEN v, long t, GEN x)
{
  long d, dm, lx, j, degrel;
  GEN y, z, Pm, Pn, T;
  if (lg(v) != 4) return x;
  y = cgetg_copy(x, &lx);
  Pm = gel(v,1);
  Pn = gel(v,2);
  T  = gel(v,3);
  d = degpol(Pn);
  dm = degpol(Pm); degrel = d / dm;
  z = RgX_rem(monomial(gen_1, t, varn(Pn)), Pn);
  for (j = 1; j < lx; j++)
  {
    GEN a = liftpol_shallow(gel(x,j));
    a = simplify_shallow( gmul(a, z) );
    if (typ(a) == t_POL)
    {
      a = gdivgs(tracerel_i(T, RgX_rem(a, Pn)), degrel);
      if (typ(a) == t_POL) a = RgX_rem(a, Pm);
    }
    gel(y,j) = a;
  }
  return y;
}

/*********************************************************************/
/*                    Simple arithmetic functions                    */
/*********************************************************************/
/* TODO: most of these should be exported and used in ifactor1.c */
/* phi(n) */
static ulong
myeulerphiu(ulong n)
{
  pari_sp av;
  GEN fa;
  if (n == 1) return 1;
  av = avma; fa = myfactoru(n);
  avma = av; return eulerphiu_fact(fa);
}

/* N\prod_{p|N} (1+1/p) */
static long
mypsiu(ulong N)
{
  pari_sp av = avma;
  GEN P = gel(myfactoru(N), 1);
  long j, l = lg(P), res = N;
  for (j = 1; j < l; ++j) res += res/P[j];
  avma = av; return res;
}

/* write -n = Df^2, D < 0 fundamental discriminant. Return D, set f. */
static long
mycoredisc2u(ulong n, long *pf)
{
  pari_sp av = avma;
  GEN fa = myfactoru(n), P = gel(fa,1), E = gel(fa,2);
  long i, l = lg(P), m = 1, f = 1;
  for (i = 1; i < l; i++)
  {
    long j, p = P[i], e = E[i];
    if (e & 1) m *= p;
    for (j = 2; j <= e; j+=2) f *= p;
  }
  if ((m&3L) != 3) { m <<= 2; f >>= 1; }
  avma = av; *pf = f; return -m;
}

static long
mubeta(long n)
{
  pari_sp av = avma;
  GEN E = gel(myfactoru(n), 2);
  long i, s = 1, l = lg(E);
  for (i = 1; i < l; ++i)
  {
    long e = E[i];
    if (e >= 3) { avma = av; return 0; }
    if (e == 1) s *= -2;
  }
  avma = av; return s;
}

/* n = n1*n2, n1 = ppo(n, m); return mubeta(n1)*moebiusu(n2).
 * N.B. If n from newt_params we, in fact, never return 0 */
static long
mubeta2(long n, long m)
{
  pari_sp av = avma;
  GEN fa = myfactoru(n), P = gel(fa,1), E = gel(fa,2);
  long i, s = 1, l = lg(P);
  for (i = 1; i < l; i++)
  {
    long p = P[i], e = E[i];
    if (m % p)
    { /* p^e in n1 */
      if (e >= 3) { avma = av; return 0; }
      if (e == 1) s *= -2;
    }
    else
    { /* in n2 */
      if (e >= 2) { avma = av; return 0; }
      s = -s;
    }
  }
  avma = av; return s;
}

/* write N = prod p^{ep} and n = df^2, d squarefree.
 * set g  = ppo(gcd(sqfpart(N), f), FC)
 *     N2 = prod p^if(e==1 || p|n, ep-1, ep-2) */
static void
newt_params(long N, long n, long FC, long *pg, long *pN2)
{
  GEN fa = myfactoru(N), P = gel(fa,1), E = gel(fa,2);
  long i, g = 1, N2 = 1, l = lg(P);
  for (i = 1; i < l; i++)
  {
    long p = P[i], e = E[i];
    if (e == 1)
    { if (FC % p && n % (p*p) == 0) g *= p; }
    else
      N2 *= upowuu(p,(n % p)? e-2: e-1);
  }
  *pg = g; *pN2 = N2;
}
/* simplified version of newt_params for n = 1 (newdim) */
static void
newd_params(long N, long *pN2)
{
  GEN fa = myfactoru(N), P = gel(fa,1), E = gel(fa,2);
  long i, N2 = 1, l = lg(P);
  for (i = 1; i < l; i++)
  {
    long p = P[i], e = E[i];
    if (e > 2) N2 *= upowuu(p, e-2);
  }
  *pN2 = N2;
}

static long
newd_params2(long N)
{
  GEN fa = myfactoru(N), P = gel(fa,1), E = gel(fa,2);
  long i, N2 = 1, l = lg(P);
  for (i = 1; i < l; i++)
  {
    long p = P[i], e = E[i];
    if (e >= 2) N2 *= upowuu(p, e);
  }
  return N2;
}

/* TODO: export, together with numdivu */
static long
numdivu_fact(GEN E)
{
  long S = 1, i, l = lg(E);
  for (i = 1; i < l; i++) S *= E[i] + 1;
  return S;
}
static long
mynumdivu(long N)
{
  pari_sp av = avma;
  GEN E = gel(myfactoru(N), 2);
  long S = numdivu_fact(E);
  avma = av; return S;
}

/*              Operations on Dirichlet characters                       */

/* A Dirichlet character can be given in GP in different formats, but in this
 * package, it will be a vector CHI=[G,chi,ord], where G is the (Z/MZ)^* to
 * which the character belongs, chi is the character in Conrey format, ord is
 * the order */

static GEN
gmfcharorder(GEN CHI) { return gel(CHI, 3); }
static long
mfcharorder(GEN CHI) { return itou(gmfcharorder(CHI)); }
static long
mfcharistrivial(GEN CHI) { return !CHI || mfcharorder(CHI) == 1; }
static long
mfcharmodulus(GEN CHI) { return itos(gmael3(CHI, 1, 1, 1)); }

/* t^k mod polcyclo(ord) */
static GEN
mygmodulo(long k, long ord)
{
  long vt;
  GEN C;
  if (!k || ord == 1) return gen_1;
  if ((k << 1) == ord) return gen_m1;
  vt = fetch_user_var("t");
  if ((ord&3L) != 2)
    C = gen_1;
  else
  {
    ord >>= 1;
    if (odd(k)) { C = gen_m1; k += ord; } else C = gen_1;
    k >>= 1;
  }
  return gmodulo(monomial(C, k, vt), polcyclo(ord, vt));
}
static long
ord_canon(long ord)
{
  if ((ord & 3L) == 2) ord >>= 1;
  return ord;
}
static GEN
mygmodulo_mod(GEN z, long ord)
{
  long vt;
  if (typ(z) != t_POL) return z;
  vt = fetch_user_var("t");
  setvarn(z, vt);
  return gmodulo(z, polcyclo(ord_canon(ord), vt));
}
/* C*zeta_ord^k */
static GEN
mygmodulo_lift(long k, long ord, GEN C)
{
  if (!k) return C;
  if ((k << 1) == ord) return gneg(C);
  if ((ord&3L) == 2)
  {
    if (odd(k)) { C = gneg(C); k += ord >> 1; }
    k >>= 1;
  }
  return monomial(C,k,0);
}

static long
znchareval_i(GEN CHI, long n, GEN ord)
{ return itos(znchareval(gel(CHI,1), gel(CHI,2), stoi(n), ord)); }

/* CHI mod N = \prod_p p^e, (n,N) = 1; let CHI = \prod CHI_p, CHI_p mod p^e
 * return CHI_p; p a prime. CHI primitive <=> CHI_p primitive for all p */
static GEN
mfcharp(GEN CHI, long p)
{
  GEN G = gel(CHI,1), c = gel(CHI,2);
  GEN cp = NULL, P, E, F = znstar_get_faN(G); /* factor(N) */
  long l = lg(c), i;
  P = gel(F,1); /* prime divisors of N */
  E = gel(F,2); /* exponents */
  if (p == 2 && E[1] >= 3)
  {
    cp = mkcol2(gel(c,1), gel(c,2));
    if (l > 3) G = znstar0(int2n(E[1]),1);
  }
  else
  {
    for (i = 1; i < l; i++)
      if (equaliu(gel(P,i), p)) { cp = mkcol(gel(c,i)); break; }
    if (l > 2) G = znstar0(powuu(p, E[i]),1);
  }
  return mkvec3(G, cp, zncharorder(G, cp));
}

static GEN
mfchar2char(GEN CHI)
{
  if (typ(CHI) != t_VEC) return znchar(CHI);
  else return mkvec2(gel(CHI,1), gel(CHI,2));
}

/* G a znstar, L a Conrey log: return a 'mfchar' */
static GEN
mfcharGL(GEN G, GEN L) { return mkvec3(G, L, zncharorder(G,L)); }
static GEN
mfchartrivial(long N)
{
  GEN G = znstar0(utoi(N), 1);
  GEN L = zerocol(lg(znstar_get_cyc(G))-1);
  return mkvec3(G, L, gen_1);
}
/* convert a generic character into an 'mfchar' */
static GEN
get_mfchar(GEN CHI)
{
  GEN G, L;
  if (typ(CHI) != t_VEC)
    CHI = znchar(CHI);
  else if (lg(CHI) != 3 || !checkznstar_i(gel(CHI,1)))
    pari_err_TYPE("checkNF [chi]", CHI);
  G = gel(CHI,1);
  L = gel(CHI,2); if (typ(L) != t_COL) L = znconreylog(G,L);
  return mfcharGL(G, L);
}
/* parse [N], [N,k], [N,k,CHI]. If 'joker' is set, allow wildcard for CHI */
static void
checkNK(GEN NK, long *aN, long *ak, GEN *aCHI, int joker)
{
  GEN CHI, T;
  long l = lg(NK), N, k;
  if (typ(NK) != t_VEC || l < 3 || l > 4) pari_err_TYPE("checkNK", NK);
  T = gel(NK,1); if (typ(T) != t_INT) pari_err_TYPE("checkNF [N]", NK);
  *aN = N = itos(T);
  T = gel(NK,2); if (typ(T) != t_INT) pari_err_TYPE("checkNF [k]", NK);
  *ak = k = itos(T);
  if (l == 3)
    CHI = mfchartrivial(N);
  else
  {
    long i, l;
    CHI = gel(NK,3); l = lg(CHI);
    if (isintzero(CHI) && joker)
      CHI = NULL; /* all character orbits */
    else if (isintm1(CHI) && joker > 1)
      CHI = gen_m1; /* sum over all character orbits */
    else if ((typ(CHI) == t_VEC &&
             (l == 1 || l != 3 || !checkznstar_i(gel(CHI,1)))) && joker)
    {
      CHI = shallowtrans(CHI); /* list of characters */
      for (i = 1; i < l; i++) gel(CHI,i) = get_mfchar(gel(CHI,i));
    }
    else
    {
      CHI = get_mfchar(CHI); /* single char */
      if (N % mfcharmodulus(CHI)) pari_err_TYPE("checkNF [chi]", NK);
    }
  }
  *aCHI = CHI;
}

static GEN
mfchargalois(long N, int odd, GEN flagorder)
{
  GEN G = znstar0(utoi(N), 1), L = znchargalois(G, flagorder);
  long l = lg(L), i, j;
  for (i = j = 1; i < l; i++)
    if (zncharisodd(G,gel(L,i)) == odd) gel(L,j++) = mfcharGL(G,gel(L,i));
  setlg(L, j); return L;
}

/* wrappers from mfchar to znchar */
static long
mfcharparity(GEN CHI)
{
  if (!CHI) return 1;
  return zncharisodd(gel(CHI,1), gel(CHI,2)) ? -1 : 1;
}
/* if CHI is primitive, return CHI itself, not a copy */
static GEN
mfchartoprimitive(GEN CHI, long *pF)
{
  pari_sp av;
  GEN G0, chi0, F;
  if (!CHI) { if (pF) *pF = 1; return mfchartrivial(1); }
  av = avma; F = znconreyconductor(gel(CHI,1), gel(CHI,2), &chi0);
  if (typ(F) == t_INT) avma = av;
  else
  {
    G0 = znstar0(F, 1);
    CHI = gerepilecopy(av, mkvec3(G0, chi0, gmfcharorder(CHI)));
  }
  if (pF) *pF = mfcharmodulus(CHI);
  return CHI;
}
static long
mfcharconductor(GEN CHI)
{
  pari_sp ltop = avma;
  GEN res = znconreyconductor(gel(CHI,1), gel(CHI,2), NULL);
  long FC;
  if (typ(res) == t_VEC) res = gel(res, 1);
  FC = itos(res); avma = ltop; return FC;
}

#if 0
/* let CHI mod N, Q || N, return CHI_Q / CHI_{N/Q} */
static GEN
zncharAL(GEN CHI, long Q)
{
  GEN G = gel(CHI,1), c = gel(CHI,2);
  GEN d, P, E, F = znstar_get_faN(G); /* factor(N) */
  long l = lg(c), N = mfcharmodulus(CHI), i;

  if (N == Q) return CHI;
  d = leafcopy(c);
  P = gel(F,1); /* prime divisors of N */
  E = gel(F,2); /* exponents */
  if (equaliu(gel(P,1), 2) && odd(Q) && E[1] >= 3)
  {
    gel(d,1) = negi(gel(d,1));
    gel(d,2) = negi(gel(d,2));
  }
  else
  {
    for (i = 1; i < l; i++)
      if (umodui(Q, gel(P,i))) { gel(d,i) = negi(gel(d,i)); break; }
  }
  return mkvec3(G, d, gel(CHI,3));
}
GEN
mfcharAL(GEN CHI, long Q)
{
  pari_sp ltop = avma;
  return gerepileupto(ltop, mfchartoprimitive(zncharAL(CHI, Q), NULL));
}
#endif

/* n coprime with the modulus of CHI */
static GEN
mfchareval_i(GEN CHI, long n)
{
  GEN ordg = gmfcharorder(CHI);
  long ord = itos(ordg);
  if (ord == 1) return gen_1;
  return mygmodulo(znchareval_i(CHI, n, ordg), ord);
}
static GEN
mfchareval(GEN CHI, long n)
{
  long N = mfcharmodulus(CHI);
  return (cgcd(N, n) > 1) ? gen_0 : mfchareval_i(CHI, n);
}
/* ordnew a multiple of ord(CHI) or 0 [use ord(CHI)]; n coprime with
 * char modulus; return CHI(n) in Z[\zeta_ordnew] */
static long
mfcharevalord(GEN CHI, long n, long ordnew)
{
  GEN ordg = gmfcharorder(CHI);
  if (equali1(ordg)) return 0;
  return znchareval_i(CHI, n, ordnew? utoi(ordnew): ordg);
}

static long
zncharisprimitive(GEN G, GEN chi)
{
  pari_sp av = avma;
  GEN res = znconreyconductor(G, chi, NULL);
  avma = av; return (typ(res) == t_INT);
}

static GEN
mfchardiv_i(GEN CHI1, GEN CHI2)
{
  GEN G1 = gel(CHI1,1), chi1 = gel(CHI1,2);
  GEN G2 = gel(CHI2,1), chi2 = gel(CHI2,2), G;
  long f1 = itou(znstar_get_N(G1));
  long f2 = itou(znstar_get_N(G2)), f = clcm(f1,f2);

  if      (f == f1) G = G1;
  else if (f == f2) G = G2;
  else G = znstar0(utoipos(f), 1);
  if (f != f1) chi1 = zncharinduce(G1, chi1, G);
  if (f != f2) chi2 = zncharinduce(G2, chi2, G);
  return mfcharGL(G, znchardiv(G, chi1, chi2));
}

/*                      Operations on mf closures                    */
static GEN
tagparams(long t) { return mkvec(mkvecsmall(t)); }
static GEN
lfuntag(long t, GEN x) { return mkvec2(mkvecsmall(t), x); }
static GEN
tag0(long t) { retmkvec(tagparams(t)); }
static GEN
tag(long t, GEN x) { retmkvec2(tagparams(t), x); }
static GEN
tag2(long t, GEN x, GEN y) { retmkvec3(tagparams(t), x,y); }
static GEN
tag3(long t, GEN x,GEN y,GEN z) { retmkvec4(tagparams(t), x,y,z); }
#if 0
static GEN
tag4(long t, GEN x, GEN y, GEN z, GEN a) { retmkvec5(tagparams(t), x,y,z,a); }
#endif
static GEN
tag5(long t, GEN x, GEN y, GEN z, GEN a, GEN b)
{ return mkvecn(6, tagparams(t), x,y,z,a,b); }
/* is F a "modular form" ? */
static long
isf(GEN F)
{ return (typ(F) == t_VEC
    && lg(F) > 1 && typ(gel(F,1)) == t_VEC
    && lg(gel(F,1)) > 1 && typ(gmael(F,1,1)) == t_VECSMALL); }
static long
f_type(GEN F) { return gmael(F,1,1)[1]; }

/* UTILITY FUNCTIONS */
/* given an mf closure, transform into vector or power series */
GEN
mftovecslice(GEN F, long a, long b)
{
  GEN V = mfcoefs(F, b, 1), v;
  long m, i;
  if (!a) return V;
  v = cgetg(b - a + 2, t_VEC);
  for (m = a, i = 1; m <= b; m++) gel(v, i++) = gel(V, m + 1);
  return v;
}

GEN
mftocol(GEN F, long lim)
{ GEN c = mfcoefs_i(F, lim, 1); settyp(c,t_COL); return c; }
GEN
mfvectomat(GEN vF, long lim)
{
  long j, l = lg(vF);
  GEN M = cgetg(l, t_MAT);
  for (j = 1; j < l; j++) gel(M,j) = mftocol(gel(vF,j), lim);
  return M;
}

static GEN
RgV_to_ser(GEN x, long v)
{
  long j, lx = lg(x);
  GEN y = cgetg(lx+1, t_SER);
  y[1] = evalvarn(v)|evalvalp(0);
  x--;
  for (j = 2; j <= lx; ++j) gel(y, j) = gel(x, j);
  return normalize(y);
}

/* TODO: delete */
static GEN
mfcoefsser(GEN F, long n, long d) { return RgV_to_ser(mfcoefs_i(F, n,d), 0); }

static GEN
sertovecslice(GEN S, long n)
{
  GEN tmp = gtovec0(S, -(lg(S) - 2 + valp(S))), res;
  long i, lt = lg(tmp), n2 = n + 2;
  if (lt < n2) pari_err_BUG("sertovecslice [n too large]");
  if (lt == n2) return tmp;
  res = cgetg(n2, t_VEC);
  for (i = 1; i < n2; ++i) gel(res, i) = gel(tmp, i);
  return res;
}

/* a, b two RgV of the same length, multiply as truncated power series */
static GEN
RgV_mul_RgXn(GEN a, GEN b)
{
  long n = lg(a)-1;
  GEN c;
  a = RgV_to_RgX(a,0);
  b = RgV_to_RgX(b,0); c = RgXn_mul(a,b,n);
  c = RgX_to_RgC(c,n); settyp(c,t_VEC); return c;
}
static GEN
RgV_pows_RgXn(GEN a, long b)
{
  long n = lg(a)-1;
  GEN c;
  a = RgV_to_RgX(a,0);
  if (b < 0) { a = RgXn_inv(a, n); b = -b; }
  c = RgXn_powu_i(a,b,n);
  c = RgX_to_RgC(c,n); settyp(c,t_VEC); return c;
}

static GEN
c_mul(long n, long d, GEN F, GEN G)
{
  pari_sp av = avma;
  long nd = n*d;
  GEN VF = mfcoefs_i(F, nd, 1);
  GEN VG = mfcoefs_i(G, nd, 1);
  return gerepilecopy(av, c_deflate(n, d, RgV_mul_RgXn(VF,VG)));
}
static GEN
c_pow(long n, long d, GEN F, GEN a)
{
  pari_sp av = avma;
  long nd = n*d;
  GEN f = RgV_pows_RgXn(mfcoefs_i(F,nd,1), itos(a));
  return gerepilecopy(av, c_deflate(n, d, f));
}

static GEN
c_mulRC(long n, long d, GEN F, GEN G, GEN gm)
{
  pari_sp av = avma;
  long i, nd = n*d;
  GEN VF = mfcoefs_i(F, nd, 1), tF = cgetg(nd+2, t_VEC);
  GEN VG = mfcoefs_i(G, nd, 1), tG = cgetg(nd+2, t_VEC);
  GEN C, mpow, res = NULL, P;
  ulong j, k, l, m = itos(gm);
  P = mfparams_ii(F); if (!P) pari_err_IMPL("mfbracket for this form");
  k = itos(gel(P, 2));
  P = mfparams_ii(G); if (!P) pari_err_IMPL("mfbracket for this form");
  l = itos(gel(P, 2));
  /* pow[i,j+1] = i^j */
  mpow = cgetg(m+2, t_MAT);
  gel(mpow,1) = const_col(nd, gen_1);
  for (j = 1; j <= m; j++)
  {
    GEN c = cgetg(nd+1, t_COL);
    gel(mpow,j+1) = c;
    for (i = 1; i <= nd; i++) gel(c,i) = muliu(gcoeff(mpow,i,j), i);
  }
  C = binomialuu(m+k-1, m);
  for (j = 0; j <= m; j++)
  { /* C = (-1)^j binom(m+l-1, j) binom(m+k-1,m-j) */
    GEN c;
    gel(tF,1) = j == 0? gel(VF,1): gen_0;
    gel(tG,1) = j == m? gel(VG,1): gen_0;
    for (i = 1; i <= nd; i++)
    {
      gel(tF, i+1) = gmul(gcoeff(mpow,i,j+1),   gel(VF, i+1));
      gel(tG, i+1) = gmul(gcoeff(mpow,i,m-j+1), gel(VG, i+1));
    }
    c = gmul(C, c_deflate(n, d, RgV_mul_RgXn(tF, tG)));
    res = res? gadd(res, c): c;
    if (j < m)
    {
      C = diviuexact(muliu(C, (m-j+l-1)*(m-j)), (j+1)*(j+k));
      togglesign_safe(&C);
    }
  }
  return gerepileupto(av, res);
}
/* linear combination \sum L[j] vecF[j] */
static GEN
c_linear(long n, long d, GEN F, GEN L)
{
  pari_sp av = avma;
  GEN S = gen_0, con;
  long j, l = lg(L);
  if (l == 1) return zerovec(n + 1);
  L = Q_primitive_part(L, &con);
  for (j = 1; j < l; ++j)
  {
    GEN tmp = gel(L, j);
    if (!gequal0(tmp)) tmp = gmul(tmp, mfcoefs_i(gel(F, j), n, d));
    else tmp = zerovec(n + 1);
    S = j == 1 ? tmp : gadd(S, tmp);
  }
  if (con) S = gmul(S, con);
  return gerepileupto(av, S);
}

/* t_MF_BD(t_MF_HECKE(t_MF_NEWTRACE)) or
 * t_MF_HECKE(t_MF_NEWTRACE)
 * or t_MF_NEWTRACE */
static void
bhn_parse(GEN tf, long *d, long *j, long *N, long *k, GEN *DATA)
{
  GEN Nk;
  long t = f_type(tf);
  *d = *j = 1;
  if (t == t_MF_BD)
  {
    *d = itos(gel(tf,2));
    tf = gel(tf,3);
    t = f_type(tf);
  }
  if (t == t_MF_HECKE)
  {
    *j = gel(tf,2)[2];
    tf = gel(tf,4);
  }
  Nk = gel(tf,2);
  *N = Nk[1];
  *k = Nk[2];
  *DATA = gel(tf,3);
}
static int
newtrace_stripped(GEN DATA)
{ return lg(DATA) == 4 && typ(gel(DATA, 3)) == t_INT; }
static GEN
newtrace_DATA(long N, GEN DATA)
{ return (newtrace_stripped(DATA))? initnewtrace(N, DATA): DATA; }
/* F not empty, same hypotheses as bhnmat_extend */
static GEN
bhnmat_extend_nocache(GEN M, long n, long d, GEN F)
{
  long Bd, j, N, k;
  cachenew_t cache;
  GEN DATA; /* F[#F-1] has largest level */
  bhn_parse(gel(F,lg(F)-1), &Bd,&j, &N,&k, &DATA);
  DATA = newtrace_DATA(N, DATA);
  init_cachenew(&cache, n*d, DATA);
  M = bhnmat_extend(M, n, d, F, &cache);
  dbg_cachenew(&cache);
  return M;
}
/* c_linear of "bhn" mf closures, same hypotheses as bhnmat_extend */
static GEN
c_linear_bhn(long n, long d, GEN F, GEN L)
{
  pari_sp av;
  GEN M, v;
  if (lg(L) == 1) return zerovec(n+1);
  av = avma;
  M = bhnmat_extend_nocache(NULL, n, d, F);
  v = RgM_RgC_mul(M,L); settyp(v, t_VEC);
  return gerepileupto(av, v);
}

/* c in K, K := Q[X]/(T) vz = vector of consecutive powers of root z of T
 * attached to an embedding s: K -> C. Return s(c) in C */
static GEN
Rg_embed(GEN c, GEN vz)
{
  long t = typ(c);
  if (t == t_POLMOD) { c = gel(c,2); t = typ(c); }
  if (t == t_POL) c = RgX_RgV_eval(c, vz);
  return c;
}
/* return s(P) in C[X] */
static GEN
RgX_embed(GEN P, GEN vz)
{
  long i, l;
  GEN Q = cgetg_copy(P, &l);
  Q[1] = P[1];
  for (i = 2; i < l; i++) gel(Q,i) = Rg_embed(gel(P,i), vz);
  return normalizepol_lg(Q,l); /* normally a no-op */
}
/* return s(P) in C^n */
static GEN
RgC_embed(GEN P, GEN vz)
{
  long i, l;
  GEN Q = cgetg_copy(P, &l);
  for (i = 1; i < l; i++) gel(Q,i) = Rg_embed(gel(P,i), vz);
  return Q;
}
/* P in L = K[X]/(U), K = Q[t]/T; s an embedding of K -> C attached
 * to a root of T, extended to an embedding of L -> C attached to a root
 * of s(U); vT powers of the root of T, vU powers of the root of s(U).
 * Return s(P) in C^n */
static GEN
Rg_embed2(GEN P, long vt, GEN vT, GEN vU)
{
  long i, l;
  GEN Q;
  P = liftpol_shallow(P);
  if (typ(P) != t_POL) return P;
  if (varn(P) == vt) return Rg_embed(P, vT);
  /* varn(P) == vx */
  Q = cgetg_copy(P, &l); Q[1] = P[1];
  for (i = 2; i < l; i++) gel(Q,i) = Rg_embed(gel(P,i), vT);
  return Rg_embed(Q, vU);
}
static GEN
RgC_embed2(GEN P, long vt, GEN vT, GEN vU)
{
  long i, l;
  GEN Q = cgetg_copy(P, &l);
  for (i = 1; i < l; i++) gel(Q,i) = Rg_embed2(gel(P,i), vt, vT, vU);
  return Q;
}

static GEN
c_embed(long n, long d, GEN F, GEN vz)
{
  pari_sp av = avma;
  GEN f = mfcoefs_i(F, n, d);
  return gerepilecopy(av, RgC_embed(f, vz));
}
static GEN
c_div(long n, long d, GEN F, GEN G)
{
  pari_sp av = avma;
  GEN VF = mfcoefsser(F, n, d);
  GEN VG = mfcoefsser(G, n, d);
  GEN a0 = polcoeff_i(VG, 0, -1), a0i, H;
  if (gequal0(a0) || gequal1(a0)) a0 = a0i = NULL;
  else
  {
    a0i = ginv(a0);
    VG = gmul(ser_unscale(VG,a0), a0i);
    VF = gmul(ser_unscale(VF,a0), a0i);
  }
  H = gdiv(VF, VG);
  if (a0) H = ser_unscale(H,a0i);
  return gerepilecopy(av, sertovecslice(H, n));
}
static GEN
c_deflate(long n, long d, GEN V)
{
  GEN res;
  long i;
  if (d == 1) return V;
  res = cgetg(n + 2, t_VEC);
  for (i = 0; i <= n; ++i) gel(res, i + 1) = gel(V, i*d + 1);
  return res;
}

static GEN
c_shift(long n, long d, GEN F, GEN gsh)
{
  pari_sp av = avma;
  GEN tmp;
  long sh = itos(gsh), n1 = n*d + sh;
  if (n1 < 0) return zerovec(n + 1);
  tmp = mfcoefs_i(F, n1, 1);
  if (sh < 0) tmp = concat(zerovec(-sh), tmp);
  else tmp = vecslice(tmp, sh + 1, n1 + 1);
  return gerepilecopy(av, c_deflate(n, d, tmp));
}

static GEN
c_deriv(long n, long d, GEN F, GEN gm)
{
  pari_sp av = avma;
  GEN V = mfcoefs_i(F, n, d), res;
  long i, m = itos(gm);
  if (m < 0) return c_integ(n, d, F, stoi(-m));
  if (m == 0) return V;
  res = cgetg(n+2, t_VEC); gel(res, 1) = gen_0;
  for (i = 1; i <= n; i++) gel(res, i+1) = gmulsg(upowuu(i,m), gel(V,i+1));
  return gerepileupto(av, res);
}

static GEN
c_derivE2(long n, long d, GEN F, GEN gm)
{
  pari_sp av = avma;
  GEN VF, VE, res, tmp, gk, P;
  long i, m = itos(gm), nd;
  if (m == 0) return mfcoefs_i(F, n, d);
  nd = n*d;
  VF = mfcoefs_i(F, nd, 1); VE = mfcoefs_i(mfEk(2), nd, 1);
  P = mfparams_ii(F);
  if (!P) pari_err_IMPL("mfderivE2 for this form");
  gk = gel(P, 2);
  if (m == 1)
  {
    res = cgetg(n+2, t_VEC);
    for (i = 0; i <= n; i++) gel(res, i+1) = gmulsg(i, gel(VF, i*d+1));
    tmp = c_deflate(n, d, RgV_mul_RgXn(VF, VE));
    return gerepileupto(av, gsub(res, gmul(gdivgs(gk, 12), tmp)));
  }
  else
  {
    long j;
    for (j = 1; j <= m; ++j)
    {
      tmp = RgV_mul_RgXn(VF, VE);
      for (i = 0; i <= nd; i++) gel(VF, i+1) = gmulsg(i, gel(VF, i+1));
      VF = gsub(VF, gmul(gdivgs(gaddgs(gk, 2*(j-1)), 12), tmp));
    }
    return gerepilecopy(av, c_deflate(n, d, VF));
  }
}

static GEN
c_integ(long n, long d, GEN F, GEN gm)
{
  pari_sp av = avma;
  GEN V = mfcoefs_i(F, n, d), res;
  long i, m = itos(gm);
  if (m < 0) return c_deriv(n, d, F, stoi(-m));
  if (m == 0) return V;
  res = cgetg(n + 2, t_VEC); gel(res, 1) = gen_0;
  for (i = 1; i <= n; ++i)
    gel(res, i + 1) = gdivgs(gel(V, i + 1), upowuu(i, m));
  return gerepileupto(av, res);
}
/* Twist by the character (D/.) */
static GEN
c_twist(long n, long d, GEN F, GEN D)
{
  pari_sp av = avma;
  GEN V = mfcoefs_i(F, n, d), res = cgetg(n + 2, t_VEC);
  long i;
  for (i = 0; i <= n; ++i)
    gel(res, i + 1) = gmulsg(krois(D, i), gel(V, i + 1));
  return gerepileupto(av, res);
}

/* form F given by closure, compute T(n)(F) as closure */
static GEN
c_hecke(long m, long l, GEN knN, GEN CHI, GEN F)
{
  pari_sp av = avma;
  return gerepilecopy(av, hecke_i(m, l, knN, CHI, F));
}
static GEN
c_const(long n, long d, GEN C)
{
  GEN V = zerovec(n+1);
  long i, j, l = lg(C);
  if (l > d*n+2) l = d*n+2;
  for (i = j = 1; i < l; i+=d, j++) gel(V, j) = gcopy(gel(C,i));
  return V;
}

static GEN
eta3_ZXn(long m)
{
  long l = m+2, n, k;
  GEN P = cgetg(l,t_POL);
  P[1] = evalsigne(1)|evalvarn(0);
  for (n = 2; n < l; n++) gel(P,n) = gen_0;
  for (n = k = 0;; n++)
  {
    k += n; if (k >= m) break;
    /* now k = n(n+1) / 2 */
    gel(P, k+2) = odd(n)? utoineg(2*n+1): utoipos(2*n+1);
  }
  return P;
}

static GEN
c_delta(long n, long d)
{
  pari_sp ltop = avma;
  long N = n*d;
  GEN e = eta3_ZXn(N);
  /* FIXME: can't use RgXn_sqr if we want FFT */
  e = RgXn_red_shallow(ZX_sqr(e), N);
  e = RgXn_red_shallow(ZX_sqr(e), N);
  e = RgXn_red_shallow(ZX_sqr(e), N); /* eta(x)^24 */
  settyp(e, t_VEC);
  gel(e,1) = gen_0; /* Delta(x) = x*eta(x)^24 as a t_VEC */
  return gerepilecopy(ltop, c_deflate(n, d, e));
}

static GEN
c_etaquo(long n, long d, GEN eta, GEN gs)
{
  pari_sp av = avma;
  GEN B = gel(eta,1), E = gel(eta,2), c = gen_1;
  long i, s = itos(gs), nd = n*d, nds = nd - s + 1, l = lg(B);
  for (i = 1; i < l; i++) c = gmul(c, gpowgs(eta_inflate_ZXn(nds, B[i]), E[i]));
  if (s > 0) c = gmul(c, gpowgs(pol_x(0), s));
  return gerepilecopy(av, c_deflate(n, d, sertovecslice(c, nd)));
}

static GEN
c_cusptrace(long n, long d, GEN Nk, GEN D)
{
  GEN res = cgetg(n+2, t_VEC);
  long i;
  gel(res, 1) = gen_0;
  for (i = 1; i <= n; i++) gel(res, i+1) = mfcusptrace_i(Nk[1], Nk[2], i*d, D);
  return res;
}

static GEN
c_newtrace(long n, long d, GEN Nk, GEN D)
{
  pari_sp av = avma;
  cachenew_t cache;
  long N = Nk[1], k = Nk[2];
  GEN v;
  D = newtrace_DATA(N, D);
  init_cachenew(&cache, n*d, D);
  v = colnewtrace(0, n, d, N, k, &cache);
  settyp(v, t_VEC); return gerepilecopy(av, v);
}

static GEN
c_Bd(long n, long l, GEN D, GEN F)
{
  pari_sp av = avma;
  long d = itou(D), dl = cgcd(d,l), ddl = d/dl, i, j;
  GEN w, v = mfcoefs_i(F, n/ddl, l/dl);
  if (d == 1) return v;
  n++; w = zerovec(n);
  for (i = j = 0; j < n; i++, j += ddl) gel(w, j+1) = gcopy(gel(v, i+1));
  return gerepileupto(av, w);
}

static GEN
c_heckeU(long n, long l, GEN d, GEN F)
{ return mfcoefs_i(F, n, itos(d)*l); }

static GEN
c_closure(long n, long d, GEN F)
{
  GEN v;
  if (closure_arity(F) == 1)
  {
    long i;
    v = cgetg(n+2, t_VEC);
    for (i = 0; i <= n; i++) gel(v, i+1) = closure_callgen1(F, utoi(i*d));
  }
  else
  {
    v = closure_callgen2(F, utoi(n), utoi(d));
    if (typ(v) != t_VEC) pari_err_TYPE("mfcoefs [from closure]",v);
    if (lg(v) != n+2) pari_err_TYPE("mfcoefs [from closure, wrong dimension]",v);
  }
  return v;
}

static GEN
c_dihedral(long n, long d, GEN bnr, GEN w, GEN Tinit, GEN k0j)
{
  pari_sp av = avma;
  GEN V = dihan(bnr, w, Tinit, k0j, n*d);
  GEN Pm = gel(Tinit,1);
  GEN A = c_deflate(n, d, V);
  if (degpol(Pm) == 1 || RgX_is_QX(A)) return gerepilecopy(av, A);
  return gerepileupto(av, gmodulo(A, Pm));
}

static GEN
c_mfeisen(long n, long d, GEN F2, GEN F3)
{
  GEN v = cgetg(n+2, t_VEC), E0 = gel(F3,1), CHI = gel(F3,2);
  long i, k = F2[1];
  gel(v, 1) = gcopy(E0); /* E(0) */
  if (lg(F3) == 5)
  {
    long ord = F2[2], j = F2[3];
    GEN CHI2 = gel(F3,3), T = gel(F3,4);
    for (i = 1; i <= n; i++) gel(v, i+1) = sigchi2(k, CHI, CHI2, i*d, ord);
    if (lg(T) == 4) v = QabV_tracerel(T, j, v);
    if (lg(T) != 1 && !RgV_is_QV(v)) v = gmodulo(v, gel(T,1));
  }
  else
  {
    for (i = 1; i <= n; i++) gel(v, i+1) = sigchi(k, CHI, i*d);
  }
  return v;
}

static GEN
c_mfeisenm1m2(long n, long d, GEN NK, GEN E0)
{
  GEN res = cgetg(n + 2, t_VEC);
  long i, N = NK[1], k = NK[2], m1 = NK[3], m2 = NK[4];
  gel(res, 1) = gcopy(E0);
  for (i = 1; i <= n; ++i) gel(res, i+1) = GammaNsig(N, k, m1, m2, i*d);
  return res;
}

/* Returns vector of coeffs from F[0], F[d], ..., F[d*n] */
static GEN
mfcoefs_i(GEN F, long n, long d)
{
  if (n < 0) return gen_0;
  switch(f_type(F))
  {
    case t_MF_CONST: return c_const(n, d, gel(F,2));
    case t_MF_EISEN: return c_mfeisen(n, d, gel(F,2), gel(F,3));
    case t_MF_Ek: return c_Ek(n, d, gel(F,2)[1], gel(F,3));
    case t_MF_DELTA: return c_delta(n, d);
    case t_MF_ETAQUO: return c_etaquo(n, d, gel(F,2), gel(F,3));
    case t_MF_ELL: return c_deflate(n, d, concat(gen_0, anell(gel(F,2), n*d)));
    case t_MF_MUL: return c_mul(n, d, gel(F,2), gel(F,3));
    case t_MF_POW: return c_pow(n, d, gel(F,2), gel(F,3));
    case t_MF_MULRC: return c_mulRC(n, d, gel(F,2), gel(F,3), gel(F,4));
    case t_MF_LINEAR: return c_linear(n, d, gel(F,2), gel(F,3));
    case t_MF_LINEAR_BHN: return c_linear_bhn(n, d, gel(F,2), gel(F,3));
    case t_MF_DIV: return c_div(n, d, gel(F,2), gel(F,3));
    case t_MF_SHIFT: return c_shift(n, d, gel(F,2), gel(F,3));
    case t_MF_DERIV: return c_deriv(n, d, gel(F,2), gel(F,3));
    case t_MF_DERIVE2: return c_derivE2(n, d, gel(F,2), gel(F,3));
    case t_MF_INTEG: return c_integ(n, d, gel(F,2), gel(F,3));
    case t_MF_EMBED: return c_embed(n, d, gel(F,2), gel(F,3));
    case t_MF_TWIST: return c_twist(n, d, gel(F,2), gel(F,3));
    case t_MF_HECKE: return c_hecke(n, d, gel(F,2), gel(F,3), gel(F,4));
    case t_MF_BD: return c_Bd(n, d, gel(F,2), gel(F,3));
    case t_MF_TRACE: return c_cusptrace(n, d, gel(F,2), gel(F,3));
    case t_MF_NEWTRACE: return c_newtrace(n, d, gel(F,2), gel(F,3));
    case t_MF_CLOSURE: return c_closure(n, d, gel(F,2));
    case t_MF_DIHEDRAL: return c_dihedral(n,d,gel(F,2),gel(F,3),gel(F,4),gel(F,5));
    case t_MF_EISENM1M2: return c_mfeisenm1m2(n, d, gel(F,2), gel(F,3));
    case t_MF_HECKEU: return c_heckeU(n, d, gel(F,2), gel(F,3));
    default: pari_err_TYPE("mfcoefs",F);
    return NULL;/* not reached */
  }
}

GEN
mfcoefs(GEN F, long n, long d)
{
  if (!isf(F)) pari_err_TYPE("mfcoefs", F);
  if (d <= 0) pari_err_DOMAIN("mfcoefs", "d", "<=", gen_0, stoi(d));
  return mfcoefs_i(F, n, d);
}

static GEN
mfak_i(GEN F, long k) { return gel(mfcoefs_i(F, 1, k), 2); }
GEN
mfcoef(GEN F, long n)
{
  pari_sp av = avma;
  if (!isf(F)) pari_err_TYPE("mfcoef",F);
  return gerepilecopy(av, mfak_i(F, n));
}

static GEN
mftrivial(void) {
  GEN f = cgetg(3, t_VEC);
  gel(f,1) = tagparams(t_MF_CONST);
  gel(f,2) = cgetg(1,t_VEC); return f;
}
GEN
mfcreate(GEN x)
{
  pari_sp av = avma;
  long t = typ(x);
  if (typ(x) == t_CLOSURE)
  {
    long a = closure_arity(x);
    if (a == 1 || a == 2) return gerepilecopy(av, tag(t_MF_CLOSURE, x));
  }
  if (gequal0(x)) return mftrivial();
  if (is_scalar_t(t)) x = mkvec(x);
  else switch(t)
  {
    case t_VEC: break;
    case t_POL: x = RgX_to_RgC(x, degpol(x)+1); settyp(x, t_VEC); break;
    case t_SER: x = sertocol(x); break;
    default: pari_err_TYPE("mfcreate", x);
  }
  return gerepilecopy(av, tag(t_MF_CONST, x));
}

GEN
mfmul(GEN F, GEN G)
{
  pari_sp av = avma;
  if (!isf(F)) pari_err_TYPE("mfmul",F);
  if (!isf(G)) pari_err_TYPE("mfmul",G);
  return gerepilecopy(av, tag2(t_MF_MUL, F, G));
}
GEN
mfpow(GEN F, GEN n)
{
  pari_sp av = avma;
  if (!isf(F)) pari_err_TYPE("mfpow",F);
  if (typ(n) != t_INT) pari_err_TYPE("mfpow",n);
  if (!signe(n)) return mfcreate(gen_1);
  return gerepilecopy(av, tag2(t_MF_POW, F, n));
}
GEN
mfbracket(GEN F, GEN G, long m)
{
  pari_sp av = avma;
  return gerepilecopy(av, tag3(t_MF_MULRC, F, G, stoi(m)));
}

/* remove 0 entries in L */
static GEN
mflinear_strip(long t, GEN F, GEN L)
{
  pari_sp av = avma;
  long i, j, l = lg(L);
  GEN F2 = cgetg(l, t_VEC), L2 = cgetg(l, t_VEC);
  for (i = j = 1; i < l; i++)
  {
    if (gequal0(gel(L,i))) continue;
    gel(F2,j) = gel(F,i);
    gel(L2,j) = gel(L,i);
    j++;
  }
  if (j == l) avma = av;
  else
  {
    setlg(F2,j); F = F2;
    setlg(L2,j); L = L2;
  }
  return tag2(t, F, L);
}
static GEN
mflinear_i(GEN F, GEN L) { return mflinear_strip(t_MF_LINEAR, F,L); }
static GEN
mflinear_bhn(GEN F, GEN L) { return mflinear_strip(t_MF_LINEAR_BHN, F,L); }
GEN
mflinear(GEN F, GEN L)
{
  pari_sp av = avma;
  long lv = lg(F);
  if (typ(F) != t_VEC) pari_err_TYPE("mflinear",F);
  if (typ(L) != t_VEC) pari_err_TYPE("mflinear",L);
  if (lg(L) != lv) pari_err_DIM("mflinear");
  return gerepilecopy(av, mflinear_i(F,L));
}

/* Non empty linear combination of linear combinations of same, not checked */
/* F_j=\sum_i \mu_{i,j}G_i so R = \sum_i (\sum_j(\la_j\mu_{i,j})) G_i */
static GEN
mflinear_linear(GEN F, GEN L)
{
  long l = lg(F), j;
  GEN M = cgetg(l, t_MAT);
  for (j = 1; j < l; j++)
  {
    GEN f = gel(F,j), c = gel(f,3);
    if (typ(c) == t_VEC) c = shallowtrans(c);
    gel(M,j) = c;
  }
  return tag2(t_MF_LINEAR, gmael(F,1,2), RgM_RgC_mul(M,L));
}

GEN
mfshift(GEN F, long sh)
{
  pari_sp av = avma;
  return gerepilecopy(av, tag2(t_MF_SHIFT, F, stoi(sh)));
}
long
mfval(GEN F)
{
  pari_sp ltop = avma;
  long i = 0, k;
  for (k = 0; k <= 6; ++k)
  {
    long k2 = 1 << k;
    GEN tmp = mfcoefs(F, k2, 1);
    for (; i <= k2; ++i)
      if (!gequal0(gel(tmp, i + 1))) { avma = ltop; return i; }
  }
  avma = ltop; return 100;
}
GEN
mfdiv_val(GEN F, GEN G, long vG)
{
  if (vG) { F = mfshift(F,vG); G = mfshift(G,vG); }
  return tag2(t_MF_DIV, F, G);
}
GEN
mfdiv(GEN F, GEN G)
{
  pari_sp av = avma;
  long vG = mfval(G);
  if (vG == 100 || (vG && !gequal0(mfcoefs(F, vG-1, 1))))
    pari_err_DOMAIN("mfdiv", "ord(G)", ">", strtoGENstr("ord(F)"),
                    mkvec2(F, G));
  return gerepilecopy(av, mfdiv_val(F, G, vG));
}
GEN
mfderiv(GEN F, long m)
{
  pari_sp av = avma;
  if (!isf(F)) pari_err_TYPE("mfderiv",F);
  return gerepilecopy(av, tag2(t_MF_DERIV, F, stoi(m)));
}
GEN
mfderivE2(GEN F, long m)
{
  pari_sp av = avma;
  if (!isf(F)) pari_err_TYPE("mfderivE2",F);
  if (m < 0) pari_err_DOMAIN("mfderivE2","m","<",gen_0,stoi(m));
  return gerepilecopy(av, tag2(t_MF_DERIVE2, F, stoi(m)));
}

GEN
mfinteg(GEN F, long m)
{
  pari_sp av = avma;
  GEN a;
  if (!isf(F)) pari_err_TYPE("mfinteg",F);
  a = mfak_i(F, 0);
  if (!gequal0(a)) pari_err_DOMAIN("mfinteg", "F(0)", "!=", gen_0, a);
  return gerepilecopy(av, tag2(t_MF_INTEG, F, stoi(m)));
}
GEN
mftwist(GEN F, GEN D)
{
  pari_sp av = avma;
  return gerepilecopy(av, tag2(t_MF_TWIST, F, D));
}

/***************************************************************/
/*                 Generic cache handling                      */
/***************************************************************/
enum { cache_FACT, cache_DIV, cache_H, cache_DIH };
typedef struct {
  const char *name;
  GEN cache;
  ulong minself;
  ulong maxself;
  void (*init)(long);
  ulong miss;
  ulong maxmiss;
} cache;

static void constdiv(long lim);
static void consttabh(long lim);
static void consttabdihedral(long lim);
static THREAD cache caches[] = {
{ "Factors",  NULL,  50000,    50000, &constdiv, 0, 0 },
{ "Divisors", NULL,  50000,    50000, &constdiv, 0, 0 },
{ "H",        NULL, 100000, 10000000, &consttabh, 0, 0 },
{ "Dihedral", NULL,   1000,     3000, &consttabdihedral, 0, 0 },
};

static void
cache_reset(long id) { caches[id].miss = caches[id].maxmiss = 0; }
static void
cache_delete(long id) { if (caches[id].cache) gunclone(caches[id].cache); }
static void
cache_set(long id, GEN S)
{
  GEN old = caches[id].cache;
  caches[id].cache = gclone(S);
  if (old) gunclone(old);
}

/* handle a cache miss: store stats, possibly reset table; return value
 * if (now) cached; return NULL on failure. HACK: some caches contain an
 * ulong where the 0 value is impossible, and return it (typecase to GEN) */
static GEN
cache_get(long id, ulong D)
{
  cache *S = &caches[id];
  /* cache_H is compressed: D=0,1 mod 4 */
  const ulong d = (id == cache_H)? D>>1: D;
  ulong max, l;

  if (!S->cache)
  {
    max = maxuu(minuu(D, S->maxself), S->minself);
    S->init(max);
    l = lg(S->cache);
  }
  else
  {
    l = lg(S->cache);
    if (l <= d)
    {
      if (D > S->maxmiss) S->maxmiss = D;
      if (DEBUGLEVEL)
        err_printf("miss in cache %s: %lu, max = %lu\n",
                   S->name, D, S->maxmiss);
      if (S->miss++ >= 5 && D < S->maxself)
      {
        max = minuu(S->maxself, (long)(S->maxmiss * 1.2));
        if (max <= S->maxself)
        {
          if (DEBUGLEVEL)
            err_printf("resetting cache %s to %lu\n", S->name, max);
          S->init(max); l = lg(S->cache);
        }
      }
    }
  }
  return (l <= d)? NULL: gel(S->cache, d);
}
static GEN
cache_report(long id)
{
  cache *S = &caches[id];
  GEN v = zerocol(5);
  gel(v,1) = strtoGENstr(S->name);
  if (S->cache)
  {
    gel(v,2) = utoi(lg(S->cache)-1);
    gel(v,3) = utoi(S->miss);
    gel(v,4) = utoi(S->maxmiss);
    gel(v,5) = utoi(gsizebyte(S->cache));
  }
  return v;
}
GEN
getcache(void)
{
  pari_sp av = avma;
  GEN M = cgetg(5, t_MAT);
  gel(M,1) = cache_report(cache_FACT);
  gel(M,2) = cache_report(cache_DIV);
  gel(M,3) = cache_report(cache_H);
  gel(M,4) = cache_report(cache_DIH);
  return gerepilecopy(av, shallowtrans(M));
}

void
pari_close_mf(void)
{
  cache_delete(cache_DIH);
  cache_delete(cache_DIV);
  cache_delete(cache_FACT);
  cache_delete(cache_H);
}

/*************************************************************************/

static long
indexu(long y, long N)
{
  long x = y%N;
  return (x <= 0) ? x + N : x;
}

static void
constdiv(long lim)
{
  pari_sp av = avma;
  GEN VFACT0, VDIV0, VFACT = caches[cache_FACT].cache;
  long N, LIM = !VFACT ? 4 : lg(VFACT)-1;
  if (lim <= 0) lim = 5;
  if (lim <= LIM) return;
  cache_reset(cache_FACT);
  cache_reset(cache_DIV);
  VFACT0 = vecfactoru_i(1, lim);
  VDIV0  = cgetg(lim+1, t_VEC);
  for (N = 1; N <= lim; ++N)
  {
    GEN fa = gel(VFACT0,N);
    gel(VDIV0, N) = divisorsu_fact(gel(fa,1), gel(fa,2));
  }
  cache_set(cache_FACT, VFACT0);
  cache_set(cache_DIV, VDIV0); avma = av;
}

/* n > 1, D = divisors(n); sets L = 2*lambda(n), S = sigma(n) */
static void
lamsig(GEN D, long *pL, long *pS)
{
  pari_sp av = avma;
  long i, l = lg(D), L = 1, S = D[l-1]+1;
  for (i = 2; i < l; ++i) /* skip d = 1 */
  {
    long d = D[i], nd = D[l-i]; /* nd = n/d */
    if (d < nd) { L += d; S += d + nd; }
    else
    {
      L <<= 1; if (d == nd) { L += d; S += d; }
      break;
    }
  }
  avma = av; *pL = L; *pS = S;
}
/* table of 6 * Hurwitz class numbers D <= lim */
static void
consttabh(long lim)
{
  pari_sp av = avma;
  GEN VHDH0, VDIV, CACHE = NULL;
  GEN VHDH = caches[cache_H].cache;
  const long cachestep = 1000; /* don't increase this: RAM cache thrashing */
  long r, N, cachea, cacheb, lim0 = VHDH? lg(VHDH)-1: 2, LIM = lim0 << 1;

  if (lim <= 0) lim = 5;
  if (lim <= LIM) return;
  cache_reset(cache_H);
  r = lim&3L; if (r) lim += 4-r;
  cache_get(cache_DIV, lim);
  VDIV = caches[cache_DIV].cache;
  VHDH0 = cgetg_block(lim/2 + 1, t_VECSMALL);
  VHDH0[1] = 2;
  VHDH0[2] = 3;
  for (N = 3; N <= lim0; N++) VHDH0[N] = VHDH[N];
  cachea = cacheb = 0;
  for (N = LIM + 3; N <= lim; N += 4)
  {
    long s = 0, limt = usqrt(N>>2), flsq = 0, ind, t, L, S;
    GEN DN, DN2;
    if (N + 2 >= lg(VDIV))
    {
      GEN F;
      if (N + 2 > cacheb)
      { /* update local cache (recycle memory) */
        cachea = N;
        if (cachea + 2*cachestep > lim)
          cacheb = lim+2; /* fuse last 2 chunks */
        else
          cacheb = cachea + cachestep;
        avma = av; /* FIXME: need only factor odd integers in the range */
        CACHE = vecfactoru_i(cachea, cacheb);
      }
      /* use local cache */
      F = gel(CACHE,N - cachea + 1); /* factoru(N) */
      DN = divisorsu_fact(gel(F,1), gel(F,2));
      F = gel(CACHE,N - cachea + 3); /* factoru(N+2) */
      DN2 = divisorsu_fact(gel(F,1), gel(F,2));
    }
    else
    { /* use global cache */
      DN = gel(VDIV,N);
      DN2 = gel(VDIV,N+2);
    }
    ind = N >> 1;
    for (t = 1; t <= limt; ++t)
    {
      ind -= (t<<2)-2; /* N/2 - 2t^2 */
      if (ind) s += VHDH0[ind]; else flsq = 1;
    }
    lamsig(DN, &L,&S);
    VHDH0[N >> 1] = 2*S - 3*L - 2*s + flsq;
    s = 0; flsq = 0; limt = (usqrt(N+2) - 1) >> 1;
    ind = (N+1) >> 1;
    for (t = 1; t <= limt; ++t)
    {
      ind -= t<<2; /* (N+1)/2 - 2t(t+1) */
      if (ind) s += VHDH0[ind]; else flsq = 1;
    }
    lamsig(DN2, &L,&S);
    VHDH0[(N+1) >> 1] = S - 3*(L >> 1) - s - flsq;
  }
  cache_set(cache_H, VHDH0); avma = av;
}

/*************************************************************************/
/* Core functions using factorizations, divisors of class numbers caches */
/* TODO: myfactoru and factorization cache should be exported */
static GEN
myfactoru(long N)
{
  GEN z = cache_get(cache_FACT, N);
  if (z) return gcopy(z);
  return factoru(N);
}
static GEN
mydivisorsu(long N)
{
  GEN z = cache_get(cache_DIV, N);
  if (z) return leafcopy(z);
  return divisorsu(N);
}

/* 1+p+...+p^e, e >= 1 */
static ulong
usumpow(ulong p, long e)
{
  ulong q = 1+p;
  long i;
  for (i = 1; i < e; i++) q = p*q + 1;
  return q;
}
/* Hurwitz(D0 F^2)/ Hurwitz(D0)
 * = \sum_{f|F}  f \prod_{p|f} (1-kro(D0/p)/p)
 * = \prod_{p^e || F} (1 + (p^e-1) / (p-1) * (p-kro(D0/p))) */
static long
get_sh(long F, long D0)
{
  GEN fa = myfactoru(F), P = gel(fa,1), E = gel(fa,2);
  long i, l = lg(P), t = 1;
  for (i = 1; i < l; ++i)
  {
    long p = P[i], e = E[i], s = kross(D0,p);
    if (e == 1) { t *= 1 + p - s; continue; }
    if (s == 1) { t *= upowuu(p,e); continue; }
    t *= 1 + usumpow(p,e-1)*(p-s);
  }
  return t;
}
/* d > 0, d = 0,3 (mod 4). Return 6*hclassno(d); -d must be fundamental
 * Faster than quadclassunit up to 5*10^5 or so */
static ulong
hclassno6u_count(ulong d)
{
  ulong a, b, b2, h = 0;
  int f = 0;

  if (d > 500000)
    return 6 * itou(gel(quadclassunit0(utoineg(d), 0, NULL, 0), 1));

  /* this part would work with -d non fundamental */
  b = d&1; b2 = (1+d)>>2;
  if (!b)
  {
    for (a=1; a*a<b2; a++)
      if (b2%a == 0) h++;
    f = (a*a==b2); b=2; b2=(4+d)>>2;
  }
  while (b2*3 < d)
  {
    if (b2%b == 0) h++;
    for (a=b+1; a*a < b2; a++)
      if (b2%a == 0) h += 2;
    if (a*a == b2) h++;
    b += 2; b2 = (b*b+d)>>2;
  }
  if (b2*3 == d) return 6*h+2;
  if (f) return 6*h+3;
  return 6*h;
}
/* D > 0; 6 * hclassno(D), using D = D0*F^2 */
static long
hclassno6u_2(ulong D, long D0, long F)
{
  long h;
  if (F == 1) h = hclassno6u_count(D);
  else
  { /* second chance */
    h = (ulong)cache_get(cache_H, -D0);
    if (!h) h = hclassno6u_count(-D0);
    h *= get_sh(F,D0);
  }
  return h;
}
/* D > 0; 6 * hclassno(D) (6*Hurwitz). Beware, cached value for D (=0,3 mod 4)
 * is stored at D>>1 */
ulong
hclassno6u(ulong D)
{
  ulong z = (ulong)cache_get(cache_H, D);
  long D0, F;
  if (z) return z;
  D0 = mycoredisc2u(D, &F);
  return hclassno6u_2(D,D0,F);
}
/* same, where the decomposition D = D0*F^2 is already known */
static ulong
hclassno6u_i(ulong D, long D0, long F)
{
  ulong z = (ulong)cache_get(cache_H, D);
  if (z) return z;
  return hclassno6u_2(D,D0,F);
}

/* D > 0, return h(-D) [ordinary class number].
 * Assume consttabh(D or more) was previously called */
static long
hfromH(long D)
{
  pari_sp ltop = avma;
  GEN m, d, fa = myfactoru(D), P = gel(fa,1), E = gel(fa,2);
  GEN VH = caches[cache_H].cache;
  long i, nd, S, l = lg(P);

  /* n = d[i] loops through squarefree divisors of f, where f^2 = largest square
   * divisor of N = |D|; m[i] = moebius(n) */
  nd = 1 << (l-1);
  d = cgetg(nd+1, t_VECSMALL);
  m = cgetg(nd+1, t_VECSMALL);
  d[1] = 1; S = VH[D >> 1]; /* 6 hclassno(-D) */
  m[1] = 1; nd = 1;
  i = 1;
  if (P[1] == 2 && E[1] <= 3) /* need D/n^2 to be a discriminant */
  { if (odd(E[1]) || (E[1] == 2 && (D & 15) == 4)) i = 2; }
  for (; i<l; i++)
  {
    long j, p = P[i];
    if (E[i] == 1) continue;
    for (j=1; j<=nd; j++)
    {
      long n, s, hn;
      d[nd+j] = n = d[j] * p;
      m[nd+j] = s = - m[j]; /* moebius(n) */
      hn = VH[(D/(n*n)) >> 1]; /* 6 hclassno(-D/n^2) */
      if (s > 0) S += hn; else S -= hn;
    }
    nd <<= 1;
  }
  avma = ltop; return S/6;
}
/* D < 0, h(D), ordinary class number */
static long
myh(long D)
{
  ulong z = (ulong)cache_get(cache_H, -D);
  if (z) return hfromH(-D); /* cache big enough */
  return itou(quadclassno(stoi(D)));
}

/*************************************************************************/
/*                          TRACE FORMULAS                               */

/* ceil(m/d) */
static long
ceildiv(long m, long d)
{
  long q;
  if (!m) return 0;
  q = m/d; return m%d? q+1: q;
}

/* contribution of scalar matrices in dimension formula */
static GEN
A1(long N, long k)
{ return gdivgs(utoi(mypsiu(N) * (k-1)), 12); }
static long
ceilA1(long N, long k)
{ return ceildiv(mypsiu(N) * (k-1), 12); }

/* sturm bound, slightly larger than dimension */
long
mfsturmNk(long N, long k) { return 1 + (mypsiu(N)*k)/12; }

/* List of all solutions of x^2 + x + 1 = 0 modulo N, x modulo N */
static GEN
sqrtm3modN(long N)
{
  pari_sp av;
  GEN L = cgetg(1, t_VECSMALL), fa, P, E, res, listchin, listchinneg;
  long lfa, i, n, ct, fl3 = 0, Ninit;
  if (!odd(N) || (N%9) == 0) return L;
  Ninit = N;
  if ((N%3) == 0) { N /= 3; fl3 = 1; }
  fa = myfactoru(N); P = gel(fa, 1); E = gel(fa, 2);
  lfa = lg(P);
  for (i = 1; i < lfa; ++i) if ((P[i]%3) == 2) return L;
  listchin = cgetg(lfa, t_VEC); ct = 0;
  for (i = 1; i < lfa; ++i)
  {
    long p = P[i], e = E[i];
    GEN tmp = Zp_sqrt(utoineg(3), utoi(p), e);
    gel(listchin, i) = mkintmod(tmp, powuu(p,e));
  }
  listchinneg = gneg(listchin);
  ct = 1 << (lfa - 1);
  res = cgetg(ct + 1, t_VECSMALL);
  av = avma;
  for (n = 1; n <= ct; ++n)
  {
    GEN listchintmp = cgetg(lfa, t_VEC);
    long m = n - 1, rr;
    for (i = 1; i < lfa; ++i)
    {
      gel(listchintmp, i) = (m&1L) ? gel(listchinneg, i) : gel(listchin, i);
      m >>= 1;
    }
    rr = itos(lift(chinese1(listchintmp)));
    avma = av;
    if (fl3)
      while (rr%3) rr += N;
    res[n] = (rr&1L) ? (rr - 1) >> 1 : (rr + Ninit - 1) >> 1;
  }
  return res;
}

/* number of elliptic points of order 3 in X0(N) */
static long
nu3(long N)
{
  long i, l;
  GEN P;
  if (!odd(N) || (N%9) == 0) return 0;
  if ((N%3) == 0) N /= 3;
  P = gel(myfactoru(N), 1); l = lg(P);
  for (i = 1; i < l; ++i) if ((P[i]%3) == 2) return 0;
  return 1L<<(l-1);
}
/* number of elliptic points of order 2 in X0(N) */
static long
nu2(long N)
{
  long i, l;
  GEN P;
  if ((N&3L) == 0) return 0;
  if (!odd(N)) N >>= 1;
  P = gel(myfactoru(N), 1); l = lg(P);
  for (i = 1; i < l; ++i) if ((P[i]&3L) == 3) return 0;
  return 1L<<(l-1);
}

/* contribution of elliptic matrices of order 3 in dimension formula
 * Only depends on CHIP the primitive char attached to CHI */
static GEN
A21(long N, long k, GEN CHI)
{
  GEN S, res;
  long a21, i, limx;
  if ((N&1L) == 0) return gen_0;
  a21 = k - 1 - 3*(k/3);
  if (!a21) return gen_0;
  if (N <= 3) return gdivgs(stoi(a21), 3);
  if (!CHI) return gdivgs(stoi(nu3(N) * a21), 3);
  res = sqrtm3modN(N); limx = (N - 1) >> 1;
  S = gen_0;
  for (i = 1; i < lg(res); ++i)
  {
    long x = res[i];
    if (x <= limx)
    { /* (x,N) = 1 */
      GEN c = mfchareval_i(CHI, x);
      S = gadd(S, gadd(c, gsqr(c)));
    }
  }
  S = polcoeff_i(ground(greal(lift(S))), 0, -1);
  return gdivgs(gmulsg(a21, S), 3);
}

/* List of all square roots of -1 modulo N */
static GEN
sqrtm1modN(long N)
{
  pari_sp av;
  GEN L = cgetg(1, t_VECSMALL), fa, P, E, res, listchin, listchinneg;
  long lfa, i, n, ct, fleven = 0;
  if ((N&3L) == 0) return L;
  if ((N&1L) == 0) { N >>= 1; fleven = 1; }
  fa = myfactoru(N); P = gel(fa, 1); E = gel(fa, 2);
  lfa = lg(P);
  for (i = 1; i < lfa; ++i) if ((P[i]&3L) == 3) return L;
  listchin = cgetg(lfa, t_VEC); ct = 0;
  for (i = 1; i < lfa; ++i)
  {
    long p = P[i], e = E[i];
    GEN t = Zp_sqrt(gen_m1, utoi(p), e);
    gel(listchin, i) = mkintmod(t, powuu(p,e));
  }
  listchinneg = gneg(listchin);
  ct = 1 << (lfa - 1);
  res = cgetg(ct + 1, t_VECSMALL);
  av = avma;
  for (n = 1; n <= ct; ++n)
  {
    GEN listchintmp = cgetg(lfa, t_VEC);
    long m = n - 1, rr;
    for (i = 1; i < lfa; ++i)
    {
      gel(listchintmp, i) = (m&1L) ? gel(listchinneg, i) : gel(listchin, i);
      m >>= 1;
    }
    rr = itos(lift(chinese1(listchintmp)));
    avma = av;
    if (fleven && ((rr&1L) == 0)) rr += N;
    res[n] = rr;
  }
  return res;
}

/* contribution of elliptic matrices of order 4 in dimension formula.
 * Only depends on CHIP the primitive char attached to CHI */
static GEN
A22(long N, long k, GEN CHI)
{
  GEN S, res;
  long a22, i, limx;
  if ((N&3L) == 0) return gen_0;
  a22 = k - 1 - 4*(k/4);
  if (!a22) return gen_0;
  if (N <= 2) return gdivgs(stoi(a22), 4);
  if (!CHI) return gdivgs(stoi(nu2(N)*a22), 4);
  if (mfcharparity(CHI) == -1) return gen_0;
  res = sqrtm1modN(N); limx = (N - 1) >> 1;
  S = gen_0;
  for (i = 1; i < lg(res); ++i)
  { /* (x,N) = 1 */
    long x = res[i];
    if (x <= limx) S = gadd(S, mfchareval_i(CHI, x));
  }
  S = polcoeff_i(ground(greal(lift(S))), 0, -1);
  return gdivgs(gmulsg(a22, S), 2);
}

/* sumdiv(N,d,eulerphi(gcd(d,N/d))) */
static long
nuinf(long N)
{
  GEN fa = myfactoru(N), P = gel(fa,1), E = gel(fa,2);
  long i, t = 1, l = lg(P);
  for (i=1; i<l; i++)
  {
    long p = P[i], e = E[i];
    if (odd(e))
      t *= upowuu(p,e>>1) << 1;
    else
      t *= upowuu(p,(e>>1)-1) * (p+1);
  }
  return t;
}

/* contribution of hyperbolic matrices in dimension formula */
static GEN
A3(long N, long FC)
{
  long i, S, NF, l;
  GEN D;
  if (FC == 1) return gdivgs(stoi(nuinf(N)),2);
  D = mydivisorsu(N); l = lg(D);
  S = 0; NF = N/FC;
  for (i = 1; i < l; ++i)
  {
    long g = cgcd(D[i], D[l-i]);
    if (NF%g == 0) S += myeulerphiu(g);
  }
  return gdivgs(stoi(S), 2);
}

/* special contribution in weight 2 in dimension formula */
static long
A4(long k, long FC)
{ return (k==2 && FC==1)? 1: 0; }

/* Trace of $T(n)$ on $(S_k(\G_0(N),CHI))$, $k$ integral.
One CAN have $\gcd(n,N)>1$. Values of CHI integers or polmods. */

static long
mycgcd(GEN GCD, long N, long x)
{ return x < N ? GCD[x + 1] : GCD[x%N + 1]; }
/* chi(gcd(x,N)) */
static GEN
mychicgcd(GEN GCD, GEN VCHI, long N, long FC, long x)
{
  long t = GCD[smodss(x, N) + 1];
  return t == 1 ? gel(VCHI, indexu(x, FC)) : gen_0;
}

/* contribution of scalar matrices to trace formula */
static GEN
TA1(long N, long k, GEN VCHI, long FC, GEN GCD, long n)
{
  pari_sp ltop = avma;
  GEN S;
  ulong sqn;
  if (!uissquareall(n, &sqn)) return gen_0;
  S = mychicgcd(GCD, VCHI, N, FC, sqn);
  if (!gequal0(S)) S = gmul(gmul(powuu(sqn, k-2), A1(N, k)), S);
  return gerepileupto(ltop, S);
}

/* Solutions of x^2 - tx + n = 0 mod N, x mod N */
GEN
sqrtmtnmodN(long N, long t, long n)
{
  pari_sp av, ltop = avma;
  GEN L = cgetg(1, t_VECSMALL), fa, P, E, res, listchin, listchinneg, listzer;
  long lfa, i, j, N4 = N << 2, D = smodss(t*t - (n << 2), N4), co = 0, com, NSH = 0;
  fa = myfactoru(N4); P = gel(fa, 1); E = gel(fa, 2);
  lfa = lg(P);
  listchin = cgetg(lfa, t_VEC);
  listzer = cgetg(lfa, t_VECSMALL);
  for (i = 1; i < lfa; ++i)
  {
    long p = P[i], a = E[i];
    ulong E;
    long b2, b = u_lvalrem(D, p, &E);
    if (a <= b)
    {
      gel(listchin, i) = mkintmod(gen_0, powuu(p, (a+1) >> 1));
      listzer[i] = 0; continue;
    }
    /* a > b */
    if (b&1L) return L;
    if (p > 2)
    {
      GEN t;
      if (kross(E, p) == -1) return L;
      b2 = b >> 1;
      t = mulii(powuu(p,b2), Zp_sqrt(stoi(E), utoi(p), a-b));
      gel(listchin, i) = mkintmod(t, powuu(p, a-b2));
      listzer[i] = 1; co++;
    }
    else
    {
      long d = a - b;
      b2 = b >> 1;
      if (d == 1)
      {
        gel(listchin, i) = mkintmod(int2n(b2), int2n(1+b2));
        listzer[i] = 0;
      }
      else if (d == 2)
      {
        if ((E&3L) != 1) return L;
        gel(listchin, i) = mkintmod(int2n(b2), int2n(1+b2));
        listzer[i] = 0;
      }
      else
      {
        GEN t;
        if ((E&7L) != 1) return L;
        t = shifti(Z2_sqrt(stoi(E), d), b2);
        gel(listchin, i) = mkintmod(t, int2n(d-2+b2));
        if (d == 3) listzer[i] = 0; else { listzer[i] = 1; co++; }
      }
    }
  }
  listchinneg = gneg(listchin);
  com = 1 << co;
  res = cgetg(com + 1, t_VECSMALL);
  av = avma;
  for (j = 1; j <= com; ++j)
  {
    GEN listchintmp = cgetg(lfa, t_VEC), gr;
    long m = j - 1;
    for (i = 1; i < lfa; ++i)
    {
      if (listzer[i])
      {
        gel(listchintmp, i) = (m&1L) ? gel(listchinneg, i) : gel(listchin, i);
        m >>= 1;
      }
      else gel(listchintmp, i) = gel(listchin, i);
    }
    gr = chinese1(listchintmp);
    if (j == 1) NSH = itos(gel(gr, 1));
    res[j] = itos(lift(gr));
    avma = av;
  }
  /* Here res contains all u mod NSH such that u^2 = t^2 - 4n modulo 4N */
  if ((NSH&1L) == 0) NSH >>= 1;
  for (j = 1; j <= com; ++j)
    res[j] = smodss((res[j] + t) >> 1, NSH);
  /* Here res contains all x mod NSH such that x^2 - tx + n = 0 modulo N */
  return gerepilecopy(ltop, mkvec2(stoi(NSH), res));
}

/* All square roots modulo 4N, x modulo 2N, precomputed to accelerate TA2 */
static GEN
mksqr(long N)
{
  pari_sp av = avma;
  long x, N2 = N << 1, N4 = N << 2;
  GEN SQRTS = const_vec(N2, cgetg(1, t_VECSMALL));
  gel(SQRTS, N2) = mkvecsmall(0); /* x = 0 */
  for (x = 1; x <= N; ++x)
  {
    long r = (((x*x - 1)%N4) >> 1) + 1;
    gel(SQRTS, r) = vecsmall_append(gel(SQRTS, r), x);
  }
  return gerepilecopy(av, SQRTS);
}

static GEN
mkgcd(long N)
{
  GEN GCD, d;
  long i, N2;
  if (N == 1) return mkvecsmall(N);
  GCD = cgetg(N + 1, t_VECSMALL);
  d = GCD+1; /* GCD[i+1] = d[i] = gcd(i,N) = gcd(N-i,N), i = 0..N-1 */
  d[0] = N; d[1] = d[N-1] = 1; N2 = N>>1;
  for (i = 2; i <= N2; i++) d[i] = d[N-i] = ugcd(N, i);
  return GCD;
}

/* Table of \sum_{x^2-tx+n=0 mod Ng}chi(x) for all g dividing gcd(N,F),
 * F^2 largest such that (t^2-4n)/F^2=0 or 1 mod 4; t >= 0 */
static GEN
mutglistall(long t, long N, long NF, GEN VCHI, long n, GEN MUP, GEN li, long FC, GEN GCD)
{
  pari_sp ltop = avma;
  long i, lx = lg(li);
  GEN DNF = mydivisorsu(NF), p2 = zerovec(NF);
  long j, g, lDNF = lg(DNF);
  for (i = 1; i < lx; i++)
  {
    long x = (li[i] + t) >> 1, xt = t - x, y, lD;
    GEN D, c = mychicgcd(GCD, VCHI, N, FC, x);
    if (li[i] && li[i] != N)
      c = gadd(c, mychicgcd(GCD, VCHI, N, FC, xt));
    if (isintzero(c)) continue;
    y = (x*(x - t) + n) / N; /* exact division */
    D = mydivisorsu(cgcd(y, NF)); lD = lg(D);
    for (j = 1; j < lD; ++j)
    {
      long g = D[j];
      gel(p2, g) = gadd(gel(p2, g), c);
    }
  }
  /* j = 1 corresponds to g = 1, and MUP[1] = 1 */
  for (j = 2; j < lDNF; j++)
  {
    g = DNF[j];
    gel(p2, g) = gmulsg(MUP[g], gel(p2, g));
  }
  return gerepileupto(ltop, p2);
}

/* special case (N,F) = 1: easier */
static GEN
mutg1(long t, long N, GEN VCHI, GEN li, long FC, GEN GCD)
{ /* (N,F) = 1 */
  pari_sp av = avma;
  GEN S = gen_0;
  long i, lx = lg(li);
  for (i = 1; i < lx; i++)
  {
    long x = (li[i] + t) >> 1, xt = t - x;
    GEN c = mychicgcd(GCD, VCHI, N, FC, x);
    if (!isintzero(c)) S = gadd(S, c);
    if (li[i] && li[i] != N)
    {
      c = mychicgcd(GCD, VCHI, N, FC, xt);
      if (!isintzero(c)) S = gadd(S, c);
    }
  }
  return gerepileupto(av, S); /* single value */
}

/* Gegenbauer pol; n > 2, P = \sum_{0<=j<=n/2} (-1)^j (n-j)!/j!(n-2*j)! X^j */
static GEN
mfrhopol(long n)
{
#ifdef LONG_IS_64BIT
  const long M = 2642249;
#else
  const long M = 1629;
#endif
  long j, d = n >> 1; /* >= 1 */
  GEN P = cgetg(d + 3, t_POL);

  if (n > M) pari_err_IMPL("mfrhopol for large weight"); /* avoid overflow */
  P[1] = evalvarn(0)|evalsigne(1);
  gel(P,2) = gen_1;
  gel(P,3) = utoineg(n-1); /* j = 1 */
  if (d > 1) gel(P,4) = utoipos(((n-3)*(n-2)) >> 1); /* j = 2 */
  if (d > 2) gel(P,5) = utoineg(((n-5)*(n-4)*(n-3)) / 6); /* j = 3 */
  for (j = 4; j <= d; ++j)
    gel(P,j+2) = divis(mulis(gel(P,j+1), (n-2*j+1)*(n-2*j+2)), (n-j+1)*(-j));
  return P;
}

/* polrecip(Q)(t2), assume Q(0) = 1 */
static GEN
ZXrecip_u_eval(GEN Q, ulong t2)
{
  GEN T = addiu(gel(Q,3), t2);
  long l = lg(Q), j;
  for (j = 4; j < l; j++) T = addii(gel(Q,j), mului(t2, T));
  return T;
}
/* return sh * sqrt(n)^nu * G_nu(t/(2*sqrt(n))) for t != 0
 * else (sh/2) * sqrt(n)^nu * G_nu(0) [ implies nu is even ]
 * G_nu(z) = \sum_{0<=j<=nu/2} (-1)^j (nu-j)!/j!(nu-2*j)! * (2z)^(nu-2*j)) */
static GEN
mfrhopowsimp(GEN Q, GEN sh, long nu, long t, long t2, long n)
{
  GEN T;
  switch (nu)
  {
    case 0: return t? sh: gmul2n(sh,-1);
    case 1: return gmulsg(t, sh);
    case 2: return t? gmulsg(t2 - n, sh): gmul(gmul2n(stoi(-n), -1), sh);
    case 3: return gmul(mulss(t, t2 - 2*n), sh);
    default:
      if (!t) return gmul(gmul2n(gel(Q, lg(Q) - 1), -1), sh);
      T = ZXrecip_u_eval(Q, t2); if (odd(nu)) T = mulsi(t, T);
      return gmul(T, sh);
  }
}

/* contribution of elliptic matrices to trace formula */
static GEN
TA2(long N, long k, GEN VCHI, long n, GEN SQRTS, GEN MUP, long FC, GEN GCD)
{
  pari_sp ltop = avma;
  GEN S, Q;
  const long n4 = n << 2, N4 = N << 2, nu = k - 2;
  long limt, t;
  const long st = (!odd(N) && odd(n)) ? 2 : 1;

  limt = usqrt(n4);
  if (limt*limt == n4) limt--;
  Q = nu > 3 ? ZX_z_unscale(mfrhopol(nu), n) : NULL;
  S = gen_0;
  for (t = odd(k)? st: 0; t <= limt; t += st) /* t^2 < 4n */
  {
    long t2 = t*t, D = n4 - t2, i, j, F, D0, NF, lDF;
    GEN DF, p2, sh, li;

    li = gel(SQRTS, (smodss(-D - 1, N4) >> 1) + 1);
    if (lg(li) == 1) continue;
    D0 = mycoredisc2u(D, &F);
    NF = mycgcd(GCD, N, F);
    if (NF == 1)
    { /* (N,F) = 1 => single value in mutglistall */
      GEN mut = mutg1(t, N, VCHI, li, FC, GCD);
      if (gequal0(mut)) continue;
      sh = gmul(gdivgs(utoipos(hclassno6u_i(D,D0,F)),6), mut);
    }
    else
    {
      sh = gen_0;
      p2 = mutglistall(t, N, NF, VCHI, n, MUP, li, FC, GCD);
      DF = mydivisorsu(F); lDF = lg(DF);
      for (i = 1; i < lDF; ++i)
      {
        long Ff, f = DF[i], g = mycgcd(GCD, N, f);
        GEN mut = gel(p2, g);
        if (gequal0(mut)) continue;
        Ff = DF[lDF-i]; /* F/f */
        if (Ff == 1) sh = gadd(sh, mut);
        else
        {
          GEN P = gel(myfactoru(Ff), 1);
          long lP = lg(P);
          for (j = 1; j < lP; ++j) { long p = P[j]; Ff -= kross(D0, p)*Ff/p; }
          sh = gadd(sh, gmulsg(Ff, mut));
        }
      }
      if (gequal0(sh)) continue;
      if (D0 == -3) sh = gdivgs(sh, 3);
      else if (D0 == -4) sh = gdivgs(sh, 2);
      else sh = gmulgs(sh, myh(D0));
    }
    S = gadd(S, mfrhopowsimp(Q, sh, nu, t, t2, n));
  }
  return gerepilecopy(ltop, S);
}

/* compute global auxiliary data for TA3 */
static GEN
mkbez(long N, long FC)
{
  long ct, i, NF = N/FC;
  GEN w, D = mydivisorsu(N);
  long l = lg(D);

  w = cgetg(l, t_VEC);
  for (i = ct = 1; i < l; ++i)
  {
    long u, v, h, c = D[i], Nc = D[l-i];
    if (c > Nc) break;
    h = cbezout(c, Nc, &u, &v);
    if (h == 1) /* shortcut */
      gel(w, ct++) = mkvecsmall5(1,u*c,v*Nc,1,i);
    else if (!(NF%h))
      gel(w, ct++) = mkvecsmall5(h,u*c/h,v*Nc/h,myeulerphiu(h),i);
  }
  setlg(w,ct); stackdummy((pari_sp)(w+ct),(pari_sp)(w+l));
  return w;
}

/* CHIP primitive */
static GEN
mkvchip(GEN CHIP)
{
  long i, N = mfcharmodulus(CHIP);
  GEN v;
  if (N == 1) return mkvec(gen_1);
  v = cgetg(N+1, t_VEC); gel(v,1) = gen_1;
  for (i = 2; i < N; ++i) gel(v,i) = ugcd(N,i)==1? mfchareval_i(CHIP,i): gen_0;
  gel(v,N) = gen_0; return v;
}

GEN
mfchartovec(GEN CHI)
{
  pari_sp av = avma;
  return gerepilecopy(av, mkvchip(CHI));
}

/* contribution of hyperbolic matrices to trace formula, d * nd = n,
 * DN = divisorsu(N) */
static GEN
auxsum(long N, GEN VCHI, long FC, GEN GCD, long d, long nd, GEN DN, GEN BEZ)
{
  GEN S = gen_0;
  long ct, g = nd - d, lDN = lg(DN), lBEZ = lg(BEZ);
  for (ct = 1; ct < lBEZ; ct++)
  {
    GEN y, B = gel(BEZ, ct);
    long ic, iNc, c, Nc, uch, vNch, ph, h = B[1];
    if (g%h) continue;
    uch = B[2];
    vNch= B[3];
    ph  = B[4];
    ic  = B[5]; iNc = lDN - ic;
    c = DN[ic];
    Nc= DN[iNc]; /* Nc = N/c */
    if (cgcd(c, d) == 1 && cgcd(Nc, nd) == 1)
    {
      y = mychicgcd(GCD, VCHI, N, FC, d*vNch + nd*uch);
      if (isintzero(y)) y = NULL;
    }
    else
      y = NULL;
    if (c != Nc && cgcd(c, nd) == 1 && cgcd(Nc, d) == 1)
    {
      GEN y2 = mychicgcd(GCD, VCHI, N, FC, d*uch + nd*vNch);
      if (!isintzero(y2)) y = y? gadd(y, y2): y2;
    }
    if (y) S = gadd(S, gmulsg(ph, y));
  }
  return S;
}

static GEN
TA3(long N, long k, GEN VCHI, long FC, GEN GCD, long n, GEN BEZ)
{
  pari_sp av = avma;
  GEN S = gen_0, D = mydivisorsu(n), DN = mydivisorsu(N);
  long i, l = lg(D);
  for (i = 1; i < l; ++i)
  {
    long d = D[i], nd = D[l-i]; /* = n/d */
    GEN t, u;
    if (d > nd) break;
    t = auxsum(N, VCHI, FC, GCD, d, nd, DN, BEZ);
    if (isintzero(t)) continue;
    u = powuu(d,k-1); if (d == nd) u = gmul2n(u,-1);
    S = gadd(S, gmul(u,t));
  }
  return gerepileupto(av, S);
}

/* special contribution in weight 2 in trace formula
 * Only depends on CHIP the primitive char attached to CHI */
static GEN
TA4(long N, long k, GEN CHI, long n, GEN GCD)
{
  pari_sp ltop = avma;
  GEN D;
  long i, l, S = 0;
  if (k != 2 || !mfcharistrivial(CHI)) return gen_0;
  D = mydivisorsu(n); l = lg(D);
  for (i = 1; i < l; ++i)
  {
    long d = D[i]; /* gcd(N,n/d) == 1? */
    if (mycgcd(GCD, N, D[l-i]) == 1) S += d;
  }
  avma = ltop; return utoi(S);
}

/* precomputation of products occurring im mutg, again to accelerate TA2 */
static GEN
mkmup(long N)
{
  GEN fa = myfactoru(N), P = gel(fa,1), E = gel(fa,2);
  GEN D = divisorsu_fact(P,E);
  long i, lP = lg(P), lD = lg(D);
  GEN MUP = const_vecsmall(N, 0);
  MUP[1] = 1;
  for (i = 2; i < lD; ++i)
  {
    long j, g = D[i], Ng = D[lD-i]; /*  N/g */
    for (j = 1; j < lP; ++j)
    {
      long p = P[j];
      if (Ng%p) g = (g/p)*(p+1);
    }
    MUP[D[i]] = g;
  }
  return MUP;
}

/* CHIP primitive. Determine all cases where newtrace must be zero. Codes:
 * [p,-2]: n%p!=1; (only for p = 4 and p = 8).
 * [p,-1]: kronecker(n,p)==-1; (only for p odd).
 * [p,j], j>=0; n%p==j; (only for j = 0 or p = 4 or p = 8). */
static GEN
mfnewzerodata(long N, GEN CHIP)
{
  GEN res, fa = myfactoru(N), P = gel(fa,1), E = gel(fa,2);
  long FC = mfcharmodulus(CHIP), i, j, l = lg(P);
  res = cgetg(2*l + 8, t_VEC);
  for (i = j = 1; i < l; ++i)
  {
    long p = P[i], e = E[i], c = u_lval(FC, p);
    GEN CHIp = c? mfcharp(CHIP,p): NULL;
    if (p > 2)
    {
      long ord = c ? mfcharorder(CHIp) : 1;
      if ((e <= 2 && c == 1 && ord == 2) || (e >= 3 && c <= e - 2))
        gel(res,j++) = mkvecsmall2(p, -1); /* sc: -p */
      if (e >= 2 && c <= e - 1)
        gel(res,j++) = mkvecsmall2(p, 0); /* sc: p */
    }
    else
    {
      if (e == 1) continue;
      /* e >= 2 */
      if (c == e - 1)
        gel(res,j++) = mkvecsmall2(1, 0); /* sc: 1 */
      if (e == 2 && c == 2)
        gel(res,j++) = mkvecsmall2(4, 3); /* sc: -4 */
      if ((e == 3 || e == 5) && c == 3)
      { /* sc: -8 (CHIp odd) and 8 (CHIp even) */
        long t = mfcharparity(CHIp) == -1? 7: 3;
        gel(res,j++) = mkvecsmall2(8, 5);
        gel(res,j++) = mkvecsmall2(8, t);
      }
      if ((e == 4 && c == 2) || (e == 5 && c <= 2) || (e == 6 && c <= 2)
           || (e >= 7 && c == e - 3))
        gel(res,j++) = mkvecsmall2(4, -2); /* sc: 4 */
      if ((e <= 4 && c == 0) || (e >= 5 && c == e - 2))
        gel(res,j++) = mkvecsmall2(2, 0); /* sc: 2 */
      if ((e == 6 && c == 3) || (e >= 7 && c <= e - 4))
        gel(res,j++) = mkvecsmall2(8, -2); /* sc: -2 */
    }
  }
  setlg(res,j); return res;
}

/* if (!VCHIP): from mfcusptrace_i;
 * else from initnewtrace and CHI is known to be primitive */
static GEN
inittrace(long N, GEN CHI, GEN VCHIP)
{
  GEN CHIP;
  long FC;
  if (VCHIP)
  {
    CHIP = CHI;
    FC = mfcharmodulus(CHI);
    return mkvecn(7, CHIP, mksqr(N), mkmup(N), mkgcd(N),
                  VCHIP, mkbez(N, FC), mfnewzerodata(N,CHIP));
  }
  else
  {
    CHIP = mfchartoprimitive(CHI, &FC);
    VCHIP = mkvchip(CHIP);
    return mkvecn(6, CHIP, mksqr(N), mkmup(N), mkgcd(N),
                  VCHIP, mkbez(N, FC));
  }
}
/* assume CHIP primitive */
static GEN
initnewtrace(long N, GEN CHI)
{
  GEN T = zerovec(N), D, CHIP, VCHIP;
  long FC, N1, N2, i, l;

  CHIP = mfchartoprimitive(CHI, &FC);
  if (N%FC)
    pari_err_DOMAIN("mfnewtrace", "N % f(chi)", "!=", gen_0, mkvec2s(N,FC));
  VCHIP = mkvchip(CHIP);
  N1 = N/FC; newd_params(N1, &N2);
  D = mydivisorsu(N1/N2); l = lg(D);
  N2 *= FC;
  for (i = 1; i < l; i++)
  {
    long M = D[i]*N2;
    gel(T,M) = inittrace(M, CHIP, VCHIP);
  }
  return T;
}

int
checkmf_i(GEN mf)
{
  long l = lg(mf);
  GEN v;
  if (typ(mf) != t_VEC) return 0;
  if (l != 6 && l != 8) return 0;
  v = gel(mf,1);
  if (typ(v) != t_VEC || lg(v) != 5) return 0;
  return typ(gel(v,1)) == t_INT
         && typ(gel(v,2)) == t_INT
         && typ(gel(v,3)) == t_VEC
         && typ(gel(v,4)) == t_INT;
}
void
checkmf(GEN mf)
{ if (!checkmf_i(mf)) pari_err_TYPE("checkmf [please use mfinit]", mf); }
void
checkmfsplit(GEN mf)
{
  checkmf(mf);
  if (lg(mf) != 8) pari_err_TYPE("checkmfsplit [please use mfsplit]", mf);
}

/* Given an ordered Vecsmall vecn, return the vector of mfmathecke
   of its entries. */
GEN
mfmathecke(GEN mf, GEN vecn)
{
  pari_sp ltop = avma;
  long lv, lvP, i, N, dim, k;
  GEN CHI, vtf, res, vT, FA, B, vP;

  checkmf(mf);
  if (typ(vecn) == t_INT)
  {
    long n = itos(vecn); if (!n) pari_err_TYPE("mfmathecke", vecn);
    return mfmathecke_i(mf, labs(n));
  }
  N = mf_get_N(mf); dim = mf_get_dim(mf); k = mf_get_k(mf);
  CHI = mf_get_CHI(mf); vtf = mf_get_vtf(mf);
  if (typ(vecn) != t_VECSMALL) vecn = gtovecsmall(vecn);
  lv = lg(vecn);
  res = cgetg(lv, t_VEC);
  FA = cgetg(lv, t_VEC);
  vP = cgetg(lv, t_VEC);
  vT = const_vec(vecsmall_max(vecn), NULL);
  for (i = 1; i < lv; ++i)
  {
    long n = vecn[i];
    GEN fa;
    if (n == 1) continue;
    if (!n) pari_err_TYPE("mfmathecke", vecn);
    gel(FA, i) = fa = myfactoru(labs(n));
    gel(vP, i) = gel(fa,1);
  }
  vP = shallowconcat1(vP); vecsmall_sort(vP);
  vP = vecsmall_uniq_sorted(vP); /* all primes occurring in vecn */
  lvP = lg(vP);
  if (lvP != 1 && k == 1 && f_type(gel(vtf,1)) == t_MF_DIV)
    B = wt1basiscols(mf, vP[lvP-1]);
  else
    B = NULL;
  for (i = 1; i < lvP; i++)
  {
    long j, e = 1, p = vP[i];
    GEN Tp, u1, u0 = gen_1;
    for (j = 1; j < lv; j++) e = maxss(e, z_lval(vecn[j], p));
    Tp = B? mfmatheckewt1(mf, p, B): mfmathecke_i(mf, p);
    gel(vT, p) = Tp;
    if (e > 1)
    {
      GEN fac = (N % p)? gmul(mfchareval_i(CHI,p), powuu(p, k-1)): NULL;
      long jj, q = p;
      for (u1=Tp, jj=2; jj <= e; ++jj)
      {
        GEN u2 = gmul(Tp, u1);
        if (fac) u2 = gsub(u2, gmul(fac, u0));
        u0 = u1; u1 = u2;
        q *= p; gel(vT, q) = u1; /* T_q, q = p^jj */
      }
    }
  }
  /* vT[p^e] = T_{p^e} for all p^e occurring below */
  for (i = 1; i < lv; ++i)
  {
    long n = vecn[i], j, lP;
    GEN fa, P, E, M;
    if (n == 1) { gel(res, i) = matid(dim); continue; }
    fa = gel(FA,i);
    P = gel(fa,1); lP = lg(P);
    E = gel(fa,2); M = gen_1;
    for (j = 1; j < lP; ++j) M = gmul(M, gel(vT, upowuu(P[j], E[j])));
    gel(res, i) = M;
  }
  return gerepilecopy(ltop, res);
}

/* (-1)^k */
static long
m1pk(long k) { return odd(k)? -1 : 1; }

static long
ischarok(long N, long k, GEN CHI)
{
  if (mfcharparity(CHI) != m1pk(k)) return 0;
  if (CHI && N % mfcharconductor(CHI)) return 0;
  return 1;
}

/* dimension of space of cusp forms S_k(\G_0(N),CHI)
 * Only depends on CHIP the primitive char attached to CHI */
long
mfcuspdim(long N, long k, GEN CHI)
{
  pari_sp av = avma;
  long FC;
  GEN s;
  if (k <= 0) return 0;
  if (k == 1) return mfwt1dim(N, CHI);
  FC = CHI? mfcharconductor(CHI): 1;
  if (FC == 1) CHI = NULL;
  s = gsub(A1(N, k), gadd(A21(N, k, CHI), A22(N, k, CHI)));
  s = gadd(s, gsubsg(A4(k, FC), A3(N, FC)));
  avma = av; return itos(s);
}

/* dimension of whole space M_k(\G_0(N),CHI)
 * Only depends on CHIP the primitive char attached to CHI; assumes ischarok */
long
mffulldim(long N, long k, GEN CHI)
{
  pari_sp av = avma;
  long FC = CHI? mfcharconductor(CHI): 1;
  GEN s;
  if (k <= 0) return (k == 0 && FC == 1)? 1: 0;
  if (k == 1)
  {
    long dim = itos(A3(N, FC));
    avma = av; return dim + mfwt1dim(N, CHI);
  }
  if (FC == 1) CHI = NULL;
  s = gsub(A1(N, k), gadd(A21(N, k, CHI), A22(N, k, CHI)));
  s = gadd(s, A3(N, FC));
  avma = av; return itos(s);
}

/* Dimension of the space of Eisenstein series */
long
mfeisendim(long N, long k, GEN CHI)
{
  pari_sp av = avma;
  long s, FC = CHI? mfcharconductor(CHI): 1;
  if (k <= 0) return (k == 0 && FC == 1)? 1: 0;
  s = itos( A3(N, FC) );
  if (k > 1) s = 2*s - A4(k, FC);
  avma = av; return s;
}

/* Trace of T(n) on space of cuspforms; only depends on CHIP the primitive char
 * attached to CHI */
static GEN
mfcusptrace_i(long N, long k, long n, GEN S)
{
  pari_sp ltop = avma;
  GEN tmp1, tmp2, CHIP, VCHIP, GCD;
  long FC;
  if (!n) return gen_0;
  CHIP = gel(S,_CHIP);
  VCHIP = gel(S,_VCHIP);
  GCD = gel(S,_GCD);
  FC = mfcharmodulus(CHIP);
  tmp1 = gadd(TA1(N, k, VCHIP, FC, GCD, n), TA4(N, k, CHIP, n, GCD));
  tmp2 = TA2(N, k, VCHIP, n, gel(S,_SQRTS), gel(S,_MUP), FC, GCD);
  tmp2 = gadd(tmp2, TA3(N, k, VCHIP, FC, GCD, n, gel(S,_BEZ)));
  tmp2 = gsub(tmp1, tmp2);
  return gerepileupto(ltop, tmp2);
}

static GEN
mfcusptracecache(long N, long k, long n, GEN S, cachenew_t *cache)
{
  GEN C = NULL, T = gel(cache->vfull,N);
  long lcache = lg(T);
  if (n < lcache) C = gel(T, n);
  if (C) cache->cuspHIT++; else C = mfcusptrace_i(N, k, n, S);
  cache->cuspTOTAL++;
  if (n < lcache) gel(T,n) = C;
  return C;
}

/* p > 2 prime */
static long
mftrconj(long N, long p)
{
  GEN fa = myfactoru(N/p), P = gel(fa,1), E = gel(fa,2);
  long i, l = lg(P);
  for (i = 1; i < l; i++)
    if (E[i] == 1 && kross(-4*p, P[i]) == 1) return 1;
  return 0;
}

/* LZ from mfnewzerodata(N,CHI); returns 1 if newtrace(n) must be zero,
 * 0 otherwise (but newtrace(n) may still be zero) */
static long
mfnewchkzero(GEN LZ, long n)
{
  long i, l = lg(LZ);
  for (i = 1; i < l; i++)
  {
    GEN V = gel(LZ, i);
    long p = V[1], j = V[2];
    switch(j)
    {
      case -1: if (krouu(n, p) == -1) return 1;
        break;
      case -2: if (n%p != 1) return 1;
        break;
      default: if (n%p == j) return 1;
        break;
    }
  }
  return 0;
}

/* Trace formula on new space. */
static GEN
mfnewtrace_i(long N, long k, long n, cachenew_t *cache)
{
  GEN s, DN1, S = cache->DATA, SN = gel(S,N);
  GEN CHIP = gel(SN, _CHIP), VCHIP = gel(SN, _VCHIP), LZ = gel(SN, _NEWLZ);
  long FC, N1, N2, N1N2, g, i, j, lDN1;

  if (!n) return gen_0;
  FC = mfcharmodulus(CHIP);
  if (mfnewchkzero(LZ, n) ||
      (k > 2 && FC==1 && n > 2 && N%n == 0 && uisprime(n) && mftrconj(N, n)))
        return gen_0;
  N1 = N/FC; newt_params(N1, n, FC, &g, &N2);
  N1N2 = N1/N2;
  DN1 = mydivisorsu(N1N2); lDN1 = lg(DN1);
  N2 *= FC;
  s = gmulsg(mubeta2(N1N2,n), mfcusptracecache(N2, k, n, gel(S,N2), cache));
  for (i = 2; i < lDN1; ++i)
  { /* skip M1 = 1, done above */
    long M1 = DN1[i], N1M1 = DN1[lDN1-i];
    GEN Dg = mydivisorsu(cgcd(M1, g));
    M1 *= N2;
    s = gadd(s, gmulsg(mubeta2(N1M1,n),
                       mfcusptracecache(M1, k, n, gel(S,M1), cache)));
    for (j = 2; j < lg(Dg); ++j) /* skip d = 1, done above */
    {
      long d = Dg[j], ndd = n/(d*d), M = M1/d;
      long mu = mubeta2(N1M1, ndd); /* != 0 */
      GEN z = mulsi(mu, powuu(d,k-1)), c = gel(VCHIP,indexu(d,FC)); /* != 0 */
      s = gadd(s, gmul(gmul(z, c), mfcusptracecache(M, k, ndd, gel(S,M), cache)));
    }
  }
  return s;
}

/* Only depends on CHIP the primitive char attached to CHI; assumes ischarok */
long
mfnewdim(long N, long k, GEN CHI)
{
  pari_sp av = avma;
  long FC, N1, N2, i, S, l;
  GEN D, CHIP = mfchartoprimitive(CHI, &FC);

  S = mfcuspdim(N, k, CHIP); if (!S) return 0;
  N1 = N/FC; newd_params(N1, &N2); /* will ensure mubeta != 0 */
  D = mydivisorsu(N1/N2); l = lg(D);
  N2 *= FC;
  for (i = 2; i < l; ++i)
  {
    long M = D[l-i]*N2, d = mfcuspdim(M, k, CHIP);
    if (d) S += mubeta(D[i]) * d;
  }
  avma = av; return S;
}

/* mfcuspdim(N,k,CHI) - mfnewdim(N,k,CHI) */
long
mfolddim(long N, long k, GEN CHI)
{
  pari_sp av = avma;
  long FC, N1, N2, i, S, l;
  GEN D, CHIP = mfchartoprimitive(CHI, &FC);

  N1 = N/FC; newd_params(N1, &N2); /* will ensure mubeta != 0 */
  D = mydivisorsu(N1/N2); l = lg(D);
  N2 *= FC; S = 0;
  for (i = 2; i < l; ++i)
  {
    long M = D[l-i]*N2, d = mfcuspdim(M, k, CHIP);
    if (d) S -= mubeta(D[i]) * d;
  }
  avma = av; return S;
}

/* trace form, given as closure */
static GEN
mftraceform_new(long N, long  k,  GEN CHI)
{ return tag2(t_MF_NEWTRACE, mkvecsmall2(N,k), initnewtrace(N,CHI)); }
static GEN
mftraceform_cusp(long N, long k, GEN CHI)
{ return tag2(t_MF_TRACE, mkvecsmall2(N,k), inittrace(N,CHI,NULL));}

static GEN
mftraceform_i(GEN NK, long space)
{
  GEN CHI;
  long N, k;
  checkNK(NK, &N, &k, &CHI, 0);
  if (space == mf_FULL)
    pari_err_DOMAIN("mftraceform", "space", "=", utoi(mf_FULL), NK);
  if (k == 1) return mfwt1trace_i(N, CHI, space);
  if (space == mf_NEW) return mftraceform_new(N, k, CHI);
  return mftraceform_cusp(N, k, CHI);
}
GEN
mftraceform(GEN NK, long space)
{ pari_sp av = avma; return gerepilecopy(av, mftraceform_i(NK,space)); }

static GEN
hecke_data(long N, long k, long n)
{ return mkvecsmall4(k, n, u_ppo(n, N), N); }

static GEN
mfhecke_i(long N, long k, GEN CHI, GEN F, long n)
{
  if (n == 1) return F;
  if (!CHI) CHI = mfchartrivial(N);
  return tag3(t_MF_HECKE, hecke_data(N,k,n), CHI, F);
}

int checkmf_i(GEN mf);

GEN
mfhecke(GEN F, long n, GEN NK)
{
  pari_sp av = avma;
  GEN CHI;
  long N, k;
  if (!NK)
  {
    GEN P = mfparams(F);
    N = itos(gel(P,1));
    k = itos(gel(P,2));
    CHI = get_mfchar(gel(P,3));
  }
  else if (!checkmf_i(NK)) checkNK(NK, &N, &k, &CHI, 0);
  else
  {
    GEN mf = NK;
    N = mf_get_N(mf);
    k = mf_get_k(mf);
    CHI = mf_get_CHI(mf);
  }
  return gerepilecopy(av, mfhecke_i(N, k, CHI, F, n));
}

/* form F given by closure, compute B(d)(F) as closure (q -> q^d) */
static GEN
mfbd_i(GEN F, long d)
{
  GEN D;
  if (d == 1) return F;
  if (d <= 0) pari_err_TYPE("mfbd [d <= 0]", stoi(d));
  if (f_type(F) != t_MF_BD) D = utoi(d);
  else { D = mului(d, gel(F,2)); F = gel(F,3); }
  return tag2(t_MF_BD, D, F);
}
GEN
mfbd(GEN F, long d)
{
  pari_sp av = avma;
  if (!isf(F)) pari_err_TYPE("mfbd",F);
  return gerepilecopy(av, mfbd_i(F, d));
}

static GEN
mfheckeU_i(GEN F, long d)
{
  GEN D;
  if (d == 1) return F;
  if (d <= 0) pari_err_TYPE("mfheckeU [d <= 0]", stoi(d));
  if (f_type(F) != t_MF_HECKEU) D = utoi(d);
  else { D = mului(d, gel(F,2)); F = gel(F,3); }
  return tag2(t_MF_HECKEU, D, F);
}
GEN
mfheckeU(GEN F, long d)
{
  pari_sp av = avma;
  if (!isf(F)) pari_err_TYPE("mfheckeU",F);
  return gerepilecopy(av, mfheckeU_i(F, d));
}

static GEN
clean(GEN W, GEN M, GEN dM, GEN d, long n, GEN y)
{
  M = rowslice(M, 1, y[lg(y)-1]);
  if (!d) d = gen_1;
  if (dM)
  {
    M = RgM_Rg_div(M, dM);
    W = (n == 1)? ZM_Z_mul(W,dM): RgM_Rg_mul(W,dM);
  }
  return mkvec3(y, mkvec2(W,d), M);
}
/* assume M without denominators (stored in dM), lg(M) > 1, full
 * column rank; y = indexrank(M)[1], P cyclotomic polynomial of order
 * n != 2 mod 4 or NULL */
static GEN
mfclean2(GEN M, GEN y, GEN P, long n, GEN dM)
{
  GEN W, d;
  W = rowpermute(M, y);
  W = P? ZabM_inv(liftpol_shallow(W), P, n, &d): ZM_inv_ratlift(W, &d);
  return clean(W,M,dM,d,n,y);
}
static GEN
mfclean(GEN M, long n)
{
  GEN W, v, y, z, d, dM;

  M = Q_remove_denom(M, &dM);
  n = ord_canon(n);
  if (n == 1)
    W = ZM_pseudoinv(M, &v, &d);
  else
  {
    GEN P = polcyclo(n, fetch_user_var("t"));
    W = ZabM_pseudoinv(liftpol_shallow(M), P, n, &v, &d);
  }
  y = gel(v,1);
  z = gel(v,2); if (lg(z) != lg(M)) M = vecpermute(M,z);
  return clean(W,M,dM,d,n,y);
}

/* in place, so that lg(v) is unaffected even if < lg(perm) */
void
vecpermute_inplace(GEN v, GEN perm)
{
  pari_sp av = avma;
  long i, l = lg(perm);
  GEN w = cgetg(l,t_VEC);
  for (i = 1; i < l; i++) gel(w,i) = gel(v,perm[i]);
  for (i = 1; i < l; i++) gel(v,i) = gel(w,i);
  avma = av;
}

/* initialize a cache of newtrace / cusptrace up to index n */
static void
init_cachenew(cachenew_t *cache, long n, GEN DATA)
{
  long i, l = lg(DATA), N = l-1;
  GEN v = cgetg(l, t_VEC);
  for (i = 1; i < l; i++) gel(v,i) = (N % i)? gen_0: const_vec(n, NULL);
  cache->vnew = v;
  cache->DATA = DATA;
  cache->newHIT = cache->newTOTAL = cache->cuspHIT = cache->cuspTOTAL = 0;
  v = cgetg(l, t_VEC);
  for (i = 1; i < l; i++)
    gel(v,i) = (typ(gel(DATA,i)) == t_INT)? gen_0: const_vec(n, NULL);
  cache->vfull = v;
  cache->VCHIP = gel(gel(DATA,l-1),_VCHIP);
}
/* reset cachenew for new level incorporating new DATA
 * (+ possibly initialize 'full' for new allowed levels) */
static void
reset_cachenew(cachenew_t *cache, GEN DATA)
{
  GEN v = gel(cache->vnew,1);
  long i, n = lg(v)-1, l = lg(DATA);
  cache->DATA = DATA;
  v = cache->vfull;
  for (i = 1; i < l; i++)
    if (typ(gel(v,i)) == t_INT && typ(gel(DATA,i)) != t_INT)
      gel(v,i) = const_vec(n, NULL);
}
static void
dbg_cachenew(cachenew_t *C)
{
  if (DEBUGLEVEL >= 2 && C)
    err_printf("newtrace cache hits: new = %ld/%ld, cusp = %ld/%ld\n",
                    C->newHIT, C->newTOTAL, C->cuspHIT, C->cuspTOTAL);
}

/* newtrace_{N,k}(d*i), i = n0, ..., n */
static GEN
colnewtrace(long n0, long n, long d, long N, long k, cachenew_t *cache)
{
  GEN v = cgetg(n-n0+2, t_COL);
  long i;
  for (i = n0; i <= n; ++i)
    gel(v, i - n0 + 1) = mfnewtracecache(N, k, i*d, cache);
  return v;
}
/* T_n(l*m0, l*(m0+1), ..., l*m) F, F = t_MF_NEWTRACE [N,k],DATA, cache
 * contains DATA as well as cached values of F */
static GEN
heckenewtrace(long m0, long m, long l, long N, long NBIG, long k, long n, cachenew_t *cache)
{
  long lD, a, k1, FC, nl = n*l;
  GEN D, V, v = colnewtrace(m0, m, nl, N, k, cache); /* d=1 */
  GEN VCHIP;
  if (n == 1) return v;
  VCHIP = cache->VCHIP; FC = lg(VCHIP) - 1;
  D = mydivisorsu(u_ppo(n, NBIG)); lD = lg(D);
  k1 = k - 1;
  for (a = 2; a < lD; a++)
  { /* d > 1, (d,N) = 1 */
    long d = D[a], c = cgcd(l, d), dl = d/c, i, j, m0d;
    GEN C = gmul(gel(cache->VCHIP, indexu(d, FC)), powuu(d, k1));
    m0d = ceildiv(m0, dl);
    /* m0=0: i = 1 => skip F(0) = 0 */
    if (!m0) { i = 1; j = dl; } else { i = 0; j = m0d*dl; }
    V = colnewtrace(m0d, m/dl, nl/(d*c), N, k, cache);
    /* C = chi(d) d^(k-1) */
    for (; j <= m; i++, j += dl)
      gel(v, j - m0 + 1) = gadd(gel(v, j - m0 + 1), gmul(C, gel(V, i + 1)));
  }
  return v;
}

/* Given v = an[i], return an[d*i] */
static GEN
anextract(GEN v, long n, long d)
{
  GEN w = cgetg(n + 2, t_VEC);
  long i;
  for (i = 0; i <= n; ++i) gel(w, i + 1) = gel(v, i*d + 1);
  return w;
}
/* T_n(F)(0, l, ..., l*m) */
static GEN
hecke_i(long m, long l, GEN knN, GEN CHI, GEN F)
{
  long k = knN[1], n = knN[2], nN = knN[3], NBIG = knN[4];
  long lD, M, a, t, nl = n*l;
  GEN D, v, AN;
  if (nN == 1) return mfcoefs_i(F,m,nl);
  if (f_type(F) == t_MF_NEWTRACE)
  { /* inline F to allow cache */
    cachenew_t cache;
    GEN Nk = gel(F, 2), DATA = gel(F, 3);
    long N = Nk[1];
    init_cachenew(&cache, m*nl, newtrace_DATA(N, DATA));
    v = heckenewtrace(0, m, l, N, NBIG, k, n, &cache);
    dbg_cachenew(&cache);
    settyp(v, t_VEC); return v;
  }
  D = mydivisorsu(nN); lD = lg(D);
  M = m + 1;
  t = nN * cgcd(nN, l);
  AN = mfcoefs_i(F, m * t, nl / t); /* usually nl = t and we gain nothing */
  v = anextract(AN, m, t); /* mfcoefs(F, m, nl); d = 1 */
  for (a = 2; a < lD; a++)
  { /* d > 1, (d, N) = 1 */
    long d = D[a], c = cgcd(l, d), dl = d/c, i, idl;
    GEN C = gmul(mfchareval_i(CHI, d), powuu(d, k-1));
    GEN V = anextract(AN, m/dl, t/(d*c)); /* mfcoefs(F, m/dl, nl/(d*c)) */
    for (i = idl = 1; idl <= M; i++, idl += dl)
      gel(v,idl) = gadd(gel(v,idl), gmul(C, gel(V,i)));
  }
  return v;
}

/* tf either a t_MF_NEWTRACE or a t_MF_HECKE of such */
static GEN
tf_get_DATA(GEN tf)
{
  if (f_type(tf) == t_MF_HECKE) tf = gel(tf,4);
  return gel(tf,3);
}

static ulong
coreu_f(ulong n)
{
  ulong a = coreu_fact(myfactoru(n));
  return usqrt(n/a);
}

/* Find basis of newspace using closures; assume k >= 2 and
 * ischarok(N, k, CHI). Return NULL if space is empty, else
 * [mf1, list of closures T(j)traceform, list of corresponding j, matrix] */
static GEN
mfnewinit(long N, long k, GEN CHI, cachenew_t *cache, long init)
{
  GEN tf, vtf, vj, M, CHIP, mf1, listj, DATA, P;
  long j, ct, ctlj, dim, jin, SB, sb, two, ord;

  dim = mfnewdim(N, k, CHI);
  if (!dim && !init) return NULL;
  sb = mfsturmNk(N, k);
  tf = mftraceform_new(N, k, CHI);
  DATA = tf_get_DATA(tf);
  /* try sbsmall first: Sturm bound not sharp for new space */
  SB = ceilA1(N, k);
  listj = cgetg(2*sb + 3, t_VECSMALL);
  for (j = 1, ctlj = 0; ctlj < 2*sb + 2; ++j)
    if (cgcd(coreu_f(j), N) == 1) listj[++ctlj] = j;
  if (init)
  {
    init_cachenew(cache, (SB+1)*listj[dim+1], DATA);
    if (init == -1 || !dim) return NULL; /* old space */
  }
  else
    reset_cachenew(cache, newtrace_DATA(N, DATA));
  CHIP = mfchartoprimitive(CHI, NULL);
  ord = mfcharorder(CHIP);
  ord = ord_canon(ord);
  P = ord <= 2? NULL: polcyclo(ord, fetch_user_var("t"));
  vj = cgetg(dim+1, t_VECSMALL);
  M = cgetg(dim+1, t_MAT);
  for (two = 1, ct = 0, jin = 1; two <= 2; ++two)
  {
    long a, jlim = jin + sb;
    for (a = jin; a <= jlim; a++)
    {
      GEN z, vecz;
      ct++; vj[ct] = listj[a];
      gel(M, ct) = heckenewtrace(0, SB, 1, N, N, k, vj[ct], cache);
      if (ct < dim) continue;

      z = P? ZabM_indexrank(liftpol_shallow(M),P,ord): ZM_indexrank(M);
      vecz = gel(z, 2); ct = lg(vecz) - 1;
      if (ct == dim) { M = mkvec3(z, gen_0, M); break; } /*maximal rank, done*/
      vecpermute_inplace(M, vecz);
      vecpermute_inplace(vj, vecz);
    }
    if (a <= jlim) break;
    /* sbsmall was not sufficient, use Sturm bound: must extend M */
    for (j = 1; j <= ct; j++)
    {
      GEN t = heckenewtrace(SB + 1, sb, 1, N, N, k, vj[j], cache);
      gel(M,j) = shallowconcat(gel(M, j), t);
    }
    jin = jlim + 1; SB = sb;
  }
  vtf = cgetg(dim + 1, t_VEC);
  /* FIXME (experiment) : remove newtrace data from vtf to save space.
   * I expect negligible slowdown */
  gel(tf, 3) = CHI;
  for (j = 1; j <= dim; ++j) gel(vtf, j) = mfhecke_i(N, k, CHIP, tf, vj[j]);
  dbg_cachenew(cache);
  mf1 = mkvec4(utoipos(N), utoipos(k), CHI, utoi(mf_NEW));
  return mkvec5(mf1, cgetg(1, t_VEC), vtf, vj, M);
}

/* Bd(f)[m0..m], v = f[ceil(m0/d)..floor(m/d)], m0d = ceil(m0/d) */
static GEN
RgC_Bd_expand(long m0, long m, GEN v, long d, long m0d)
{
  long i, j;
  GEN w;
  if (d == 1) return v;
  w = zerocol(m-m0+1);
  if (!m0) { i = 1; j = d; } else { i = 0; j = m0d*d; }
  for (; j <= m; i++, j += d) gel(w,j-m0+1) = gel(v,i+1);
  return w;
}
/* vtf a non-empty vector of t_MF_BD(t_MF_HECKE(t_MF_NEWTRACE)); M the matrix
 * of their coefficients up to m0 (~ mfvectomat) or NULL (empty),
 * extend it to coeffs up to m > m0. The forms B_d(T_j(tf_N))in vtf should be
 * sorted by level N, then j, then increasing d. No reordering here. */
static GEN
bhnmat_extend(GEN M, long m, long r, GEN vtf, cachenew_t *cache)
{
  long i, m0, Nold = 0, jold = 0, l = lg(vtf);
  GEN MAT = cgetg(l, t_MAT), v = NULL;
  m0 = M? nbrows(M): 0;
  for (i = 1; i < l; i++)
  {
    long d, j, N, k, m0d;
    GEN DATA, c;
    bhn_parse(gel(vtf,i), &d, &j, &N, &k, &DATA);
    m0d = ceildiv(m0,d);
    if (N!=Nold)
    { reset_cachenew(cache, newtrace_DATA(N,DATA)); Nold=N; jold=0; }
    if (j!=jold || m0)
    { v = heckenewtrace(m0d, m/d, r, N, N, k, j,cache); jold=j; }
    c = RgC_Bd_expand(m0, m, v, d, m0d);
    if (M) c = shallowconcat(gel(M,i), c);
    gel(MAT,i) = c;
  }
  return MAT;
}

/* vmf by increasing level, mf1 for final (concatenated) MF */
static GEN
mfinitjoin(GEN vmf, GEN mf1, cachenew_t *cache)
{
  GEN gmf1 = mkvec(mf1);
  long i, ind, L = 0, N = mf_get_N(gmf1), k = mf_get_k(gmf1), l = lg(vmf);
  GEN P, vvtf, vMjd, MAT, z, vBd = cgetg(l, t_VEC);
  long ord = mfcharorder(mf_get_CHI(gmf1));
  for (i = 1; i < l; i++)
  {
    GEN mf = gel(vmf,i), D;
    gel(vBd,i) = D = mydivisorsu(N/mf_get_N(mf));
    L += (lg(D)-1) * mf_get_dim(mf);
  }
  vvtf = cgetg(L+1, t_VEC);
  vMjd = cgetg(L+1, t_VEC);
  for (i = ind = 1; i < l; i++)
  {
    GEN DNM = gel(vBd,i), mf = gel(vmf,i);
    GEN vtf = mf_get_vtf(mf), vj = mfnew_get_vj(mf);
    long a, lvtf = lg(vtf), lDNM = lg(DNM), M = mf_get_N(mf);
    for (a = 1; a < lvtf; a++)
    {
      GEN tf = gel(vtf,a);
      long b, j = vj[a];
      for (b = 1; b < lDNM; b++)
      {
        long d = DNM[b];
        gel(vvtf, ind) = mfbd_i(tf, d);
        gel(vMjd, ind) = mkvecsmall3(M, j, d);
        ind++;
      }
    }
  }
  MAT = bhnmat_extend(NULL,ceilA1(N,k),1, vvtf, cache);
  ord = ord_canon(ord);
  P = (ord == 1)? NULL: polcyclo(ord, fetch_user_var("t"));
  z = P? ZabM_indexrank(liftpol_shallow(MAT), P, ord): ZM_indexrank(MAT);
  if (lg(gel(z,2)) == lg(MAT))
    MAT = mfclean2(MAT, gel(z,1), P, ord, NULL);
  else
  {
    MAT = bhnmat_extend(MAT, mfsturmNk(N,k), 1, vvtf, cache);
    MAT = mfclean(MAT, ord);
  }
  dbg_cachenew(cache);
  return mkvec5(mf1, cgetg(1, t_VEC), vvtf, vMjd, MAT);
}
static GEN
mfinitcusp(long N, long k, GEN CHI, GEN mf1, long space)
{
  long lDN1, FC, N1, d1, i, ind, init;
  GEN DN1, vmf, CHIP = mfchartoprimitive(CHI, &FC);
  cachenew_t cache;

  d1 = (space == mf_OLD)? mfolddim(N, k, CHIP): mfcuspdim(N, k, CHIP);
  if (!d1) return NULL;
  N1 = N/FC; DN1 = mydivisorsu(N1); lDN1 = lg(DN1);
  init = (space == mf_OLD)? -1: 1;
  vmf = cgetg(lDN1, t_VEC);
  for (i = lDN1 - 1, ind = 1; i; i--)
  { /* by decreasing level to allow cache */
    GEN mf = mfnewinit(FC*DN1[i], k, CHIP, &cache, init);
    if (mf) gel(vmf, ind++) = mf;
    init = 0;
  }
  setlg(vmf, ind); /* reorder by increasing level */
  return mfinitjoin(vecreverse(vmf), mf1, &cache);
}

static long
mfsturm_mf(GEN mf)
{
  GEN Mindex;
  if (!mf_get_dim(mf)) return 0;
  Mindex = mf_get_Mindex(mf);
  return Mindex[lg(Mindex)-1];
}
long
mfsturm(GEN mf)
{
  long N, k;
  GEN CHI;
  if (checkmf_i(mf)) return mfsturm_mf(mf);
  checkNK(mf, &N, &k, &CHI, 0);
  return mfsturmNk(N, k);
}

long
mfisequal(GEN F, GEN G, long lim)
{
  pari_sp av = avma;
  GEN P;
  long t, sb;
  if (!isf(F)) pari_err_TYPE("mfisequal",F);
  if (!isf(G)) pari_err_TYPE("mfisequal",G);
  if (lim) sb = lim;
  else
  {
    P = mfparams_ii(F);
    if (!P) pari_err_IMPL("mfisequal for these forms");
    sb = mfsturmNk(itos(gel(P,1)), itos(gel(P,2)));
    P = mfparams_ii(G);
    if (!P) pari_err_IMPL("mfisequal for these forms");
    sb = maxss(sb, mfsturmNk(itos(gel(P,1)), itos(gel(P,2))));
  }
  t = gequal(mfcoefs_i(F, sb+1, 1), mfcoefs_i(G, sb+1, 1));
  avma = av; return t;
}

GEN
mffields(GEN mf)
{
  if (lg(mf) == 6) return utoi(mf_get_dim(mf));
  if (lg(mf) < 8) pari_err_TYPE("mffields", mf);
  return gcopy(mf_get_fields(mf));
}

/* F non-empty vector of wt1 forms of the form mfdiv(wt2, eis) or
 * mflinear(dihedral,L) */
static GEN
mflinear_wt1(GEN F, GEN L)
{
  long l = lg(F), j;
  GEN v, E, f;
  if (lg(L) != l) pari_err_DIM("mflinear_wt1");
  f = gel(F,1); /* l > 1 */
  if (f_type(f) != t_MF_DIV)
    return mflinear_linear(F, L);
  E = gel(f,3);
  v = cgetg(l, t_VEC);
  for (j = 1; j < l; j++) { GEN f = gel(F,j); gel(v,j) = gel(f,2); }
  return mfdiv(mflinear_linear(v,L), E);
}
GEN
mfeigenbasis(GEN mf)
{
  pari_sp ltop = avma;
  GEN mfsplit, vtf, res;
  long i, l, k;

  checkmfsplit(mf);
  k = mf_get_k(mf);
  vtf = mf_get_vtf(mf); if (lg(vtf) == 1) return cgetg(1, t_VEC);
  mfsplit = mf_get_newforms(mf);
  res = cgetg_copy(mfsplit, &l);
  if (k == 1)
    for (i = 1; i < l; i++)
      gel(res,i) = mflinear_wt1(vtf, gel(mfsplit,i));
  else
    for (i = 1; i < l; i++)
      gel(res,i) = mflinear_bhn(vtf, gel(mfsplit,i));
  return gerepilecopy(ltop, res);
}

/* Minv = [primitive part, denominator], v a t_COL; return Minv*v */
static GEN
Minv_RgC_mul(GEN Minv, GEN v)
{
  GEN A = gel(Minv,1), d = gel(Minv,2);
  v = RgM_RgC_mul(A, v);
  if (!equali1(d)) v = RgC_Rg_div(v, d);
  return v;
}
static GEN
Minv_RgM_mul(GEN Minv, GEN v)
{
  long j, l = lg(v);
  GEN M = cgetg(l, t_MAT);
  for (j = 1; j < l; j++) gel(M, j) = Minv_RgC_mul(Minv, gel(v, j));
  return M;
}

/* perm vector of strictly increasing indices, v a vector or arbitrary length;
 * the last r entries of perm fall beyond v.
 * Return v o perm[1..(-r)], discarding the last r entries of v */
static GEN
vecpermute_partial(GEN v, GEN perm, long *r)
{
  long i, n = lg(v)-1, l = lg(perm);
  GEN w;
  if (perm[l-1] <= n) { *r = 0; return vecpermute(v,perm); }
  for (i = 1; i < l; i++)
    if (perm[i] > n) break;
  *r = l - i; l = i;
  w = cgetg(l, typ(v));
  for (i = 1; i < l; i++) gel(w,i) = gel(v,perm[i]);
  return w;
}

/* given form F, find coeffs of F on mfbasis(mf). If power series, not
 * guaranteed correct if precision less than Sturm bound */
static GEN
mftobasis_i(GEN mf, GEN F)
{
  GEN v, Mindex, Minv;
  if (!mf_get_dim(mf)) return cgetg(1, t_COL);
  Mindex = mf_get_Mindex(mf);
  Minv = mf_get_Minv(mf);
  if (isf(F))
  {
    long n = Mindex[lg(Mindex)-1];
    v = vecpermute(mfcoefs_i(F, n, 1), Mindex);
    return Minv_RgC_mul(Minv, v);
  }
  else
  {
    GEN A = gel(Minv,1), d = gel(Minv,2);
    long r;
    v = F;
    switch(typ(F))
    {
      case t_SER: v = sertocol(v);
      case t_VEC: case t_COL: break;
      default: pari_err_TYPE("mftobasis", F);
    }
    if (lg(v) == 1) pari_err_TYPE("mftobasis",v);
    v = vecpermute_partial(v, Mindex, &r);
    if (!r) return Minv_RgC_mul(Minv, v); /* single solution */
    /* affine space of dimension r */
    v = RgM_RgC_mul(vecslice(A, 1, lg(v)-1), v);
    if (!equali1(d)) v = RgC_Rg_div(v,d);
    return mkvec2(v, vecslice(A, lg(A)-r, lg(A)-1));
  }
}

static GEN
const_mat(long n, GEN x)
{
  long j, l = n+1;
  GEN A = cgetg(l,t_MAT);
  for (j = 1; j < l; j++) gel(A,j) = const_col(n, x);
  return A;
}

/* L is the mftobasis of a form on CUSP space */
static GEN
mftonew_i(GEN mf, GEN L, long *plevel)
{
  GEN vtf, listMjd, CHI, res, Aclos, Acoef, D, perm;
  long N1, LC, lD, i, l, t, level, N = mf_get_N(mf);

  if (mf_get_k(mf) == 1) pari_err_IMPL("mftonew in weight 1");
  listMjd = mf_get_listj(mf);
  CHI = mf_get_CHI(mf); LC = mfcharconductor(CHI);
  vtf = mf_get_vtf(mf);

  N1 = N/LC;
  D = mydivisorsu(N1); lD = lg(D);
  perm = cgetg(N1+1, t_VECSMALL);
  for (i = 1; i < lD; i++) perm[D[i]] = i;
  Aclos = const_mat(lD-1, cgetg(1,t_VEC));
  Acoef = const_mat(lD-1, cgetg(1,t_VEC));
  l = lg(listMjd);
  for (i = 1; i < l; ++i)
  {
    long M, d;
    GEN v;
    if (gequal0(gel(L,i))) continue;
    v = gel(listMjd, i);
    M = perm[ v[1]/LC ];
    d = perm[ v[3] ];
    gcoeff(Aclos,M,d) = shallowconcat(gcoeff(Aclos,M,d), mkvec(gel(vtf,i)));
    gcoeff(Acoef,M,d) = shallowconcat(gcoeff(Acoef,M,d), gel(L,i));
  }
  res = cgetg(l, t_VEC); level = 1;
  for (i = t = 1; i < lD; i++)
  {
    long j, M = D[i]*LC;
    for (j = 1; j < lD; j++)
    {
      GEN f = gcoeff(Aclos,i,j), C;
      long d;
      if (lg(f) == 1) continue;
      d = D[j];
      C = gcoeff(Acoef,i,j);
      level = clcm(level, M*d);
      gel(res,t++) = mkvec3(utoipos(M), utoipos(d), mflinear_i(f,C));
    }
  }
  if (plevel) *plevel = level;
  setlg(res, t); return res;
}
GEN
mftonew(GEN mf, GEN F)
{
  pari_sp av = avma;
  checkmf(mf);
  if (mf_get_space(mf) != mf_CUSP)
    pari_err_TYPE("mftonew [not a cuspidal space]", mf);
  F = mftobasis_i(mf, F);
  return gerepilecopy(av, mftonew_i(mf,F, NULL));
}
long
mfconductor(GEN mf, GEN F)
{
  pari_sp av = avma;
  long N;
  checkmf(mf);
  if (mf_get_space(mf) != mf_CUSP)
    pari_err_TYPE("mfconductor [not a cuspidal space]", mf);
  F = mftobasis_i(mf, F);
  (void)mftonew_i(mf, F, &N);
  avma = av; return N;
}

/* Here an mf closure F is of the type DIV(LINEAR(...,...),EISEN1),
 * F[2]=LINEAR(...,...), F[2][2]=wt2 basis, F[2][3]=linear combination coeffs
 * F[3]=EISEN1; return cols of mfbasis wt1 */
static GEN
wt1basiscols(GEN mf, long n)
{
  pari_sp btop;
  GEN vtf = mf_get_vtf(mf), F = gel(vtf, 1), LI = gmael(F, 2, 2);
  GEN EI, EIc, V, B, a0;
  long lLI = lg(LI), i, j, l, b = n * mfsturm_mf(mf);

  EI = mfcoefsser(gel(F,3),b,1);
  a0 = polcoeff_i(EI, 0, -1);
  if (gequal0(a0) || gequal1(a0))
    a0 = NULL;
  else
    EI = gdiv(ser_unscale(EI, a0), a0);
  EIc = ginv(EI);
  if (DEBUGLEVEL) err_printf("need %ld series in wt1basiscols\n", lLI - 1);
  btop = avma;
  V = zerovec(lLI - 1);
  for (i = 1; i < lLI; i++)
  {
    GEN LISer = mfcoefsser(gel(LI,i),b,1), f;
    if (a0) LISer = gdiv(ser_unscale(LISer, a0), a0);
    f = gmul(LISer, EIc);
    if (a0) f = ser_unscale(f, ginv(a0));
    f = sertocol(f);
    setlg(f, b+2);
    gel(V, i) = f;
    if (gc_needed(btop, 1))
    {
      if (DEBUGMEM > 1) pari_warn(warnmem,"wt1basiscols i = %ld", i);
      V = gerepilecopy(btop, V);
    }
  }
  V = gerepilecopy(btop, V);
  l = lg(vtf); btop = avma;
  B = zerovec(l-1);
  if (DEBUGLEVEL) err_printf("%ld divs to do\n", l - 1);
  for (j = 1; j < l; ++j)
  {
    GEN S = gen_0, coe;
    F = gel(vtf, j); /* t_MF_DIV */
    coe = gmael(F,2,3);
    for (i = 1; i < lLI; ++i)
    {
      GEN co = gel(coe, i);
      if (!gequal0(co)) S = gadd(S, gmul(co, gel(V, i)));
    }
    gel(B, j) = S;
    if (gc_needed(btop, 1))
    {
      if (DEBUGMEM > 1) pari_warn(warnmem,"wt1basiscols j = %ld", j);
      gerepileall(btop, 1, &B);
    }
  }
  return B;
}

/* B from wt1basiscols */
static GEN
mfmatheckewt1(GEN mf, long n, GEN B)
{
  pari_sp av = avma;
  GEN CHI, Mindex, Minv, D, Q, vC;
  long lMindex, l, lD, k, N, nN, i, j;

  l = lg(B);
  k = mf_get_k(mf);
  N = mf_get_N(mf);
  nN = u_ppo(n, N); /* largest divisor of n coprime to N */
  CHI = mf_get_CHI(mf);
  Mindex = mf_get_Mindex(mf); lMindex = lg(Mindex);
  Minv = mf_get_Minv(mf);
  Q = cgetg(l, t_MAT);
  for (j = 1; j < l; j++) gel(Q,j) = cgetg(lMindex, t_COL);
  D = mydivisorsu(nN); lD = lg(D);
  vC = cgetg(nN+1, t_VEC);
  for (j = 2; j < lD; j++) /* skip d = 1 */
  {
    long d = D[j];
    gel(vC, d) = gmul(mfchareval_i(CHI, d), powuu(d, k-1));
  }

  for (i = 1; i < lMindex; i++)
  {
    long m = Mindex[i]-1, mn = m*n;
    D = mydivisorsu(cgcd(m, nN)); lD = lg(D);
    for (j = 1; j < l; j++)
    {
      GEN S = gel(B,j), s = gel(S, mn + 1);
      long jj;
      for (jj = 2; jj < lD; jj++) /* skip d = 1 */
      {
        long d = D[jj]; /* coprime to N */
        s = gadd(s, gmul(gel(vC,d), gel(S, mn/(d*d) + 1)));
      }
      gcoeff(Q, i, j) = s;
    }
  }
  return gerepileupto(av, Minv_RgM_mul(Minv, Q));
}

/* Matrix of T(n), assume n > 0 */
static GEN
mfmathecke_i(GEN mf, long n)
{
  pari_sp av = avma;
  GEN CHI, Minv, v, b, Mindex, knN;
  long N, k, j, l, sb;

  b = mf_get_basis(mf); l = lg(b);
  if (l == 1) return cgetg(1, t_MAT);
  if (n == 1) return matid(l-1);
  k = mf_get_k(mf);
  if (k == 1 && f_type(gel(b,1)) == t_MF_DIV)
    return mfmatheckewt1(mf, n, wt1basiscols(mf, n));
  N = mf_get_N(mf);
  CHI = mf_get_CHI(mf);
  Mindex = mf_get_Mindex(mf);
  sb = Mindex[lg(Mindex) - 1];
  Minv = mf_get_Minv(mf);
  knN = hecke_data(N, k, n);
  v = cgetg(l, t_VEC);
  for (j = 1; j < l; j++)
  {
    GEN vj = hecke_i(sb, 1, knN, CHI, gel(b,j)); /* Tp f[j] */
    settyp(vj,t_COL); gel(v, j) = vecpermute(vj, Mindex);
  }
  return gerepileupto(av, Minv_RgM_mul(Minv,v));
}

/* f = \sum_i v[i] T_listj[i] (Trace Form) attached to v; replace by f/a_1(f) */
static GEN
mf_normalize(GEN v1, GEN v)
{
  GEN c, dc = NULL;
  v = Q_primpart(v);
  c = ginv(RgV_dotproduct(v1, v));
  if (typ(c) == t_POLMOD) c = Q_remove_denom(c, &dc);
  v = RgC_Rg_mul(v, c);
  return dc? RgC_Rg_div(v, dc): v;
}
/* normalize */
static GEN
mfspcleanrat(GEN v1, GEN simplesp)
{
  GEN res, D;
  long l = lg(simplesp), i;
  res = cgetg(l, t_VEC); D = cgetg(l, t_VECSMALL);
  for (i = 1; i < l; ++i) D[i] = lg(gmael(simplesp, i, 2));
  simplesp = vecpermute(simplesp, vecsmall_indexsort(D));
  for (i = 1; i < l; ++i)
  {
    GEN ATP = gel(simplesp,i), A = gel(ATP,1);
    gel(res,i) = mf_normalize(v1, gel(A,1));
  }
  return mkvec2(res, const_vec(l-1, pol_x(1)));
}

/* Diagonalize and normalize. See mfsplit for meaning of flag. */

static GEN
mfspclean(GEN v1, GEN NF, long ord, GEN simplesp, long k, long flag)
{
  GEN res, D, pols;
  long i, l = lg(simplesp);

  res = cgetg(l, t_VEC);
  pols = cgetg(l, t_VEC);
  D = cgetg(l, t_VEC); /* sort by increasing dimension */
  for (i = 1; i < l; ++i) D[i] = lg(gmael(simplesp, i, 2));
  simplesp = vecpermute(simplesp, vecsmall_indexsort(D));
  for (i = 1; i < l; ++i)
  {
    GEN v, ATP = gel(simplesp, i), A = gel(ATP,1), P = gel(ATP,3);
    long d = degpol(P), vz = varn(P);
    if (d == 1) { P = pol_x(vz); v = gel(A,1); }
    else
    {
      GEN den, K, M, a, D = RgX_disc(P), T = gel(ATP,2);
      long j;
      if (typ(D) != t_INT)
      {
        D = gnorm(D);
        if (typ(D) != t_INT) pari_err_BUG("mfnewsplit");
      }
      if (k <= 2 || expi(D) < 62)
      {
        GEN z;
        if (expi(D) < 31)
          z = NF? rnfpolredabs(NF, P,1): polredabs0(P,1);
        else
          z = NF? rnfpolredbest(NF,P,1): polredbest(P,1);
        P = gel(z,1);
        a = gel(z,2); if (typ(a) == t_POLMOD) a = gel(a,2);
      }
      else
        a = pol_x(vz);
      /* Mod(a,P) root of charpoly(T), K*gpowers(Mod(a,P)) = eigenvector of T */
      if (flag < 0 && d > -flag)
        v = zerovec(d);
      else
      {
        T = shallowtrans(T);
        M = cgetg(d+1, t_MAT); /* basis of cyclic vectors */
        gel(M,1) = vec_ei(d,1);
        for (j = 2; j <= d; j++) gel(M,j) = RgM_RgC_mul(T, gel(M,j-1));
        M = Q_primpart(M);
        K = NF? ZabM_inv(liftpol_shallow(M), nf_get_pol(NF), ord, &den)
              : ZM_inv_ratlift(M,&den);
        K = shallowtrans(K);
        v = gequalX(a)? pol_x_powers(d, vz): RgXQ_powers(a, d-1, P);
        v = gmodulo(RgM_RgC_mul(A, RgM_RgC_mul(K,v)), P);
      }
    }
    if (!flag || d <= flag) v = mf_normalize(v1, v);
    gel(res, i) = v;
    gel(pols, i) = P;
  }
  return mkvec2(res, pols);
}

/* return v = v_{X-r}(P), and set Z = P / (X-r)^v */
static long
RgX_valrem_root(GEN P, GEN r, GEN *Z)
{
  long v;
  for (v = 0; degpol(P); v++)
  {
    GEN t, Q = RgX_div_by_X_x(P, r, &t);
    if (!gequal0(t)) break;
    P = Q;
  }
  *Z = P; return v;
}
static GEN
mynffactor(GEN NF, GEN P, long dimlim)
{
  long i, l, v;
  GEN R, E;
  if (dimlim != 1)
  {
    R = NF? nffactor(NF, P): QX_factor(P);
    if (!dimlim) return R;
    E = gel(R,2);
    R = gel(R,1); l = lg(R);
    for (i = 1; i < l; i++)
      if (degpol(gel(R,i)) > dimlim) break;
    if (i == 1) return NULL;
    setlg(E,i);
    setlg(R,i); return mkmat2(R, E);
  }
  /* dimlim = 1 */
  R = nfroots(NF, P); l = lg(R);
  if (l == 1) return NULL;
  v = varn(P);
  settyp(R, t_COL);
  if (degpol(P) == l-1)
    E = const_vec(l-1, gen_1);
  else
  {
    E = cgetg(l, t_COL);
    for (i = 1; i < l; i++) gel(E,i) = utoi(RgX_valrem_root(P, gel(R,i), &P));
  }
  R = deg1_from_roots(R, v);
  return mkmat2(R, E);
}

/* Let K be a number field attached to NF (Q if NF = NULL). A K-vector
 * space of dimension d > 0 is given by a t_MAT A (n x d, full column rank)
 * giving a K-basis, X a section (d x n: left pseudo-inverse of A). Return a
 * pair (T, fa), where T is an element of the Hecke algebra (a sum of Tp taken
 * from vector vTp) acting on A (a d x d t_MAT) and fa is the factorization of
 * its characteristic polynomial, limited to factors of degree <= dimlim if
 * dimlim != 0 (return NULL if there are no factors of degree <= dimlim) */
static GEN
findbestsplit(GEN NF, GEN vTp, GEN A, GEN X, long dimlim, long vz)
{
  GEN T = NULL, Tkeep = NULL, fakeep = NULL;
  long lmax = 0, i, lT = lg(vTp);
  for (i = 1; i < lT; i++)
  {
    GEN D, P, E, fa, TpA = gel(vTp,i);
    long l;
    if (typ(TpA) == t_INT) break;
    if (lg(TpA) > lg(A)) TpA = RgM_mul(X, RgM_mul(TpA, A)); /* Tp | A */
    T = T ? RgM_add(T, TpA) : TpA;
    if (!NF) { P = QM_charpoly_ZX(T); setvarn(P, vz); }
    else
    {
      P = charpoly(Q_remove_denom(T, &D), vz);
      if (D) P = gdiv(RgX_unscale(P, D), powiu(D, degpol(P)));
    }
    fa = mynffactor(NF, P, dimlim);
    if (!fa) return NULL;
    E = gel(fa, 2);
    /* characteristic polynomial is separable ? */
    if (isint1(vecmax(E))) { Tkeep = T; fakeep = fa; break; }
    l = lg(E);
    /* characteristic polynomial has more factors than before ? */
    if (l > lmax) { lmax = l; Tkeep = T; fakeep = fa; }
  }
  return mkvec2(Tkeep, fakeep);
}

static GEN
nfcontent(GEN nf, GEN v)
{
  long i, l = lg(v);
  GEN c = gel(v,1);
  for (i = 2; i < l; i++) c = idealadd(nf, c, gel(v,i));
  if (typ(c) == t_MAT && gequal1(gcoeff(c,1,1))) c = gen_1;
  return c;
}
static GEN
nf_primpart(GEN nf, GEN B)
{
  switch(typ(B))
  {
    case t_COL:
    {
      GEN A = matalgtobasis(nf, B), c = nfcontent(nf, A);
      if (typ(c) == t_INT) return B;
      c = idealred_elt(nf,c);
      A = Q_primpart( nfC_nf_mul(nf, A, Q_primpart(nfinv(nf,c))) );
      A = liftpol_shallow( matbasistoalg(nf, A) );
      if (gexpo(A) > gexpo(B)) A = B;
      return A;
    }
    case t_MAT:
    {
      long i, l;
      GEN A = cgetg_copy(B, &l);
      for (i = 1; i < l; i++) gel(A,i) = nf_primpart(nf, gel(B,i));
      return A;
    }
    default:
      pari_err_TYPE("nf_primpart", B);
      return NULL; /*LCOV_EXCL_LINE*/
  }
}

/* rotate entries of v to accomodate new entry 'x' (push out oldest entry) */
static void
vecpush(GEN v, GEN x)
{
  long i;
  for (i = lg(v)-1; i > 1; i--) gel(v,i) = gel(v,i-1);
  gel(v,1) = x;
}

/* A non-empty matrix */
static GEN
RgM_getnf(GEN A)
{
  long i, j, l = lg(A), m = lgcols(A);
  for (j = 1; j < l; j++)
    for (i = 1; i < m; i++)
    {
      GEN c = gcoeff(A,i,j);
      if (typ(c) == t_POLMOD) return nfinit(gel(c,1), DEFAULTPREC);
    }
  return NULL;
}

/* mf is either new space of whole cuspidal space in weight 1. If dimlim > 0,
 * keep only the dimension <= dimlim eigenspaces. See mfsplit for the meaning
 * of flag. */
static GEN
mfsplit_i(GEN mf, long dimlim, long flag)
{
  forprime_t iter;
  GEN v, NF, POLCYC, CHI, todosp, Tpbigvec, simplesp, empty = cgetg(1, t_VEC);
  long N, k, ord, FC, newdim, dim = mf_get_dim(mf), dimsimple = 0;
  const long NBH = 5, vz = 1;
  ulong p;

  newdim = dim;
  switch(mf_get_space(mf))
  {
    case mf_NEW: break;
    case mf_CUSP: /* in wt1 much faster to compute mfolddim */
      if (dimlim) pari_err_FLAG("mfsplit [cusp space]");
      newdim -= mfolddim(mf_get_N(mf), mf_get_k(mf), mf_get_CHI(mf));
      break;
    default: pari_err_TYPE("mfsplit [cannot split old/fullspace]", mf);
  }
  if (!newdim) return shallowconcat(mf, mkvec2(empty, empty));
  N = mf_get_N(mf);
  k = mf_get_k(mf);
  CHI = mf_get_CHI(mf);
  FC = mfcharconductor(CHI);
  ord = mfcharorder(CHI);
  if (ord > 2)
  {
    ord = ord_canon(ord);
    POLCYC = polcyclo(ord, fetch_user_var("t"));
    NF = nfinit(POLCYC, DEFAULTPREC);
  }
  else
  {
    ord = 1;
    POLCYC = NULL;
    NF = NULL;
  }
  todosp = mkvec(mkvec2(matid(dim), matid(dim)));
  simplesp = empty;
  Tpbigvec = zerovec(NBH);
  u_forprime_init(&iter, 2, ULONG_MAX);
  while (dimsimple < newdim && (p = u_forprime_next(&iter)))
  {
    GEN nextsp;
    long ind;
    if (N % (p*p) == 0 && N/p % FC == 0) continue; /* T_p = 0 in this case */
    vecpush(Tpbigvec, mfmathecke_i(mf,p));
    if (k == 1 && !NF) NF = RgM_getnf(gel(Tpbigvec,1));
    nextsp = empty;
    for (ind = 1; ind < lg(todosp); ++ind)
    {
      GEN tmp = gel(todosp, ind), fa, P, E, D, Tp, DTp;
      GEN A = gel(tmp, 1);
      GEN X = gel(tmp, 2);
      long lP, i;
      tmp = findbestsplit(NF, Tpbigvec, A, X, dimlim, vz);
      if (!tmp) continue; /* nothing there */
      Tp = gel(tmp, 1);
      fa = gel(tmp, 2);
      P = gel(fa, 1);
      E = gel(fa, 2); lP = lg(P);
      /* lP > 1 */
      if (DEBUGLEVEL) err_printf("Exponents = %Ps\n", E);
      if (lP == 2)
      {
        GEN P1 = gel(P,1);
        long e1 = itos(gel(E,1)), d1 = degpol(P1);
        if (e1 * d1 == lg(Tp)-1)
        {
          if (e1 > 1) nextsp = shallowconcat(nextsp, mkvec(mkvec2(A,X)));
          else
          { /* simple module */
            simplesp = shallowconcat(simplesp, mkvec(mkvec3(A,Tp,P1)));
            dimsimple += d1;
          }
          continue;
        }
      }
      /* Found splitting */
      DTp = Q_remove_denom(Tp, &D);
      for (i = 1; i < lP; ++i)
      {
        GEN Ai, Xi, dXi, AAi, v, y, Pi = gel(P,i);
        Ai = RgX_RgM_eval(D? RgX_rescale(Pi,D): Pi, DTp);
        Ai = QabM_ker(Ai, POLCYC, ord);
        if (NF) Ai = nf_primpart(NF, Ai);

        AAi = RgM_mul(A, Ai);
        /* gives section, works on nonsquare matrices */
        Xi = QabM_pseudoinv(Ai, POLCYC, ord, &v, &dXi);
        Xi = RgM_Rg_div(Xi, dXi);
        y = gel(v,1);
        if (isint1(gel(E,i)))
        {
          GEN Tpi = RgM_mul(Xi, RgM_mul(rowpermute(Tp,y), Ai));
          simplesp = shallowconcat(simplesp, mkvec(mkvec3(AAi, Tpi, Pi)));
          dimsimple += degpol(Pi);
        }
        else
        {
          Xi = RgM_mul(Xi, rowpermute(X,y));
          nextsp = shallowconcat(nextsp, mkvec(mkvec2(AAi, Xi)));
        }
      }
    }
    todosp = nextsp; if (lg(todosp) == 1) break;
  }
  v = row(mf_get_M(mf),2); /* v[i] = vtf[i](1) */
  if (DEBUGLEVEL) err_printf("end split, need to clean\n");
  if (dimlim == 1)
    v = mfspcleanrat(v, simplesp);
  else
    v = mfspclean(v, NF, ord, simplesp, k, flag);
  return shallowconcat(mf, v);
}
/* mf is either already split or output by mfinit. Splitting is done only for
 * newspace except in weight 1. If flag = 0 (default) split completely.
 * If flag = d > 0, give the Galois polynomials and the nonnormalized
 * eigenforms in degree > d, otherwise all. If flag = -d < 0, only
 * give the Galois polynomials in degree > d, otherwise all. Flag is ignored if
 * dimlim = 1. */
GEN
mfsplit(GEN mf, long dimlim, long flag)
{
  pari_sp av = avma;
  if (lg(mf) == 1) return mf;
  if (typ(mf) != t_VEC) pari_err_TYPE("mfsplit", mf);
  if (typ(gel(mf, 1)) == t_VEC)
  {
    long lv = lg(gel(mf, 1));
    if (lv == 6 || lv == 8)
    {
      long lmf = lg(mf), i;
      GEN V = cgetg(lmf, t_VEC);
      for (i = 1; i < lmf; ++i)
        gel(V, i) = mfsplit(gel(mf, i), dimlim, flag);
      return V;
    }
    if (lv != 5) pari_err_TYPE("mfsplit", mf);
  }
  if (!checkmf_i(mf)) mf = mfinit_i(mf, mf_NEW);
  if (lg(mf) == 8)
  {
    GEN pols, forms;
    long j, l;
    mf = gcopy(mf); if (!dimlim) return mf;
    pols = mf_get_fields(mf); l = lg(pols);
    forms = mf_get_newforms(mf);
    for (j = 1; j < l; j++)
      if (degpol(gel(pols,j)) > dimlim) break;
    setlg(pols, j);
    setlg(forms,j); return mf;
  }
  return gerepilecopy(av, mfsplit_i(mf, dimlim, flag));
}

/*************************************************************************/
/*                     Modular forms of Weight 1                         */
/*************************************************************************/
/* S_1(G_0(N)), small N. Return 1 if definitely empty; return 0 if maybe
 * non-empty  */
static int
wt1empty(long N)
{
  if (N <= 100) switch (N)
  { /* non-empty [32/100] */
    case 23: case 31: case 39: case 44: case 46:
    case 47: case 52: case 55: case 56: case 57:
    case 59: case 62: case 63: case 68: case 69:
    case 71: case 72: case 76: case 77: case 78:
    case 79: case 80: case 83: case 84: case 87:
    case 88: case 92: case 93: case 94: case 95:
    case 99: case 100: return 0;
    default: return 1;
  }
  if (N <= 600) switch(N)
  { /* empty [111/500] */
    case 101: case 102: case 105: case 106: case 109:
    case 113: case 121: case 122: case 123: case 125:
    case 130: case 134: case 137: case 146: case 149:
    case 150: case 153: case 157: case 162: case 163:
    case 169: case 170: case 173: case 178: case 181:
    case 182: case 185: case 187: case 193: case 194:
    case 197: case 202: case 205: case 210: case 218:
    case 221: case 226: case 233: case 241: case 242:
    case 245: case 246: case 250: case 257: case 265:
    case 267: case 269: case 274: case 277: case 281:
    case 289: case 293: case 298: case 305: case 306:
    case 313: case 314: case 317: case 326: case 337:
    case 338: case 346: case 349: case 353: case 361:
    case 362: case 365: case 369: case 370: case 373:
    case 374: case 377: case 386: case 389: case 394:
    case 397: case 401: case 409: case 410: case 421:
    case 425: case 427: case 433: case 442: case 449:
    case 457: case 461: case 466: case 481: case 482:
    case 485: case 490: case 493: case 509: case 514:
    case 521: case 530: case 533: case 534: case 538:
    case 541: case 545: case 554: case 557: case 562:
    case 565: case 569: case 577: case 578: case 586:
    case 593: return 1;
    default: return 0;
  }
  return 0;
}

static GEN
initwt1trace(long N, GEN CHI)
{
  GEN mf = mfinit_i(mkvec3(utoi(N), gen_1, CHI), mf_CUSP), vtf = mf_get_vtf(mf);
  GEN v, Mindex, Minv, la, HEC, Mindexmin;
  long lM, i;
  if (lg(vtf) == 1) return mkvec2(mf, gen_0);
  Mindex = mf_get_Mindex(mf); lM = lg(Mindex);
  Minv = mf_get_Minv(mf);
  v = cgetg(lM, t_VEC);
  Mindexmin = cgetg(lM, t_VECSMALL);
  for (i = 1; i < lM; i++) Mindexmin[i] = Mindex[i] - 1;
  HEC = mfmathecke(mf, Mindexmin);
  for (i = 1; i < lM; i++) gel(v, i) = gtrace(gel(HEC, i));
  la = Minv_RgC_mul(Minv, v);
  return mkvec2(mf, mflinear_wt1(vtf, la));
}

/* Return mf full space and newtrace form */
static GEN
initwt1newtrace(long N, GEN CHI)
{
  GEN D, vtf, mf, mftfN, la, Mindex, Minv, res;
  long FC, lD, i, sb, N1, N2, lM;
  CHI = mfchartoprimitive(CHI, &FC);
  if (N % FC || mfcharparity(CHI) == 1) return mkvec2(gen_0, mfcreate(gen_0));
  D = mydivisorsu(N/FC); lD = lg(D);
  mftfN = initwt1trace(N, CHI);
  mf = gel(mftfN, 1);
  vtf = mf_get_vtf(mf);
  if (lg(vtf) == 1) return mkvec2(mf, mfcreate(gen_0));
  N2 = newd_params2(N);
  N1 = N / N2;
  Mindex = mf_get_Mindex(mf);
  Minv = mf_get_Minv(mf);
  lM = lg(Mindex);
  sb = Mindex[lM-1];
  res = zerovec(sb+1);
  for (i = 1; i < lD; ++i)
  {
    long M = FC*D[i], j;
    GEN tf = (M == N)? gel(mftfN, 2): gel(initwt1trace(M, CHI), 2);
    GEN listd, v;
    if (gequal0(tf)) continue;
    v = mfcoefs_i(tf, sb, 1);
    if (M == N) { res = gadd(res, v); continue; }
    listd = mydivisorsu(u_ppo(cgcd(N/M, N1), FC));
    for (j = 1; j < lg(listd); j++)
    {
      long d = listd[j], d2 = d*d; /* coprime to FC */
      GEN dk = mfchareval_i(CHI, d);
      long NMd = N/(M*d), m;
      for (m = 1; m <= sb/d2; m++)
      {
        long be = mubeta2(NMd, m);
        if (be)
        {
          GEN c = gmul(dk, gmulsg(be, gel(v, m+1)));
          long n = m*d2;
          gel(res, n+1) = gadd(gel(res, n+1), c);
        }
      }
    }
  }
  if (gequal0(gel(res,2))) return mkvec2(mf, mfcreate(gen_0));
  la = Minv_RgC_mul(Minv, vecpermute(res,Mindex));
  return mkvec2(mf, mflinear_wt1(vtf, la));
}
static GEN
mfwt1trace_i(long N, GEN CHI, long space)
{
  GEN T = (space == mf_NEW)? initwt1newtrace(N,CHI): initwt1trace(N,CHI);
  return gel(T, 2);
}

/* Matrix of T(p), p \nmid N */
static GEN
Tpmat(long p, long lim, GEN CHI)
{
  GEN M = zeromatcopy(lim, p*lim), chip = mfchareval_i(CHI, p); /* != 0 */
  long i, j, pi, pj;
  gcoeff(M, 1, 1) = gaddsg(1, chip);
  for (i = 1, pi = p; i < lim; i++,  pi += p) gcoeff(M, i+1, pi+1) = gen_1;
  for (j = 1, pj = p; pj < lim; j++, pj += p) gcoeff(M, pj+1, j+1) = chip;
  return M;
}

/* assume !wt1empty(N), in particular N>25 */
/* Returns [[lim,p], mf (weight 2), p*lim x dim matrix, echelonized series] */
static GEN
mfwt1_pre(long N)
{
  GEN M, mf = mfinit_i(mkvec2(utoi(N), gen_2), mf_CUSP); /*not empty for N>25*/
  long p, lim;
  if (uisprime(N))
  {
    p = 2; /*N>25 is not 2 */
    lim = ceilA1(N, 3);
  }
  else
  {
    forprime_t S;
    u_forprime_init(&S, 2, N);
    while ((p = u_forprime_next(&S)))
      if (N % p) break;
    lim = mfsturm_mf(mf) + 1;
  }
  /* p = smalllest prime not dividing N */
  M = bhnmat_extend_nocache(mf_get_M(mf), p*lim-1, 1, mf_get_vtf(mf));
  return mkvec3(mkvecsmall2(lim, p), mf, M);
}

/* lg(A) > 1, E a t_POL */
static GEN
mfmatsermul(GEN A, GEN E)
{
  long j, l = lg(A), r = nbrows(A);
  GEN M = cgetg(l, t_MAT);
  for (j = 1; j < l; j++)
  {
    GEN c = RgV_to_RgX(gel(A,j), 0);
    gel(M, j) = RgX_to_RgC(RgXn_mul(c, E, r+1), r);
  }
  return M;
}
/* lg(Ap) > 1, Ep an Flxn */
static GEN
mfmatsermul_Fl(GEN Ap, GEN Ep, ulong p)
{
  long j, l = lg(Ap), r = nbrows(Ap);
  GEN M = cgetg(l, t_MAT);
  for (j = 1; j < l; j++)
  {
    GEN c = Flv_to_Flx(gel(Ap,j), 0);
    gel(M,j) = Flx_to_Flv(Flxn_mul(c, Ep, r+1, p), r);
  }
  return M;
}

/* minimal Dirichlet character in a given Galois orbit */
static long
getminvnum(long N, long ordw, long *ptvnum)
{
  long vnum = *ptvnum, k0 = 1, vnum0 = vnum, vnummin = vnum, k;
  for (k = 2; k < ordw; ++k)
  {
    vnum0 = (vnum*vnum0) % N;
    if (cgcd(k, ordw) == 1 && vnum0 < vnummin) { k0 = k; vnummin = vnum0; }
  }
  *ptvnum = vnummin; return k0;
}

/* CHI mod F | N, return mfchar of modulus N.
 * FIXME: wasteful, G should be precomputed  */
static GEN
mfcharinduce(GEN CHI, long N)
{
  GEN G, chi;
  if (mfcharmodulus(CHI) == N) return CHI;
  G = znstar0(utoipos(N), 1);
  chi = zncharinduce(gel(CHI,1), gel(CHI,2), G);
  return mkvec3(G, chi, gel(CHI,3));
}

static GEN
zncharno(GEN CHI) { return znconreyexp(gel(CHI,1), gel(CHI,2)); }
static GEN
gmfcharno(GEN CHI)
{
  GEN G = gel(CHI,1), chi = gel(CHI,2);
  return mkintmod(znconreyexp(G, chi), znstar_get_N(G));
}
static long
mfcharno(GEN CHI) { return itos(zncharno(CHI)); }

/* compute mfcharacter with minimal conrey number in Galois orbit of CHI */
static GEN
mfconreyminimize(long N, GEN CHI, long *ptvnum, long *ptk)
{
  long vnum;
  GEN G;
  CHI = mfcharinduce(CHI, N); /* if CHI not mod N, induce it */
  vnum = mfcharno(CHI);
  *ptk = getminvnum(N, mfcharorder(CHI), &vnum);
  *ptvnum = vnum; G = gel(CHI,1);
  return mfcharGL(G, znconreylog(G, utoipos(vnum)));
}

/* M is the matrix of Fourier coeffs attached to (F, C); Minv is the
 * operator yielding the Gauss-Jordan form of M. Update M & C */
static void
Minv_RgM_mul2(GEN Minv, GEN *M, GEN *C)
{
  GEN A = gel(Minv,1), d = gel(Minv,2);
  if (gequal1(d)) d = NULL;
  *M = RgM_mul(*M, A); if (d) *M = RgM_Rg_div(*M,d);
  *C = RgM_mul(*C, A); if (d) *C = RgM_Rg_div(*C,d);
}
/* do not use mflinear: wt1basiscols rely on F being constant across the
 * basis where mflinear_i strips the ones matched by 0 coeffs */
static GEN
vecmflinear(GEN F, GEN C)
{
  long i, l = lg(C);
  GEN v = cgetg(l, t_VEC);
  for (i = 1; i < l; i++) gel(v,i) = tag2(t_MF_LINEAR, F, gel(C,i));
  return v;
}

/* find scalar c such that first non-0 entry of c*v is 1; return c*v
 * (set c = NULL for 1) */
static GEN
RgV_normalize(GEN v, GEN *pc)
{
  long i, l = lg(v);
  *pc = NULL;
  for (i = 1; i < l; i++)
  {
    GEN c = gel(v,i);
    if (!gequal0(c))
    {
      if (gequal1(c)) { *pc = gen_1; return v; }
      *pc = ginv(c); return RgV_Rg_mul(v, *pc);
    }
  }
  return v;
}
/* ordchi != 2 mod 4 */
static GEN
mftreatdihedral(GEN DIH, long ordchi, long biglim, GEN *pvtf)
{
  GEN M, Minv, C;
  long l, i;
  l = lg(DIH); if (l == 1) return NULL;
  if (!pvtf) return DIH;
  C = cgetg(l, t_VEC);
  M = cgetg(l, t_MAT);
  for (i = 1; i < l; ++i)
  {
    GEN c, v = mfcoefs_i(gel(DIH,i), biglim, 1);
    gel(M,i) = RgV_normalize(v, &c);
    gel(C,i) = Rg_col_ei(c, l-1, i);
  }
  Minv = gel(mfclean(M,ordchi),2);
  Minv_RgM_mul2(Minv, &M,&C);
  *pvtf = vecmflinear(DIH, C);
  return M;
}

/* D = divisors(N/FC), ord != 2 mod 4 (order of cyclotomic polynomial
 * generating Q(chi)); dimold > 0 */
static GEN
mftreatoldstuff(GEN D, GEN Vvtf, long dimold, long ord, long biglim, GEN *pvtf)
{
  GEN POLCYC, M, Minv, C, V, z, vecz, MdM, dM;
  long i, j, dAF = 1, ld = lg(D)-1;
  for (j = 1; j < ld; j++)
  {
    GEN vtf = gel(Vvtf, j);
    if (typ(vtf) != t_INT) dAF += mynumdivu(D[ld-j]) * (lg(vtf)-1);
  }
  C = cgetg(dAF, t_VEC);
  M = cgetg(dAF, t_MAT);
  V = cgetg(dAF, t_VEC);
  for (j = i = 1; j < ld; j++)
  {
    GEN vtf = gel(Vvtf,j), Dj;
    long lj, j1, j2;
    if (typ(vtf) == t_INT) continue;
    Dj = mydivisorsu(D[ld-j]);
    lj = lg(Dj);
    for (j1 = 1; j1 < lg(vtf); j1++)
    {
      GEN F = gel(vtf, j1);
      for (j2 = 1; j2 < lj; j2++, i++)
      {
        GEN c, Fd = mfbd(F, Dj[j2]), v = mfcoefs_i(Fd, biglim, 1);
        gel(M,i) = RgV_normalize(v, &c);
        gel(C,i) = Rg_col_ei(c, dAF-1, i);
        gel(V,i) = Fd;
      }
    }
  }
  POLCYC = (ord == 1)? NULL: polcyclo(ord, fetch_user_var("t"));
  MdM = Q_remove_denom(M, &dM);
  z = POLCYC? ZabM_indexrank(liftpol_shallow(MdM), POLCYC, ord)
            : ZM_indexrank(MdM);
  vecz = gel(z,2);
  if (lg(vecz)-1 != dimold) pari_err_BUG("mfwt1basis [old]");
  C = shallowmatextract(C, vecz, vecz);
  M = vecpermute(M, vecz);
  V = vecpermute(V, vecz);

  Minv = gel(mfclean2(M, gel(z,1), POLCYC, ord, dM), 2);
  Minv_RgM_mul2(Minv, &M,&C);
  *pvtf = vecmflinear(V, C);
  return M;
}

static GEN
mfstabiter(GEN M, GEN A2, GEN E1inv, long lim, GEN P, long ordchi)
{
  GEN A, VC, con;
  E1inv = primitive_part(E1inv, &con);
  VC = con? ginv(con): gen_1;
  A = mfmatsermul(A2, E1inv);
  while(1)
  {
    long lA = lg(A);
    GEN Ash = rowslice(A, 1, lim);
    GEN R = shallowconcat(RgM_mul(M, A), Ash);
    GEN B = QabM_ker(R, P, ordchi);
    if (lg(B) == 1) return mkvec2(A, VC);
    if (lg(B) == lA) break;
    B = rowslice(B, 1, lA-1);
    if (ordchi != 1) B = gmodulo(B, P);
    A = Q_primitive_part(RgM_mul(A,B), &con);
    VC = gmul(VC,B); /* first VC is a scalar, then a RgM */
    if (con) VC = RgM_Rg_div(VC, con);
  }
  return mkvec2(A, VC);
}
static long
mfstabitermodp(GEN Mp, GEN Ap, long p, long lim)
{
  GEN VC = NULL;
  while (1)
  {
    long lAp = lg(Ap);
    GEN Ashp = rowslice(Ap, 1, lim);
    GEN Rp = shallowconcat(Flm_mul(Mp, Ap, p), Ashp);
    GEN Bp = Flm_ker(Rp, p);
    if (lg(Bp) == 1) return 0;
    if (lg(Bp) == lAp) return lAp-1;
    Bp = rowslice(Bp, 1, lAp-1);
    Ap = Flm_mul(Ap, Bp, p);
    VC = VC? Flm_mul(VC, Bp, p): Bp;
  }
}

static GEN
mfintereis(GEN A, GEN M2, GEN y, GEN den, GEN E2, GEN P, long ordchi)
{
  pari_sp av = avma;
  GEN z, M1 = mfmatsermul(A,E2), M1den = is_pm1(den)? M1: RgM_Rg_mul(M1,den);
  M2 = RgM_mul(M2, rowpermute(M1, y));
  z = QabM_ker(RgM_sub(M2,M1den), P, ordchi);
  if (ordchi != 1) z = gmodulo(z, P);
  return gerepilecopy(av, mkvec2(RgM_mul(A, z), z));
}
static GEN
mfintereismodp(GEN A, GEN M2, GEN E2, ulong p)
{
  pari_sp av = avma;
  GEN M1 = mfmatsermul_Fl(A, E2, p), z;
  long j, lx = lg(A);
  z = Flm_ker(shallowconcat(M1, M2), p);
  for (j = lg(z) - 1; j; j--) setlg(z[j], lx);
  return gerepilecopy(av, mkvec2(Flm_mul(A, z, p), z));
}

static GEN
mfcharinv_i(GEN CHI)
{
  GEN G = gel(CHI,1), chi = zncharconj(G, gel(CHI,2));
  return mkvec3(G, chi, gel(CHI,3));
}

/* upper bound dim S_1(Gamma_0(N),chi) performing the linear algebra mod p */
static long
mfwt1dimmodp(GEN A, GEN ES, GEN M, long ordchi, long dimdih, long lim, long plim)
{
  GEN Ap, C, ApF, ES1p, ES1INVp, Mp, VC, ApC;
  ulong r, p;
  long i;

  ordchi = ord_canon(ordchi);
  r = QabM_init(ordchi, &p);
  ApF = Ap = QabM_to_Flm(A, r, p);
  VC = NULL;
  ES1p = QabX_to_Flx(gel(ES,1), r, p);
  if (lg(ES) >= 3)
  {
    GEN M2 = mfmatsermul_Fl(ApF, ES1p, p);
    for (i = 2; i < lg(ES); ++i)
    {
      GEN ESip = QabX_to_Flx(gel(ES,i), r, p);
      ApC = mfintereismodp(Ap, M2, ESip, p);
      Ap = gel(ApC,1);
      C = gel(ApC,2); VC = VC? Flm_mul(VC, C, p): C;
      if (lg(Ap) == 1) return 0;
      if (lg(Ap) == dimdih+1) return dimdih;
    }
  }
  /* intersection of Eisenstein series quotients non empty: use Schaeffer */
  ES1INVp = Flxn_inv(ES1p, plim, p);
  Ap = mfmatsermul_Fl(Ap, ES1INVp, p);
  Mp = QabM_to_Flm(M, r, p);
  return mfstabitermodp(Mp, Ap, p, lim);
}


/* Compute the full S_1(\G_0(N),\chi). If pvtf is NULL, only the dimension
 * dim, in the form of a vector having dim components. Otherwise output
 * a basis: ptvf contains a pointer to the vector of forms, and the
 * program returns the corresponding matrix of Fourier expansions.
 * ptdimdih gives the dimension of the subspace generated by dihedral forms;
 * TMP is from mfwt1_pre or NULL. If non NULL, Vvtf is the vector
 * of the vtf's of S_1(\G_0(M),\chi) for f(\chi)\mid M\mid N, M < N. */
static GEN
mfwt1basis(long N, GEN CHI, GEN TMP, GEN *pvtf, long *ptdimdih, GEN Vvtf)
{
  GEN ES, mf, A, M, Tp, tmp1, tmp2, den, CHIP;
  GEN vtf, ESA, VC, C, Ash, POLCYC, ES1, ES1INV, DIH, D, a0, a0i;
  long N1, plim, lim, biglim, i, p, dA, dimp, ordchi, dimdih;
  long lim2, dimold, ld, FC;

  if (ptdimdih) *ptdimdih = 0;
  if (pvtf) *pvtf = NULL;
  if (wt1empty(N) || mfcharparity(CHI) != -1) return NULL;
  ordchi = ord_canon(mfcharorder(CHI));
  if (uisprime(N) && ordchi > 4) return NULL;
  if (!pvtf)
  {
    dimdih = mfdihedralcuspdim(N, CHI);
    DIH = zerovec(dimdih);
  }
  else
  {
    DIH = mfdihedralcusp(N, CHI);
    dimdih = lg(DIH) - 1;
  }
  if (ptdimdih) *ptdimdih = dimdih;
  if (DEBUGLEVEL) err_printf("dimdih = %ld\n", dimdih);
  biglim = mfsturmNk(N, 2);
  if (N < 200 && N != 124 && N != 133 && N != 148 && N != 171)
    return mftreatdihedral(DIH, ordchi, biglim, pvtf);
  if (!TMP) TMP = mfwt1_pre(N);
  tmp1= gel(TMP,1); lim = tmp1[1]; p = tmp1[2]; plim = p*lim;
  mf  = gel(TMP,2);
  A   = gel(TMP,3);
  /* A p*lim x dim matrix, res echelonized series, B transf. matrix */
  vtf = mf_get_vtf(mf);
  ESA = mfeisenbasis_i(N, 1, mfcharinv_i(CHI));
  ES = RgM_to_RgXV(mfvectomat(ESA, plim+1), 0);
  ES1 = gel(ES,1); /* does not vanish at oo */
  Tp = Tpmat(p, lim, CHI);
  dimp = mfwt1dimmodp(A, ES, Tp, ordchi, dimdih, lim, plim);
  if (!dimp) return NULL;
  if (DEBUGLEVEL) err_printf("dimmodp = %ld\n", dimp);
  if (dimp == dimdih) return mftreatdihedral(DIH, ordchi, biglim, pvtf);
  /* we have dimold <= dim <= dimp, so dimp == dimold => dim = dimold */
  CHIP = mfchartoprimitive(CHI, &FC);
  N1 = N/FC; D = mydivisorsu(N1);
  if (!Vvtf) Vvtf = mfwt1basisdiv(D, CHIP);
  ld = lg(D)-1; /* remove N/FC */
  for (i = 1, dimold = 0; i < ld; ++i)
  {
    GEN vtfi = gel(Vvtf, i);
    if (!gequal0(vtfi)) dimold -= mubeta(D[ld-i])*(lg(vtfi) - 1);
  }
  if (DEBUGLEVEL) err_printf("dimold = %ld\n", dimold);
  if (dimp == dimold)
  {
    if (!pvtf) return zerovec(dimold);
    return mftreatoldstuff(D, Vvtf, dimold, ordchi, biglim, pvtf);
  }
  if (DEBUGLEVEL) err_printf("begin hard stuff\n");
  VC = matid(lg(A) - 1);
  lim2 = (3*lim)/2 + 1;
  Ash = rowslice(A, 1, lim2);
  POLCYC = (ordchi == 1)? NULL: polcyclo(ordchi, fetch_user_var("t"));
  if (lg(ES) >= 3)
  {
    pari_sp btop;
    GEN v, y, M2M2I, M2I, M2 = mfmatsermul(Ash, ES1);
    M2I = QabM_pseudoinv(M2, POLCYC, ordchi, &v, &den);
    y = gel(v,1);
    M2M2I = RgM_mul(M2,M2I);
    btop = avma;
    for (i = 2; i < lg(ES); ++i)
    {
      GEN APC = mfintereis(Ash, M2M2I, y, den, gel(ES,i), POLCYC,ordchi);
      Ash = gel(APC,1);
      if (lg(Ash) == 1) return NULL;
      VC = RgM_mul(VC, gel(APC,2));
      if (gc_needed(btop, 1))
      {
        if (DEBUGMEM > 1) pari_warn(warnmem,"mfwt1basis i = %ld", i);
        gerepileall(btop, 2, &Ash, &VC);
      }
    }
  }
  A = RgM_mul(A, vecslice(VC,1, lg(Ash)-1));
  a0 = gel(ES1,2); /* non-zero */
  if (gequal1(a0)) a0 = a0i = NULL;
  else
  {
    a0i = ginv(a0);
    ES1 = RgX_Rg_mul(RgX_unscale(ES1,a0), a0i);
  }
  ES1INV = RgXn_inv(ES1, plim-1);
  if (a0) ES1INV = RgX_Rg_mul(RgX_unscale(ES1INV, a0i), a0i);
  tmp2 = mfstabiter(Tp, A, ES1INV, lim, POLCYC, ordchi);
  A = gel(tmp2,1); dA = lg(A);
  if (dA == 1) return NULL;
  VC = gmul(VC, gel(tmp2,2));
  C = cgetg(dA, t_VEC);
  M = cgetg(dA, t_MAT);
  for (i = 1; i < dA; ++i)
  {
    GEN c, v = gel(A,i);
    gel(M,i) = RgV_normalize(v, &c);
    gel(C,i) = RgC_Rg_mul(gel(VC,i), c);
  }
  if (pvtf)
  {
    GEN v, Minv = gel(mfclean(M, ordchi), 2), ES1clos = gel(ESA,1);
    Minv_RgM_mul2(Minv, &M,&C);
    *pvtf = v = vecmflinear(vtf, C);
    for (i = 1; i < dA; i++) gel(v,i) = mfdiv_val(gel(v,i), ES1clos, 0);
  }
  return M;
}

/* mfwt1basis for all divisors; D = divisors(N/FC), CHIP primitive */
static GEN
mfwt1basisdiv(GEN D, GEN CHIP)
{
  long FC = mfcharmodulus(CHIP), lD, i;
  GEN Vvtf;

  lD = lg(D) - 1;
  Vvtf = zerovec(lD - 1);
  for (i = 1; i < lD; i++) /* skip N/FC */
  {
    GEN z, vtf, Vvtfs;
    long d = D[i], M = d*FC, j, ct;
    if (wt1empty(M)) continue;
    Vvtfs = cgetg(i, t_VEC);
    for (j = ct = 1; j < i; j++)
      if (d % D[j] == 0) gel(Vvtfs, ct++) = gel(Vvtf, j);
    setlg(Vvtfs, ct);
    z = mfwt1basis(M, mfcharinduce(CHIP,M), NULL, &vtf, NULL, Vvtfs);
    if (z) gel(Vvtf, i) = vtf;
  }
  return Vvtf;
}

static GEN
mfwt1init(long N, GEN CHI, GEN TMP)
{
  GEN mf1, vtf, M = mfwt1basis(N, CHI, TMP, &vtf, NULL, NULL);
  if (!M) return NULL;
  mf1 = mkvec4(stoi(N), gen_1, CHI, utoi(mf_CUSP));
  return mkvec5(mf1, cgetg(1,t_VEC), vtf, gen_0, mfclean(M, mfcharorder(CHI)));
}

static GEN
fmt_dim(GEN CHI, long d, long dih)
{ return mkvec4(gmfcharorder(CHI), gmfcharno(CHI), utoi(d), stoi(dih)); }

static GEN
mfwt1chars(long N)
{
  long i, j, l, Nprime = uisprime(N);
  GEN w = mfchargalois(N, 1, Nprime? mkvecsmall2(2,4): NULL); /* Tate theorem */
  l = lg(w); w = leafcopy(w);
  for (i = j = 1; i < l; i++)
  {
    GEN CHI = gel(w,i);
    if (mfcharparity(CHI) == -1)
    {
      if (Nprime) { long o = mfcharorder(CHI); if (o!=2 && o!=4) continue; }
      gel(w,j++) = CHI;
    }
  }
  return w;
}

static GEN
mfEMPTY(GEN mf1)
{
  GEN M = mkvec3(cgetg(1,t_VECSMALL), cgetg(1,t_MAT),cgetg(1,t_MAT));
  return mkvec5(mf1, cgetg(1,t_VEC), cgetg(1,t_VEC), cgetg(1,t_VEC), M);
}
static GEN
mfwt1EMPTY(long N, GEN CHI, long space)
{
  GEN mf1 = mkvec4(utoi(N), gen_1, CHI, utoi(space));
  return mfEMPTY(mf1);
}
static GEN
mfwt1EMPTYall(long N, GEN vCHI, long space)
{
  long i, l = lg(vCHI);
  GEN w = cgetg(l, t_VEC);
  for (i = 1; i < l; i++) gel(w,i) = mfwt1EMPTY(N, gel(vCHI,i), space);
  return w;
}

/* Compute all $S_1(\G_0(N),\chi)$ for all $\chi$ up to Galois conjugation
 * w is NULL or a vector of mfchars. */

static GEN
mfwt1initall(long N, GEN vCHI, long space)
{
  GEN res, TMP, w, z = gen_0;
  long i, j, l;

  if (wt1empty(N)) return vCHI? mfwt1EMPTYall(N,vCHI,space): cgetg(1,t_VEC);
  w = vCHI? vCHI: mfwt1chars(N);
  l = lg(w); if (l == 1) return cgetg(1,t_VEC);
  res = cgetg(l, t_VEC);
  TMP = mfwt1_pre(N);
  for (i = j = 1; i < l; ++i)
  {
    GEN CHI = gel(w,i);
    switch (space)
    {
      case mf_NEW: z = mfwt1newinit(N, gel(w,i), TMP); break;
      case mf_CUSP: z = mfwt1init(N, gel(w,i), TMP); break;
      default: pari_err_FLAG("mfwt1initall");
    }
    if (vCHI && !z) z = mfwt1EMPTY(N, CHI, space);
    if (z) gel(res, j++) = z;
  }
  setlg(res,j); return res;
}

static GEN
mfdim0all(GEN w)
{
  GEN v, z;
  long i, l;
  if (!w) return cgetg(1,t_VEC);
  l = lg(w); v = cgetg(l, t_VEC); z = zerovec(2);
  for (i = 1; i < l; i++) gel(v,i) = z;
  return v;
}
static GEN
mfwt1dimall(long N, GEN vCHI)
{
  GEN z, TMP, w;
  long i, j, l;
  if (wt1empty(N)) return mfdim0all(vCHI);
  w = vCHI? vCHI: mfwt1chars(N);
  l = lg(w); if (l == 1) return cgetg(1,t_VEC);
  z = cgetg(l, t_VEC);
  TMP = mfwt1_pre(N);
  for (i = j = 1; i < l; ++i)
  {
    long d, dimdih;
    GEN CHI = gel(w,i), b = mfwt1basis(N, CHI, TMP, NULL, &dimdih, NULL);
    d = b? lg(b)-1: 0;
    if (vCHI)
      gel(z,j++) = mkvec2s(d, dimdih);
    else if (d)
      gel(z,j++) = fmt_dim(CHI, d, dimdih);
  }
  setlg(z,j); return z;
}

long
mfwt1dim(long N, GEN CHI)
{
  pari_sp av = avma;
  GEN M = mfwt1basis(N, CHI, NULL, NULL, NULL, NULL);
  avma = av; return M? lg(M)-1: 0;
}

/* Dimension of $S_1(\G_1(N))$ */
/* Warning: vres[i] is of the form
   [N,[Vecsmall(order,conrey,dimension),Vecsmall(or...)]]; Change if format
   changes. */
static long
mfwt1dim_i(long N)
{
  pari_sp av = avma;
  GEN v = mfwt1dimall(N, NULL);
  long i, ct = 0, l = lg(v);
  for (i = 1; i < l; i++)
  {
    GEN w = gel(v, i);
    ct += itou(gel(w,3))*myeulerphiu(itou(gel(w,1)));
  }
  avma = av; return ct;
}

static GEN
mfwt1newdimall(long N, GEN vCHI)
{
  GEN z, w, vTMP, D;
  long i, c, lw;
  if (wt1empty(N)) return mfdim0all(vCHI);
  w = vCHI? vCHI: mfwt1chars(N);
  lw = lg(w); if (lw == 1) return cgetg(1,t_VEC);
  D = mydivisorsu(N);
  vTMP = const_vec(N, NULL);
  gel(vTMP,N) = mfwt1_pre(N);
  z = cgetg(lw, t_VEC);
  for (i = c = 1; i < lw; i++)
  {
    long j, l, F, S = 0, dimdihnew = 0, dimdih = 0;
    GEN Di, CHI = gel(w, i), CHIP = mfchartoprimitive(CHI,&F);
    GEN b = mfwt1basis(N, CHI, gel(vTMP,N), NULL, &dimdih, NULL);
    if (!b)
    {
      if (vCHI) gel(z, c++) = zerovec(2);
      continue;
    }
    S = lg(b) - 1;
    dimdihnew = dimdih;
    Di = mydivisorsu(N/F); l = lg(Di)-1; /* skip last M = N */
    for (j = 1; j < l; j++)
    {
      long M = D[j]*F, mb;
      GEN TMP;
      if (wt1empty(M) || !(mb = mubeta(N/M))) continue;
      TMP = gel(vTMP,M);
      if (!TMP) gel(vTMP,M) = TMP = mfwt1_pre(M);
      b = mfwt1basis(M, CHIP, TMP, NULL, &dimdih, NULL);
      if (b) { S += mb * (lg(b)-1); dimdihnew += mb * dimdih; }
    }
    if (vCHI)
      gel(z,c++) = mkvec2s(S, dimdihnew);
    else if (S)
      gel(z, c++) = fmt_dim(CHI, S, dimdihnew);
  }
  setlg(z,c); return z;
}

static GEN
mfwt1olddimall(long N, GEN vCHI)
{
  long i, j, l;
  GEN z, w;
  if (wt1empty(N)) return mfdim0all(vCHI);
  w = vCHI? vCHI: mfwt1chars(N);
  l = lg(w); z = cgetg(l, t_VEC);
  for (i = j = 1; i < l; ++i)
  {
    GEN CHI = gel(w,i);
    long d = mfolddim(N, 1, CHI);
    if (vCHI)
      gel(z,j++) = mkvec2s(d,d?-1:0);
    else if (d)
      gel(z, j++) = fmt_dim(CHI, d, -1);
  }
  setlg(z,j); return z;
}

static long
mfwt1newdim(long N)
{
  GEN D;
  long N2, i, l, S;
  newd_params(N, &N2); /* will ensure mubeta != 0 */
  D = mydivisorsu(N/N2); l = lg(D);
  S = mfwt1dim_i(N); if (!S) return 0;
  for (i = 2; i < l; ++i)
  {
    long M = D[l-i]*N2, d = mfwt1dim_i(M);
    if (d) S += mubeta(D[i]) * d;
  }
  return S;
}

/* Guess Galois type of wt1 eigenforms. */
/* NK can be mf or [N,1,CHI] */

/* Prove (if it is the case) that a form is not dihedral. */
static long
notdih(long N, GEN van, long D)
{
  forprime_t iter;
  long p, lim = lg(van) - 2;
  if (D == 1) return 1;
  u_forprime_init(&iter, 2, lim);
  while((p = u_forprime_next(&iter)))
  {
    if (!(N%p)) continue;
    if (kross(D, p) == -1 && !gequal0(gel(van, p+1))) return 1;
  }
  return 0;
}

/* return 1 if not dihedral */
static long
mfisnotdihedral(long N, GEN van)
{
  GEN P = gel(myfactoru(N), 1), D = mydivisorsu( zv_prod(P) );
  long i, lD = lg(D);
  for (i = 1; i < lD; i++)
  {
    long d = D[i], r = d&3L;
    switch (r) /* != 0 since d squarefree */
    {
      case 3: d = -d; /* fall through */
      case 1:
        if (!notdih(N,van,d)) return 0;
        if (!(N&1L) && !notdih(N,van,-4*d)) return 0;
        break;
      case 2:
        if (!notdih(N,van,4*d) || !notdih(N,van,-4*d)) return 0;
        break;
    }
  }
  return 1;
}

static long
mfisdihedral(GEN van, GEN matdih)
{
  pari_sp av = avma;
  GEN v, res;
  if (lg(matdih) == 1) return 0;
  v = vecslice(van, 1, nbrows(matdih)); settyp(v, t_COL);
  res = inverseimage(matdih, v);
  avma = av; return lg(res) != 1;
}

static ulong
radical_u(ulong n)
{ return zv_prod(gel(myfactoru(n),1)); }

/* list of fundamental discriminants unramified outside N */
static GEN
mfunram(long N)
{
  long cN = radical_u(N >> vals(N)), l, c, i;
  GEN D = divisorsu(cN), res;
  l = lg(D);
  res = cgetg(6*l - 5, t_VECSMALL);
  for (i = c = 1; i < l; ++i)
  {
    long d = D[i], d4 = d & 3L; /* d odd, squarefree */
    if (d > 1 && d4 == 1) res[c++] = d;
    if (d4 == 3) res[c++] = -d;
    if ((N&1L) == 0)
    {
      if (d4 == 2 || d4 == 3) res[c++] = 4*d;
      if (d4 == 2 || d4 == 1) res[c++] =-4*d;
      if (d & 1) { res[c++] = 8*d; res[c++] = -8*d; }
    }
  }
  setlg(res, c); return res;
}

static long
mfisnotS4(long N, GEN CHI, GEN van)
{
  forprime_t iter;
  GEN D = mfunram(N), res;
  long i, lim = lg(van) - 2, lD = lg(D);
  for (i = 1; i < lD; i++)
  {
    long p, d = D[i], ok = 0;
    u_forprime_init(&iter, 2, lim);
    while((p = u_forprime_next(&iter)))
    {
      if (!(N%p) || kross(d, p) != -1) continue;
      res = gdiv(gsqr(gel(van, p+1)), mfchareval(CHI, p));
      if (!gequal0(res) && !gequal(res, gen_2)) { ok = 1; break; }
    }
    if (!ok) return 0;
  }
  return 1;
}

static long
mfisnotA5_simple(GEN van)
{
  long l = lg(van) - 2, i, vz = 1;
  GEN pol5 = gsubgs(gsqr(pol_x(vz)), 5);
  for (i = 1; i < l; i++)
  {
    GEN c = gel(van, i);
    if (i != 1 && !uisprime(i+1)) continue; /* only test a_0 and a_prime */
    if (typ(c) == t_POLMOD)
    {
      GEN T = gel(c,1);
      if (varn(T) == vz)
      { /* K / Q(zeta_n) / Q */
        GEN t = NULL, p = NULL;
        if (!RgX_is_FpXQX(T, &t,&p) || p) pari_err_TYPE("mfgaloistype", c);
        if (t) T = rnfequation(t,T);
        if (typ(nfisincl(pol5, T)) != t_INT) return 0;
      }
      else
      { /* Q(zeta_n) / Q */
        long n = poliscyclo(T);
        if (!n) pari_err_TYPE("mfgaloistype", c);
        if (n % 5 == 0) return 0;
      }
    }
  }
  return 1;
}

/* Given x = z + 1/z with z prim. root of unity of order n, find n */
static long
mffindrootof1(GEN u1)
{
  pari_sp av = avma;
  GEN u0 = gen_2, u1k = u1, u2;
  long c = 1;
  while (!gequalsg(2, lift_shallow(u1))) /* u1 = z^c + z^-c */
  {
    u2 = gsub(gmul(u1k, u1), u0);
    u0 = u1; u1 = u2; c++;
  }
  avma = av; return c;
}

static long
mfgaloistype_i(long N, GEN CHI, GEN van, GEN matdih)
{
  forprime_t iter;
  GEN CT = const_vecsmall(100, 0);
  ulong p, i, ct = 0, ordmax = 1, R = 1, lim, limct = 100;
  lim = lg(van) - 2;
  u_forprime_init(&iter, 2, lim);
  while((p = u_forprime_next(&iter)))
  {
    GEN u;
    ulong ro1;
    if (!(N%p)) continue;
    u = gdiv(gsqr(gel(van, p+1)), mfchareval(CHI, p));
    ro1 = mffindrootof1(gsubgs(u,2));
    if (ro1 >= 3) R = clcm(R, ro1);
    while (ro1 > limct)
    {
      i = limct + 1; limct *= 2;
      CT = vecsmall_lengthen(CT, limct);
      for (; i <= limct; ++i) CT[i] = 0;
    }
    CT[ro1]++; ct++;
    ordmax = maxss(ro1, ordmax);
  }
  R = (R == 1)? 4: 2*R;
  setlg(CT, maxss(6, ordmax + 1));
  if (DEBUGLEVEL) err_printf("CT = %Ps\n", CT);
  if (ordmax >= 6) return R; /* Here F is PROVED to be dihedral. */
  if (mfisnotdihedral(N,van))
  { /* we have PROVED that F is NOT dihedral: A4, S4 or A5. */
    if (CT[4]) return -24; /* S4 */
    if (CT[5]) return -60; /* A5 */
    if (!mfisnotS4(N, CHI, van)) return 0; /* failure, may be S4. */
    /* we know it is not S4 */
    if (mfisnotA5_simple(van)) return -12; /* A4. */
    return 0; /* FAILURE */
  }
  else
  { /* Here F is probably dihedral. Let's prove it. */
    if (!mfisdihedral(van, matdih)) return 0; /* FAILURE */
    return R;
  }
}

static GEN
mfgaloistype0(long N, GEN CHI, GEN F, GEN matdih, long lim)
{
  pari_sp av = avma;
  for(;;)
  {
    long gt = mfgaloistype_i(N, CHI, mfcoefs_i(F,lim,1), matdih);
    avma = av; if (gt) return stoi(gt);
    lim += lim >> 1;
  }
}

/* If f is NULL, give all the galoistypes, otherwise just for f */
GEN
mfgaloistype(GEN NK, GEN f, long lim)
{
  pari_sp av = avma;
  GEN CHI, mf, T, F, matdih;
  long N, k, lL, i, dim, SB;

  if (checkmf_i(NK))
  {
    mf = NK;
    N = mf_get_N(mf);
    k = mf_get_k(mf);
    CHI = mf_get_CHI(mf);
  }
  else
  {
    checkNK(NK, &N, &k, &CHI, 0);
    mf = f? NULL: mfinit_i(NK, mf_NEW);
  }
  if (k != 1) pari_err_DOMAIN("mfgaloistype", "k", "!=", gen_1, stoi(k));
  if (!lim) lim = 200;
  SB = mfsturmNk(N,1) + 1;
  lim = maxss(lim, 3*SB);
  matdih = mfvectomat(mfdihedralnew(N,CHI), SB);
  if (f) return gerepileuptoint(av, mfgaloistype0(N,CHI, f, matdih, lim));

  dim = lg(mf_get_vtf(mf)) - 1;
  if (!dim) { avma = av; return cgetg(1, t_VEC); }
  if (lg(mf) != 8) mf = mfsplit(mf, 0, 0);
  F = mfeigenbasis(mf); lL = lg(F);
  T = cgetg(lL, t_VEC);
  for (i=1; i < lL; i++) gel(T,i) = mfgaloistype0(N,CHI, gel(F,i), matdih, lim);
  return gerepileupto(av, T);
}

/******************************************************************/
/*                   Find all dihedral forms.                     */
/******************************************************************/
/* lim >= 2 */
static void
consttabdihedral(long lim)
{ cache_set(cache_DIH, mfdihedralall(mkvecsmall2(1,lim))); }

/* a ideal coprime to bnr modulus */
static long
mfdiheval(GEN bnr, GEN w, GEN a)
{
  GEN L, cycn = gel(w,1), chin = gel(w,2);
  long ordmax = cycn[1];
  L = ZV_to_Flv(isprincipalray(bnr,a), ordmax);
  return Flv_dotproduct(chin, L, ordmax);
}

/* A(x^k) mod T */
static GEN
Galois(GEN A, long k, GEN T)
{
  if (typ(A) != t_POL) return A;
  return gmod(RgX_inflate(A, k), T);
}
static GEN
vecGalois(GEN v, long k, GEN T)
{
  long i, l;
  GEN w = cgetg_copy(v,&l);
  for (i = 1; i < l; i++) gel(w,i) = Galois(gel(v,i), k, T);
  return w;
}

static GEN
fix_pol(GEN S, GEN Pn, int *trace)
{
  if (typ(S) != t_POL) return S;
  setvarn(S, varn(Pn));
  S = simplify_shallow(RgX_rem(S, Pn));
  if (typ(S) == t_POL) *trace = 1;
  return S;
}

static GEN
dihan(GEN bnr, GEN w, GEN Tinit, GEN k0j, ulong lim)
{
  GEN nf = bnr_get_nf(bnr), f = bid_get_ideal(bnr_get_bid(bnr));
  GEN v = zerovec(lim+1), cycn = gel(w,1), Pn = gel(w,3);
  long j, ordmax = cycn[1], k0 = k0j[1], jdeg = k0j[2];
  long D = itos(nf_get_disc(nf));
  int trace = 0;
  ulong p, n;
  forprime_t T;

  gel(v,2) = gen_1;
  u_forprime_init(&T, 2, lim);
  /* fill in prime powers first */
  while ((p = u_forprime_next(&T)))
  {
    GEN vP, vchiP, S;
    long k, lP;
    ulong q, qk;
    if (kross(D,p) >= 0) q = p;
    else
    {
      q = umuluu_or_0(p,p);
      if (!q || q > lim) continue;
    }
    /* q = Norm P */
    vP = idealprimedec(nf, utoipos(p));
    lP = lg(vP);
    vchiP = cgetg(lP, t_VECSMALL);
    for (j = k = 1; j < lP; j++)
    {
      GEN P = gel(vP,j);
      if (!idealval(nf, f, P)) vchiP[k++] = mfdiheval(bnr,w,P);
    }
    if (k == 1) continue;
    setlg(vchiP, k); lP = k;
    if (lP == 2)
    { /* one prime above p not dividing f */
      long s, s0 = vchiP[1];
      for (qk=q, s = s0;; s = Fl_add(s,s0,ordmax))
      {
        S = mygmodulo_lift(s, ordmax, gen_1);
        gel(v, qk+1) = fix_pol(S, Pn, &trace);
        qk = umuluu_or_0(qk, q); if (!qk || qk > lim) break;
      }
    }
    else /* two primes above p not dividing f */
    {
      long s, s0 = vchiP[1], s1 = vchiP[2];
      for (qk=q, k = 1;; k++)
      { /* sum over a,b s.t. Norm( P1^a P2^b ) = q^k, i.e. a+b = k */
        long a;
        GEN S = gen_0;
        for (a = 0; a <= k; a++)
        {
          s = Fl_add(Fl_mul(a, s0, ordmax), Fl_mul(k-a, s1, ordmax), ordmax);
          S = gadd(S, mygmodulo_lift(s, ordmax, gen_1));
        }
        gel(v, qk+1) = fix_pol(S, Pn, &trace);
        qk = umuluu_or_0(qk, q); if (!qk || qk > lim) break;
      }
    }
  }
  /* complete with non-prime powers */
  for (n = 2; n <= lim; n++)
  {
    GEN S, fa = myfactoru(n), P = gel(fa, 1), E = gel(fa, 2);
    long q;
    if (lg(P) == 2) continue;
    /* not a prime power */
    q = upowuu(P[1],E[1]);
    S = gmul(gel(v, q + 1), gel(v, n/q + 1));
    gel(v, n+1) = fix_pol(S, Pn, &trace);
  }
  if (trace)
  {
    if (lg(Tinit) == 4) v = QabV_tracerel(Tinit, jdeg, v);
    /* Apply Galois Mod(k0, ordw) */
    if (k0 > 1) { GEN Pm = gel(Tinit,1); v = vecGalois(v, k0, Pm); }
  }
  return v;
}

/* as cyc_normalize for t_VECSMALL cyc */
static GEN
cyc_normalize_zv(GEN cyc)
{
  long i, o = cyc[1], l = lg(cyc); /* > 1 */
  GEN D = cgetg(l, t_VECSMALL);
  D[1] = o; for (i = 2; i < l; i++) D[i] = o / cyc[i];
  return D;
}
/* as char_normalize for t_VECSMALLs */
static GEN
char_normalize_zv(GEN chi, GEN ncyc)
{
  long i, l = lg(chi);
  GEN c = cgetg(l, t_VECSMALL);
  if (l > 1) {
    c[1] = chi[1];
    for (i = 2; i < l; i++) c[i] = chi[i] * ncyc[i];
  }
  return c;
}

static GEN
dihan_bnf(long D)
{ setrand(gen_1); return Buchall(quadpoly(stoi(D)), 0, LOWDEFAULTPREC); }
static GEN
dihan_bnr(GEN bnf, GEN A)
{ setrand(gen_1); return bnrinit0(bnf, A, 1); }

static GEN
dihan_init(GEN bnr, GEN chi)
{
  GEN cycn = cyc_normalize_zv( ZV_to_zv( bnr_get_cyc(bnr) ) );
  GEN chin = char_normalize_zv(chi, cycn);
  long ord = ord_canon(cycn[1]);
  GEN Pn = (ord == 1)? gen_0: polcyclo(ord, fetch_user_var("t"));
  return mkvec3(cycn, chin, Pn);
}

/* Hecke xi * (D/.) = Dirichlet chi, return v in Q^r st chi(g_i) = e(v[i]).
 * cycn = cyc_normalize_zv(bnr.cyc), chin = char_normalize_zv(chi,cyc) */
static GEN
bnrchartwist2conrey(GEN chin, GEN cycn, GEN bnrconreyN, GEN kroconreyN)
{
  long l = lg(bnrconreyN), c1 = cycn[1], i;
  GEN v = cgetg(l, t_COL);
  for (i = 1; i < l; i++)
  {
    GEN d = gdivgs(utoi(zv_dotproduct(chin, gel(bnrconreyN,i))), c1);
    if (kroconreyN[i] < 0) d = gadd(d, ghalf);
    gel(v,i) = d;
  }
  return v;
}

/* chi(g_i) = e(v[i]) denormalize wrt Conrey generators orders */
static GEN
conreydenormalize(GEN znN, GEN v)
{
  GEN gcyc = znstar_get_conreycyc(znN), w;
  long l = lg(v), i;
  w = cgetg(l, t_COL);
  for (i = 1; i < l; i++)
    gel(w,i) = modii(gmul(gel(v,i), gel(gcyc,i)), gel(gcyc,i));
  return w;
}

static long
Miyake(GEN vchi, GEN gb, GEN cycn)
{
  long i, e = cycn[1], lb = lg(gb);
  GEN v = char_normalize_zv(vchi, cycn);
  for (i = 1; i < lb; i++)
    if ((zv_dotproduct(v, gel(gb,i)) -  v[i]) % e) return 1;
  return 0;
}

/* list of Hecke characters not induced by a Dirichlet character up to Galois
 * conjugation, whose conductor is bnr.cond; cycn = cyc_normalize(bnr.cyc)*/
static GEN
mklvchi(GEN bnr, GEN con, GEN cycn)
{
  GEN gb = NULL, cyc = bnr_get_cyc(bnr), cycsmall = ZV_to_zv(cyc);
  GEN vchi = cyc2elts(cycsmall);
  long ordmax = cycsmall[1], c, i, l;
  if (con)
  {
    GEN g = bnr_get_gen(bnr), nf = bnr_get_nf(bnr);
    long lg = lg(g);
    gb = cgetg(lg, t_VEC);
    for (i = 1; i < lg; ++i)
      gel(gb,i) = ZV_to_zv(isprincipalray(bnr, galoisapply(nf, con, gel(g,i))));
  }
  l = lg(vchi);
  for (i = c = 1; i < l; i++)
  {
    GEN chi = gel(vchi,i);
    if (!con || Miyake(chi, gb, cycn)) gel(vchi, c++) = Flv_to_ZV(chi);
  }
  setlg(vchi, c); l = c;
  for (i = 1; i < l; i++)
  {
    GEN chi = gel(vchi,i);
    long n;
    if (!chi) continue;
    for (n = 2; n < ordmax; n++)
      if (cgcd(n, ordmax) == 1)
      {
        GEN tmp = vecmodii(gmulsg(n, chi), cyc);
        long j;
        for (j = i+1; j < l; ++j)
          if (gel(vchi,j) && gequal(gel(vchi,j), tmp)) gel(vchi,j) = NULL;
      }
  }
  for (i = c = 1; i < l; i++)
  {
    GEN chi = gel(vchi,i);
    if (chi && bnrisconductor(bnr, chi)) gel(vchi, c++) = chi;
  }
  setlg(vchi, c); return vchi;
}

/* con = NULL if D > 0 or if D < 0 and id != idcon. */
static GEN
mfdihedralcommon(GEN bnf, GEN id, GEN znN, GEN kroconreyN, long N, long D, GEN con)
{
  GEN bnr, bnrconreyN, cyc, cycn, Lvchi, res, g;
  long i, j, ordmax, l, lc, deghecke, degrel;

  bnr = dihan_bnr(bnf, id);
  cyc = ZV_to_zv( bnr_get_cyc(bnr) );
  lc = lg(cyc); if (lc == 1) return NULL;

  g = znstar_get_conreygen(znN); l = lg(g);
  bnrconreyN = cgetg(l, t_VEC);
  for (i = 1; i < l; i++)
    gel(bnrconreyN,i) = ZV_to_zv(isprincipalray(bnr,gel(g,i)));

  cycn = cyc_normalize_zv(cyc);
  ordmax = cyc[1];
  deghecke = myeulerphiu(ordmax);
  Lvchi = mklvchi(bnr, con, cycn); l = lg(Lvchi);
  if (l == 1) return NULL;
  res = cgetg(l, t_VEC);
  for (j = 1; j < l; j++)
  {
    GEN T, Tinit, v, vchi = ZV_to_zv(gel(Lvchi,j));
    GEN chin = char_normalize_zv(vchi, cycn);
    long ordw, vnum, k0;
    v = bnrchartwist2conrey(chin, cycn, bnrconreyN, kroconreyN);
    ordw = itos(Q_denom(v));
    Tinit = Qab_trace_init(ord_canon(ordmax), ord_canon(ordw));
    vnum = itos(znconreyexp(znN, conreydenormalize(znN, v)));
    degrel = deghecke / myeulerphiu(ordw);
    k0 = getminvnum(N, ordw, &vnum);
    /* encodes degrel forms: jdeg = 0..degrel-1 */
    T = mkvecsmalln(6, N, k0, vnum, D, ordmax, degrel);
    gel(res,j) = mkvec4(T, id, vchi, Tinit);
  }
  return res;
}

/* Append to v all dihedral weight 1 forms coming from D, if fundamental. */
/* B a t_VECSMALL: if #B=1, only that level; if B=[Bmin,Bmax], Bmin <= Bmax:
 * between those levels. */
static void
append_dihedral(GEN v, long D, GEN B)
{
  long Da = labs(D), no, N, i, numi, ct, min, max;
  GEN bnf, con, LI, resall, varch;
  pari_sp av;

  if (lg(B) == 2)
  {
    long b = B[1], m = D > 0? 3: 1;
    min = b / Da;
    if (b % Da || min < m) return;
    max = min;
  }
  else
  { /* assume B[1] < B[2] */
    min = (B[1] + Da-1)/Da;
    max = B[2]/Da;
  }
  if (!sisfundamental(D)) return;

  av = avma;
  bnf = dihan_bnf(D);
  con = gel(galoisconj(bnf,gen_1), 2);
  LI = ideallist(bnf, max);
  numi = 0; for (i = min; i <= max; i++) numi += lg(gel(LI, i)) - 1;
  if (D > 0)
  {
    numi <<= 1;
    varch = mkvec2(mkvec2(gen_1,gen_0), mkvec2(gen_0,gen_1));
  }
  else
    varch = NULL;
  resall = cgetg(numi+1, t_VEC); ct = 1;
  for (no = min; no <= max; no++)
  {
    GEN LIs, znN, conreyN, kroconreyN;
    long flcond, lgc, lglis;
    if (D < 0)
      flcond = (no == 2 || no == 3 || (no == 4 && (D&7L)==1));
    else
      flcond = (no == 4 && (D&7L) != 1);
    if (flcond) continue;
    LIs = gel(LI, no);
    N = Da*no;
    znN = znstar0(utoi(N), 1);
    conreyN = znstar_get_conreygen(znN); lgc = lg(conreyN);
    kroconreyN = cgetg(lgc, t_VECSMALL);
    for (i = 1; i < lgc; ++i) kroconreyN[i] = krosi(D, gel(conreyN, i));
    lglis = lg(LIs);
    for (i = 1; i < lglis; ++i)
    {
      GEN id = gel(LIs, i), idcon, conk;
      long j, inf, maxinf;
      if (typ(id) == t_INT) continue;
      idcon = galoisapply(bnf, con, id);
      conk = (D < 0 && gequal(idcon, id)) ? con : NULL;
      for (j = i; j < lglis; ++j)
        if (gequal(idcon, gel(LIs, j))) gel(LIs, j) = gen_0;
      maxinf = (D < 0 || gequal(idcon,id))? 1: 2;
      for (inf = 1; inf <= maxinf; inf++)
      {
        GEN ide = (D > 0)? mkvec2(id, gel(varch,inf)): id;
        GEN res = mfdihedralcommon(bnf, ide, znN, kroconreyN, N, D, conk);
        if (res) gel(resall, ct++) = res;
      }
    }
  }
  if (ct == 1) avma = av;
  else
  {
    setlg(resall, ct);
    vectrunc_append(v, gerepilecopy(av, shallowconcat1(resall)));
  }
}

static long
di_N(GEN a) { return gel(a,1)[1]; }
/* All primitive dihedral wt1 forms: LIM a t_VECSMALL with a single component
 * (only level LIM) or 2 components [m,M], m < M (between m and M) */
static GEN
mfdihedralall(GEN LIM)
{
  GEN res, z;
  long limD, ct, i, l1, l2;

  if (lg(LIM) == 2) l1 = l2 = LIM[1]; else { l1 = LIM[1]; l2 = LIM[2]; }
  limD = l2;
  res = vectrunc_init(2*limD);
  if (l1 == l2)
  {
    GEN D = mydivisorsu(l1);
    long l = lg(D), j;
    for (j = 2; j < l; ++j)
    {
      long d = D[j];
      append_dihedral(res, -d, LIM);
      if (d >= 5 && D[l-j] >= 3) append_dihedral(res, d, LIM);
    }
  }
  else
  {
    long D;
    for (D = -3; D >= -limD; D--) append_dihedral(res, D, LIM);
    limD /= 3;
    for (D = 5; D <= limD;   D++) append_dihedral(res, D, LIM);
  }
  ct = lg(res);
  if (ct > 1)
  { /* concat and sort wrt N */
    res = shallowconcat1(res);
    res = vecpermute(res, indexvecsort(res, mkvecsmall(1)));
    ct = lg(res);
  }
  z = const_vec(l2-l1+1, cgetg(1,t_VEC));
  for (i = 1; i < ct;)
  { /* regroup result sharing the same N */
    long n = di_N(gel(res,i)), j = i+1, k;
    GEN v;
    while (j < ct && di_N(gel(res,j)) == n) j++;
    n -= l1-1;
    gel(z, n) = v = cgetg(j-i+1, t_VEC);
    for (k = 1; i < j; k++,i++) gel(v,k) = gel(res,i);
  }
  return z;
}
static GEN
mfdihedral(long N)
{
  GEN z = cache_get(cache_DIH, N);
  if (z) return z;
  z = mfdihedralall(mkvecsmall(N)); return gel(z,1);
}

/* k0 defined and invertible mod ordw | ordmax; lift it to an invertible
 * mod ordmax */
static long
lift_k0(long k0, long ordw, long ordmax)
{
  while (cgcd(k0, ordmax) > 1) k0 += ordw;
  return k0 % ordmax;
}
static long
get_k0(long ordw, long k0, GEN T)
{
  long ordmax = T[5], k = T[2];
  k0 = lift_k0(k0,ordw,ordmax);
  k0 = (Fl_inv(k0,ordmax)* k) % ordmax;
  return lift_k0(k0,ordw,ordmax);
}

/* return [vF, index], where vecpermute(vF,index) generates dihedral forms
 * for character CHI */
static GEN
mfdihedralnew_i(long N, GEN CHI)
{
  GEN Pm, vf, M, V, SP = mfdihedral(N);
  long d, ordw, i, SB, c, l, k0, k1, chino, chinoorig, lv;

  ordw = mfcharorder(CHI);
  chinoorig = mfcharno(CHI);
  CHI = mfconreyminimize(N, CHI, &chino, &k0);
  k1 = Fl_inv(k0 % ordw, ordw);
  lv = lg(SP); V = cgetg(lv, t_VEC);
  d = 0;
  for (i = l = 1; i < lv; i++)
  {
    GEN sp = gel(SP,i), T = gel(sp,1);
    if (T[3] != chino) continue;
    d += T[6];
    if (k1 != 1)
    {
      GEN t = leafcopy(T); t[3] = chinoorig; t[2] = (t[2]*k1)%ordw;
      sp = mkvec4(t, gel(sp,2), gel(sp,3), gel(sp,4));
    }
    gel(V, l++) = sp;
  }
  setlg(V, l); /* dihedral forms of level N and character CHI */
  if (l == 1) return NULL;

  SB = myeulerphiu(ordw) * mfsturmNk(N,1) + 1;
  M = cgetg(d+1, t_MAT);
  vf = cgetg(d+1, t_VEC);
  for (i = c = 1; i < l; i++)
  { /* T = [N, k0, conreyno, D, ordmax, degrel] */
    GEN an, bnf, bnr, w, Vi = gel(V,i);
    GEN T = gel(Vi,1), id = gel(Vi,2), vchi = gel(Vi,3), Tinit = gel(Vi,4);
    long k0i, jdeg, D = T[4], degrel = T[6];
    k0i = get_k0(ordw, k0, T);
    bnf = dihan_bnf(D);
    bnr = dihan_bnr(bnf, id);
    w = dihan_init(bnr, vchi);
    for (jdeg = 0; jdeg < degrel; jdeg++,c++)
    {
      GEN k0j = mkvecsmall2(k0i, jdeg);
      an = dihan(bnr, w, Tinit, k0j, SB);
      settyp(an, t_COL); gel(M,c) = Q_primpart(an);
      gel(vf,c) = tag5(t_MF_DIHEDRAL, bnr, w, Tinit, k0j, CHI);
    }
  }
  Pm = gmael3(V,1,4,1);
  V = (degpol(Pm) == 1)? ZM_indexrank(M): ZabM_indexrank(M,Pm,ord_canon(ordw));
  return mkvec2(vf,gel(V,2));
}
static long
mfdihedralnewdim(long N, GEN CHI)
{
  pari_sp av = avma;
  GEN S = mfdihedralnew_i(N, CHI);
  long d = S ? lg(gel(S,2))-1: 0;
  avma = av; return d;
}
static GEN
mfdihedralnew(long N, GEN CHI)
{
  pari_sp av = avma;
  GEN S = mfdihedralnew_i(N, CHI);
  if (!S) { avma = av; return cgetg(1, t_VEC); }
  return vecpermute(gel(S,1), gel(S,2));
}

static long
mfdihedralcuspdim(long N, GEN CHI)
{
  pari_sp av = avma;
  GEN D, CHIP;
  long F, i, lD, dim;

  CHIP = mfchartoprimitive(CHI, &F);
  D = divisorsu(N/F); lD = lg(D);
  dim = mfdihedralnewdim(N, CHI); /* d = 1 */
  for (i = 2; i < lD; ++i)
  {
    long d = D[i], M = N/d;
    dim += mfdihedralnewdim(M, mfcharinduce(CHIP,M)) * mynumdivu(d);
  }
  avma = av; return dim;
}

static GEN
mfbdall(GEN E, long N)
{
  GEN v, D = mydivisorsu(N);
  long i, j, lD = lg(D) - 1, lE = lg(E) - 1;
  v = cgetg(lD*lE + 1, t_VEC);
  for (j = 0; j < lE; j++)
  {
    GEN Ej = gel(E, j+1);
    for (i = 0; i < lD; i++) gel(v, i*lE + j+1) = mfbd_i(Ej, D[i+1]);
  }
  return v;
}
static GEN
mfdihedralcusp(long N, GEN CHI)
{
  pari_sp av = avma;
  GEN D, CHIP, z;
  long F, i, lD;

  CHIP = mfchartoprimitive(CHI, &F);
  D = divisorsu(N/F); lD = lg(D);
  z = cgetg(lD, t_VEC);
  gel(z,1) = mfdihedralnew(N, CHI);
  for (i = 2; i < lD; ++i) /* skip 1 */
  {
    long d = D[i], M = N / d;
    GEN LF = mfdihedralnew(M, mfcharinduce(CHIP, M));
    gel(z,i) = mfbdall(LF, d);
  }
  return gerepilecopy(av, shallowconcat1(z));
}

long
mfdihedraldim(long N, GEN CHI, long space)
{
  CHI = get_mfchar(CHI);
  return space==mf_NEW? mfdihedralnewdim(N, CHI): mfdihedralcuspdim(N, CHI);
}

static void
mf_set_space(GEN mf, long x) { gmael(mf,1,4) = utoi(x); }
static void
mf_set_vtf(GEN mf, GEN x) { gel(mf,3) = x; }
static void
mf_set_newforms(GEN mf, GEN x) { gel(mf,6) = x; }
static void
mf_set_Ms(GEN mf, GEN x) { gel(mf,5) = x; }

static GEN
mfwt1newinit(long N, GEN CHI, GEN TMP)
{
  const long vy = 1;
  GEN mf, vtf, galpols, F, vtfnew, vnewforms, M, z, MZ, tmp;
  long dimcusp, nbgal, dimnew, i, ct, sb, ord;

  mf = mfwt1init(N, CHI, TMP);
  if (!mf) return NULL;
  mf = mfsplit(mf, 0, 0);
  mf_set_space(mf, mf_NEW);
  vtf = mf_get_vtf(mf);
  dimcusp = lg(vtf) - 1;
  galpols = mf_get_fields(mf);
  F = mf_get_newforms(mf);
  nbgal = lg(galpols) - 1;
  dimnew = 0;
  for (i = 1; i <= nbgal; i++) dimnew += degpol(gel(galpols,i));
  vtfnew = cgetg(dimnew + 1, t_VEC); ct = 0;
  vnewforms = cgetg(nbgal + 1, t_VEC);
  for (i = 1; i <= nbgal; i++)
  {
    GEN pol = gel(galpols, i), f = liftpol_shallow(gel(F,i));
    long d = degpol(pol), j;
    if (d == 1)
    {
      gel(vtfnew, ++ct) = mflinear_wt1(vtf, f);
      tmp = mkvec(gen_1);
    }
    else
    {
      f = shallowtrans( RgXV_to_RgM(f, dimcusp) );
      for (j = 1; j <= d; j++) gel(vtfnew, ++ct) = mflinear_wt1(vtf, gel(f,j));
      tmp = gmodulo(pol_x_powers(d, vy), pol);
    }
    if (ct - d) tmp = concat(zerovec(ct - d), tmp);
    if (dimnew - ct) tmp = concat(tmp, zerovec(dimnew - ct));
    gel(vnewforms, i) = tmp;
  }
  mf_set_vtf(mf, vtfnew);
  mf_set_newforms(mf, vnewforms);
  sb = mfsturmNk(N, 1);
  M = mfvectomat(vtfnew, sb);
  ord = mfcharorder(CHI);
  if (ord <= 2)
  {
    MZ = vec_Q_primpart(M);
    z = ZM_indexrank(MZ);
  }
  else
  {
    MZ = vec_Q_primpart(liftpol_shallow(M));
    ord = ord_canon(ord);
    z = ZabM_indexrank(MZ, polcyclo(ord, fetch_user_var("t")), ord);
  }
  /* TODO Minv */
  mf_set_Ms(mf, mkvec3(z, gen_0, M));
  return mf;
}

/* CHI an mfchar */
static GEN
toNK(long N, long k, GEN CHI)
{ return mkvec3(utoi(N),utoi(k),mfchar2char(CHI)); }
static int
cmp_ord(void *E, GEN a, GEN b)
{
  GEN chia = mf_get_CHI(a), chib = mf_get_CHI(b);
  (void)E; return cmpii(gmfcharorder(chia), gmfcharorder(chib));
}
static GEN
mfwttrivialall(GEN mf1, GEN CHI)
{
  long i, l;
  GEN v;
  if (!CHI) return cgetg(1, t_VEC);
  l = lg(CHI); v = cgetg(l, t_VEC);
  for (i = 1; i < l; i++)
  {
    GEN w = leafcopy(mf1);
    gel(w,3) = gel(CHI,i);
    gel(v,i) = mfEMPTY(w);
  }
  return v;
}
static int
space_is_cusp(long space) { return space != mf_FULL && space != mf_EISEN; }
/* mfinit structures. Can be length 5 (full/cusp/oldspace or newspace nonsplit)
   or length 7 (newspace split).
-- mf[1] contains [N,k,CHI,space],
-- mf[2] contains vector of closures of Eisenstein series, empty if not
   full space.
-- mf[3] contains vector of closures, so #mf[3] = dimension of cusp/new space.
-- mf[4] contains the corresponding indices: either j for T(j)tf if newspace,
   or [M,j,d] for B(d)T(j)tf_M if cuspspace or oldspace.
-- mf[5] contains the matrix M of first coefficients of basis, never cleaned.
-- mf[6] contains the vector of vectors of coefficients on mf[3] of the
   eigenspaces, as polmods in the variable y, so #mf[6] is the number of
   eigenspaces.
-- mf[7] contains the defining polynomials of the polmods, so #mf[7] is also
   the number of eigenspaces, and the degrees of the polynomials are the
   dimensions.
 * NK is either [N,k] or [N,k,CHI].
 * mfinit does not do the splitting, only the basis generation. */
static GEN
mfinit_i(GEN NK, long space)
{
  GEN mf = NULL, mf1, CHI;
  long N, k, joker;
  checkNK(NK, &N, &k, &CHI, 1);
  joker = !CHI || typ(CHI) == t_COL;
  mf1 = mkvec4(utoi(N), stoi(k), CHI, utoi(space));
  if (k < 0) return joker? mfwttrivialall(mf1, CHI): mfEMPTY(mf1);
  if (joker)
  {
    GEN vCHI = CHI;
    long i, j, l;
    if (CHI && lg(CHI) == 1) return cgetg(1,t_VEC);
    if (k == 1)
    {
      if (space != mf_CUSP && space != mf_NEW)
        pari_err_IMPL("mfinit([N,1,wildcard], space != cusp or new space)");
      mf = mfwt1initall(N, CHI, space);
    }
    else
    {
      if (!vCHI) vCHI = mfchargalois(N, k & 1, NULL);
      l = lg(vCHI); mf = cgetg(l, t_VEC);
      for (i = j = 1; i < l; i++)
      {
        GEN v = mfinit_i(toNK(N,k,gel(vCHI,i)), space);
        if (mf_get_dim(v) || CHI) gel(mf, j++) = v;
      }
      setlg(mf,j);
    }
    if (!CHI) gen_sort_inplace(mf, NULL, &cmp_ord, NULL);
    return mf;
  }
  if (!ischarok(N, k, CHI)) return mfEMPTY(mf1);
  if (k == 0) /*nothing*/;
  else if (k == 1)
  {
    switch (space)
    {
      case mf_NEW: mf = mfwt1newinit(N, CHI, NULL); break;
      case mf_FULL:
      case mf_CUSP: mf = mfwt1init(N, CHI, NULL); break;
      case mf_EISEN:mf = mfEMPTY(NULL); break;
      case mf_OLD: pari_err_IMPL("mfinit in weight 1 for old space");
      default: pari_err_FLAG("mfinit");
    }
  }
  else /* k >= 2 */
  {
    switch(space)
    {
      cachenew_t cache;
      case mf_NEW:  mf = mfnewinit(N, k, CHI, &cache, 1); break;
      case mf_EISEN:mf = mfEMPTY(NULL); break;
      case mf_CUSP:
      case mf_OLD:
      case mf_FULL: mf = mfinitcusp(N, k, CHI, mf1, space); break;
      default: pari_err_FLAG("mfinit");
    }
  }
  if (!mf) mf = mfEMPTY(mf1);
  else
  {
    gel(mf,1) = mf1;
    if (space == mf_NEW)
    { /* clean mf */
      GEN dM, P, z = mf_get_Mindex(mf), M = mf_get_M(mf);
      long ord = ord_canon(mfcharorder(CHI));
      P = (ord == 1)? NULL: polcyclo(ord, fetch_user_var("t"));
      M = Q_remove_denom(M, &dM);
      gel(mf,5) = mfclean2(M, gel(z,1), P, ord, dM);
    }
  }
  if (!space_is_cusp(space))
  {
    long sb = mfsturmNk(N,k);
    GEN M;
    gel(mf,2) = mfeisenbasis_i(N, k, CHI);
    M = mfvectomat(mf_get_basis(mf), sb+1); /* uses mf[2] */
    gel(mf,5) = mfclean(M, mfcharorder(CHI));
  }
  return mf;
}
GEN
mfinit(GEN NK, long space)
{
  pari_sp av = avma;
  return gerepilecopy(av, mfinit_i(NK, space));
}

/* UTILITY FUNCTIONS */

/* mfeval for an element of S_k(\SL_2(\Z)), also valid near cusps
 * vtau a t_VEC of elements */
static GEN
mfzeval(long k, GEN F, GEN vtau, long bitprec)
{
  pari_sp ltop = avma;
  GEN vga, vtau1, vres0, vres;
  long lv = lg(vtau), i;
  vga = cgetg(lv, t_VEC);
  vtau1= cgetg(lv, t_VEC);
  for (i = 1; i < lv; ++i) gel(vtau1,i) = cxredsl2(gel(vtau,i), &gel(vga,i));
  vres0 = mfeval0(0, k, F, vtau1, bitprec);
  vres = cgetg(lv, t_VEC);
  for (i = 1; i < lv; ++i)
    if (gexpo(imag_i(gel(vtau1,i))) > 10)
      gel(vres,i) = gen_0;
    else
    {
      GEN z = gel(vtau,i), g = gel(vga,i), c = gcoeff(g,2,1), d = gcoeff(g,2,2);
      gel(vres,i) = gmul(gpowgs(gadd(gmul(c,z), d), -k), gel(vres0, i));
    }
  return gerepileupto(ltop, vres);
}

static int
RgV_embedded(GEN v)
{
  long i, l = lg(v);
  for (i = 1; i < l; i++)
    if (typ(gel(v,i)) == t_POLMOD) return 0;
  return 1;
}

/* evaluate an mf closure numerically, i.e., in the usual sense,
either for a single tau or a vector of tau. If N=1, assume that
F is in S_k(\SL_2(\Z)), otherwise imaginary part must not be too small. */
static GEN
mfeval0(long N, long k, GEN F, GEN vtau, long bitprec)
{
  pari_sp ltop = avma;
  GEN vs, vq, PI2I, an, vecan;
  double tmpdbl, nlimdbl;
  long ta, nlim, lv, i, n, pr, prec = nbits2prec(bitprec), flscal = 0;

  ta = typ(vtau);
  if (ta != t_VEC && ta != t_COL) { flscal = 1; vtau = mkvec(vtau); }
  if (N == 1)
  {
    vs = mfzeval(k, F, vtau, bitprec);
    return flscal ? gerepilecopy(ltop, gel(vs, 1)) : vs;
  }
  if (!N) N = 1;
  tmpdbl = 2*M_PI*gtodouble(vecmin(imag_i(vtau)));
  pr = bitprec + 10;
  nlimdbl = ceil(pr*LOG2/tmpdbl);
  tmpdbl -= (k-1)/(2*nlimdbl); if (tmpdbl < 1) tmpdbl = 1.;
  nlimdbl += ceil((0.7+(k-1)/2*log(nlimdbl))/tmpdbl);
  nlim = (long)nlimdbl;
  lv = lg(vtau);
  vs = cgetg(lv, ta);
  vq = cgetg(lv, t_VEC);
  PI2I = PiI2(prec);
  vecan = mfcoefs(F, nlim, 1);
  if (!RgV_embedded(vecan)) pari_err_TYPE("mfeval [use mfembed first]",vecan);
  for (i = 1; i < lv; ++i)
  {
    gel(vs, i) = gel(vecan, nlim + 1);
    gel(vq, i) = gexp(gmul(PI2I, gel(vtau,i)), prec);
  }
  for (n = nlim - 1; n >= 0; --n)
  {
    an = gel(vecan, n + 1);
    for (i = 1; i < lv; ++i)
      gel(vs, i) = gadd(an, gmul(gel(vq, i), gel(vs, i)));
  }
  if (flscal) vs = gel(vs, 1);
  return gerepilecopy(ltop, vs);
}

GEN
mfeval(GEN F, GEN vtau, long bitprec)
{
  GEN P;
  long N, k;
  if (!isf(F)) pari_err_TYPE("mfeval", F);
  P = mfparams_ii(F); if (!P) pari_err_IMPL("mfeval for this form");
  N = itos(gel(P, 1)); k = itos(gel(P, 2));
  return mfeval0(N, k, F, vtau, bitprec);
}

static GEN
get_laq(GEN msp, GEN R, GEN veval, GEN c)
{
  GEN a = gen_0, b = gen_0;
  long j, l = lg(msp);
  for (j = 1; j < l; ++j)
  {
    GEN c = gel(msp,j), v = gel(veval,j);
    if (R) c = Rg_embed(c, R);
    a = gadd(a, gmul(c, gel(v,1)));
    b = gadd(b, gmul(c, gel(v,2)));
  }
  return gdiv(b, gmul(a,c));
}

/* P in ZX */
static GEN
ZX_roots(GEN P, long prec)
{
  long d = degpol(P);
  if (d == 1) return mkvec(gen_0);
  if (d == 2 && isint1(gel(P,2)) && isintzero(gel(P,3)) && isint1(gel(P,4)))
    return mkvec2(gen_I(), gneg(gen_I()));
  if (ZX_sturm(P) == d) return realroots(P, NULL, prec);
  return QX_complex_roots(P, prec);
}
/* P in Z[chi][X] */
static GEN
rootsC(GEN P, GEN zcyclo, long prec)
{
  GEN Q;
  if (RgX_is_QX(P)) return ZX_roots(P, prec);
  Q = RgX_embed(P, zcyclo); return roots(Q, prec);
}
/* initializations for RgX_RgV_eval / RgC_embed */
static GEN
rootspowers(GEN v)
{
  long i, l;
  GEN w = cgetg_copy(v, &l);
  for (i = 1; i < l; i++) gel(w,i) = gpowers(gel(v,i), l-2);
  return w;
}
/* split mf, quadratic character */
static GEN
mfQeigenroots(GEN mf, long prec)
{
  GEN z, vP = mf_get_fields(mf);
  long i, l = lg(vP);
  z = cgetg(l, t_VEC);
  for (i = 1; i < l; i++) gel(z,i) = rootspowers(ZX_roots(gel(vP,i),prec));
  return z;
}
/* non-real character of order o != 2 mod 4 */
static GEN
mfeigenroots(GEN mf, GEN zcyclo, long prec)
{
  GEN z, vP = mf_get_fields(mf);
  long i, l = lg(vP);
  z = cgetg(l, t_VEC);
  for (i = 1; i < l; i++) gel(z,i) = rootspowers(rootsC(gel(vP,i),zcyclo,prec));
  return z;
}

/* split mf */
static GEN
mfeigendims(GEN mf)
{
  GEN z, vP = mf_get_fields(mf);
  long i, l = lg(vP);
  z = cgetg(l, t_VECSMALL);
  for (i = 1; i < l; i++) z[i] = degpol(gel(vP,i));
  return z;
}

/* split mf; assume dim >=1, mfcharorder(CHI) = 2.
 * Here cannot use mfeigeneval since mfeigeneval uses mffricke. */
static GEN
mffrickeeigenvalues(GEN mf, GEN RO, long bitprec)
{
  GEN vtf, F, tau, wtau, Z, v, sqN, coe;
  long N, k, i, j, nbgal, dim, prec = nbits2prec(bitprec);

  N = mf_get_N(mf);
  vtf = mf_get_vtf(mf);
  dim = lg(vtf) - 1;
  F = mf_get_newforms(mf);
  nbgal = lg(F) - 1;
  Z = cgetg(nbgal+1, t_VEC);
  k = mf_get_k(mf);
  sqN = sqrtr_abs(utor(N, prec));
  tau = mkcomplex(ginv(utoi(1000)), ginv(sqN));
  wtau = ginv(gmulsg(-N, tau));
  coe = gpowgs(gmul(sqN, tau), k);
  v = cgetg(dim + 1, t_VEC);
  for (j = 1; j <= dim; ++j)
    gel(v,j) = mfeval0(N, k, gel(vtf,j), mkvec2(tau, wtau), bitprec);
  for (i = 1; i <= nbgal; i++)
  {
    GEN z, ro = gel(RO,i), f = gel(F,i);
    long l = lg(ro);
    if (l == 2) z = get_laq(f, NULL, v, coe);
    else
    {
      f = liftpol_shallow(f);
      z = cgetg(l, t_VEC);
      for (j = 1; j < l; j++) gel(z,j) = get_laq(f, gel(ro,j), v, coe);
    }
    gel(Z,i) = z;
  }
  return Z;
}

static long
atkin_check(long N, long Q)
{
  long NQ = N/Q;
  if (N % Q) pari_err_DOMAIN("mfatkineigenvalues","N % Q","!=",gen_0,utoi(Q));
  if (cgcd(NQ, Q) > 1)
    pari_err_DOMAIN("mfatkineigenvalues","gcd(Q,N/Q)","!=",gen_1,utoi(Q));
  return NQ;
}

static GEN
mfatkineigenvalues_i(GEN mf, long Q, GEN RO, long bitprec)
{
  GEN laq2, CHI, vtf, F, tau, wtau, Z, veval, den, CHIP, coe, sqrtQ;
  long FC, NQ, t, yq, i, j, nbgal, dim, muQ, prec = nbits2prec(bitprec);
  long N = mf_get_N(mf), k = mf_get_k(mf);

  NQ = atkin_check(N,Q);
  vtf = mf_get_vtf(mf); dim = lg(vtf) - 1;
  if (!dim) return cgetg(1, t_VEC);
  CHI = mf_get_CHI(mf);
  if (mfcharorder(CHI) > 2) pari_err_IMPL("nonreal CHI in mfatkineigenvalues");
  CHIP = mfchartoprimitive(CHI, &FC);
  if (NQ % FC)
  {
    if (Q != N) pari_err_IMPL("pseudo eigenvalues for W_Q");
    return mffrickeeigenvalues(mf, RO, bitprec);
  }
  /* Q coprime to FC */
  F = mf_get_newforms(mf);
  nbgal = lg(F) - 1;
  if (Q == 1)
  {
    GEN dims = mfeigendims(mf);
    long i, l = lg(dims);
    Z = cgetg(l,t_VEC);
    for (i = 1; i < l; ++i) gel(Z, i) = const_vec(dims[i], gen_1);
    return Z;
  }
  /* Q != 1 */
  if (!odd(k) && (muQ = moebiusu(Q)))
  {
    GEN vtfQ = cgetg(dim+1,t_VEC), dims = mfeigendims(mf), Qk = powuu(Q,k/2-1);
    long i, l = lg(dims), ok = 1;
    Z = cgetg(l, t_VEC);
    for (j = 1; j <= dim; j++) gel(vtfQ,j) = mfak_i(gel(vtf,j), Q);
    for (i = 1; i < l; i++)
    {
      GEN S = gen_0, f = gel(F,i);
      for (j = 1; j <= dim; j++)
      {
        GEN t = liftpol_shallow(gel(f,j));
        S = gadd(S, gmul(t, gel(vtfQ,j)));
      }
      if (typ(S) == t_POL) S = degpol(S) < 0? gen_0: gel(S,2);
      if (muQ == -1) S = gneg(S);
      if (ok && gequal0(S)) ok = 0;
      gel(Z, i) = const_vec(dims[i], gdiv(S, Qk));
    }
    if (ok) return Z;
  }
  else
    Z = zerovec(nbgal);
  laq2 = mfchareval_i(CHIP, Q); /* 1 or -1 */
  (void)cbezout(Q, NQ, &t, &yq);
  sqrtQ = sqrtr_abs(utor(Q,prec));
  tau = mkcomplex(gadd(gdivgs(stoi(-t), NQ), ginv(utoi(1000))),
                  divru(sqrtQ, N));
  den = gaddgs(gmulsg(NQ, tau), t);
  wtau = gdiv(gsub(tau, gdivgs(stoi(yq), Q)), den);
  coe = gpowgs(gmul(sqrtQ, den), k);
  veval = cgetg(dim + 1, t_VEC);
  for (j = 1; j <= dim; j++)
    gel(veval,j) = mfeval0(N, k, gel(vtf,j), mkvec2(tau,wtau), bitprec);
  for (i = 1; i <= nbgal; i++)
  {
    GEN z, ro = gel(RO,i), f = gel(F,i);
    long l = lg(ro);

    if (l == 2)
    {
      GEN lar = get_laq(f, NULL, veval, coe);
      lar = ground(lar);
      if (gexpo(gsub(gsqr(lar), laq2)) > -(bitprec>>1))
        pari_err_PREC("mfatkineigenvalues");
      z = mkvec(lar);
    }
    else
    {
      f = liftpol_shallow(f);
      z = cgetg(l, t_VEC);
      for (j = 1; j < l; j++)
      {
        GEN lar, laq = get_laq(f, gel(ro,j), veval, coe);
        if (gexpo(gsub(gsqr(laq), laq2)) > -(bitprec>>1))
          pari_err_PREC("mfatkineigenvalues");
        lar = ground(laq);
        if (typ(lar) == t_INT && is_pm1(lar))
        {
          if (j != 1) pari_err_BUG("mfatkineigenvalues [1]");
          z = const_vec(l-1, lar); break;
        }
        gel(z,j) = lar;
      }
    }
    if (!gequal0(gel(Z,i)) && !gequal(gel(Z,i), z))
      pari_err_BUG("mfatkineigenvalues [2]");
    gel(Z, i) = z;
  }
  return Z;
}
GEN
mfatkineigenvalues(GEN mf, long Q, long bit)
{
  pari_sp av = avma;
  GEN RO;
  checkmfsplit(mf); RO = mfQeigenroots(mf, nbits2prec(bit));
  return gerepilecopy(av, mfatkineigenvalues_i(mf,Q,RO,bit));
}

/* assume mf a split newspace for a real character, RO = mfQeigenroots(mf) */
static GEN
mfQeigenembed(GEN mf, GEN RO)
{
  long i, ct = 0, dim = mf_get_dim(mf);
  GEN F = mf_get_newforms(mf), M = cgetg(dim+1, t_MAT);
  for (i = 1; i < lg(F); i++)
  {
    GEN ro = gel(RO,i), f = gel(F,i);
    long j, l = lg(ro);
    if (l == 2) gel(M, ++ct) = f;
    else
      for (j = 1; j < l; j++) gel(M, ++ct) = RgC_embed(f, gel(ro,j));
  }
  return M; /* ct = dim */
}
/* assume mf a split newspace, general character, RO = mfQeigenroots(mf) */
static GEN
mfeigenembed(GEN mf, long vt, GEN vcyclo, GEN RO)
{
  long i, ct = 0, dim = mf_get_dim(mf);
  GEN F = mf_get_newforms(mf), M = cgetg(dim+1, t_MAT);
  for (i = 1; i < lg(F); i++)
  {
    GEN ro = gel(RO,i), f = gel(F,i);
    long j, l = lg(ro);
    for (j = 1; j < l; j++) gel(M, ++ct) = RgC_embed2(f, vt, vcyclo, gel(ro,j));
  }
  return M; /* ct = dim */
}

/* FIXME */
static long
RgC_study_fields(GEN mf, GEN v)
{
  const long vy = 1;
  long i, l = lg(v);
  GEN T = NULL, P = mf_get_fields(mf);
  for (i = 1; i < l; i++)
  {
    GEN c = gel(v,i);
    long t = typ(c);
    if (t == t_POLMOD && varn(gel(c,1)) == vy)
    { if (!T) T = gel(c,1); else if (!gequal(T,gel(c,1))) return -1; }
  }
  l = lg(P);
  for (i = 1; i < l; i++)
    if (gequal(T,gel(P,i))) return i;
  return 0;
}

/* split mf, embed F */
GEN
mftoeigenbasis(GEN mf, GEN F, long prec)
{
  GEN M, RO;
  long o;
  checkmfsplit(mf);
  o = ord_canon(mfcharorder(mf_get_CHI(mf)));
  F = mftobasis(mf, F, 0);
  if (o == 1)
  {
    RO = mfQeigenroots(mf,prec);
    M = mfQeigenembed(mf, RO);
    F = RgC_embed(F, RO);
  }
  else
  {
    const long vt = fetch_user_var("t");
    long i;
    GEN vcyclo = grootsof1(o, prec);
    RO = mfeigenroots(mf,vcyclo,prec);
    M = mfeigenembed(mf, vt, vcyclo, RO);
    i = RgC_study_fields(mf, F);
    if (i < 0) pari_err_IMPL("mftoeigenbasis in this case");
    if (i)
      F = RgC_embed2(F, vt, vcyclo, gmael(RO,i,1));
    else
      F = RgC_embed(F, vcyclo);
  }
  return RgM_solve(M,F);
}

static GEN
matapprox(GEN A, GEN dA)
{
  long e;
  A = grndtoi(RgM_Rg_mul(A,dA), &e);
  return (e < -32)? RgM_Rg_div(A, dA): NULL;
}

static GEN
mfmatatkin_i(GEN mf, long Q, long *cM)
{
  GEN M, M1, D, DN, MF, den, RO;
  long radN, N, k, i, l, dim, prec, s, bitprec;

  checkmfsplit(mf);
  if (mf_get_space(mf) != mf_NEW) pari_err_IMPL("mfmatatkin for full space");
  *cM = 1; dim = mf_get_dim(mf);
  if (!dim) return cgetg(1, t_MAT);
  N = mf_get_N(mf);
  k = mf_get_k(mf);
  radN = radical_u(N);
  den = muliu( gel(mf_get_Minv(mf), 2), radN);
  bitprec = expi(den) + 64;
  prec = nbits2prec(bitprec);
  RO = mfQeigenroots(mf, prec);
  D = mfatkineigenvalues_i(mf, Q, RO, bitprec);
  D = diagonal_shallow(shallowconcat1(D));
  M = mfQeigenembed(mf, RO);
  MF = gmul(M, gmul(D, ginv(M)));
  if (!odd(k) || Q != N || mfcharistrivial(mf_get_CHI(mf))) s = 1;
  else { MF = imag_i(MF); s = -1; }
  M1 = matapprox(MF, den);
  if (M1) { *cM = s; return M1; }
  DN = mydivisorsu(radN);
  l = lg(DN);
  for (i = 2; i < l; i++) /* skip 1 */
  {
    long d = DN[i];
    GEN MG = RgM_Rg_mul(MF, sqrtr_abs(utor(d,prec)));
    M1 = matapprox(MG, den);
    if (M1) { *cM = s * d; return M1; }
  }
  pari_err_BUG("mfmatatkin [no good approximation found]");
  return NULL;/*LCOV_EXCL_LINE*/
}
GEN
mfmatatkin(GEN mf, long Q, GEN *cM)
{
  pari_sp av = avma;
  long c;
  GEN M = gerepilecopy(av, mfmatatkin_i(mf, Q, &c));
  if (cM) *cM = utoipos(c);
  return M;
}

/* Apply atkin Q to closure F */
GEN
mfatkin(GEN mf, GEN F, GEN Q, long bitprec)
{
  pari_sp av = avma;
  GEN z;
  long A, prec = nbits2prec(bitprec);
  checkmf(mf);
  z = mftobasis_i(mf, F);
  switch(typ(Q))
  {
    case t_INT: Q = mfmatatkin_i(mf, itos(Q), &A); break;
    case t_VEC:
      if (lg(Q) == 3 && typ(gel(Q,1))==t_MAT && typ(gel(Q,2))==t_INT)
      {
        A = itos(gel(Q,2));
        Q = gel(Q,1); break;
      }
    default: pari_err_TYPE("mfatkin", Q);
             return NULL; /*LCOV_EXCL_LINE*/
  }
  z = RgM_RgC_mul(Q, z);
  if (A != 1) z = gdiv(z, sqrtr(stor(A,prec)));
  return gerepilecopy(av, mflinear_i(mf_get_vtf(mf), z));
}

/* Fourier expansion of form F (closure) at a cusp */
GEN
mfcuspexpansion(GEN mf, GEN F, GEN cusp, long n)
{
  pari_sp ltop = avma;
  GEN M, a;
  long N, Q, c = 0;

  checkmf(mf); N = mf_get_N(mf);
  if (n < 0) pari_err_DOMAIN("mfcuspexpansion", "n", "<", gen_0, stoi(n));
  switch(typ(cusp))
  {
    case t_INFINITY: c = N; break;
    case t_INT:   c = 1; break;
    case t_FRAC : c = itos(gel(cusp,2)); break;
    default: pari_err_TYPE("mfcuspexpansion", cusp);
  }
  if (N%c) pari_err_TYPE("mfcuspexpansion [cusp = a/b, with b|N]", cusp);
  Q = N/c;
  if (cgcd(c, Q) > 1)
    pari_err_IMPL("mfcuspexpansion for cusp a/c with gcd(c,N/c) > 1");
  M = mfmatatkin(mf, Q, NULL);
  a = RgM_RgC_mul(M, mftobasis_i(mf,F));
  a = c_linear(n, 1, mf_get_vtf(mf), a);
  return gerepileupto(ltop, a);
}

static GEN
search_from_mf(GEN mf, GEN vap, GEN vlp)
{
  pari_sp av = avma;
  long lvlp = lg(vlp), N = mf_get_N(mf);
  GEN v, M = NULL, vtf = mf_get_vtf(mf), S = mf_get_newforms(mf);
  long j, jv, lS;
  if (lvlp > 1) M = rowpermute(mfvectomat(vtf, vlp[lvlp-1]), vlp);
  v = cgetg_copy(S, &lS);
  for (j = jv = 1; j < lS; j++)
  {
    GEN vF = gel(S,j);
    long t;
    for (t = lvlp-1; t > 0; t--)
    { /* lhs = vlp[j]-th coefficient of eigenform */
      GEN rhs = gel(vap,t), lhs = RgMrow_RgC_mul(M, vF, t);
      if (!gequal(lhs, rhs)) break;
    }
    if (t) continue;
    gel(v,jv++) = mkvec2(utoi(N), mflinear_i(vtf,vF));
  }
  if (jv == 1) { avma = av; return NULL; }
  setlg(v,jv); return v;
}
GEN
mfsearch(GEN NK, GEN AP)
{
  pari_sp av = avma;
  GEN k, vap, vlp, vres = cgetg(1, t_VEC), D;
  long N, N0, i, l, even;

  if (!AP) l = 1;
  else
  {
    l = lg(AP);
    if (typ(AP) != t_VEC) pari_err_TYPE("mfsearch",AP);
  }
  vap = cgetg(l, t_VEC);
  vlp = cgetg(l, t_VEC);
  if (l > 1)
  {
    GEN perm = indexvecsort(AP, mkvecsmall(1));
    for (i = 1; i < l; ++i)
    {
      GEN v = gel(AP,perm[i]), gp, ap;
      if (typ(v) != t_VEC || lg(v) != 3) pari_err_TYPE("mfsearch", AP);
      gp = gel(v,1);
      ap = gel(v,2);
      if (typ(gp) != t_INT || (typ(ap) != t_INT && typ(ap) != t_INTMOD))
        pari_err_TYPE("mfsearch", AP);
      gel(vap,i) = ap;
      vlp[i] = itos(gp)+1; if (vlp[i] < 0) pari_err_TYPE("mfsearch", AP);
    }
  }
  l = lg(NK);
  if (typ(NK) != t_VEC || l != 3
      || typ(gel(NK,1)) != t_INT
      || typ(gel(NK,2)) != t_INT) pari_err_TYPE("mfsearch",NK);
  N0 = itos(gel(NK,1));
  k = gel(NK,2);
  vecsmall_sort(vlp);
  even = !mpodd(k);
  for (N = 1; N <= N0; N++)
  {
    pari_sp av2 = avma;
    GEN mf, L;
    if (even) D = gen_1;
    else
    {
      long r = (N&3L);
      if (r == 1 || r == 2) continue;
      D = stoi( corediscs(-N, NULL) ); /* < 0 */
    }
    mf = mfsplit(mkvec3(utoipos(N), k, D), 1, 0);
    L = search_from_mf(mf, vap, vlp);
    if (L) vres = shallowconcat(vres, L); else avma = av2;
  }
  return gerepilecopy(av, vres);
}

/* tf_{N,k}(n) */
static GEN
mfnewtracecache(long N, long k, long n, cachenew_t *cache)
{
  GEN C = NULL, S;
  long lcache;
  if (!n) return gen_0;
  S = gel(cache->vnew,N);
  lcache = lg(S);
  if (n < lcache) C = gel(S, n);
  if (C) cache->newHIT++;
  else C = mfnewtrace_i(N,k,n,cache);
  cache->newTOTAL++;
  if (n < lcache) gel(S,n) = C;
  return C;
}

static long
mfwt1dimsum(long N, long space)
{
  switch(space)
  {
    case mf_NEW:  return mfwt1newdim(N);
    case mf_CUSP: return mfwt1dim_i(N);
    case mf_OLD:  return mfwt1dim_i(N) - mfwt1newdim(N);
  }
  pari_err_FLAG("mfdim");
  return 0; /*LCOV_EXCL_LINE*/
}
static long
mfwtkdimsum(long N, long k, long space)
{
  GEN w = mfchargalois(N, k & 1, NULL);
  long i, j, d = 0, l = lg(w);
  for (i = j = 1; i < l; i++)
  {
    GEN CHI = gel(w,i);
    d += itou( mfdim(toNK(N,k,CHI), space) );
  }
  return d;
}
static GEN
mfwt1dims(long N, GEN vCHI, long space)
{
  GEN D = NULL;
  switch(space)
  {
    case mf_NEW: D = mfwt1newdimall(N, vCHI); break;
    case mf_CUSP:D = mfwt1dimall(N, vCHI); break;
    case mf_OLD: D = mfwt1olddimall(N, vCHI); break;
    default: pari_err_FLAG("mfdim");
  }
  return D;
}
static GEN
mfwtkdims(long N, long k, GEN vCHI, long space)
{
  GEN D, w = vCHI? vCHI: mfchargalois(N, k & 1, NULL);
  long i, j, l = lg(w);
  D = cgetg(l, t_VEC);
  for (i = j = 1; i < l; i++)
  {
    GEN CHI = gel(w,i);
    long d = itou( mfdim(toNK(N,k,CHI), space) );
    if (vCHI)
      gel(D, j++) = mkvec2s(d, 0);
    else if (d)
      gel(D, j++) = fmt_dim(CHI, d, 0);
  }
  setlg(D,j); return D;
}
GEN
mfdim(GEN NK, long space)
{
  pari_sp av = avma;
  long N, k, joker;
  GEN CHI;
  if (checkmf_i(NK)) return utoi(mf_get_dim(NK));
  checkNK(NK, &N, &k, &CHI, 2);
  if (!CHI) joker = 1;
  else
    switch(typ(CHI))
    {
      case t_INT: joker = 2; break;
      case t_COL: joker = 3; break;
      default: joker = 0; break;
    }
  if (joker)
  {
    long d;
    GEN D;
    if (k < 0) switch(joker)
    {
      case 1: return cgetg(1,t_VEC);
      case 2: return gen_0;
      case 3: return mfdim0all(CHI);
    }
    if (k == 0)
    {
      if (space_is_cusp(space)) switch(joker)
      {
        case 1: return cgetg(1,t_VEC);
        case 2: return gen_0;
        case 3: return mfdim0all(CHI);
      }
      switch(joker)
      {
        long i, l;
        case 1: retmkvec(fmt_dim(mfchartrivial(1),0,0));
        case 2: return gen_1;
        case 3: l = lg(CHI); D = cgetg(l,t_VEC);
                for (i = 1; i < l; i++)
                {
                  long t = mfcharistrivial(gel(CHI,i));
                  gel(D,i) = mkvec2(t? gen_1: gen_0, gen_0);
                }
                return D;
      }
    }
    if (k == 1)
    {
      if (!space_is_cusp(space))
        pari_err_IMPL("noncuspidal dimension of G_1(N)");
      if (joker == 2) { d = mfwt1dimsum(N, space); avma = av; return utoi(d); }
      D = mfwt1dims(N, CHI, space);
    }
    else
    {
      if (joker == 2) { d = mfwtkdimsum(N,k,space); avma = av; return utoi(d); }
      D = mfwtkdims(N, k, CHI, space);
    }
    if (!CHI) return gerepileupto(av, vecsort(D, mkvecsmall(1)));
    return gerepilecopy(av, D);
  }
  if (k < 0 || !ischarok(N,k,CHI)) return gen_0;
  if (k == 0)
    return mfcharistrivial(CHI) && !space_is_cusp(space)? gen_1: gen_0;
  switch(space)
  {
    case mf_NEW: return utoi( mfnewdim(N,k,CHI) );
    case mf_CUSP:return utoi( mfcuspdim(N,k,CHI) );
    case mf_OLD: return utoi( mfolddim(N,k,CHI) );
    case mf_FULL:return utoi( mffulldim(N,k,CHI) );
    case mf_EISEN: return utoi( mfeisendim(N,k,CHI) );
    default: pari_err_FLAG("mfdim");
  }
  return NULL;/*LCOV_EXCL_LINE*/
}

/* Given a closure F and a vector of complex numbers z, output the vector of
 * closures corresponding to all embeddings X -> z[j] */
static GEN
allembed(GEN F, GEN z)
{
  long l = lg(z), j;
  GEN r = cgetg(l, t_VEC);
  for (j = 1; j < l; j++) gel(r,j) = tag2(t_MF_EMBED, F, gel(z,j));
  return r;
}
GEN
mfembed(GEN F, long prec)
{
  pari_sp av = avma;
  GEN vecan = mfcoefs(F, 20, 1);
  long n;
  for (n = 0; n < 20; n++)
  {
    GEN an = gel(vecan, n+1);
    if (typ(an) == t_POLMOD)
    {
      GEN z = rootspowers( ZX_roots(gel(an,1), prec) );
      return gerepilecopy(av, allembed(F, z));
    }
  }
  avma = av; return mkveccopy(F);
}
/* polmods */
static int
RgV_polmods(GEN v, GEN *P, GEN *T)
{
  const long vy = 1;
  long i, l = lg(v), vt = fetch_user_var("t");
  *T = *P = NULL;
  for (i = 1; i < l; i++)
  {
    GEN c = gel(v,i);
    long t = typ(c);
    if (t == t_POLMOD)
    {
      long vc = varn(gel(c,1));
      GEN Q = NULL;
      if (vc == vy)
      {
        GEN p = NULL;
        if (*T)
        {
          if (gequal(*T,gel(c,1))) continue;
          return 0;
        }
        *T = gel(c,1);
        if (!RgX_is_FpXQX(*T,&p,&Q) || p) return 0;
        if (!Q) continue;
        vc = varn(Q);
      }
      else
      {
        if (vc != vt) return 0;
        Q = gel(c,1);
      }
      if (!*P) *P = Q; else if (!gequal(*P,Q)) return 0;
    }
  }
  return 1;
}
GEN
mfreltoabs(GEN F)
{
  pari_sp av = avma;
  GEN S, P, T;
  RgV_polmods(mfcoefs(F,20,1), &P, &T);
  if (!P) /* Q(chi) = Q */
    S = T;
  else
    S = rnfequation2(P, T);
  return gerepilecopy(av, tag2(t_MF_RELTOABS,F,S));
}

static GEN
mftolfun_i(GEN F, GEN sd, GEN N, GEN k, GEN r, long cuspidal, long bitprec)
{
  GEN LF = cuspidal? cgetg(7, t_VEC): cgetg(8, t_VEC);
  gel(LF,1) = lfuntag(t_LFUN_MFCLOS, F);
  gel(LF,2) = sd;
  gel(LF,3) = mkvec2(gen_0, gen_1);
  gel(LF,4) = k;
  gel(LF,5) = N;
  gel(LF,6) = r;
  if (!cuspidal) gel(LF, 7) = gen_0;
  if (gequal0(r))
  {
    GEN v = lfunrootres(LF, bitprec + 32), po;
    gel(LF,6) = gel(v,3);
    if (!cuspidal)
    {
      po = gel(v, 1);
      if (isintzero(po)) setlg(LF, 7);
      else gel(LF, 7) = po;
    }
  }
  return LF;
}
static GEN
mftolfunall(GEN mf, long real, long bitprec)
{
  GEN L, M, SD, F, A, RO, gN, gk;
  long l, i, N, k, prec = nbits2prec(bitprec);

  M = mfeigenbasis(mf);
  N = mf_get_N(mf); gN = utoipos(N);
  k = mf_get_k(mf); gk = utoipos(k);
  RO = mfQeigenroots(mf, prec);
  A = mfatkineigenvalues_i(mf, N, RO, bitprec);
  l = lg(RO);
  SD = cgetg(l, t_VEC);
  F = cgetg(l, t_VEC);
  for (i = 1; i < l; i++)
  {
    GEN ro = gel(RO,i), f = gel(M,i);
    long n = lg(ro)-1;
    int sd = (typ(gel(ro,n)) == t_COMPLEX);
    if (real && sd) pari_err_FLAG("mftolfun [not a real eigenform]");
    gel(F,i) = allembed(f, ro);
    gel(SD,i) = const_vec(n, sd? gen_1: gen_0);
  }
  A = shallowconcat1(A);
  F = shallowconcat1(F);
  SD= shallowconcat1(SD);
  l = lg(A); L = cgetg(l, t_VEC);
  for (i = 1; i < l; i++)
  {
    GEN r = mulcxpowIs(gel(A,i), k);
    gel(L,i) = mftolfun_i(gel(F,i), gel(SD,i), gN, gk, r, 1, bitprec);
  }
  return L;
}
GEN
mftolfun(GEN F, long flag, long bitprec)
{
  pari_sp av = avma;
  GEN z;
  if (!isf(F)) z = mftolfunall(F, flag & 1, bitprec);
  else
  {
    GEN Nk, sd = flag & 1? gen_0: gen_1;
    Nk = mfparams_ii(F); if (!Nk) pari_err_TYPE("mftolfun",F);
    z = mftolfun_i(F, sd, gel(Nk,1), gel(Nk,2), gen_0, flag & 2, bitprec);
  }
  return gerepilecopy(av,z);
}

static GEN
get_theta(GEN LD, GEN tdom, GEN vtau, long bit)
{
  GEN z, LT = lfunthetainit(LD, tdom, 0, bit);
  long j, l;
  if (!is_vec_t(typ(vtau))) return lfuntheta(LT, vtau, 0, bit);
  l = lg(vtau); z = cgetg(l, t_VEC);
  for (j = 1; j < l; ++j) gel(z,j) = lfuntheta(LT, gel(vtau,j), 0, bit);
  return z;
}
/* Here F is an eigenform already embedded, hence an mf closure. */
GEN
mfeigeneval(GEN mf, GEN vtau, long bitprec)
{
  pari_sp av = avma;
  GEN L, tdom, z;
  long prec, N;

  if (isf(mf))
  {
    GEN P = mfparams_ii(mf);
    if (!P) pari_err_IMPL("mfeigeneval for this form");
    N = itos(gel(P, 1));
    L = mftolfun(mf, 0, bitprec);
    mf = NULL;
  }
  else
  {
    checkmfsplit(mf);
    N = mf_get_N(mf);
    L = mftolfunall(mf, 0, bitprec);
  }
  prec = nbits2prec(bitprec);
  vtau = gmul(sqrtr_abs(utor(N, prec)), mulcxmI(vtau));
  tdom = mkvec2(vecmin(gabs(vtau,prec)), vecmax(gabs(garg(vtau,prec),prec)));
  if (!mf)
    z  = get_theta(L, tdom, vtau, bitprec);
  else
  {
    long i, l = lg(L);
    z = cgetg(l, t_VEC);
    for (i = 1; i < l; i++) gel(z,i) = get_theta(gel(L,i), tdom, vtau, bitprec);
  }
  return gerepileupto(av, gmul2n(z, -1));
}

GEN
mffromell(GEN E)
{
  pari_sp av = avma;
  GEN mf, F, z, S;
  long N, i, l;

  checkell(E);
  if (ell_get_type(E) != t_ELL_Q) pari_err_TYPE("mfffromell [E not over Q]", E);
  N = itos(gel(ellglobalred(E), 1));
  mf = mfsplit(mfinit(mkvec2(utoi(N), gen_2), mf_NEW), 1, 0);
  F = tag(t_MF_ELL, E);
  z = mftobasis_i(mf, F);
  S = mf_get_newforms(mf); l = lg(S);
  for(i = 1; i < l; i++)
    if (gequal(z, gel(S, i))) break;
  if (i == l) pari_err_BUG("mffromell [E is not modular]");
  return gerepilecopy(av, mkvec3(mf, F, z));
}

/* returns -1 if not, degree otherwise */
long
polishomogeneous(GEN P)
{
  long i, D, l;
  if (typ(P) != t_POL) return 0;
  D = -1; l = lg(P);
  for (i = 2; i < l; i++)
  {
    GEN c = gel(P,i);
    long d;
    if (gequal0(c)) continue;
    d = polishomogeneous(c);
    if (d < 0) return -1;
    if (D < 0) D = d + i-2; else if (D != d + i-2) return -1;
  }
  return D;
}

/* 1 if spherical, 0 otherwise */
static long
polisspherical(GEN Qi, GEN P)
{
  pari_sp av = avma;
  GEN va, S;
  long lva, i, j, r;
  if (gequal0(P) || poldegree(P, -1) <= 1) return 1;
  va = variables_vecsmall(P); lva = lg(va);
  if (lva > lg(Qi))
    pari_err(e_MISC, "too many variables in mffromqf");
  S = gen_0;
  for (j = 1; j < lva; ++j)
  {
    GEN col = gel(Qi, j), Pj = deriv(P, va[j]);
    for (i = 1; i <= j; ++i)
    {
      GEN coe = gel(col, i);
      if (i != j) coe = gmul2n(coe, 1);
      if (!gequal0(coe))
        S = gadd(S, gmul(coe, deriv(Pj, va[i])));
    }
  }
  r = gequal0(S); avma = av; return r;
}

static GEN
c_QFsimple(long n, GEN Q, GEN P)
{
  pari_sp av = avma;
  GEN V, v = qfrep0(Q, utoi(n), 1);
  long i, l = lg(v);
  V = cgetg(l+1, t_VEC);
  if (!P || equali1(P))
  {
    gel(V,1) = gen_1;
    for (i = 2; i <= l; i++) gel(V,i) = utoi(v[i-1] << 1);
  }
  else
  {
    gel(V,1) = gcopy(P);
    for (i = 2; i <= l; i++) gel(V,i) = gmulgs(P, v[i-1] << 1);
  }
  return gerepileupto(av, V);
}
static GEN
c_QF(long n, GEN Q, GEN P)
{
  pari_sp av = avma;
  GEN V, v, va;
  long i, lva, lq, l;
  if (!P || typ(P) != t_POL) return c_QFsimple(n, Q, P);
  v = gel(minim(Q, utoi(2*n), NULL), 3);
  va = variables_vec(P); lq = lg(Q) - 1; lva = lg(va) - 1;
  V = zerovec(n + 1); l = lg(v);
  for (i = 1; i < l; ++i)
  {
    GEN X = gel(v,i);
    long ind = (itos(qfeval0(Q, X, NULL)) >> 1) + 1;
    if (lq > lva) X = vecslice(X, 1, lva);
    gel(V, ind) = gadd(gel(V, ind), gsubstvec(P, va, X));
  }
  return gerepilecopy(av, gmul2n(V,1));
}
GEN
mffromqf(GEN Q, GEN P)
{
  pari_sp av = avma;
  GEN Qi, F, D, N, mf, res;
  long m, k, d, space;
  if (typ(Q) != t_MAT) pari_err_TYPE("mffromqf", Q);
  if (!RgM_is_ZM(Q) || !qf_iseven(Q))
    pari_err_TYPE("mffromqf [not integral or even]", Q);
  m = lg(Q)-1;
  if (odd(m)) pari_err_TYPE("mffromqf [odd dimension]", Q);
  k = m >> 1;
  Qi = ZM_inv_ratlift(Q, &N);
  if (!qf_iseven(Qi)) N = shifti(N, 1);
  if (!P || gequal1(P)) { d = 0; P = NULL; }
  else
  {
    d = polishomogeneous(P);
    if (d < 0) pari_err_TYPE("mffromqf [not homogeneous t_POL]", P);
    if (!polisspherical(Qi, P))
      pari_err_TYPE("mffromqf [not a spherical t_POL]", P);
    if (d == 0) P = simplify_shallow(P);
  }
  D = ZM_det(Q); if (k&1L) D = negi(D);
  space = d > 0 ? mf_CUSP : mf_FULL;
  mf = mfinit(mkvec3(N, utoi(k + d), znchar_quad(N,D)), space);
  if (odd(d))
  {
    F = tag(t_MF_CONST, mkvec(gen_0));
    res = zerocol(mf_get_dim(mf));
  }
  else
  {
    F = c_QF(mfsturm(mf), Q, P);
    res = mftobasis_i(mf, F);
    F = mflinear_i(mf_get_basis(mf), res);
  }
  return gerepilecopy(av, mkvec3(mf, F, res));
}

/***********************************************************************/
/*                          Eisenstein Series                          */
/***********************************************************************/
#if 0
/* radical(u_ppo(g,q)) */
static long
u_pporad(long g, long q)
{
  GEN F = myfactoru(g), P = gel(F,1);
  long i, l, n;
  if (q == 1) return zv_prod(P);
  l = lg(P);
  for (i = n = 1; i < l; i++)
  {
    long p = P[i];
    if (q % p) n *= p;
  }
  return n;
}
#endif
/* \sigma_{k-1}(\chi,n) */
static GEN
sigchi(long k, GEN CHI, long n)
{
  pari_sp av = avma;
  GEN S = gen_0, D = mydivisorsu(u_ppo(n,mfcharmodulus(CHI)));
  long i, l = lg(D);
  if (k == 1)
    for (i = 1; i < l; ++i) S = gadd(S, mfchareval_i(CHI, D[i]));
  else
    for (i = 1; i < l; ++i)
    {
      long d = D[i];
      S = gadd(S, gmul(powuu(d, k-1), mfchareval_i(CHI, d)));
    }
  return gerepileupto(av,S);
}

/* sigma_{k-1}(\chi_1,\chi_2,n), ord multiple of lcm(ord(CHI1),ord(CHI2)) */
static GEN
sigchi2(long k, GEN CHI1, GEN CHI2, long n, long ord)
{
  pari_sp av = avma;
  GEN S = gen_0, D;
  long i, l, N1 = mfcharmodulus(CHI1), N2 = mfcharmodulus(CHI2);
  D = mydivisorsu(u_ppo(n,N1));
  l = lg(D);
  for (i = 1; i < l; ++i)
  { /* S += d^(k-1)*chi1(d)*chi2(n/d) */
    long a, d = D[i], nd = n/d; /* (d,N1)=1 */
    if (cgcd(nd,N2) != 1) continue;
    a = mfcharevalord(CHI1, d, ord) + mfcharevalord(CHI2, nd, ord);
    if (a >= ord) a -= ord;
    S = gadd(S, mygmodulo_lift(a, ord, powuu(d, k-1)));
  }
  return gerepileupto(av, mygmodulo_mod(S, ord));
}

/**********************************************************************/
/* Fourier expansions of Eisenstein series over G(N) and G_0(N),chi   */
/**********************************************************************/
/* \sigma_{k-1}(n;m1,m2) */
static GEN
GammaNsig(long N, long k, long m1, long m2, long n)
{
  pari_sp ltop = avma;
  GEN S = gen_0, D = mydivisorsu(n);
  long lD = lg(D), i, mm2;

  m2 = smodss(m2, N);
  mm2 = m2? N-m2: 0;
  for (i = 1; i < lD; ++i)
  {
    long d = D[i], nd = D[lD-i];
    if ((m1 - nd) % N == 0)
    {
      GEN q = powuu(d,k-1);
      S = gadd(S, mygmodulo_lift(Fl_mul(m2,d,N), N, q));
    }
    if ((m1 + nd) % N == 0)
    {
      GEN q = powuu(d,k-1);
      if (odd(k)) q = negi(q);
      S = gadd(S, mygmodulo_lift(Fl_mul(mm2,d,N), N, q));
    }
  }
  return gerepileupto(ltop, mygmodulo_mod(S, N));
}

static GEN /* order(CHI) | ord != 0 */
charLFwt1_o(GEN CHI, long ord)
{
  pari_sp av;
  GEN S;
  long r, m = mfcharmodulus(CHI);

  if (m == 1) return gen_m1;
  av = avma; S = gen_0;
  for (r = 1; r < m; ++r)
  { /* S += r*chi(r) */
    long a;
    if (cgcd(m,r) != 1) continue;
    a = mfcharevalord(CHI,r,ord);
    S = gadd(S, mygmodulo_lift(a, ord, utoi(r)));
  }
  S = gdivgs(S, -m);
  return gerepileupto(av, mygmodulo_mod(S, ord));
}
static GEN /* order(CHI) | ord != 0 */
charLFwtk_o(long k, GEN CHI, long ord)
{
  pari_sp av;
  GEN S, P;
  long r, m;

  if (k == 1) return charLFwt1_o(CHI, ord);
  m = mfcharmodulus(CHI);
  if (m == 1) return gdivgs(bernfrac(k),-k);
  av = avma; S = gen_0;
  P = RgX_rescale(bernpol(k,0), utoi(m));
  for (r = 1; r < m; ++r)
  { /* S += B_k(r/m)*chi(r) */
    long a;
    if (ugcd(r,m) != 1) continue;
    a = mfcharevalord(CHI,r,ord);
    S = gadd(S, mygmodulo_lift(a, ord, poleval(P, utoi(r))));
  }
  S = gdivgs(S, -k*m);
  return gerepileupto(av, mygmodulo_mod(S, ord));
}

/* L(\chi,k-1) */
GEN
charLFwtk(long k, GEN CHI) { return charLFwtk_o(k, CHI, mfcharorder(CHI)); }

static GEN
mfeisen_1_0(long k, GEN CHI)
{ GEN E0 = gmul2n(charLFwtk(k, CHI), -1); return mkvec2(E0, CHI); }
static GEN /* ord != 0 */
mfeisen_2_0(long k, GEN CHI1, GEN CHI2, long *ord)
{
  GEN E0;
  *ord = clcm(mfcharorder(CHI1), mfcharorder(CHI2));
  if (k == 1 && mfcharistrivial(CHI1))
    E0 = gmul2n(charLFwt1_o(CHI2, *ord), -1);
  else if (mfcharistrivial(CHI2))
    E0 = gmul2n(charLFwtk_o(k, CHI1, *ord), -1);
  else
    E0 = gen_0;
  return mkvec4(E0,CHI1,CHI2,cgetg(1,t_VEC));
}
static GEN
mfeisen_i(long k, GEN CHI1, GEN CHI2)
{
  long s = 1, ord;
  GEN vchi, CHI;
  if (CHI2) { CHI2 = get_mfchar(CHI2); if (mfcharparity(CHI2) < 0) s = -s; }
  if (CHI1) { CHI1 = get_mfchar(CHI1); if (mfcharparity(CHI1) < 0) s = -s; }
  if (s != m1pk(k)) return mftrivial();
  if (!CHI1)
    CHI = CHI2? CHI2: mfchartrivial(1);
  else if (!CHI2)
    CHI = CHI1;
  else
    CHI = NULL;
  /* E_k(chi) */
  if (CHI) return tag2(t_MF_EISEN, mkvecsmall(k), mfeisen_1_0(k,CHI));
  /* E_k(chi1,chi2) */
  vchi = mfeisen_2_0(k, CHI1, CHI2, &ord);
  return tag2(t_MF_EISEN, mkvecsmall3(k,ord,0), vchi);
}
GEN
mfeisen(long k, GEN CHI1, GEN CHI2)
{
  pari_sp av = avma;
  return gerepilecopy(av, mfeisen_i(k, CHI1, CHI2));
}

static GEN
mfeisen2closvec(long k, GEN CHI1, GEN CHI2, long ordchi)
{
  long ord, j, d;
  GEN E, vchi = mfeisen_2_0(k, CHI1, CHI2, &ord);
  GEN T = Qab_trace_init(ord_canon(ord), ord_canon(ordchi));
  gel(vchi,4) = T;
  d = (lg(T)==4)? itou(gmael(T,3,1)): 1;
  E = cgetg(d+1, t_VEC);
  for (j = 1; j <= d; j++)
    gel(E,j) = tag2(t_MF_EISEN, mkvecsmall3(k,ord,j-1), vchi);
  return E;
}

/* Basic theorems:
   (k>=3): In weight k >= 3, basis of Eisenstein series for
   M_k(G_0(N),CHI) is B(d)E(CHI1,(CHI/CHI1)_prim) (mfeisen2 above), where
   CHI1 is primitive modulo N1, and if N2 is the conductor of CHI/CHI1
   then d*N1*N2|N.
   (k=2): In weight k=2, same if CHI is nontrivial. If CHI is trivial, must
   not take CHI1 trivial, and must add E_2(tau)-dE_2(d tau)), where
   d|N, d > 1.
   (k=1): In weight k=1, same as k >= 3 except that we must restrict to
   CHI1 even character. */

/* Given f1 and f2 find lower bound for conductor of product of characters
 * of conductors fi. P is a list of primes containing all prime divisors
 * of f1 and f2 */
static long
boundcondprod(GEN P, ulong f1, ulong f2)
{
  long i, l = lg(P);
  ulong res = 1;
  for (i = 1; i < l; i++)
  {
    ulong p = P[i], e1 = u_lvalrem(f1, p, &f1), e2 = u_lvalrem(f2, p, &f2);
    if (e1 != e2) res *= upowuu(p, maxuu(e1,e2));
    if (f1 == 1) return res * f2;
    if (f2 == 1) return res * f1;
  }
  return res;
}

/* CHI primitive, f(CHI) | N
 * FIXME: implement a local algorithm N = \prod_p p^e_p,
 * chi = \prod chi_p; find chi1_p chi2_p = chi_p */
static GEN
mfeisenbasis_pre(long N, long k, GEN CHI)
{
  pari_sp av = avma;
  GEN D = mydivisorsu(N), RES = cgetg(N+1, t_VEC);
  GEN G = gel(CHI,1), L = gel(CHI,2), CHI0, GN, LN, Lchi, LG, P;
  long i, j, l = lg(D), ord = mfcharorder(CHI), f = mfcharmodulus(CHI);

  CHI0 = (f == 1)? CHI: mfchartrivial(1);
  Lchi = cgetg(N + 1, t_VECSMALL);
  LG = const_vec(N, NULL); /* LG[D] = znstar(D,1) or NULL */
  P = gel(myfactoru(N), 1);
  gel(LG,1) = gel(CHI0,1);
  if (f == N)
  {
    GN = G;
    LN = L;
  }
  else
  {
    GN = znstar0(utoi(N),1);
    LN = zncharinduce(G, L, GN);
    gel(LG,f) = G;
  }
  gel(LG,N) = GN;
  j = 1;
  /* N1 = 1 */
  if (f != 1 || k != 2)
  {
    gel(RES, j++) = mkvec2(CHI0, CHI);
    if (f != 1 && k != 1) gel(RES, j++) = mkvec2(CHI, CHI0);
  }
  for (i = 2; i < l-1; ++i) /* skip N1 = 1 and N */
  {
    long N1 = D[i], D1 = D[l-i], n;
    GEN G1;
    if (ugcd(D1, f) == 1)
    { /* (N/N1,f)=1 => (N2,f)=1 => conductor(chi1 = chi/chi2) = N1 = f*N2 */
      /* N.B. N2 = 1 is done already */
      if (N1 == f || N1 % f || (D1 % (N1/f))) continue;
    }
    else
      if (D1 % boundcondprod(P, f, N1)) continue;
    if (!gel(LG,N1)) gel(LG,N1) = znstar0(utoi(N1), 1);
    G1 = gel(LG,N1);
    for (n = 1; n < N1; n++) /* reset Lchi */
       Lchi[n] = cgcd(n, N1) == 1? 1: 0;
    for (n = 2; n < N1; n++) /* remove 1: trivial char */
    {
      GEN L1;
      if (!Lchi[n]) continue;
      /* n coprime to N1 */
      L1 = znconreylog(G1, utoipos(n));
      if (k == 1 && zncharisodd(G1,L1)) continue;
      if (zncharisprimitive(G1, L1))
      { /* need f(CHI / CHI1) | N/N1, f(CHI1) = N1 */
        GEN gN2, CHI1, CHI2, L2 = znchardiv(GN, LN, zncharinduce(G1,L1,GN));
        long t, ochi12, N2;

        gN2 = znconreyconductor(GN, L2, &L2);
        /* if L2 is primitive, then N2 = N => N1 = 1; done already */
        if (typ(gN2) == t_INT) continue;
        N2 = itou(gel(gN2,1));
        if (N2 == 1 || D1 % N2) continue; /* N2 = 1; done already */
        if (!gel(LG,N2)) gel(LG,N2) = znstar0(gN2, 1);
        CHI1 = mfcharGL(G1, L1);
        CHI2 = mfcharGL(gel(LG,N2), L2);
        gel(RES, j++) = mkvec2(CHI1, CHI2);
        ochi12 = clcm(mfcharorder(CHI1), mfcharorder(CHI2));
        Lchi[n] = 0;
        for (t = 1 + ord; t <= ochi12; t += ord)
          if (ugcd(t, ochi12) == 1)
          {
            long ind = Fl_powu(n, t, N1);
            if (!ind) ind = N1;
             Lchi[ind] = 0;
          }
      }
    }
  }
  setlg(RES, j);
  return gerepilecopy(av, RES);
}

/* C-basis of E_k(Gamma_0(N),chi). If k = 1, the first basis element must not
 * vanish at oo [used in mfwt1basis]. Here E_1(CHI), whose q^0 coefficient
 * does not vanish (since L(CHI,0) does not) *if* CHI is not trivial; which
 * must be the case in weight 1. */
GEN
mfeisenbasis_i(long N, long k, GEN CHI)
{
  GEN RES, LI, P = NULL;
  long i, j, f, l, lLI, ordchi;

  if (!ischarok(N, k, CHI)) return cgetg(1, t_VEC);
  if (k == 0) return mfcharistrivial(CHI)? mkvec(mfcreate(gen_1))
                                         : cgetg(1, t_VEC);
  if (!CHI) CHI = mfchartrivial(1);
  CHI = mfchartoprimitive(CHI, &f);
  ordchi = mfcharorder(CHI);
  LI = mfeisenbasis_pre(N, k, CHI);
  l = lLI = lg(LI);
  if (f == 1 && k == 2)
  {
    P = mydivisorsu(N);
    l += lg(P) - 2;
  }
  RES = cgetg(l, t_VEC);
  for (j = 1; j < lLI; j++)
  {
    GEN CHI1 = gmael(LI, j, 1), CHI2 = gmael(LI, j, 2);
    long N0 = mfcharmodulus(CHI1) * mfcharmodulus(CHI2);
    GEN E = mfeisen2closvec(k, CHI1, CHI2, ordchi);
    gel(RES, j) = mfbdall(E, N/N0);
  }
  if (P)
  {
    GEN E2 = mfeisen(k, NULL, NULL);
    l = lg(P);
    for (i = 2; i < l; i++, j++)
    {
      long d = P[i];
      GEN E2d = mfbd_i(E2, d);
      GEN Ed = mflinear_i(mkvec2(E2, E2d), mkvec2(gen_1, utoineg(d)));
      gel(RES, j) = mkvec(Ed);
    }
  }
  return lg(RES) == 1 ? RES : shallowconcat1(RES);
}

/* check parameters rigorously, but not coefficients */
static long
mfisinspace_i(GEN mf, GEN F)
{
  GEN P, CHI1, CHI2;
  long Nmf, N, k, space = mf_get_space(mf);

  P = mfparams_i(F);
  if (!P) pari_err_IMPL("mfisinspace for this F");
  Nmf = mf_get_N(mf);
  N = itou(gel(P,1));
  if (space == mf_NEW)
  { if (N != Nmf) return 0; }
  else
  { if (Nmf % N) return 0; }
  k = itou(gel(P,2));
  if (mf_get_k(mf) != k) return 0;
  CHI1 = mf_get_CHI(mf); CHI1 = mfchar2char(CHI1);
  CHI1 = znchartoprimitive(gel(CHI1,1), gel(CHI1,2));
  CHI2 = mfchar2char(gel(P,3));
  CHI2 = znchartoprimitive(gel(CHI2,1), gel(CHI2,2));
  return gequal(CHI1,CHI2);
}
static void
err_space(GEN F)
{
  pari_err_DOMAIN("mftobasis", "form", "not in",
                  strtoGENstr("this modular form space"), F);
}
/* when flag set, do not return error message */
GEN
mftobasis(GEN mf, GEN F, long flag)
{
  pari_sp av2, av = avma;
  GEN G, v, y;
  long B;

  checkmf(mf);
  if (isf(F) && !mfisinspace_i(mf, F))
  {
    if (flag) return cgetg(1, t_COL);
    err_space(F);
  }
  /* at least the parameters are right */
  B = mfsturmNk(mf_get_N(mf), mf_get_k(mf)) + 1;
  if (isf(F)) v = mfcoefs_i(F,B,1);
  else
  {
    switch(typ(F))
    { /* F(0),...,F(lg(v)-2) */
      case t_SER: v = sertocol(F); settyp(v,t_VEC); break;
      case t_VEC: v = F; break;
      case t_COL: v = shallowtrans(F); break;
      default: pari_err_TYPE("mftobasis",F);
               v = NULL;/*LCOV_EXCL_LINE*/
    }
    if (flag) B = minss(B, lg(v)-2);
  }
  y = mftobasis_i(mf, v);
  if (typ(y) == t_VEC)
  {
    if (flag) return gerepilecopy(av, y);
    pari_err(e_MISC, "not enough coefficients in mftobasis");
  }
  av2 = avma;
  if (mf_get_space(mf) == mf_FULL || mfsturm(mf)+1 == B) return y;
  G = mflinear_i(mf_get_basis(mf), y);
  if (!gequal(v, mfcoefs_i(G, lg(v)-2,1))) y = NULL;
  avma = av2;
  if (!y)
  {
    if (flag) { avma = av; return cgetg(1, t_COL); }
    err_space(F);
  }
  return gerepileupto(av, y);
}

/* FIXME: remove static variant in modsym.c */
ulong
mfnumcuspsu_fact(GEN fa)
{
  GEN P = gel(fa,1), E = gel(fa,2);
  long i, l = lg(P);
  ulong T = 1;
  for (i = 1; i < l; i++)
  {
    long e = E[i], e2 = e >> 1; /* floor(E[i] / 2) */
    ulong p = P[i];
    if (odd(e))
      T *= 2 * upowuu(p, e2);
    else
      T *= (p+1) * upowuu(p, e2-1);
  }
  return T;
}
ulong
mfnumcuspsu(ulong n)
{
  pari_sp av = avma;
  ulong t = mfnumcuspsu_fact( factoru(n) );
  avma = av; return t;
}
/* \sum_{d | N} \phi(gcd(d, N/d)), using multiplicativity. fa = factor(N) */
GEN
mfnumcusps_fact(GEN fa)
{
  GEN P = gel(fa,1), E = gel(fa,2), T = gen_1;
  long i, l = lg(P);
  for (i = 1; i < l; i++)
  {
    GEN p = gel(P,i), c;
    long e = itos(gel(E,i)), e2 = e >> 1; /* floor(E[i] / 2) */
    if (odd(e))
      c = shifti(powiu(p, e2), 1);
    else
      c = mulii(addiu(p,1), powiu(p, e2-1));
    T = T? mulii(T, c): c;
  }
  return T? T: gen_1;
}
GEN
mfnumcusps(GEN n)
{
  pari_sp av = avma;
  GEN F = check_arith_pos(n,"mfnumcusps");
  if (!F)
  {
    if (lgefint(n) == 3) return utoi( mfnumcuspsu(n[2]) );
    F = absZ_factor(n);
  }
  return gerepileuptoint(av, mfnumcusps_fact(F));
}

/* List of cusps of Gamma_0(N) */
GEN
mfcusps(long N)
{
  pari_sp av = avma;
  GEN D, v;
  long i, c, l;

  if (N <= 0) pari_err_DOMAIN("mfcusps", "N", "<", gen_0, stoi(N));
  D = mydivisorsu(N); l = lg(D);
  c = mfnumcuspsu_fact(myfactoru(N));
  v = cgetg(c + 1, t_VEC);
  for (i = c = 1; i < l; i++)
  {
    long C = D[i], NC = D[l-i], lima = ugcd(C, NC), A0, A;
    for (A0 = 0; A0 < lima; A0++)
      if (cgcd(A0, lima) == 1)
      {
        A = A0; while (ugcd(A,C) > 1) A += lima;
        gel(v, c++) = gdivgs(utoi(A), C);
      }
  }
  return gerepileupto(av, v);
}

static void
cusp_canon(GEN cusp, long N, long *pA, long *pC)
{
  pari_sp av = avma;
  long A, C, tc;
  if (!cusp || (tc = typ(cusp)) == t_INFINITY) { *pA = 1; *pC = N; return; }
  if (tc != t_INT && tc != t_FRAC ) pari_err_TYPE("checkcusp", cusp);
  C = itos(Q_denom(cusp));
  A = itos(gmulgs(cusp, C));
  if (N % C)
  {
    ulong uC;
    long u = Fl_invgen(C, N, &uC);
    A = Fl_mul(A, u, N);
    C = (long)uC;
  }
  *pA = A; *pC = C; avma = av;
}
long
mfcuspwidth(long N, GEN cusp)
{
  long A, C;
  cusp_canon(cusp, N, &A, &C);
  if (C == N) return 1;
  return N/cgcd(N, C*C);
}

/* Some useful closures */

/* sum_{d|n} d^k */
static GEN
mysumdivku(ulong n, ulong k) { return usumdivk_fact(myfactoru(n),k); }
static GEN
c_Ek(long n, long d, long k, GEN C)
{
  GEN E = cgetg(n + 2, t_VEC);
  long i;
  gel (E, 1) = gen_1;
  for (i = 1; i <= n; i++)
  {
    pari_sp av = avma;
    gel(E, i+1) = gerepileupto(av, gmul(C, mysumdivku(i*d, k-1)));
  }
  return E;
}

GEN
mfEk(long k)
{
  pari_sp av = avma;
  GEN E0;
  if (k <= 0 || (k & 1L)) pari_err_TYPE("mfEk [incorrect k]", stoi(k));
  E0 = gdivsg(-2*k, bernfrac(k));
  return gerepilecopy(av, tag2(t_MF_Ek, mkvecsmall(k), E0));
}

GEN
mfDelta(void) { return tag0(t_MF_DELTA); }
GEN
mfetaquo(GEN eta)
{
  pari_sp av = avma;
  GEN B, E;
  long s, i;
  if (typ(eta) != t_MAT || !RgM_is_ZM(eta)) pari_err_TYPE("mfetaquo", eta);
  if (lg(eta) != 3 || lg(gel(eta,1)) == 1)
    pari_err_TYPE("mfetaquo [not a factorization]", eta);
  B = ZV_to_zv(gel(eta,1));
  E = ZV_to_zv(gel(eta,2)); s = 0;
  for (i = 1; i < lg(B); i++) s += B[i]*E[i];
  s = maxss(0, s/24);
  return gerepilecopy(av, tag2(t_MF_ETAQUO, mkvec2(B,E), stoi(s)));
}

/* Tr_{Q(zeta_n)/Q} (zeta_n^j * x), j = 0 .. phi(n) */
static GEN
mytraceall(GEN x, GEN P)
{
  long j, degrel = degpol(P);
  GEN res = cgetg(degrel + 1, t_VEC), X = pol_x(varn(P));

  x = liftpol_shallow(x);
  for (j = 0; j < degrel; ++j)
  {
    GEN y = gmul(x, gmodulo(gpowgs(X, j), P));
    gel(res, j + 1) = gtrace(y);
  }
  return res;
}

static GEN
mfeisenbasis(long N, long k, GEN CHI, long lim)
{ return mfvectomat(mfeisenbasis_i(N, k, CHI), lim); }

static void
update_Mj(GEN *M, GEN *vecj)
{
  GEN z = ZM_indexrank(*M), perm = gel(z, 2);
  *M = vecpermute(*M, perm);
  *vecj = vecpermute(*vecj, perm);
}
/* Space generated by products of two Eisenstein series */
GEN
mfeisenspaceinit(GEN NK)
{
  pari_sp ltop = avma;
  GEN G, M, CHI, lisC, vecj;
  long lim, i, k2, j, N, k, dim, ct, llC;

  checkNK(NK, &N, &k, &CHI, 0);
  k2 = k/2;
  if (!CHI) CHI = mfchartrivial(1);
  dim = mffulldim(N, k, CHI);
  lim = mfsturmNk(N, k) + 1;
  M = mfeisenbasis(N, k, CHI, lim);
  ct = lg(M) - 1;
  vecj = cgetg(ct+1, t_VEC);
  for (i = 1; i <= ct; ++i)
  {
    gel(vecj,i) = mkvecsmall5(0,k,0,0,i);
    gel(M,i) = Q_primpart(gel(M,i));
  }
  G = gel(CHI,1);
  lisC = znchargalois(G, NULL); llC = lg(lisC);
  if (mfcharorder(CHI) > 1)
    pari_err_IMPL("nontrivial CHI not yet implemented in mfeisenspace");
  for (j = 1; j < llC; ++j)
  {
    GEN CHI1 = mfcharGL(G, gel(lisC, j));
    GEN P = polcyclo(ord_canon(mfcharorder(CHI1)), fetch_user_var("t"));
    GEN CHI2 = mfchardiv_i(CHI, CHI1);
    long l, linit = (mfcharparity(CHI1) == -1)? 1: 2;
    for (l = linit; l <= k2; l += 2)
    {
      GEN B2, B1 = RgM_to_RgXV(mfeisenbasis(N, l, CHI1, lim), 0);
      long j1;
      if (l == k - l && gequal(CHI2, CHI1))
        B2 = B1;
      else
        B2 = RgM_to_RgXV(mfeisenbasis(N, k-l, CHI2, lim), 0);
      for (j1 = 1; j1 < lg(B1); j1++)
      {
        long j2;
        for (j2 = (B1 == B2)? j1 : 1; j2 < lg(B2); j2++)
        {
          GEN tmp = RgX_to_RgC(RgXn_mul(gel(B1,j1), gel(B2,j2), lim+1), lim+1);
          long j3;
          tmp = mytraceall(tmp, P);
          for (j3 = 1; j3 < lg(tmp); j3++)
          {
            M = shallowconcat(M, Q_primpart(gel(tmp,j3)));
            vecj = shallowconcat(vecj, mkvec(mkvecsmall5(j,l,j1,j2,j3)));
            if (++ct >= dim)
            {
              update_Mj(&M, &vecj); ct = lg(vecj) - 1;
              if (ct == dim) return gerepilecopy(ltop, mkvec2(M, vecj));
            }
          }
        }
      }
    }
  }
  update_Mj(&M, &vecj);
  return gerepilecopy(ltop, mkvec2(M, vecj));
}

static GEN
sertocol2(GEN S, long l)
{
  GEN C = cgetg(l + 2, t_COL);
  long i;
  for (i = 0; i <= l; ++i) gel(C, i+1) = polcoeff0(S, i, -1);
  return C;
}

/* Compute polynomial P0 such that F=E4^(k/4)P0(E6/E4^(3/2)). */
static GEN
mfcanfindp0(GEN F, long k)
{
  pari_sp ltop = avma;
  GEN E4, E6, V, V1, Q, W, res, M, B;
  long l, j;
  l = k/6 + 2;
  V = mfcoefsser(F,l,1);
  E4 = mfcoefsser(mfEk(4),l,1);
  E6 = mfcoefsser(mfEk(6),l,1);
  V1 = gdiv(V, gpow(E4, gdivgs(utoi(k), 4), 0));
  Q = gdiv(E6, gpow(E4, gdivsg(3, gen_2), 0));
  W = gpowers(Q, l - 1);
  M = cgetg(l + 1, t_MAT);
  for (j = 1; j <= l; ++j) gel(M, j) = sertocol2(gel(W, j), l);
  B = sertocol2(V1, l);
  res = inverseimage(M, B);
  if (lg(res) == 1) err_space(F);
  return gerepilecopy(ltop, gtopolyrev(res, 0));
}

/* Compute the first n+1 Taylor coeffs at tau=I of a modular form
 * on SL_2(Z). */
GEN
mftaylor(GEN F, long n, long flreal, long prec)
{
  pari_sp ltop = avma;
  GEN P, P0, Pm1 = gen_0, v;
  GEN X2 = mkpoln(3, ghalf,gen_0,gneg(ghalf)); /* (x^2-1) / 2 */
  long k, m;
  if (!isf(F)) pari_err_TYPE("mftaylor",F);
  P = mfparams_ii(F); if (!P) pari_err_IMPL("mftaylor for this form");
  k = itos(gel(P, 2)); P0 = mfcanfindp0(F, k);
  v = cgetg(n+2, t_VEC); gel(v, 1) = RgX_coeff(P0,0);
  for (m = 0; m < n; m++)
  {
    GEN P1 = gdivgs(gmulsg(-(k + 2*m), RgX_shift(P0,1)), 12);
    P1 = gadd(P1, gmul(X2, RgX_deriv(P0)));
    if (m) P1 = gsub(P1, gdivgs(gmulsg(m*(m+k-1), Pm1), 144));
    Pm1 = P0; P0 = P1;
    gel(v, m+2) = RgX_coeff(P0, 0);
  }
  if (flreal)
  {
    GEN pi2 = Pi2n(1, prec), pim4 = gmulsg(-2, pi2), VPC;
    GEN C = gmulsg(3, gdiv(gpowgs(ggamma(ginv(utoi(4)), prec), 8), gpowgs(pi2, 6)));
    /* E_4(i): */
    GEN facn = gen_1;
    VPC = gpowers(gmul(pim4, gsqrt(C, prec)), n);
    C = gpow(C, gdivgs(utoi(k), 4), prec);
    for (m = 0; m <= n; m++)
    {
      gel(v, m+1) = gdiv(gmul(C, gmul(gel(v, m+1), gel(VPC, m+1))), facn);
      facn = gmulgs(facn, m+1);
    }
  }
  return gerepilecopy(ltop, v);
}

#if 0
/* To be used in mfsearch() */
GEN
mfreadratfile()
{
  GEN eqn;
  pariFILE *F = pari_fopengz("rateigen300.gp");
  eqn = gp_readvec_stream(F->file);
  pari_fclose(F);
  return eqn;
}
#endif

/********************************************************************/
/*                     EISENSTEIN AT CUSPS                          */
/********************************************************************/

/* Eisenstein evaluation, for now in weight not 2.
   First part, as complex numbers. */
GEN
mfcharcxeval(GEN CHI, long m, long prec)
{
  long N = mfcharmodulus(CHI);
  GEN o;
  if (cgcd(m, N) > 1) return gen_0;
  o = gmfcharorder(CHI);
  return chareval(gel(CHI,1), gel(CHI,2), utoi(m),
                  mkvec2(rootsof1_cx(o,prec), o));
}

long
mfcuspisregular(GEN NK, GEN cusp)
{
  GEN CHI;
  long A, C, N, k;
  if (checkmf_i(NK))
  { N = mf_get_N(NK); k = mf_get_k(NK); CHI = mf_get_CHI(NK); }
  else { checkNK(NK, &N, &k, &CHI, 0); if (!CHI) return 1; }
  if(typ(cusp) == t_INFINITY) return 1;
  C = itos(denom(cusp));
  A = itos(numer(cusp));
  return gequal1(mfchareval(CHI, 1 + A*N/cgcd(C, N/C)));
}

static GEN
char2vecexpo(GEN CHI)
{
  long i, N = mfcharmodulus(CHI);
  GEN ord = gmfcharorder(CHI);
  GEN T = cgetg(N+1, t_VECSMALL);
  for (i = 0; i < N; i++) T[i+1] = znchareval_i(CHI, i, ord);
  return T;
}
/* v non empty t_VECSMALL */
static GEN
vecsmall_to_fact(GEN v)
{
  long i, j, k, c, l = lg(v);
  GEN P = cgetg(l, t_COL), E = cgetg(l, t_COL);
  c = v[1]; j = 1;
  for (k = 1, i = 2; i < l; i++, k++)
  {
    if (v[i] != c)
    {
      gel(P, j) = utoi(c);
      gel(E, j) = utoipos(k);
      j++;
      c = v[i];
      k = 0;
    }
  }
  if (k)
  {
    gel(P, j) = utoi(c);
    gel(E, j) = utoipos(k);
    j++;
  }
  if (j == 1) return NULL;
  setlg(P, j);
  setlg(E, j); return mkmat2(P,E);
}

/* g=gcd(e,C), g1=gcd(N1*g,C), g2=gcd(N2*g,C); */
/* known: $C\mid g*N1*N2$ and $C*g\mid g1*g2$. */
/* datacusp=Vecsmall(N1*g/g1,N2*g/g2,C/g,C/g1,C/g2,(N1*g/g1)^{-1},(N2*g/g2)^{-1},-(A*e/g)^{-1}) */
/* (inverses mod C/g1, C/g2, and C/g respectively) */
static GEN
doublecharsum_i(GEN T1, GEN T2, long ord1, long ord2, GEN datacusp, long a1, long a2)
{
  long N1 = lg(T1) - 1, N2 = lg(T2) - 1, s1, s2, iT;
  long N1sg1 = datacusp[1], N2sg2 = datacusp[2], Csg = datacusp[3];
  long Csg1 = datacusp[4], Csg2 = datacusp[5];
  long N1i = datacusp[6], N2i = datacusp[7], Aei = datacusp[8];
  long M = clcm(Csg, clcm(ord1, ord2));
  long v1 = M/ord1, v2 = M/ord2, v3 = Aei*(M/Csg);
  GEN T = cgetg((Csg/Csg1)*(Csg/Csg2) + 1, t_VECSMALL);
  iT = 1;
  for (s1 = Fl_mul(a1, N1i, Csg1); s1 < Csg; s1 += Csg1)
  {
    long w1 = (a1 - N1sg1*s1)/Csg1;
    if (cgcd(w1, N1) != 1) continue;
    w1 %= N1; if (w1 < 0) w1 += N1;
    for (s2 = Fl_mul(a2, N2i, Csg2); s2 < Csg; s2 += Csg2)
    {
      long w2 = (a2 - N2sg2*s2)/Csg2, t;
      if (cgcd(w2, N2) != 1) continue;
      w2 %= N2; if (w2 < 0) w2 += N2;
      t = T1[w1 + 1]*v1 + T2[w2 + 1]*v2 + s1*s2*v3;
      t %= M; if (t < 0) t += M;
      T[iT++] = t;
    }
  }
  if (iT == 1) return NULL;
  setlg(T, iT); vecsmall_sort(T);
  return vecsmall_to_fact(T);
}

/* cusp = mkvecsmall2(A, C) */
GEN
doublecharsum(GEN CHI1, GEN CHI2, GEN cusp, long e, long a1, long a2)
{
  pari_sp av = avma;
  GEN T1, T2, datacusp, res;
  long A = cusp[1], C = cusp[2], N1, N2, g, g1, g2, Ai, u1, u2, ord1, ord2, junk;
  g = cbezout(-A*e,C, &Ai, &junk);
  CHI1 = get_mfchar(CHI1); N1 = mfcharmodulus(CHI1);
  CHI2 = get_mfchar(CHI2); N2 = mfcharmodulus(CHI2);
  g1 = cbezout(N1*g, C, &u1, &junk);
  if (cgcd(N1*g/g1, a1) != 1) return gen_0;
  g2 = cbezout(N2*g, C, &u2, &junk);
  if (cgcd(N2*g/g2, a2) != 1) return gen_0;
  ord1 = mfcharorder(CHI1); T1 = char2vecexpo(CHI1);
  ord2 = mfcharorder(CHI2); T2 = char2vecexpo(CHI2);
  datacusp = mkvecsmalln(8,N1*g/g1,N2*g/g2,C/g,C/g1,C/g2,u1,u2,Ai);
  res = doublecharsum_i(T1,T2,ord1,ord2,datacusp,a1,a2);
  if (!res) { avma = av; return gen_0; }
  else return gerepilecopy(av, res);
}

static int
cmpi(void *E, GEN a, GEN b)
{ (void)E; return cmpii(a, b); }

/* n > 0; true a(n) must be multiplied by \z_N^{A^{-1}(g1g2/C)n},
 * n1 = n*g1*g2 */
static GEN
mfeisenchi1chi2coeff_i(GEN T1, GEN T2, long ord1, long ord2, GEN datacusp,
                       long N1Csg, long N2Csg, long k, long n1)
{
  long i, l;
  GEN D, S = mkmat2(cgetg(1, t_COL), cgetg(1, t_COL));
  D = mydivisorsu(n1); l = lg(D);
  for (i = 1; i < l; i++)
  {
    long m1 = D[i], a1 = D[l-i] % N1Csg, a2 = m1 % N2Csg;
    GEN G, t = powuu(m1, k - 1);
    G = doublecharsum_i(T1, T2, ord1, ord2, datacusp, a1, a2);
    if (G)
    {
      G = mkmat2(gel(G, 1), ZC_Z_mul(gel(G, 2), t));
      S = merge_factor(S, G, NULL, &cmpi);
    }
    a1 = Fl_neg(a1, N1Csg);
    a2 = Fl_neg(a2, N2Csg);
    G = doublecharsum_i(T1, T2, ord1, ord2, datacusp, a1, a2);
    if (G)
    {
      G = mkmat2(gel(G, 1), ZC_Z_mul(gel(G, 2), (k & 1L) ? negi(t) : t));
      S = merge_factor(S, G, NULL, &cmpi);
    }
  }
  return S;
}

static GEN
mfeisenclean(GEN vres, long re)
{
  GEN wres;
  long lv = lg(vres) - 2, n;
  wres = cgetg(lv/re + 2, t_VEC);
  gel(wres, 1) = gel(vres, 1);
  for (n = 1; n <= lv; n++)
  {
    GEN tmp = gmael(vres, n+1, 1);
    if (n%re && lg(tmp) > 1) pari_err_BUG("mfeisenchi1chi2cusp");
    if (n%re == 0) gel(wres, n/re + 1) = gel(vres, n + 1);
  }
  return wres;
}

/*****************************************************************/
/*                          f(0)                                 */
/*****************************************************************/

/* Computation of Q_k(\z_N^s) as a polynomial in \z_N^s. FIXME: explicit
 * formula ? */
GEN
mfqk(long k, long N)
{
  GEN X = pol_x(0), P = gsubgs(gpowgs(X,N), 1), ZI, Q, Xm1, invden;
  long i;
  ZI = cgetg(N, t_VEC);
  for (i = 1; i < N; i++) gel(ZI, i) = utoi(i);
  ZI = gtopoly(ZI, 0);
  if (k == 1) return ZI;
  invden = RgXQ_powu(ZI, k, P);
  Q = gneg(X); Xm1 = gsubgs(X, 1);
  for (i = 2; i < k; i++)
    Q = gmul(X, ZX_add(gmul(Xm1, ZX_deriv(Q)), gmulsg(-i, Q)));
  return RgXQ_mul(Q, invden, P);
}
GEN
mfsk(GEN CHI, GEN Q, long k)
{
  long i, l, m, F, F1, M, o;
  GEN v, w, D, T;

  CHI = get_mfchar(CHI);
  M = mfcharmodulus(CHI);
  o = mfcharorder(CHI);
  CHI = mfchartoprimitive(CHI, &F);
  T = char2vecexpo(CHI);
  v = zerovec(o);
  for (m = 0; m < F; m++)
  {
    long j = T[m + 1]; /* chi(m) = zeta_o^T[m+1] */
    if (j < 0) continue;
    if (j) j = o - j;
    gel(v, j+1) = addii(gel(v, j+1), RgX_coeff(Q,m));
  }
  /* \sum \bar{chi}(m) Q[m] */
  F1 = M / F;
  D = mydivisorsu(F1);
  l = lg(D);
  w = zerovec(o);
  for (i = 1; i < l; i++)
  {
    long j, d = D[i], d1 = D[l-i], mu = moebiusu(d);
    GEN q;
    if (!mu) continue; /* FIXME ! */
    j = T[d + 1];
    if (j < 0) continue;
    q = powuu(d1, k);
    if (mu < 0) q = negi(q);
    gel(w, j+1) = addii(gel(w, j+1), q);
  }
  return RgXQ_mul(RgV_to_RgX(v, 0), RgV_to_RgX(w, 0), polcyclo(o,0));
}

/* vector of coefficients from a(0) to a(lim); cusp a vecsmall */
GEN
mfeisenchi1chi2cusp(GEN CHI1, GEN CHI2, GEN cusp, long e, long k, long lim)
{
  pari_sp ltop = avma;
  GEN vres = cgetg(lim + 2, t_VEC), T1, T2, datacusp;
  long A = cusp[1], C = cusp[2], g = cgcd(e, C);
  long N1 = mfcharmodulus(CHI1), N2 = mfcharmodulus(CHI2);
  long ord1, ord2, g1, g2, g1g2, u1, u2, N = e*N1*N2, Csg = C/g;
  long Ai, Aei, M, junk, NsM, Aig, n1, N1Csg = N1*Csg, N2Csg = N2*Csg;

  cbezout(A, N, &Ai, &junk);
  g = cbezout(-A*e, C, &Aei, &junk);
  g1 = cbezout(N1*g, C, &u1, &junk);
  g2 = cbezout(N2*g, C, &u2, &junk);
  g1g2 = g1*g2;
  Aig = ((Ai * g1g2) / C) % N; if (Aig < 0) Aig += N;
  ord1 = mfcharorder(CHI1); T1 = char2vecexpo(CHI1);
  ord2 = mfcharorder(CHI2); T2 = char2vecexpo(CHI2);
  datacusp = mkvecsmalln(8, N1*g/g1, N2*g/g2, C/g, C/g1, C/g2, u1, u2, Aei);
  M = clcm(Csg, clcm(ord1, ord2));
  NsM = N / M;
  for (n1 = 1; n1 <= lim; n1++)
  {
    GEN tmp = mfeisenchi1chi2coeff_i(T1, T2, ord1, ord2, datacusp,
                                     N1Csg, N2Csg, k, n1);
    GEN P = gel(tmp, 1), E = gel(tmp, 2);
    long i, l = lg(P);
    for (i = 1; i < l; i++)
    {
      long pi = (NsM*itos(gel(P, i)) + n1*Aig)%N;
      if (pi < 0) pi += N;
      gel(P, i) = utoi(pi);
    }
    gel(vres, n1 + 1) = mkvec2(P, E);
  }
  /*
  if (k > 1)
    gel(vres, 1) = mfeisenchi1chi20(...);
  else
  gel(vres, 1) = mfeisenchi1chi2wt10(...); */
  gel(vres, 1) = gen_0;
  vres = mfeisenclean(vres, cgcd(C*C, N*e) / (g1*g2));
  return gerepilecopy(ltop, vres);
}

GEN
mftsteisencusp(GEN CHI1, GEN CHI2, GEN cusp, long e, long k, long lim)
{
  long A, C, N;
  CHI1 = get_mfchar(CHI1);
  CHI2 = get_mfchar(CHI2);
  N = e*mfcharmodulus(CHI1)*mfcharmodulus(CHI2);
  cusp_canon(cusp, N, &A, &C);
  cusp = mkvecsmall2(A, C);
  return mfeisenchi1chi2cusp(CHI1, CHI2, cusp, e, k, lim);
}

/*****************************************************************/
/*                       END EISENSTEIN CUSPS                    */
/*****************************************************************/

/* Period polynomials (only for SL_2(\Z) for now) */
/* flag = 0: full, flag = +1 or -1, odd/even */

/* Basis of period polynomials */
GEN
mfperiodpolbasis(long k, long flag)
{
  pari_sp av = avma;
  long i, j, km2 = k - 2;
  GEN M, C;
  if (k <= 4) return cgetg(1,t_VEC);
  M = cgetg(k, t_MAT);
  C = matpascal(km2);
  if (!flag)
    for (j = 0; j <= km2; j++)
    {
      GEN v = cgetg(k, t_COL);
      for (i = 0; i <= j; i++) gel(v, i+1) = gcoeff(C, j+1, i+1);
      for (; i <= km2; i++) gel(v, i+1) = gcoeff(C, km2-j+1, i-j+1);
      gel(M, j+1) = v;
    }
  else
    for (j = 0; j <= km2; ++j)
    {
      GEN v = cgetg(k, t_COL);
      for (i = 0; i <= km2; ++i)
      {
        GEN a = i < j ? gcoeff(C, j+1, i+1) : gen_0;
        if (i + j >= km2)
        {
          GEN b = gcoeff(C, j+1, i+j-km2+1);
          a = flag < 0 ? addii(a,b) : subii(a,b);
        }
        gel(v, i+1) = a;
      }
      gel(M, j+1) = v;
    }
  return gerepilecopy(av, RgM_to_RgXV(ZM_ker(M), 0));
}

/* period polynomial associated to an eigenform in SL_2(Z) (not checked),
 * assumed already embedded using mfembed. flag is as above.
 * der is the order of derivation of the lambda function */
GEN
mfperiodpol(GEN F, long flag, long der, long bitprec)
{
  pari_sp ltop = avma;
  GEN sdom, L, V, B, P;
  long k, km2, n, step, flagmf, n0;
  if (!isf(F)) pari_err_TYPE("mfperiodpol", F);
  P = mfparams_ii(F);
  if (!P) pari_err_IMPL("mfperiodpol for this form");
  if (!gequal1(gel(P,1))) pari_err_IMPL("mfperiodpol in level > 1");
  k = itos(gel(P, 2)); km2 = k-2;
  flagmf = gequal0(mfak_i(F, 0)) ? 3: 1;
  sdom = mkvec3(stoi(k/2), stoi(k/2), gen_1);
  L = lfuninit(mftolfun(F, flagmf, bitprec), sdom, der, bitprec);
  V = zerovec(k-1);
  B = vecbinomial(km2);
  step = flag? 2: 1;
  n0 = flag >= 0? 0: 1;
  for (n = n0; n <= km2; n += step)
  {
    GEN z = lfunlambda0(L, stoi(n+1), der, bitprec);
    gel(V, n+1) = gmul(mulcxpowIs(gel(B, n+1), 1-n), z);
  }
  return gerepileupto(ltop, gtopoly(V, 0));
}

/*************************************************************/
/* Implementation of mfparams: give level, weight, character */

/* mfparams: function called by the user; mfparams_i: inner function with
   character calculation; mfparams_ii: inner function without character,
   returns [N,k,code]. */

/* codes:
[CHI]: take as such, [1, CHI1, CHI2]: charmul,
[0, [CHI1,...]: must have all induced CHI1 equal, [2, CHI1, CHI2]: chardiv,
[3, CHI]: charinv.
*/

static GEN
params_linear(GEN F, GEN L)
{
  long lF, i, c;
  GEN N = gen_1, k = NULL, v = cgetg_copy(L,&lF);
  for (i = c = 1; i < lF; ++i)
  {
    GEN Q;
    if (gequal0(gel(L, i))) continue;
    Q = mfparams_ii(gel(F,i));
    if (k && !gequal(k, gel(Q,2))) return NULL;
    N = lcmii(N, gel(Q,1));
    k = gel(Q,2);
    gel(v, c++) = gel(F,i);
  }
  if (!k) return NULL;
  setlg(v, c); return mkvec3(N, k, v);
}

/* FIXME: unify with lfunetaquotype */
static GEN
params_eta(GEN eta)
{
  GEN M = gel(eta,1), R = gel(eta,2), gN, S, P, D;
  long N, k, i, lD, lM = lg(M);
  N = 1; for(i = 1; i < lM; i++) N = clcm(N, M[i]);
  D = divisorsu(N); lD = lg(D);
  S = gen_0; P = gen_1; k = 0;
  for (i = 1; i < lD; ++i)
  {
    long m = D[i], r = 0, j;
    for (j = 1; j < lM; ++j)
      if (m == M[j]) r += R[j];
    S = gadd(S, gdivgs(utoi(r), 24*m));
    if (odd(r)) P = mulis(P, m);
    k += r;
  }
  k >>= 1;
  gN = lcmii(stoi(N), Q_denom(S));
  D = odd(k)? negi(P): P;
  return mkvec3(gN, utoi(k), coredisc(D));
}

/* char operations not done but encoded */
static GEN
mfparams_ii(GEN F)
{
  GEN gN, C, CHI, D, P, P1, P2, gm, F2, F3;
  long N, k, n;
  switch(f_type(F))
  {
    case t_MF_CONST:
      C = gel(F,2);
      return (lg(C) != 2) ? NULL : mkvec3(gen_1, gen_0, gen_1);
    case t_MF_EISEN:
      F2 = gel(F,2); k = F2[1];
      F3 = gel(F,3); CHI = gel(F3,2);
      N = mfcharmodulus(CHI);
      if (lg(F3) == 3) CHI = mkvec(CHI);
      else
      {
        GEN CHI2 = gel(F3,3);
        N = clcm(N, mfcharmodulus(CHI2));
        CHI = mkvec2(CHI, CHI2);
      }
      return mkvec3(stoi(N), stoi(k), CHI);
    case t_MF_Ek:
      k = gel(F,2)[1];
      return mkvec3(gen_1, stoi(k), gen_1);
    case t_MF_DELTA:
      return mkvec3(gen_1, utoi(12), gen_1);
    case t_MF_ETAQUO:
      return params_eta(gel(F,2));
    case t_MF_ELL:
      gN = ellQ_get_N(gel(F,2));
      return mkvec3(gN, gen_2, gen_1);
    case t_MF_MUL:
      P1 = mfparams_ii(gel(F,2)); if (!P1) return NULL;
      P2 = mfparams_ii(gel(F,3)); if (!P2) return NULL;
      gN = lcmii(gel(P1,1), gel(P2,1));
      return mkvec3(gN, gadd(gel(P1,2), gel(P2,2)), gen_0);
    case t_MF_POW:
      P = mfparams_ii(gel(F,2)); if (!P) return NULL;
      n = itos(gel(F,3));
      return mkvec3(gel(P,1), gmulsg(n,gel(P,2)), gen_0);
    case t_MF_MULRC:
      P1 = mfparams_ii(gel(F,2)); if (!P1) return NULL;
      P2 = mfparams_ii(gel(F,3)); if (!P2) return NULL;
      gN = lcmii(gel(P1,1), gel(P2,1));
      return mkvec3(gN, gaddgs(gadd(gel(P1,2),gel(P2,2)),2*itos(gel(F,4))), gen_0);
    case t_MF_LINEAR: case t_MF_LINEAR_BHN:
      return params_linear(gel(F,2), gel(F,3));
    case t_MF_DIV:
      P1 = mfparams_ii(gel(F,2)); if (!P1) return NULL;
      P2 = mfparams_ii(gel(F,3)); if (!P2) return NULL;
      gN = lcmii(gel(P1,1), gel(P2,1));
      CHI = mkvec3(gen_2, gel(P1,3), gel(P2,3));
      return mkvec3(gN, gsub(gel(P1,2), gel(P2,2)), CHI);
    case t_MF_SHIFT: return mfparams_ii(gel(F,2));
    case t_MF_DERIV: case t_MF_DERIVE2:
      P = mfparams_ii(gel(F,2)); if (!P) return NULL;
      gm = gel(F,3);
      return mkvec3(gel(P,1), gadd(gel(P,2), shifti(gm,1)), gel(P,3));
    case t_MF_INTEG:
      P = mfparams_ii(gel(F,2)); if (!P) return NULL;
      gm = gel(F,3);
      return mkvec3(gel(P,1), gsub(gel(P,2), shifti(gm,1)), gel(P,3));
    case t_MF_TWIST:
      P = mfparams_ii(gel(F,2)); if (!P) return NULL;
      D = gel(F,3);
      return mkvec3(mulii(gel(P,1), sqri(D)), gel(P,2), gel(P,3));
    case t_MF_HECKE:
      P = mfparams_ii(gel(F,4));
      gel(P, 1) = glcm(gel(P, 1), stoi(gel(F,2)[4]));
      return P;
    case t_MF_BD:
      P = mfparams_ii(gel(F,3)); if (!P) return NULL;
      D = gel(F,2);
      return mkvec3(mulii(gel(P,1), D), gel(P,2), gel(P,3));
    case t_MF_TRACE:
      return mkvec3(stoi(gel(F,2)[1]), stoi(gel(F,2)[2]), gel(gel(F,3),_CHIP));
    case t_MF_RELTOABS:
      return mfparams_ii(gel(F,2));
    case t_MF_NEWTRACE:
    {
      GEN NK = gel(F,2), DATA = gel(F,3), CHI;
      CHI = newtrace_stripped(DATA)? DATA: gel(gel(DATA,1),_CHIP);
      return mkvec3(stoi(NK[1]), stoi(NK[2]), CHI);
    }
    case t_MF_DIHEDRAL:
    {
      GEN CHI = gel(F,6), G = gel(CHI,1);
      return mkvec3(znstar_get_N(G), gen_1, CHI);
    }
    case t_MF_CLOSURE: case t_MF_EISENM1M2:
      return NULL;
    case t_MF_EMBED: case t_MF_HECKEU:
      return mfparams_ii(gel(F,2));
    default: pari_err_TYPE("mfparams", F);
    return NULL;/* not reached */
  }
}

static GEN
induce(GEN G, GEN CHI)
{
  GEN o, chi;
  if (typ(CHI) == t_INT) /* Kronecker */
  {
    chi = gel(znchar_quad(G, CHI), 2);
    o = ZV_equal0(chi)? gen_1: gen_2;
  }
  else
  {
    if (mfcharmodulus(CHI) == itos(znstar_get_N(G))) return CHI;
    chi = zncharinduce(gel(CHI,1), gel(CHI,2), G);
    o = gel(CHI, 3);
  }
  return mkvec3(G, chi, o);
}

static GEN
mfcharmul(GEN G, GEN CHI1, GEN CHI2)
{
  GEN CHI3;
  CHI1 = induce(G, CHI1);
  CHI2 = induce(G, CHI2);
  CHI3 = zncharmul(G, gel(CHI1,2), gel(CHI2,2));
  return mkvec3(G, CHI3, zncharorder(G, CHI3));
}

static GEN
mfcharpow(GEN G, GEN CHI, long n)
{
  GEN CHI1 = induce(G, CHI), CHI3;
  CHI3 = zncharpow(G, gel(CHI1,2), stoi(n));
  return mkvec3(G, CHI3, zncharorder(G, CHI3));
}

static GEN
mfchardiv(GEN G, GEN CHI1, GEN CHI2)
{
  GEN CHI3;
  CHI1 = induce(G, CHI1);
  CHI2 = induce(G, CHI2);
  CHI3 = znchardiv(G, gel(CHI1, 2), gel(CHI2, 2));
  return mkvec3(G, CHI3, zncharorder(G, CHI3));
}

static GEN
mfparams_chi(GEN F) { return gel(mfparams_i(F),3); }

static GEN
mfparams_i(GEN F)
{
  GEN gN, P, CHIcode, k, CHI, CHI1, CHI2, G;
  long i, n;
  P = mfparams_ii(F); if (!P) return NULL;
  gN = gel(P,1);
  k  = gel(P,2);
  CHIcode = gel(P,3);
  G = znstar0(gN,1);
  switch(f_type(F))
  {
    case t_MF_EISEN:
      CHI = gel(CHIcode,1);
      if (lg(CHIcode) != 2) CHI = mfcharmul(G, CHI, gel(CHIcode,2));
      return mkvec3(gN, k, CHI);
    case t_MF_MUL: case t_MF_MULRC:
      CHI1 = mfparams_chi(gel(F,2));
      CHI2 = mfparams_chi(gel(F,3));
      return mkvec3(gN, k, mfcharmul(G, CHI1, CHI2));
    case t_MF_POW:
      CHI = mfparams_chi(gel(F,2));
      n = itos(gel(F,3));
      return mkvec3(gN, k, mfcharpow(G, CHI, n));
    case t_MF_LINEAR: case t_MF_LINEAR_BHN:
      CHI = induce(G, mfparams_chi(gel(CHIcode,1)));
      for (i = 2; i < lg(CHIcode); i++)
      {
        CHI1 = induce(G, mfparams_chi(gel(CHIcode,i)));
        if (!gequal(CHI,CHI1)) return NULL;
      }
      return mkvec3(gN, k, CHI);
    case t_MF_DIV:
      CHI1 = mfparams_chi(gel(F,2));
      CHI2 = mfparams_chi(gel(F,3));
      return mkvec3(gN, k, mfchardiv(G, CHI1, CHI2));
    case t_MF_DERIV: case t_MF_DERIVE2: case t_MF_INTEG:
    case t_MF_TWIST: case t_MF_RELTOABS:
      return mkvec3(gN, k, mfparams_chi(gel(F,2)));
    case t_MF_BD:
      return mkvec3(gN, k, mfparams_chi(gel(F,3)));
    case t_MF_EMBED: case t_MF_HECKEU: case t_MF_SHIFT:
      return mfparams_i(gel(F,2));
    case t_MF_HECKE:
      P = mfparams_i(gel(F,4));
      gel(P, 1) = glcm(gel(P, 1), stoi(gel(F,2)[4]));
      return P;
    case t_MF_DIHEDRAL:
      return mkvec3(gN, k, gen_0);
    case t_MF_CLOSURE: case t_MF_EISENM1M2:
      return NULL;
    default:
      return P;
  }
}

GEN
mfparams(GEN F)
{
  pari_sp av = avma;
  GEN z, CHI;
  if (checkmf_i(F))
  {
    long N = mf_get_N(F), k = mf_get_k(F);
    z = mkvec3(utoi(N), utoi(k), mf_get_CHI(F));
  }
  else
  {
    if (!isf(F)) pari_err_TYPE("mfparams", F);
    z = mfparams_i(F);
    if (!z) { avma = av; return mkvec3(gen_0, gen_0, gen_0); }
  }
  CHI = gel(z,3);
  if (typ(CHI) != t_INT)
  {
    GEN G = gel(CHI,1), chi = gel(CHI,2);
    switch(mfcharorder(CHI))
    {
      case 1: chi=gen_1; break;
      case 2: chi=znchartokronecker(G,chi,1); break;
      default:chi=mkintmod(znconreyexp(G,chi), znstar_get_N(G)); break;
    }
    gel(z,3) = chi;
  }
  return gerepilecopy(av, z);
}

static GEN
mfiscuspidal_i(GEN F)
{
  GEN P, mf, V;
  long lv;
  if (!isf(F)) pari_err_TYPE("mfiscuspidal", F);
  P = mfparams_i(F);
  if (!P) pari_err_IMPL("mfiscuspidal for this F");
  mf = mfinit(P, mf_CUSP);
  V = mftobasis(mf, F, 1); lv = lg(V) - 1;
  return lv ? mkvec2(mf, V) : NULL;
}

long
mfiscuspidal(GEN F)
{
  pari_sp av = avma;
  GEN MFV = mfiscuspidal_i(F);
  long r = MFV ? 1 : 0;
  avma = av; return r;
}

GEN
mfisCM(GEN F)
{
  pari_sp ltop = avma;
  forprime_t S;
  GEN P, V, v, w;
  long N, k, lV, ct, sb, p, i;
  if (!isf(F)) pari_err_TYPE("mfisCM", F);
  P = mfparams_i(F);
  if (!P) pari_err_IMPL("mfisCM for this F");
  N = itos(gel(P, 1)); k = itos(gel(P, 2));
  V = mfunram(N); lV = lg(V);
  for (ct = 0, i = 1; i < lV; ++i)
    if (V[i] < 0) ct++;
  sb = maxss(mfsturmNk(N, k), 4*N);
  v = mfcoefs_i(F, sb, 1);
  u_forprime_init(&S, 2, sb);
  while ((p = u_forprime_next(&S)))
  {
    GEN ap = gel(v, p + 1);
    if (!gequal0(ap))
    {
      for (i = 1; i < lV; ++i)
        if (V[i] < 0 && kross(V[i], p) == -1) { V[i] = 0; ct--; }
    }
  }
  if (!ct) { avma = ltop; return gen_0; }
  if (ct == 1)
    for (i = 1; i < lV; ++i)
      if (V[i] < 0) return gerepileupto(ltop, stoi(V[i]));
  if (k > 1) pari_err_BUG("mfisCM");
  w = cgetg(ct + 1, t_VECSMALL); ct = 0;
  for (i = 1; i < lV; ++i)
    if (V[i] < 0) { ct++; w[ct] = V[i]; }
  return gerepileupto(ltop, w);
}

static long
mfspace_i(GEN F)
{
  GEN P, mf, vF;
  long leis, l, i, N;

  if (!isf(F)) { checkmf(F); return mf_get_space(F); }
  P = mfparams_i(F); if (!P) pari_err_IMPL("mfspace for this F");
  gel(P,3) = mfchar2char(gel(P,3));
  mf = mfinit(P, mf_FULL);
  vF = mftobasis_i(mf, F); /* rigorous */
  l = lg(vF); if (l == 1) return -1;
  leis = lg(mf_get_eisen(mf));
  for (i = 1; i < leis; i++)
    if (!gequal0(gel(vF, i)))
    {
      for (i = leis; i < l; i++)
        if (!gequal0(gel(vF,i))) return mf_FULL;
      return mf_EISEN;
    }
  vF = mftonew_i(mf, vecslice(vF, leis, l-1), &N);
  if (N != mf_get_N(mf)) return mf_OLD;
  l = lg(vF);
  for (i = 1; i < l; i++)
    if (itos(gmael(vF,i,1)) != N) return mf_CUSP;
  return mf_NEW;
}
long
mfspace(GEN F)
{
  pari_sp av = avma;
  long s = mfspace_i(F);
  avma = av; return s;
}

static GEN
mfscalmul(GEN F, GEN la)
{ return mflinear_i(mkvec(F), mkvec(la)); }
/* Always returns 0 if F does not belong to the new space and level > 1 */
long
mfisselfdual(GEN F)
{
  pari_sp av = avma;
  GEN P, gN, mf, V, G, cof, cog;
  long r;
  if (!isf(F)) pari_err_TYPE("mfisselfdual", F);
  cof = mfak_i(F, 1);
  if (gequal0(cof)) { avma = av; return 0; }
  P = mfparams_i(F); gN = gel(P,1);
  if (!signe(gN)) pari_err_IMPL("mfisselfdual for this F");
  if (is_pm1(gN)) { avma = av; return 1; }
  mf = mfsplit(mfinit(P, mf_NEW), 0, 0); /* FIXME: could guess dimlim ? */
  V = mftobasis(mf, F, 1);
  if (lg(V) == 1) pari_err_IMPL("mfisselfdual outside of new space");
  G = mfatkin(mf, F, gN, 128);
  cog = mfak_i(G, 1);
  r = mfisequal(mfscalmul(F, gdiv(cog,cof)), G, 0);
  avma = av; return r;
}

static GEN
lfunfindchi(GEN ldata, long prec)
{
  long k = ldata_get_k(ldata), ct, i, nb, l;
  long N = itou(ldata_get_conductor(ldata)), B = N+1;
  GEN L = mfchargalois(N, odd(k), gen_2), V;

  l = lg(L); nb = l-1; V = const_vecsmall(nb, 1);
  ct = 0;
  for(;;)
  {
    GEN vecan = ldata_vecan(ldata_get_an(ldata), B, prec);
    for (i = 1; i < l; ++i)
      if (V[i])
      {
        GEN CHI = gel(L,i);
        long n;
        for (n = 1; n <= B; ++n)
        {
          GEN an;
          if (cgcd(n, N) > 1) continue;
          an = gel(vecan, n);
          if (!gequal0(an) && !gequal(gmul(mfchareval(CHI, n), gconj(an)), an))
          {
            nb--; V[i] = 0;
            break;
          }
        }
      }
    if (nb == 1) break;
    if (++ct >= 4) pari_err_BUG("lfunfindchi [too many iterations]");
    B *= 2;
  }
  for (i = 1; i < l; ++i)
    if (V[i]) { GEN CHI = gel(L,i); return mkvec2(gel(CHI,1), gel(CHI,2)); }
  return gen_0; /*LCOV_EXCL_LINE*/
}

GEN
mffromlfun(GEN L, long prec)
{
  pari_sp ltop = avma;
  GEN ldata = lfunmisc_to_ldata_shallow(L);
  GEN Vga = ldata_get_gammavec(ldata);
  GEN mf, V, vecan, a0, CHI;
  long k, N, sb, space;
  if (!gequal(Vga, mkvec2(gen_0, gen_1)))
    pari_err_TYPE("mffromlfun", L);
  if (!ldata_isreal(ldata))
    pari_err(e_MISC, "Only real L-functions in mffromlfun");
  k = ldata_get_k(ldata);
  N = itos(ldata_get_conductor(ldata));
  space = lg(ldata) == 7 ? mf_CUSP : mf_FULL;
  CHI = lfunfindchi(ldata, prec);
  mf = mfinit(mkvec3(stoi(N), stoi(k), CHI), space);
  sb = mfsturm(mf);
  vecan = ldata_vecan(ldata_get_an(ldata), sb + 2, prec);
  if (space == mf_CUSP) a0 = gen_0;
  else a0 = gneg(lfun(L, gen_0, prec2nbits(prec)));
  vecan = shallowconcat(a0, vecan);
  V = mftobasis(mf, vecan, 1);
  if (lg(V) == 1) pari_err_BUG("mffromlfun");
  return gerepilecopy(ltop, mflinear_i(mfbasis(mf), V));
}

/* Copyright (C) 2000  The PARI group.

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

/********************************************************************/
/**                                                                **/
/**           ASSOCIATIVE ALGEBRAS, CENTRAL SIMPLE ALGEBRAS        **/
/**                 contributed by Aurel Page (2014)               **/
/**                                                                **/
/********************************************************************/
static GEN al_subalg(GEN al, GEN basis);
static GEN al_maximal_primes(GEN al, GEN P);
static GEN alnatmultable(GEN al, long D);
static GEN _tablemul_ej(GEN mt, GEN x, long j);
static GEN _tablemul_ej_Fp(GEN mt, GEN x, long j, GEN p);
static GEN _tablemul_ej_Fl(GEN mt, GEN x, long j, ulong p);
static ulong altracei(GEN mt, ulong p, ulong expo, ulong modu);

int
checkal_i(GEN al)
{
  GEN mt;
  if (typ(al) != t_VEC || lg(al) != 12) return 0;
  mt = al_get_multable(al);
  if (typ(mt) != t_VEC || lg(mt) == 1 || typ(gel(mt,1)) != t_MAT) return 0;
  return 1;
}
void
checkal(GEN al)
{ if (!checkal_i(al)) pari_err_TYPE("checkal [please apply alinit()]",al); }

/**  ACCESSORS  **/
long
al_type(GEN al)
{
  if (isintzero(al_get_splitting(al)) || !gequal0(al_get_char(al))) return al_TABLE;
  switch(typ(gmael(al,2,1))) {
    case t_MAT: return al_CSA;
    case t_POL:
    case t_POLMOD: return al_CYCLIC;
    default: return al_NULL;
  }
  return -1; /*not reached*/
}
long
altype(GEN al)
{ return checkal_i(al)? al_type(al): al_NULL; }

/* absdim == dim for al_TABLE. */
long
al_get_dim(GEN al)
{
  long d;
  switch(al_type(al)) {
    case al_TABLE: return lg(al_get_multable(al))-1;
    case al_CSA: return lg(al_get_relmultable(al))-1;
    case al_CYCLIC: d = al_get_degree(al); return d*d;
    default: pari_err_TYPE("al_get_dim", al);
  }
  return -1; /*not reached*/
}
long
algetdim(GEN al)
{ checkal(al); return al_get_dim(al); }

long
al_get_absdim(GEN al)
{
  switch(al_type(al)) {
    case al_TABLE: return lg(al_get_multable(al))-1;
    case al_CSA: return al_get_dim(al)*nf_get_degree(al_get_center(al));
    case al_CYCLIC:
      return rnf_get_absdegree(al_get_splitting(al))*al_get_degree(al);
    default: pari_err_TYPE("al_get_absdim", al);
  }
  return -1;/*not reached*/
}
long
algetabsdim(GEN al)
{ checkal(al); return al_get_absdim(al); }

/* only cyclic */
GEN
al_get_auts(GEN al)
{
  if (al_type(al) != al_CYCLIC) pari_err_TYPE("al_get_auts", al);
  return gel(al,2);
}
GEN
al_get_aut(GEN al)
{
  if (al_type(al) != al_CYCLIC) pari_err_TYPE("al_get_aut", al);
  return gel(al_get_auts(al),1);
}
GEN
algetaut(GEN al) { checkal(al); return al_get_aut(al); }
GEN
al_get_b(GEN al)
{
  if (al_type(al) != al_CYCLIC) pari_err_TYPE("al_get_b", al);
  return gel(al,3);
}
GEN
algetb(GEN al) { checkal(al); return al_get_b(al); }

/* only CSA */
GEN
al_get_relmultable(GEN al) { return gel(al,2); }
GEN
algetrelmultable(GEN al) { checkal(al); return al_get_relmultable(al); }
GEN
al_get_splittingdata(GEN al) { return gel(al,3); }
GEN
algetsplittingdata(GEN al) { checkal(al); return al_get_splittingdata(al); }
GEN
al_get_splittingbasis(GEN al) { return gmael(al,3,2); }
GEN
al_get_splittingbasisinv(GEN al) { return gmael(al,3,3); }

/* only cyclic and CSA */
GEN
al_get_splitting(GEN al) { return gel(al,1); }
GEN
algetsplitting(GEN al) { checkal(al); return al_get_splitting(al); }
long
al_get_degree(GEN al) { return rnf_get_degree(al_get_splitting(al)); }
long
algetdegree(GEN al)
{
  GEN rnf;
  checkal(al);
  rnf = al_get_splitting(al);
  if (typ(rnf)!=t_VEC) pari_err_TYPE("algetdegree",al);
  return rnf_get_degree(rnf);
}

GEN
al_get_center(GEN al) { return rnf_get_nf(al_get_splitting(al)); }
GEN
algetcenter(GEN al)
{
  GEN rnf;
  checkal(al);
  rnf = al_get_splitting(al);
  if (typ(rnf)!=t_VEC) pari_err_TYPE("algetdegree",al);
  return rnf_get_nf(rnf);
}
GEN
al_get_splitpol(GEN al) { return rnf_get_pol(al_get_splitting(al)); }
GEN
al_get_abssplitting(GEN al) { return gel(al,6); }
GEN
al_get_hasse_i(GEN al) { return gel(al,4); }
GEN
algethassei(GEN al) { checkal(al); return al_get_hasse_i(al); }
GEN
al_get_hasse_f(GEN al) { return gel(al,5); }
GEN
algethassef(GEN al) { checkal(al); return al_get_hasse_f(al); }

/* all types */
GEN
al_get_ord(GEN al) { return gel(al,7); }
GEN
algetord(GEN al) { checkal(al); return al_get_ord(al); }
GEN
al_get_invord(GEN al) { return gel(al,8); }
GEN
algetinvord(GEN al) { checkal(al); return al_get_invord(al); }
GEN
al_get_multable(GEN al) { return gel(al,9); }
GEN
algetmultable(GEN al) { checkal(al); return al_get_multable(al); }
GEN
al_get_char(GEN al) { return gel(al,10); }
GEN
algetchar(GEN al) { checkal(al); return al_get_char(al); }
GEN
al_get_tracebasis(GEN al) { return gel(al,11); }

/** ADDITIONAL **/

/* FIXME: not rigorous */
static long
rnfrealdec(GEN rnf, long k)
{
  GEN nf = rnf_get_nf(rnf), pol = rnf_get_pol(rnf);
  long i, l = lg(pol);
  pol = shallowcopy(pol);
  for (i=2; i<l; i++) gel(pol,i) = nfembed(nf, gel(pol,i), k);
  return sturm(pol);
}

/* pl : requested signs for real embeddings, 0 = no sign constraint */
/* FIXME: not rigorous */
static long
ispositive(GEN nf, GEN x, GEN pl)
{
  long l = lg(pl), i;
  for (i = 1; i < l; i++)
    if (pl[i] && pl[i] != gsigne(nfembed(nf,x,i))) return 0;
  return 1;
}

/** IDEALCHINESE **/

GEN
extchinese(GEN nf, GEN x, GEN y, GEN pl, GEN* red)
{
  pari_sp av = avma;
  long i, r, e;
  GEN y0, G, I,x0, Mr, MI, lambda, mlambda, C, sol, nz;

  y0 = idealchinese(nf, x, y);
  I = factorbackprime(nf, gel(x,1), gel(x,2));
  G = nf_get_roundG(nf);
  *red = ZM_mul(I,ZM_lll(ZM_mul(G,I), 0.99, LLL_IM));
  y0 = ZC_reducemodmatrix(y0,*red);

  if (ispositive(nf, y0, pl)) {
    gerepileall(av, 2, &y0, red);
    return y0;
  }

  nz = vecsmall01_to_indices(pl);
  Mr = rowpermute(nf_get_M(nf), nz);
  MI = RgM_mul(Mr,*red);
  lambda = gdivgs(matrixnorm(MI,DEFAULTPREC), 2);
  mlambda = gneg(lambda);

  r = lg(nz); C = cgetg(r, t_COL);
  for (i = 1; i < r; i++) gel(C,i) = pl[nz[i]] < 0? mlambda: lambda;
  C = RgC_sub(C, RgM_RgC_mul(Mr,y0));

  sol = inverseimage(MI, C);
  x0 = ZM_ZC_mul(*red, grndtoi(sol, &e));
  y0 = ZC_add(y0,x0);

  gerepileall(av, 2, &y0, red);
  return y0;
}

/* no garbage collection */
static GEN
backtrackfacto(GEN y0, long n, GEN red, GEN pl, GEN nf, GEN data, int (*test)(GEN,GEN,GEN), GEN* fa, GEN N, GEN I)
{
  pari_sp av = avma;
  long b, i;
  GEN y1, y2, ny, fan;
  long v[n+1];
  for (b = 0;; b = b+(2*b)/(3*n)+1)
  {
    avma = av;
    for (i=1; i<=n; i++) v[i] = -b;
    v[n]--;
    while (1) {
      i=n;
      while (i>0) {
        if (v[i]==b) {
          v[i] = -b;
          i--;
        }
        else {
          v[i]++;
          break;
        }
      }
      if (i==0) break;

      y1 = y0;
      for (i=1; i<=n; i++) y1 = nfadd(nf, y1, ZC_z_mul(gel(red,i), v[i]));

      if (!ispositive(nf, y1, pl)) continue;

      ny = absi(nfnorm(nf, y1));
      if (!signe(ny)) continue;
      ny = diviiexact(ny,gcdii(ny,N));
      fan = Z_factor_limit(ny,1<<17);
      if (lg(fan)>1 && nbrows(fan)>0 && !isprime(gcoeff(fan,nbrows(fan),1)))
        continue;

      y2 = idealdivexact(nf,y1,idealadd(nf,y1,I));
      *fa = idealfactor(nf, y2);
      if (data==gen_0 || test(data,y1,*fa)) return y1;
    }
  }
}

/* if data == gen_0, the test is skipped */
/* in the test, the factorization does not contain the known factors */
GEN
factoredextchinesetest(GEN nf, GEN x, GEN y, GEN pl, GEN* fa, GEN data, int (*test)(GEN,GEN,GEN))
{
  pari_sp av = avma;
  long n,i;
  GEN y0, y1, red, N, I, vals;
  n = nf_get_degree(nf);
  y0 = extchinese(nf, x, y, pl, &red);

  vals = shallowcopy(gel(x,2));
  if (!gequal0(y0))
    for (i=1; i<lg(vals); i++) {
      gel(vals,i) = stoi(nfval(nf,y0,gcoeff(x,i,1)));
      if (cmpii(gel(vals,i),gcoeff(x,i,2))>0) gel(vals,i) = gcoeff(x,i,2);
    }
  /* N and I : known factors */
  I = factorbackprime(nf, gel(x,1), vals);
  N = idealnorm(nf,I);

  y1 = backtrackfacto(y0, n, red, pl, nf, data, test, fa, N, I);

  /* restore known factors */
  for (i=1; i<lg(vals); i++) gel(vals,i) = stoi(nfval(nf,y1,gcoeff(x,i,1)));
  *fa = famat_reduce(famat_mul_shallow(*fa, mkmat2(gel(x,1), vals)));

  gerepileall(av, 2, &y1, fa);
  return y1;
}

GEN
factoredextchinese(GEN nf, GEN x, GEN y, GEN pl, GEN* fa)
{ return factoredextchinesetest(nf,x,y,pl,fa,gen_0,NULL); }

/** OPERATIONS ON ASSOCIATIVE ALGEBRAS algebras.c **/

/*
Convention:
(K/F,sigma,b) = sum_{i=0..n-1} u^i*K
t*u = u*sigma(t)

Natural basis:
1<=i<=d*n^2
b_i = u^((i-1)/(dn))*ZKabs.((i-1)%(dn)+1)

Integral basis:
Basis of some order.

al:
1- rnf of the cyclic splitting field of degree n over the center nf of degree d
2- VEC of aut^i 1<=i<=n
3- b in nf
4- infinite hasse invariants (mod n) : VECSMALL of size r1, values only 0 or n/2 (if integral)
5- finite hasse invariants (mod n) : VEC[VEC of primes, VECSMALL of hasse inv mod n]
6- nf of the splitting field (absolute)
7* dn^2*dn^2 matrix expressing the integral basis in terms of the natural basis
8* dn^2*dn^2 matrix expressing the natural basis in terms of the integral basis
9* VEC of dn^2 matrices giving the dn^2*dn^2 left multiplication tables of the integral basis
10* characteristic of the base field (used only for algebras given by a multiplication table)

If al is given by a multiplication table, only the * fields are present.
*/

/*
TODO:
- add a T2 norm : non canonical... just choose one !
- LLL-reduce the integral basis
- more general rnfkummer --> prime powers ?
- al_hasse : try to descent to Q in non-kummer case
- al_hasse : appeler polsubcyclo au lieu de rnfkummer quand possible
- al_hasse : do a rnfpolredbest at every step
- assisted factorization when possible : factorint(famat)
- tests for consistency of input
- optimize b by reducing mod n-powers (when creating al_hasse/can be called independently alred)
- in all transformations (tensor, optimize...), also return the isomorphism (flag:maps)
- allow more general elements in operations : integers, rationals, nf (F), nf
(K), rnf (K).
- effective GW : check whether condition descends to Q as well
- opposite algebra and involution
- optimize basismul using the property that the first element is the identity
- use famat input for bnrinit etc : useful ? only small primes in the conductor, so factorization is fast anyways.
- check naming conventions.
- aldisc: reduced disc for al_CYCLIC and al_CSA
- in alpow, use charpol when better.

Karim :
- maxord: project on central idempotents corresp. to decomposition of p (reduce
size of involved matrices)
- test p-maximality before launching general algorithm
- easy maximal order when pr unramified in L/K
- precompute projectors and LLL-reduced basis in extchinese
*/

/* assumes same center and same variable */
/* currently only works for coprime degrees */
GEN
altensor(GEN al1, GEN al2, int maxord) {
  pari_sp av = avma;
  long v, k, d1, d2;
  GEN nf, P1, P2, aut1, aut2, b1, b2, C, rnf, aut, b, x1, x2, al;

  checkal(al1);
  checkal(al2);
  if (al_type(al1) != al_CYCLIC  || al_type(al2) != al_CYCLIC)
    pari_err_IMPL("tensor of non-cyclic algebras"); /* TODO: do it. */

  nf=al_get_center(al1);
  P1=al_get_splitpol(al1); aut1=al_get_aut(al1); b1=al_get_b(al1);
  P2=al_get_splitpol(al2); aut2=al_get_aut(al2); b2=al_get_b(al2);
  d1=al_get_degree(al1);
  d2=al_get_degree(al2);
  v=varn(P1);

  C = nfcompositum(nf, P1, P2, 3);
  rnf = rnfinit(nf,gel(C,1));
  x1 = gel(C,2);
  x2 = gel(C,3);
  k = itos(gel(C,4));
  aut = gadd(gsubst(aut2,v,x2),gmulsg(k,gsubst(aut1,v,x1)));
  b = nfmul(nf,nfpow_u(nf,b1,d2),nfpow_u(nf,b2,d1));
  al = al_cyclic(rnf,aut,b,maxord);
  return gerepilecopy(av,al);
}

/* M an n x d Flm of rank d, n >= d. Initialize Mx = y solver */
static GEN
Flm_invimage_init(GEN M, ulong p)
{
  GEN v = Flm_indexrank(M, p), perm = gel(v,1);
  GEN MM = rowpermute(M, perm); /* square invertible */
  return mkvec2(Flm_inv(MM,p), perm);
}
/* assume Mx = y has a solution, v = Flm_invimage_init(M,p); return x */
static GEN
Flm_invimage_pre(GEN v, GEN y, ulong p)
{
  GEN inv = gel(v,1), perm = gel(v,2);
  return Flm_Flc_mul(inv, vecsmallpermute(y, perm), p);
}

GEN
alradical(GEN al)
{
  pari_sp av = avma;
  GEN I, x, traces, K, MT, P, mt;
  long l,i,ni, n;
  ulong modu, expo, p;
  checkal(al);
  P = al_get_char(al);
  mt = al_get_multable(al);
  n = al_get_absdim(al);
  traces = altracematrix(al);
  if (!signe(P))
  {
    K = ker(traces);
    ni = lg(K)-1; if (!ni) { avma = av; return gen_0; }
    return gerepileupto(av, K);
  }
  K = FpM_ker(traces, P);
  ni = lg(K)-1; if (!ni) { avma = av; return gen_0; }
  if (cmpiu(P,n)>0) return gerepileupto(av, K);

  /* tough case, p <= n. Ronyai's algorithm */
  p = P[2]; l = 1;
  expo = p; modu = p*p;
  while (modu<=(ulong)n) { l++; modu *= p; }
  MT = ZMV_to_FlmV(mt, modu);
  I = ZM_to_Flm(K,p); /* I_0 */
  for (i=1; i<=l; i++) {/*compute I_i, expo = p^i, modu = p^(l+1) > n*/
    long j, lig,col;
    GEN v = cgetg(ni+1, t_VECSMALL);
    GEN invI = Flm_invimage_init(I, p);
    traces = cgetg(ni+1,t_MAT);
    for (j = 1; j <= ni; j++)
    {
      GEN M = albasismultable_Flm(MT, gel(I,j), modu);
      uel(v,j) = altracei(M, p,expo,modu);
    }
    for (col=1; col<=ni; col++)
    {
      GEN t = cgetg(n+1,t_VECSMALL); gel(traces,col) = t;
      x = gel(I, col); /*col-th basis vector of I_{i-1}*/
      for (lig=1; lig<=n; lig++)
      {
        GEN y = _tablemul_ej_Fl(MT,x,lig,p);
        GEN z = Flm_invimage_pre(invI, y, p);
        uel(t,lig) = Flv_dotproduct(v, z, p);
      }
    }
    K = Flm_ker(traces, p);
    ni = lg(K)-1; if (!ni) { avma = av; return gen_0; }
    I = Flm_mul(I,K,p);
    expo *= p;
  }
  return Flm_to_ZM(I);
}

static GEN
al_quotient0(GEN al, GEN S, GEN Si, long nq, GEN p, int maps)
{
  GEN mt = cgetg(nq+1,t_VEC);
  long i;
  for (i=1; i<=nq; i++)
  {
    GEN mti = almultable(al,gel(S,i));
    if (signe(p)) gel(mt,i) = FpM_mul(Si, FpM_mul(mti,S,p), p);
    else          gel(mt,i) = ZM_mul(Si, ZM_mul(mti,S));
  }
  al = altableinit(mt,p);
  if (maps) al = mkvec3(al,Si,S); /*algebra, proj, lift*/
  return al;
}

/*quotient of an algebra by a nontrivial two-sided ideal*/
GEN
al_quotient(GEN al, GEN I, int maps)
{
  pari_sp av = avma;
  GEN p, IS, ISi, S, Si;
  long n, ni;

  checkal(al);
  p = al_get_char(al);
  n = al_get_absdim(al);
  ni = lg(I)-1;

  /*force first vector of complement to be the identity*/
  IS = shallowconcat(I, gcoeff(al_get_multable(al),1,1));
  if (signe(p)) {
    IS = FpM_suppl(IS,p);
    ISi = FpM_inv(IS,p);
  }
  else {
    IS = suppl(IS);
    ISi = RgM_inv(IS);
  }
  S = vecslice(IS, ni+1, n);
  Si = rowslice(ISi, ni+1, n);
  return gerepilecopy(av, al_quotient0(al, S, Si, n-ni, p, maps));
}

/* z[1],...z[nz] central elements such that z[1]A + z[2]A + ... + z[nz]A = A
 * is a direct sum. idempotents ==> first basis element is identity */
GEN
al_centralproj(GEN al, GEN z, int maps)
{
  pari_sp av = avma;
  GEN S, U, Ui, alq, p;
  long i, iu, lz = lg(z);

  checkal(al);
  if (typ(z) != t_VEC) pari_err_TYPE("alcentralproj",z);
  p = al_get_char(al);
  S = cgetg(lz,t_VEC); /*S[i] = Im(z_i)*/
  for (i=1; i<lz; i++)
  {
    GEN mti = almultable(al, gel(z,i));
    if (signe(p)) gel(S,i) = FpM_image(mti,p);
    else          gel(S,i) = image(mti);
  }
  U = shallowconcat1(S); /*U = [Im(z_1)|Im(z_2)|...|Im(z_nz)], n x n*/
  if (signe(p)) Ui = FpM_inv(U,p);
  else          Ui = RgM_inv(U);
  if (!Ui) pari_err_TYPE("alcentralproj",z);

  alq = cgetg(lz,t_VEC);
  for (iu=0,i=1; i<lz; i++)
  {
    long nq = lg(gel(S,i))-1, ju = iu + nq;
    GEN Si = rowslice(Ui, iu+1, ju);
    gel(alq, i) = al_quotient0(al,gel(S,i),Si,nq,p,maps);
    iu = ju;
  }
  return gerepilecopy(av, alq);
}

GEN
alcenter(GEN al)
{
  pari_sp av = avma;
  long n, i, j, k, ic;
  GEN C, cij, mt, p;
  checkal(al);
  n = al_get_absdim(al);
  mt = al_get_multable(al);
  p = al_get_char(al);
  C = cgetg(n+1,t_MAT);
  for (j=1; j<=n; j++)
  {
    gel(C,j) = cgetg(n*n-n+1,t_COL);
    ic = 1;
    for (i=2; i<=n; i++) {
      if (signe(p)) cij = FpC_sub(gmael(mt,i,j),gmael(mt,j,i),p);
      else          cij = RgC_sub(gmael(mt,i,j),gmael(mt,j,i));
      for (k=1; k<=n; k++, ic++) gcoeff(C,ic,j) = gel(cij, k);
    }
  }
  if (signe(p)) return gerepileupto(av, FpM_ker(C,p));
  else          return gerepileupto(av, ker(C));
}

/* Only in positive characteristic. Assumes that al is semisimple. */
GEN
alprimesubalg(GEN al)
{
  pari_sp av = avma;
  GEN p, Z, F, K;
  long nz, i;
  checkal(al);
  p = al_get_char(al);
  if (!signe(p)) pari_err_DOMAIN("alprimesubalg","characteristic","=",gen_0,p);

  Z = alcenter(al);
  nz = lg(Z)-1;
  if (nz==1) return Z;

  F = cgetg(nz+1, t_MAT);
  for (i=1; i<=nz; i++) {
    GEN zi = gel(Z,i);
    gel(F,i) = FpC_sub(alpow(al,zi,p),zi,p);
  }
  K = FpM_ker(F,p);
  return gerepileupto(av, FpM_mul(Z,K,p));
}


static GEN
_FpX_mul(void* D, GEN x, GEN y) { return FpX_mul(x,y,(GEN)D); }
static GEN
_FpX_pow(void* D, GEN x, GEN n) { return FpX_powu(x,itos(n),(GEN)D); }
static GEN
FpX_factorback(GEN fa, GEN p)
{
  return gen_factorback(gel(fa,1), zv_to_ZV(gel(fa,2)), &_FpX_mul, &_FpX_pow, (void*)p);
}

static GEN
out_decompose(GEN t, GEN Z, GEN P, GEN p)
{
  GEN ali = gel(t,1), projm = gel(t,2), liftm = gel(t,3), pZ;
  if (signe(p)) pZ = FpM_image(FpM_mul(projm,Z,p),p);
  else          pZ = image(RgM_mul(projm,Z));
  return mkvec5(ali, projm, liftm, pZ, P);
}
/* fa factorization of charpol(x) */
static GEN
al_decompose0(GEN al, GEN x, GEN fa, GEN Z, int mini)
{
  long k = lgcols(fa)-1, k2 = mini? 1: k/2;
  GEN v1 = rowslice(fa,1,k2);
  GEN v2 = rowslice(fa,k2+1,k);
  GEN alq, P,Q, mx, p = al_get_char(al);
  if (signe(p)) {
    P = FpX_factorback(v1, p);
    Q = FpX_factorback(v2, p);
    P = FpX_mul(P, FpXQ_inv(P,Q,p), p);
  }
  else {
    P = factorback(v1);
    Q = factorback(v2);
    P = RgX_mul(P, RgXQ_inv(P,Q));
  }
  mx = almultable(al, x);
  P = alpoleval(al, P, mx);
  if (signe(p)) Q = FpC_sub(col_ei(lg(P)-1,1), P, p);
  else          Q = gsub(gen_1, P);
  if(gequal0(P) || gequal0(Q)) return NULL;
  alq = al_centralproj(al, mkvec2(P,Q), 1);

  P = out_decompose(gel(alq,1), Z, P, p); if (mini) return P;
  Q = out_decompose(gel(alq,2), Z, Q, p);
  return mkvec2(P,Q);
}

static GEN
random_pm1(long n)
{
  GEN z = cgetg(n+1,t_VECSMALL);
  long i;
  for (i = 1; i <= n; i++) z[i] = random_bits(5)%3 - 1;
  return z;
}

static GEN al_decompose(GEN al, GEN Z, int mini);
/* Try to split al using x's charpoly. Return gen_0 if simple, NULL if failure.
 * And a splitting otherwise */
static GEN
try_fact(GEN al, GEN x, GEN zx, GEN Z, GEN Zal, long mini)
{
  GEN z, dec0, dec1, cp = alcharpoly(Zal,zx,0), fa, p = al_get_char(al);
  long nfa, e;
  if (signe(p)) fa = FpX_factor(cp,p);
  else          fa = factor(cp);
  nfa = nbrows(fa);
  if (nfa == 1) {
    if (signe(p)) e = gel(fa,2)[1];
    else          e = itos(gcoeff(fa,1,2));
    return e==1 ? gen_0 : NULL;
  }
  dec0 = al_decompose0(al, x, fa, Z, mini);
  if (!dec0) return NULL;
  if (isintzero(dec0)) return gen_0;
  if (!mini) return dec0;
  dec1 = al_decompose(gel(dec0,1), gel(dec0,4), 1);
  z = gel(dec0,5);
  if (!isintzero(dec1)) {
    if (signe(p)) z = FpM_mul(z,dec1,p);
    else          z = RgM_mul(z,dec1);
  }
  return z;
}
static GEN
randcol(long n, GEN b)
{
  GEN N = addiu(shifti(b,1), 1);
  long i;
  GEN res =  cgetg(n+1,t_COL);
  for (i=1; i<=n; i++)
  {
    pari_sp av = avma;
    gel(res,i) = gerepileuptoint(av, subii(randomi(N),b));
  }
  return res;
}
/* Return gen_0 if already simple. mini: only returns a central idempotent
 * corresponding to one simple factor */
static GEN
al_decompose(GEN al, GEN Z, int mini)
{
  pari_sp av;
  GEN Zal, x, zx, rand, dec0, B, p;
  long i, nz = lg(Z)-1;

  if (nz==1) return gen_0;
  av = avma;
  rand = random_pm1(nz);
  zx = zc_to_ZC(rand);
  p = al_get_char(al);
  if (signe(p)) {
    zx = FpC_red(zx,p);
    x = ZM_zc_mul(Z,rand);
    x = FpC_red(x,p);
  }
  else x = RgM_zc_mul(Z,rand);
  Zal = al_subalg(al,Z);
  dec0 = try_fact(al,x,zx,Z,Zal,mini);
  if (dec0) return dec0;
  avma = av;
  for (i=2; i<=nz; i++)
  {
    dec0 = try_fact(al,gel(Z,i),col_ei(nz,i),Z,Zal,mini);
    if (dec0) return dec0;
    avma = av;
  }
  B = int2n(10);
  for(;;)
  {
    GEN x = randcol(nz,B), zx = ZM_ZC_mul(Z,x);
    dec0 = try_fact(al,x,zx,Z,Zal,mini);
    if (dec0) return dec0;
    avma = av;
  }
}

/*TODO guarantee that the images of the liftm form a direct sum*/
static GEN
al_decompose_total(GEN al, GEN Z, int maps)
{
  GEN dec, sc, p;
  long i;

  dec = al_decompose(al, Z, 0);
  if (isintzero(dec))
  {
    if (maps) {
      long n = al_get_absdim(al);
      al = mkvec3(al, matid(n), matid(n));
    }
    return mkvec(al);
  }
  p = al_get_char(al); if (!signe(p)) p = NULL;
  sc = cgetg(lg(dec), t_VEC);
  for (i=1; i<lg(sc); i++) {
    GEN D = gel(dec,i), a = gel(D,1), Za = gel(D,4);
    GEN S = al_decompose_total(a, Za, maps);
    gel(sc,i) = S;
    if (maps)
    {
      GEN projm = gel(D,2), liftm = gel(D,3);
      long j, lS = lg(S);
      for (j=1; j<lS; j++)
      {
        GEN Sj = gel(S,j), p2 = gel(Sj,2), l2 = gel(Sj,3);
        if (p) p2 = FpM_mul(p2, projm, p);
        else   p2 = RgM_mul(p2, projm);
        if (p) l2 = FpM_mul(liftm, l2, p);
        else   l2 = RgM_mul(liftm, l2);
        gel(Sj,2) = p2;
        gel(Sj,3) = l2;
      }
    }
  }
  return shallowconcat1(sc);
}

static GEN
al_subalg(GEN al, GEN basis)
{
  GEN invbasis, mt, p = al_get_char(al);
  long i, j, n = lg(basis)-1;
  if (!signe(p)) p = NULL;
  if (p) { /*TODO change after bugfix?*/
    GEN complbasis = FpM_suppl(basis,p);
    invbasis = rowslice(FpM_inv(complbasis,p),1,n);
  }
  else invbasis = RgM_inv(basis);
  mt = cgetg(n+1,t_VEC);
  gel(mt,1) = matid(n);
  for(i=2; i<=n; i++) {
    GEN mtx = cgetg(n+1,t_MAT), x = gel(basis,i);
    gel(mtx,1) = col_ei(n,i);
    for(j=2; j<=n; j++) {
      GEN xy = almul(al, x, gel(basis,j));
      if (p) gel(mtx,j) = FpM_FpC_mul(invbasis, xy, p);
      else   gel(mtx,j) = RgM_RgC_mul(invbasis, xy);
    }
    gel(mt,i) = mtx;
  }
  return altableinit(mt,p);
}
GEN
alsubalg(GEN al, GEN basis)
{
  pari_sp av = avma;
  GEN p;
  checkal(al);
  if (typ(basis) != t_MAT) pari_err_TYPE("alsubalg",basis);
  p = al_get_char(al);
  if (signe(p)) basis = RgM_to_FpM(basis,p);
  return gerepileupto(av, al_subalg(al,basis));
}

GEN
alsimpledec(GEN al, int maps)
{
  pari_sp av = avma;
  GEN Z, p, res;
  long n;
  checkal(al);
  p = al_get_char(al);
  if (signe(p)) Z = alprimesubalg(al);
  else          Z = alcenter(al);

  if (lg(Z) == 2)/*dim Z = 1*/
  {
    n = al_get_absdim(al);
    avma = av;
    if (!maps) return mkveccopy(al);
    retmkvec(mkvec3(gcopy(al), matid(n), matid(n)));
  }
  res = al_decompose_total(al, Z, maps);
  return gerepilecopy(av, res);
}

GEN
al_decomposition(GEN al)
{
  pari_sp av = avma;
  /*GEN p = al_get_char(al);*/
  GEN rad, alq, dec, res;
  rad = alradical(al);
  alq = gequal0(rad) ? al : al_quotient(al,rad,0);
  dec = alsimpledec(alq,0);
  res = mkvec2(rad, dec); /*TODO si char 0, reconnaitre les centres comme nf et descendre les tables de multiplication*/
  return gerepilecopy(av,res);
}

/* multiplication table sanity checks */
static GEN
check_mt(GEN mt, GEN p)
{
  long i, l;
  GEN MT = cgetg_copy(mt, &l);
  if (typ(MT) != t_VEC || l == 1) return NULL;
  for (i = 1; i < l; i++)
  {
    GEN M = gel(mt,i);
    if (typ(M) != t_MAT || lg(M) != l || lgcols(M) != l) return NULL;
    if (p) M = RgM_to_FpM(M,p);
    if (i > 1 && ZC_is_ei(gel(M,1)) != i) return NULL; /* i = 1 checked at end*/
    gel(MT,i) = M;
  }
  if (!ZM_isidentity(gel(MT,1))) return NULL;
  return MT;
}

long
alisassociative(GEN mt0, GEN p)
{
  pari_sp av = avma;
  long i, j, k, n;
  GEN M, mt;

  if (checkal_i(mt0)) { p = al_get_char(mt0); mt0 = al_get_multable(mt0); }
  if (typ(p) != t_INT) pari_err_TYPE("alisassociative",p);
  mt = check_mt(mt0, isintzero(p)? NULL: p);
  if (!mt) pari_err_TYPE("alisassociative (mult. table)", mt0);
  n = lg(mt)-1;
  M = cgetg(n+1,t_MAT);
  for (j=1; j<=n; j++) gel(M,j) = cgetg(n+1,t_COL);
  for (i=1; i<=n; i++)
  {
    GEN mi = gel(mt,i);
    for (j=1; j<=n; j++) gcoeff(M,i,j) = gel(mi,j); /* ei.ej */
  }
  for (i=2; i<=n; i++) {
    GEN mi = gel(mt,i);
    for (j=2; j<=n; j++) {
      for (k=2; k<=n; k++) {
        GEN x, y;
        if (signe(p)) {
          x = _tablemul_ej_Fp(mt,gcoeff(M,i,j),k,p);
          y = FpM_FpC_mul(mi,gcoeff(M,j,k),p);
        }
        else {
          x = _tablemul_ej(mt,gcoeff(M,i,j),k);
          y = RgM_RgC_mul(mi,gcoeff(M,j,k));
        }
        /* not cmp_universal: mustn't fail on 0 == Mod(0,2) for instance */
        if (!gequal(x,y)) { avma = av; return 0; }
      }
    }
  }
  avma = av; return 1;
}

long
aliscommutative(GEN al) /* assumes e_1 = 1 */
{
  long i,j,k,N,sp;
  GEN mt,a,b,p;
  checkal(al);
  if(al_type(al) != al_TABLE) return al_get_degree(al)==1;
  N = al_get_absdim(al);
  mt = al_get_multable(al);
  p = al_get_char(al);
  sp = signe(p);
  for(i=2; i<=N; i++)
    for(j=2; j<=N; j++)
      for(k=1; k<=N; k++) {
        a = gcoeff(gel(mt,i),k,j);
        b = gcoeff(gel(mt,j),k,i);
        if(sp) {
          if(cmpii(Fp_red(a,p), Fp_red(b,p))) return 0;
        }
        else if(gcmp(a,b)) return 0;
      }
  return 1;
}

long
alissemisimple(GEN al)
{
  pari_sp av = avma;
  GEN rad;
  checkal(al);
  if(al_type(al) != al_TABLE) return 1;
  rad = alradical(al);
  avma = av;
  return gequal0(rad);
}

/** OPERATIONS ON ELEMENTS operations.c **/

long
al_model(GEN al, GEN x)
{
  long D = al_get_absdim(al);
  if (typ(x) != t_COL) pari_err_TYPE("al_model", x);
  if (D==1) return al_TRIVIAL; /* cannot distinguish basis and alg from size */
  if (lg(x)==D+1) return al_BASIS;
  return al_ALGEBRAIC;
}

GEN
aladd(GEN al, GEN x, GEN y)
{
  pari_sp av = avma;
  long tx, ty;
  GEN p;
  checkal(al);
  tx = al_model(al,x);
  ty = al_model(al,y);
  p = al_get_char(al);
  if (signe(p)) return FpC_add(x,y,p);
  if (tx==ty) return gadd(x,y);
  if (tx==al_ALGEBRAIC)       x = alalgtobasis(al,x);
  else if (ty==al_ALGEBRAIC)  y = alalgtobasis(al,y);
  return gerepileupto(av, gadd(x,y));
}

GEN
alneg(GEN al, GEN x) { checkal(al); (void)al_model(al,x); return gneg(x); }

GEN
alsub(GEN al, GEN x, GEN y)
{
  long tx, ty;
  pari_sp av = avma;
  GEN p;
  checkal(al);
  tx = al_model(al,x);
  ty = al_model(al,y);
  p = al_get_char(al);
  if (signe(p)) return FpC_sub(x,y,p);
  if (tx==ty) return gsub(x,y);
  if (tx==al_ALGEBRAIC)       x = alalgtobasis(al,x);
  else if (ty==al_ALGEBRAIC)  y = alalgtobasis(al,y);
  return gerepileupto(av, gsub(x,y));
}

static GEN
alalgmul_cyc(GEN al, GEN x, GEN y)
{
  pari_sp av = avma;
  long n = al_get_degree(al), i, k;
  GEN xalg, yalg, res, rnf, auts, sum, b, prod, autx;
  rnf = al_get_splitting(al);
  auts = al_get_auts(al);
  b = al_get_b(al);

  xalg = cgetg(n+1, t_COL);
  for (i=0; i<n; i++) gel(xalg,i+1) = lift(rnfbasistoalg(rnf,gel(x,i+1)));

  yalg = cgetg(n+1, t_COL);
  for (i=0; i<n; i++) gel(yalg,i+1) = rnfbasistoalg(rnf,gel(y,i+1));

  res = cgetg(n+1,t_COL);
  for (k=0; k<n; k++) {
    gel(res,k+1) = gmul(gel(xalg,k+1),gel(yalg,1));
    for (i=1; i<=k; i++) {
      autx = poleval(gel(xalg,k-i+1),gel(auts,i));
      prod = gmul(autx,gel(yalg,i+1));
      gel(res,k+1) = gadd(gel(res,k+1), prod);
    }

    sum = gen_0;
    for (; i<n; i++) {
      autx = poleval(gel(xalg,k+n-i+1),gel(auts,i));
      prod = gmul(autx,gel(yalg,i+1));
      sum = gadd(sum,prod);
    }
    sum = gmul(b,sum);

    gel(res,k+1) = gadd(gel(res,k+1),sum);
  }

  return gerepilecopy(av, res);
}

static GEN
_tablemul(GEN mt, GEN x, GEN y)
{
  pari_sp av = avma;
  long D = lg(mt)-1, i;
  GEN res = NULL;
  for (i=1; i<=D; i++) {
    GEN c = gel(x,i);
    if (!gequal0(c)) {
      GEN My = RgM_RgC_mul(gel(mt,i),y);
      GEN t = RgC_Rg_mul(My,c);
      res = res? RgC_add(res,t): t;
    }
  }
  if (!res) { avma = av; return zerocol(D); }
  return gerepileupto(av, res);
}

static GEN
_tablemul_Fp(GEN mt, GEN x, GEN y, GEN p)
{
  pari_sp av = avma;
  long D = lg(mt)-1, i;
  GEN res = NULL;
  for (i=1; i<=D; i++) {
    GEN c = gel(x,i);
    if (signe(c)) {
      GEN My = FpM_FpC_mul(gel(mt,i),y,p);
      GEN t = FpC_Fp_mul(My,c,p);
      res = res? FpC_add(res,t,p): t;
    }
  }
  if (!res) { avma = av; return zerocol(D); }
  return gerepileupto(av, res);
}

/* x*ej */
static GEN
_tablemul_ej(GEN mt, GEN x, long j)
{
  pari_sp av = avma;
  long D = lg(mt)-1, i;
  GEN res = NULL;
  for (i=1; i<=D; i++) {
    GEN c = gel(x,i);
    if (!gequal0(c)) {
      GEN My = gel(gel(mt,i),j);
      GEN t = RgC_Rg_mul(My,c);
      res = res? RgC_add(res,t): t;
    }
  }
  if (!res) { avma = av; return zerocol(D); }
  return gerepileupto(av, res);
}
static GEN
_tablemul_ej_Fp(GEN mt, GEN x, long j, GEN p)
{
  pari_sp av = avma;
  long D = lg(mt)-1, i;
  GEN res = NULL;
  for (i=1; i<=D; i++) {
    GEN c = gel(x,i);
    if (!gequal0(c)) {
      GEN My = gel(gel(mt,i),j);
      GEN t = FpC_Fp_mul(My,c,p);
      res = res? FpC_add(res,t,p): t;
    }
  }
  if (!res) { avma = av; return zerocol(D); }
  return gerepileupto(av, res);
}
GEN
albasismul_ej(GEN al, GEN x, long j)
{ return _tablemul_ej(al_get_multable(al), x, j); }
static GEN
_tablemul_ej_Fl(GEN mt, GEN x, long j, ulong p)
{
  pari_sp av = avma;
  long D = lg(mt)-1, i;
  GEN res = NULL;
  for (i=1; i<=D; i++) {
    ulong c = x[i];
    if (c) {
      GEN My = gel(gel(mt,i),j);
      GEN t = Flc_Fl_mul(My,c, p);
      res = res? Flv_add(res,t, p): t;
    }
  }
  if (!res) { avma = av; return zero_Flv(D); }
  return gerepileupto(av, res);
}

static GEN
alalgmul_csa(GEN al, GEN x, GEN y)
{ return _tablemul(al_get_relmultable(al), x, y); }

GEN
alalgmul(GEN al, GEN x, GEN y)
{
  switch(al_type(al))
  {
    case al_CYCLIC: return alalgmul_cyc(al, x, y);
    case al_CSA: return alalgmul_csa(al, x, y);
    default:
      pari_err_DOMAIN("alalgmul", "al_type(al)", "=", stoi(al_type(al)), stoi(al_type(al)));
  }
  return NULL; /*not reached*/
}

GEN
albasismul(GEN al, GEN x, GEN y)
{
  GEN mt = al_get_multable(al), p = al_get_char(al);
  if (signe(p)) return _tablemul_Fp(mt, x, y, p);
  return _tablemul(mt, x, y);
}

GEN
almul(GEN al, GEN x, GEN y)
{
  pari_sp av = avma;
  long tx, ty;
  checkal(al);
  tx = al_model(al,x);
  ty = al_model(al,y);
  if (signe(al_get_char(al))) return albasismul(al,x,y);
  if (tx==al_TRIVIAL) return gerepilecopy(av,mkcol(gmul(gel(x,1),gel(y,1))));
  if (tx==al_ALGEBRAIC && ty==al_ALGEBRAIC) return alalgmul(al,x,y);
  if (tx==al_ALGEBRAIC) x = alalgtobasis(al,x);
  if (ty==al_ALGEBRAIC) y = alalgtobasis(al,y);
  return gerepileupto(av,albasismul(al,x,y));
}

GEN
alsqr(GEN al, GEN x)
{
  pari_sp av = avma;
  long tx;
  checkal(al);
  tx = al_model(al,x);
  if (signe(al_get_char(al))) return albasismul(al,x,x);
  if (tx==al_TRIVIAL) return gerepilecopy(av,mkcol(gsqr(gel(x,1))));
  if (tx==al_ALGEBRAIC) return alalgmul(al,x,x);
  return gerepileupto(av,albasismul(al,x,x));
}

static GEN
almtK2Z_cyc(GEN al, GEN m)
{
  pari_sp av = avma;
  GEN nf = al_get_abssplitting(al), res, mt, rnf = al_get_splitting(al), c, dc;
  long n = al_get_degree(al), N = nf_get_degree(nf), Nn, i, j, i1, j1;
  Nn = N*n;
  res = zeromatcopy(Nn,Nn);
  for (i=0; i<n; i++)
  for (j=0; j<n; j++) {
    c = gcoeff(m,i+1,j+1);
    if (!gequal0(c)) {
      c = rnfeltreltoabs(rnf,c);
      c = algtobasis(nf,c);
      c = Q_remove_denom(c,&dc);
      mt = zk_multable(nf,c);
      if (dc) mt = ZM_Z_div(mt,dc);
      for (i1=1; i1<=N; i1++)
      for (j1=1; j1<=N; j1++)
        gcoeff(res,i*N+i1,j*N+j1) = gcoeff(mt,i1,j1);
    }
  }
  return gerepilecopy(av,res);
}

static GEN
almtK2Z_csa(GEN al, GEN m)
{
  pari_sp av = avma;
  GEN nf = al_get_center(al), res, mt, c, dc;
  long d2 = al_get_dim(al), n = nf_get_degree(nf), D, i, j, i1, j1;
  D = d2*n;
  res = zeromatcopy(D,D);
  for (i=0; i<d2; i++)
  for (j=0; j<d2; j++) {
    c = gcoeff(m,i+1,j+1);
    if (!gequal0(c)) {
      c = algtobasis(nf,c);
      c = Q_remove_denom(c,&dc);
      mt = zk_multable(nf,c);
      if (dc) mt = ZM_Z_div(mt,dc);
      for (i1=1; i1<=n; i1++)
      for (j1=1; j1<=n; j1++)
        gcoeff(res,i*n+i1,j*n+j1) = gcoeff(mt,i1,j1);
    }
  }
  return gerepilecopy(av,res);
}

static GEN
almtK2Z(GEN al, GEN m)
{
  switch(al_type(al))
  {
    case al_CYCLIC: return almtK2Z_cyc(al, m);
    case al_CSA: return almtK2Z_csa(al, m);
    default:
      pari_err_DOMAIN("almtK2Z", "al_type(al)", "=", stoi(al_type(al)), stoi(al_type(al)));
  }
  return NULL; /*not reached*/
}

/* remove? */
#if 0
static GEN
almtZ2K_cyc(GEN al, GEN m)
{
  pari_sp av = avma;
  GEN nf = al_get_abssplitting(al), rnf = al_get_splitting(al), res, c;
  long n = al_get_degree(al), N = nf_get_degree(nf), i, j, i1;
  res = zeromatcopy(n,n);
  c = cgetg(N+1, t_COL);
  for (i=0; i<n; i++)
  for (j=0; j<n; j++) {
    for (i1=1; i1<=N; i1++) gel(c,i1) = gcoeff(m,i*N+i1,j*N+1);
    gcoeff(res,i+1,j+1) = rnfeltabstorel(rnf,basistoalg(nf,c));
  }
  return gerepilecopy(av,res);
}
#endif

/* left multiplication table, as a vector space of dimension n over the splitting field (by right multiplication) */
static GEN
alalgmultable_cyc(GEN al, GEN x)
{
  pari_sp av = avma;
  long n = al_get_degree(al), i, j;
  GEN res, rnf, auts, b, pol;
  rnf = al_get_splitting(al);
  auts = al_get_auts(al);
  b = al_get_b(al);
  pol = rnf_get_pol(rnf);

  res = zeromatcopy(n,n);
  for (i=0; i<n; i++)
    gcoeff(res,i+1,1) = lift(rnfbasistoalg(rnf,gel(x,i+1)));

  for (i=0; i<n; i++) {
    for (j=1; j<=i; j++)
      gcoeff(res,i+1,j+1) = gmodulo(poleval(gcoeff(res,i-j+1,1),gel(auts,j)),pol);
    for (; j<n; j++)
      gcoeff(res,i+1,j+1) = gmodulo(gmul(b,poleval(gcoeff(res,n+i-j+1,1),gel(auts,j))), pol);
  }

  for (i=0; i<n; i++)
    gcoeff(res,i+1,1) = gmodulo(gcoeff(res,i+1,1),pol);

  return gerepilecopy(av, res);
}

static GEN
elementmultable(GEN mt, GEN x)
{
  pari_sp av = avma;
  long D = lg(mt)-1, i;
  GEN res, c;
  res = zeromatcopy(D,D);
  for (i=1; i<=D; i++) {
    c = gel(x,i);
    if (!gequal0(c)) res = RgM_add(res, RgM_Rg_mul(gel(mt,i),c));
  }
  return gerepileupto(av, res);
}

static GEN
elementabsmultable(GEN mt, GEN x)
{
  pari_sp av = avma;
  long D = lg(mt)-1, i;
  GEN res, c, d=NULL;
  res = zeromatcopy(D,D);
  x = Q_remove_denom(x, &d);
  for (i=1; i<=D; i++) {
    c = gel(x,i);
    if (!gequal0(c)) res = ZM_add(res, ZM_Z_mul(gel(mt,i),c));
  }
  if (d) res = ZM_Z_div(res, d);
  return gerepileupto(av, res);
}

static GEN
elementabsmultable_Fp(GEN mt, GEN x, GEN p)
{
  pari_sp av = avma;
  long D = lg(mt)-1, i;
  GEN res, c;
  res = zeromatcopy(D,D);
  for (i=1; i<=D; i++) {
    c = gel(x,i);
    if (!gequal0(c)) res = FpM_add(res, FpM_Fp_mul(gel(mt,i),c,p), p);
  }
  return gerepileupto(av, res);
}

static GEN
alalgmultable_csa(GEN al, GEN x)
{
  return elementmultable(al_get_relmultable(al), x);
}

GEN
alalgmultable(GEN al, GEN x)
{
  switch(al_type(al))
  {
    case al_CYCLIC: return alalgmultable_cyc(al, x);
    case al_CSA: return alalgmultable_csa(al, x);
    default:
      pari_err_DOMAIN("alalgmultable", "al_type(al)", "=", stoi(al_type(al)), stoi(al_type(al)));
  }
  return NULL; /*not reached*/
}

/*on the natural basis*/
static GEN
alZmultable(GEN al, GEN x) {
  pari_sp av = avma;
  GEN res, x0;
  long tx = al_model(al,x);
  switch(tx) {
    case al_TRIVIAL:
      x0 = gel(x,1);
      if(typ(x0)==t_POLMOD) x0 = gel(x0,2);
      if(typ(x0)==t_POL) x0 = constant_term(x0);
      res = mkmatcopy(mkcol(x0));
      break;
    case al_ALGEBRAIC: res = almtK2Z(al,alalgmultable(al,x)); break;
    default: res = albasismultable(al,x);
  }
  return gerepileupto(av,res);
}

static GEN
albasisrightmultable(GEN al, GEN x)
{
  long N = al_get_absdim(al), i,j,k;
  GEN res = zeromatcopy(N,N), c, mt = al_get_multable(al);
  for(i=1; i<=N; i++) {
    c = gel(x,i);
    if (!gequal0(c)) {
      for(j=1; j<=N; j++)
      for(k=1; k<=N; k++)
        gcoeff(res,k,j) = addii(gcoeff(res,k,j), mulii(c, gcoeff(gel(mt,j),k,i)));
    }
  }
  return res;
}

GEN
albasismultable(GEN al, GEN x)
{
  GEN p = al_get_char(al);
  if (signe(p)) return elementabsmultable_Fp(al_get_multable(al), x, p);
  return elementabsmultable(al_get_multable(al), x);
}
/* mt a t_VEC of Flm modulo m */
GEN
albasismultable_Flm(GEN mt, GEN x, ulong m)
{
  pari_sp av = avma;
  long D = lg(gel(mt,1))-1, i;
  GEN res = NULL;
  for (i=1; i<=D; i++) {
    ulong c = x[i];
    GEN M = Flm_Fl_mul(gel(mt,i),c, m);
    if (c) res = res? Flm_add(res, M, m): M;
  }
  if (!res) { avma = av; return zero_Flm(D,D); }
  return gerepileupto(av, res);
}

/* left multiplication table on elements of the same model as x */
GEN
almultable(GEN al, GEN x)
{
  pari_sp av = avma;
  long tx;
  GEN res;
  checkal(al);
  tx = al_model(al,x);
  switch(tx) {
    case al_TRIVIAL : res = mkmatcopy(mkcol(gel(x,1))); break;
    case al_ALGEBRAIC : res = alalgmultable(al,x); break;
    case al_BASIS : res = albasismultable(al,x); break;
    default : return NULL;
  }
  return gerepileupto(av,res);
}

static GEN
albasissplittingmatrix_csa(GEN al, GEN x)
{
  long d = al_get_degree(al), i, j;
  GEN rnf = al_get_splitting(al), splba = al_get_splittingbasis(al), splbainv = al_get_splittingbasisinv(al), M;
  M = albasismultable(al,x);
  M = RgM_mul(M, splba); /* TODO best order ? big matrix /Q vs small matrix /nf */
  M = RgM_mul(splbainv, M);
  for(i=1; i<=d; i++)
  for(j=1; j<=d; j++)
    gcoeff(M,i,j) = rnfeltabstorel(rnf, gcoeff(M,i,j));
  return M;
}

GEN
alsplittingmatrix(GEN al, GEN x)
{
  pari_sp av = avma;
  GEN res = NULL;
  long tx;
  checkal(al);
  tx = al_model(al,x);
  switch(al_type(al))
  {
    case al_CYCLIC:
      if (tx==al_BASIS) x = albasistoalg(al,x);
      res = alalgmultable(al,x);
      break;
    case al_CSA:
      if (tx==al_ALGEBRAIC) x = alalgtobasis(al,x);
      res = albasissplittingmatrix_csa(al,x);
      break;
    default:
      pari_err_DOMAIN("alsplittingmatrix", "al_type(al)", "=", stoi(al_type(al)), stoi(al_type(al)));
  }
  return gerepilecopy(av,res);
}

/*  x^(-1)*y, NULL if no solution */
static GEN
aldivl_i(GEN al, GEN x, GEN y) {
  pari_sp av = avma;
  long tx = al_model(al,x), ty = al_model(al,y);
  GEN res, p = al_get_char(al);
  if (tx != ty) {
    if (tx==al_ALGEBRAIC) x = alalgtobasis(al,x);
    if (ty==al_ALGEBRAIC) y = alalgtobasis(al,y);
  }
  if (signe(p)) res = FpM_FpC_invimage(almultable(al,x),y,p);
  else          res = inverseimage(almultable(al,x),y);
  if (!res || lg(res)==1) { avma = av; return NULL; }
  return gerepileupto(av,res);
}
GEN
aldivl(GEN al, GEN x, GEN y)
{
  GEN z;
  checkal(al); z = aldivl_i(al,x,y);
  if (!z) pari_err_INV("aldivl", x);
  return z;
}

static GEN
alinv_i(GEN al, GEN x)
{
  pari_sp av = avma;
  GEN res = NULL, p = al_get_char(al);
  long tx = al_model(al,x), n;
  switch(tx) {
    case al_TRIVIAL :
      if (signe(p)) { res = mkcol(Fp_inv(gel(x,1),p)); break; }
      else          { res = mkcol(ginv(gel(x,1))); break; }
    case al_ALGEBRAIC :
      switch(al_type(al)) {
        case al_CYCLIC: n = al_get_degree(al); break;
        case al_CSA: n = al_get_dim(al); break;
        default: pari_err_TYPE("alinv_i", al); return NULL;
      }
      res = aldivl_i(al, x, scalarcol_shallow(gen_1, n)); break;
    case al_BASIS : res = aldivl_i(al, x, scalarcol_shallow(gen_1, al_get_absdim(al))); break;
  }
  if (!res) { avma = av; return NULL; }
  return gerepilecopy(av,res);
}
GEN
alinv(GEN al, GEN x)
{
  GEN z;
  checkal(al);
  z = alinv_i(al,x);
  if (!z) pari_err_INV("alinv", x);
  return z;
}

int
alisinv(GEN al, GEN x, GEN* ptix)
{
  pari_sp av = avma;
  GEN ix = alinv_i(al,x);
  if (!ix) { avma = av; return 0; }
  *ptix = ix; return 1;
}

/*  x*y^(-1)  */
GEN
aldivr(GEN al, GEN x, GEN y) { return almul(al, x, alinv(al, y)); }

static GEN _mul(void* data, GEN x, GEN y) { return almul((GEN)data,x,y); }
static GEN _sqr(void* data, GEN x) { return alsqr((GEN)data,x); }

GEN
alpow(GEN al, GEN x, GEN n)
{
  pari_sp av = avma;
  GEN res;
  checkal(al);
  switch(signe(n)) {
    case 0 :         res = scalarcol_shallow(gen_1,al_get_absdim(al)); break;
    case 1 :         res = gen_pow(x, n, (void*)al, _sqr, _mul); break;
    default : /*-1*/ res = gen_pow(alinv(al,x), gneg(n), (void*)al, _sqr, _mul);
  }
  return gerepileupto(av,res);
}

static GEN
alredcharpoly_i(GEN al, GEN x, long v)
{
  GEN rnf = al_get_splitting(al);
  GEN cp = charpoly(alsplittingmatrix(al,x),v);
  long i, m = lg(cp);
  for (i=2; i<m; i++) gel(cp,i) = rnfeltdown(rnf, gel(cp,i));
  return cp;
}

static GEN
alredcharpoly(GEN al, GEN x, long v)
{
  pari_sp av = avma;
  switch(al_type(al))
  {
    case al_CYCLIC:
    case al_CSA:
      return gerepileupto(av, alredcharpoly_i(al, x, v));
    default:
      pari_err_DOMAIN("alredcharpoly", "al_type(al)", "=", stoi(al_type(al)), stoi(al_type(al)));
  }
  return NULL; /*not reached*/
}

GEN
albasischarpoly(GEN al, GEN x, long v)
{
  pari_sp av = avma;
  GEN p = al_get_char(al);
  if (signe(p)) {
    GEN res = FpM_charpoly(albasismultable(al,x),p);
    setvarn(res,v);
    return gerepileupto(av, res);
  }
  return gerepileupto(av, charpoly(albasismultable(al,x),v));
}

GEN
alcharpoly(GEN al, GEN x, long v)
{
  checkal(al);
  if (v<0) v=0;

  /* gneg(x[1]) left on stack */
  if (al_model(al,x) == al_TRIVIAL) {
    GEN p = al_get_char(al);
    if (signe(p)) return deg1pol(gen_1,Fp_neg(gel(x,1),p),v);
    return deg1pol(gen_1,gneg(gel(x,1)),v);
  }

  switch(al_type(al)) {
    case al_CYCLIC: case al_CSA: return alredcharpoly(al,x,v);
    case al_TABLE: return albasischarpoly(al,x,v);
    default : return NULL; /* not reached */
  }
}

static GEN
alabstrace(GEN al, GEN x)
{
  pari_sp av = avma;
  GEN res = NULL, p = al_get_char(al);
  if (signe(p)) return FpV_dotproduct(x, al_get_tracebasis(al), p);
  switch(al_model(al,x)) {
    case al_TRIVIAL: return gcopy(gel(x,1)); break;
    case al_BASIS: res = RgV_dotproduct(x, al_get_tracebasis(al)); break;
    case al_ALGEBRAIC:
      switch(al_type(al))
      {
        case al_CYCLIC:
        case al_CSA:
          return alabstrace(al, alalgtobasis(al,x));
        default: return NULL;
      }
  }
  return gerepileupto(av,res);
}

static GEN
alredtrace(GEN al, GEN x)
{
  pari_sp av = avma;
  GEN res = NULL;
  switch(al_model(al,x)) {
    case al_TRIVIAL: return gcopy(gel(x,1)); break;
    case al_BASIS: return alredtrace(al, albasistoalg(al,x)); /* TODO precompute too? */
    case al_ALGEBRAIC:
      switch(al_type(al))
      {
        case al_CYCLIC:
          res = rnfelttrace(al_get_splitting(al),gel(x,1));
          break;
        case al_CSA:
          res = gtrace(alalgmultable_csa(al,x));
          res = gdiv(res, stoi(al_get_degree(al)));
          break;
        default: return NULL;
      }
  }
  return gerepileupto(av,res);
}

GEN
altrace(GEN al, GEN x)
{
  checkal(al);
  switch(al_type(al)) {
    case al_CYCLIC: case al_CSA: return alredtrace(al,x);
    case al_TABLE: return alabstrace(al,x);
    default : return NULL;
  }
}

static GEN
ZM_trace(GEN x)
{
  long i, lx = lg(x);
  GEN t;
  if (lx < 3) return lx == 1? gen_0: gcopy(gcoeff(x,1,1));
  t = gcoeff(x,1,1);
  for (i = 2; i < lx; i++) t = addii(t, gcoeff(x,i,i));
  return t;
}
static GEN
FpM_trace(GEN x, GEN p)
{
  long i, lx = lg(x);
  GEN t;
  if (lx < 3) return lx == 1? gen_0: gcopy(gcoeff(x,1,1));
  t = gcoeff(x,1,1);
  for (i = 2; i < lx; i++) t = Fp_add(t, gcoeff(x,i,i), p);
  return t;
}

static GEN
altracebasis(GEN al)
{
  pari_sp av = avma;
  GEN mt = al_get_multable(al), p = al_get_char(al);
  long i, l = lg(mt);
  GEN v = cgetg(l, t_VEC);
  if (signe(p)) for (i=1; i < l; i++) gel(v,i) = FpM_trace(gel(mt,i), p);
  else          for (i=1; i < l; i++) gel(v,i) = ZM_trace(gel(mt,i));
  return gerepileupto(av,v);
}

/* Assume: i > 0, expo := p^i <= absdim, x contained in I_{i-1} given by mult
 * table modulo modu=p^(i+1). Return Tr(x^(p^i)) mod modu */
static ulong
altracei(GEN mt, ulong p, ulong expo, ulong modu)
{
  pari_sp av = avma;
  long j, l = lg(mt);
  ulong tr = 0;
  mt = Flm_powu(mt,expo,modu);
  for (j=1; j<l; j++) tr += ucoeff(mt,j,j);
  avma = av; return (tr/expo) % p;
}

GEN
alnorm(GEN al, GEN x)
{
  pari_sp av = avma;
  GEN p, rnf, res;
  checkal(al);
  p = al_get_char(al);
  if (signe(p)) return gerepileupto(av, FpM_det(albasismultable(al,x),p));
  if (al_model(al,x) == al_TRIVIAL) return gcopy(gel(x,1));

  switch(al_type(al)) {
    case al_CYCLIC: case al_CSA:
      rnf = al_get_splitting(al);
      res = rnfeltdown(rnf, det(alsplittingmatrix(al,x)));
      break;
    case al_TABLE:
      res = det(albasismultable(al,x));
      break;
    default: return NULL; /* not reached */
  }
  return gerepileupto(av, res);
}

static GEN
alalgtonat_cyc(GEN al, GEN x)
{
  pari_sp av = avma;
  GEN nf = al_get_abssplitting(al), rnf = al_get_splitting(al), res, c;
  long n = al_get_degree(al), N = nf_get_degree(nf), i, i1;
  res = zerocol(N*n);
  for (i=0; i<n; i++) {
    c = gel(x,i+1);
    c = rnfeltreltoabs(rnf,c);
    if (!gequal0(c)) {
      c = algtobasis(nf,c);
      for (i1=1; i1<=N; i1++) gel(res,i*N+i1) = gel(c,i1);
    }
  }
  return gerepilecopy(av, res);
}

static GEN
alalgtonat_csa(GEN al, GEN x)
{
  pari_sp av = avma;
  GEN nf = al_get_center(al), res, c;
  long d2 = al_get_dim(al), n = nf_get_degree(nf), i, i1;
  res = zerocol(d2*n);
  for (i=0; i<d2; i++) {
    c = gel(x,i+1);
    if (!gequal0(c)) {
      c = algtobasis(nf,c);
      for (i1=1; i1<=n; i1++) gel(res,i*n+i1) = gel(c,i1);
    }
  }
  return gerepilecopy(av, res);
}

GEN
alalgtonat(GEN al, GEN x)
{
  switch(al_type(al))
  {
    case al_CYCLIC: return alalgtonat_cyc(al, x);
    case al_CSA: return alalgtonat_csa(al, x);
    default:
      pari_err_DOMAIN("alalgtonat", "al_type(al)", "=", stoi(al_type(al)), stoi(al_type(al)));
  }
  return NULL; /*not reached*/
}

static GEN
alnattoalg_cyc(GEN al, GEN x)
{
  pari_sp av = avma;
  GEN nf = al_get_abssplitting(al), rnf = al_get_splitting(al), res, c;
  long n = al_get_degree(al), N = nf_get_degree(nf), i, i1;
  res = zerocol(n);
  c = zerocol(N);
  for (i=0; i<n; i++) {
    for (i1=1; i1<=N; i1++) gel(c,i1) = gel(x,i*N+i1);
    gel(res,i+1) = rnfeltabstorel(rnf,basistoalg(nf,c));
  }
  return gerepilecopy(av, res);
}

static GEN
alnattoalg_csa(GEN al, GEN x)
{
  pari_sp av = avma;
  GEN nf = al_get_center(al), res, c;
  long d2 = al_get_dim(al), n = nf_get_degree(nf), i, i1;
  res = zerocol(d2);
  c = zerocol(n);
  for (i=0; i<d2; i++) {
    for (i1=1; i1<=n; i1++) gel(c,i1) = gel(x,i*n+i1);
    gel(res,i+1) = basistoalg(nf,c);
  }
  return gerepilecopy(av, res);
}

GEN
alnattoalg(GEN al, GEN x)
{
  switch(al_type(al))
  {
    case al_CYCLIC: return alnattoalg_cyc(al, x);
    case al_CSA: return alnattoalg_csa(al, x);
    default:
      pari_err_DOMAIN("alnattoalg", "al_type(al)", "=", stoi(al_type(al)), stoi(al_type(al)));
  }
  return NULL; /*not reached*/
}

GEN
alalgtobasis(GEN al, GEN x)
{
  pari_sp av;
  checkal(al);
  if (al_model(al,x)==al_BASIS) return gcopy(x);
  av = avma;
  x = alalgtonat(al,x);
  x = RgM_RgC_mul(al_get_invord(al),x);
  return gerepileupto(av, x);
}

GEN
albasistoalg(GEN al, GEN x)
{
  pari_sp av;
  checkal(al);
  if (al_model(al,x)==al_ALGEBRAIC) return gcopy(x);
  av = avma;
  x = RgM_RgC_mul(al_get_ord(al),x);
  x = alnattoalg(al,x);
  return gerepileupto(av, x);
}

GEN
alrandom(GEN al, GEN b)
{
  GEN res, p, N;
  long i, n;
  if (typ(b) != t_INT) pari_err_TYPE("alrandom",b);
  checkal(al);
  n = al_get_absdim(al);
  N = addiu(shifti(b,1), 1); /* left on stack */
  p = al_get_char(al);
  res = cgetg(n+1,t_COL);
  for (i=1; i<= n; i++)
  {
    pari_sp av = avma;
    gel(res,i) = gerepileuptoint(av, subii(randomi(N),b));
  }
  if (signe(p)) res = FpC_red(res, p); /*FIXME: need garbage collection here?*/
  return res;
}

/*Assumes pol has coefficients in the same ring as the COL x; x either
 * in basis or mult. table form. TODO more general version*/
GEN
alpoleval(GEN al, GEN pol, GEN x)
{
  pari_sp av = avma;
  GEN p, mx, res;
  long i;
  checkal(al);
  p = al_get_char(al);
  if (typ(pol) != t_POL) pari_err_TYPE("alpoleval",pol);
  mx = (typ(x) == t_MAT)? x: almultable(al,x);
  res = zerocol(lg(mx)-1);
  if (signe(p)) {
    for (i=lg(pol)-1; i>1; i--)
    {
      gel(res,1) = Fp_add(gel(res,1), gel(pol,i), p);
      if (i>2) res = FpM_FpC_mul(mx, res, p);
    }
  }
  else {
    for (i=lg(pol)-1; i>1; i--)
    {
      gel(res,1) = gadd(gel(res,1), gel(pol,i));
      if (i>2) res = RgM_RgC_mul(mx, res);
    }
  }
  return gerepileupto(av, res);
}

/** GRUNWALD-WANG **/
/*
These de Song Wang (pages des pdf)
p.25 def de chi_b. K^Ker(chi_b) = K(b^(1/m))
p.26 borne sur le conducteur (also Cohen adv. p.166)
p.21 & p.34 description special case, also on wikipedia:
http://en.wikipedia.org/wiki/Grunwald%E2%80%93Wang_theorem#Special_fields
p.77 Kummer case
*/

/* n > 0. Is n = 2^k ? */
static int
uispow2(ulong n) { return !(n &(n-1)); }

static GEN
get_phi0(GEN bnr, GEN Lpr, GEN Ld, GEN pl, long *pr, long *pn)
{
  const long NTRY = 10; /* FIXME: magic constant */
  const long n = (lg(Ld)==1)? 2: vecsmall_max(Ld);
  GEN S = bnr_get_cyc(bnr);
  GEN Sst, G, globGmod, loc, X, Rglob, Rloc, H, U, real;
  long i, j, r, nbreal=0, nbfrob, nbloc, nz, t;

  *pn = n;
  *pr = r = lg(S)-1;
  if (!r) return NULL;
  real = new_chunk(lg(pl)-1);
  if (uispow2(n))
    for (i=1; i<lg(pl); i++)
      if (pl[i]==-1) real[nbreal++] = i;
  nbfrob = lg(Lpr)-1;
  nbloc = nbfrob+nbreal;

  /* compute Z/n-dual */
  Sst = cgetg(r+1, t_VECSMALL);
  for (i=1; i<=r; i++) Sst[i] = ugcd(umodiu(gel(S,i), n), n);
  if (Sst[1] != n) return NULL;

  globGmod = cgetg(r+1,t_MAT);
  G = cgetg(r+1,t_VECSMALL);
  for (i=1; i<=r; i++)
  {
    G[i] = n / Sst[i]; /* pairing between S and Sst */
    gel(globGmod,i) = cgetg(nbloc+1,t_VECSMALL);
  }

  /* compute images of Frobenius elements (and complex conjugation) */
  loc = cgetg(nbloc+1,t_VECSMALL);
  for (i=1; i<=nbloc; i++) {
    long L;
    if (i<=nbfrob)
    {
      X = isprincipalray(bnr,gel(Lpr,i));
      L = Ld[i];
    }
    else
    {
      X = bnrconj(bnr,real[i-nbfrob-1]);
      L = 2;
    }
    X = ZV_to_Flv(X, n);
    for (nz=0,j=1; j<=r; j++)
    {
      ulong c = (X[j] * G[j]) % L;
      ucoeff(globGmod,i,j) = c;
      if (c) nz = 1;
    }
    if (!nz) return NULL;
    loc[i] = L;
  }

  /* try some random elements in the dual */
  Rglob = cgetg(r+1,t_VECSMALL);
  for (t=0; t<NTRY; t++) {
    for (j=1; j<=r; j++) Rglob[j] = random_Fl(Sst[j]);
    Rloc = zm_zc_mul(globGmod,Rglob);
    for (i=1; i<=nbloc; i++)
      if (Rloc[i] % loc[i] == 0) break;
    if (i > nbloc)
      return zv_to_ZV(Rglob);
  }

  /* try to realize some random elements of the product of the local duals */
  H = ZM_hnfall(shallowconcat(zm_to_ZM(globGmod),
                              diagonal_shallow(zv_to_ZV(loc))), &U, 2);
  /* H,U nbloc x nbloc */
  Rloc = cgetg(nbloc+1,t_COL);
  for (t=0; t<NTRY; t++) {
    /* nonzero random coordinate */ /*TODO add special case ?*/
    for (i=1; i<=nbloc; i++) gel(Rloc,i) = stoi(1 + random_Fl(loc[i]-1));
    Rglob = hnf_invimage(H, Rloc);
    if (Rglob)
    {
      Rglob = ZM_ZC_mul(U,Rglob);
      return vecslice(Rglob,1,r);
    }
  }
  return NULL;
}

GEN
bnrgwsearch(GEN bnr, GEN Lpr, GEN Ld, GEN pl)
{
  pari_sp av = avma;
  long n, r;
  GEN phi0 = get_phi0(bnr,Lpr,Ld,pl, &r,&n), gn, v, H,U;
  if (!phi0) { avma = av; return gen_0; }
  gn = stoi(n);
  /* compute kernel of phi0 */
  v = ZV_extgcd(shallowconcat(phi0, gn));
  U = vecslice(gel(v,2), 1,r);
  H = ZM_hnfmodid(rowslice(U, 1,r), gn);
  return gerepileupto(av, H);
}

GEN
bnfgwgeneric(GEN bnf, GEN Lpr, GEN Ld, GEN pl, long var)
{
  pari_sp av = avma;
  const long n = (lg(Ld)==1)? 2: vecsmall_max(Ld);
  forprime_t S;
  GEN bnr = NULL, ideal = gen_1, nf, dec, H = gen_0, finf, pol;
  ulong ell, p;
  long deg, i, degell;
  (void)uisprimepower(n, &ell);
  nf = bnf_get_nf(bnf);
  deg = nf_get_degree(nf);
  degell = cgcd(deg,ell-1);
  finf = cgetg(lg(pl),t_VEC);
  for (i=1; i<lg(pl); i++) gel(finf,i) = pl[i]==-1 ? gen_1 : gen_0;

  u_forprime_init(&S, 2, ULONG_MAX);
  while ((p = u_forprime_next(&S))) {
    if (Fl_powu(p % ell, degell, ell) != 1) continue; /* ell | p^deg-1 ? */
    dec = idealprimedec(nf, utoipos(p));
    for (i=1; i<lg(dec); i++) {
      GEN pp = gel(dec,i);
      if (RgV_isin(Lpr,pp)) continue; /*TODO accepter aussi les ideaux premiers auxquels on pose une condition (utiliser Artin local) ?*/
      if (smodis(idealnorm(nf,pp),ell) != 1) continue; /* ell | N(pp)-1 ? */
      ideal = idealmul(bnf,ideal,pp);
      /* TODO: give factorization ?*/
      bnr = Buchray(bnf, mkvec2(ideal,finf), nf_GEN|nf_INIT);
      H = bnrgwsearch(bnr,Lpr,Ld,pl);
      if (H != gen_0)
      {
        pol = rnfkummer(bnr,H,0,nf_get_prec(nf));
        setvarn(pol, var);
        return gerepileupto(av,pol);
      }
    }
  }
  pari_err_BUG("bnfgwgeneric (no suitable p)");
  return NULL;/*not reached*/
}

GEN
bnrconj(GEN bnr, long i)
{
  pari_sp av = avma;
  GEN x,y, nf = bnr_get_nf(bnr), I = gel(bnr_get_bid(bnr),3), pl, red;
  long r1 = nf_get_r1(nf), n = nbrows(I);

  pl = const_vecsmall(r1,1);
  pl[i] = -1;
  y = const_vec(n, gen_1);
  x = extchinese(nf,I,y,pl,&red);
  return gerepileupto(av, isprincipalray(bnr,x));
}

/* no garbage collection */
static GEN
localextdeg(GEN nf, GEN pr, GEN cnd, long d, long ell, long n)
{
  long g = n/d;
  GEN res, modpr, ppr = pr, T, p, gen, k;
  if (d==1) return gen_1;
  if (equalsi(ell,pr_get_p(pr))) { /* ell == p */
    res = nfadd(nf, gen_1, pr_get_gen(pr));
    res = nfpowmodideal(nf, res, stoi(g), cnd);
  }
  else { /* ell != p */
    k = powis(stoi(ell),Z_lval(subis(pr_norm(pr),1),ell));
    k = divis(k,g);
    modpr = nf_to_Fq_init(nf, &ppr, &T, &p);
    (void)Fq_sqrtn(gen_1,k,T,p,&gen);
    res = Fq_to_nf(gen, modpr);
  }
  return res;
}

/* Ld[i] must be nontrivial powers of the same prime ell */
/* pl : -1 at real places at which the extention must ramify, 0 elsewhere */
GEN
nfgwkummer(GEN nf, GEN Lpr, GEN Ld, GEN pl, long var)
{
  const long n = (lg(Ld)==1)? 2: vecsmall_max(Ld);
  pari_sp av = avma;
  ulong ell;
  long i, v;
  GEN cnd, y, x, red, pol;
  v = uisprimepower(n, &ell);
  cnd = zeromatcopy(lg(Lpr)-1,2);

  y = vec_ei(lg(Lpr)-1,1);
  for (i=1; i<lg(Lpr); i++) {
    GEN pr = gel(Lpr,i), p = pr_get_p(pr), E;
    long e = pr_get_e(pr);
    gcoeff(cnd,i,1) = pr;

    if (!equalui(ell,p))
      E = gen_1;
    else
      E = addsi(1 + v*e, divsi(e,subis(p,1)));
    gcoeff(cnd,i,2) = E;
    gel(y,i) = localextdeg(nf, pr, idealpow(nf,pr,E), Ld[i], ell, n);
  }

  x = extchinese(nf, cnd, y, pl, &red); /* TODO use a factoredextchinese to ease computations afterwards ? */
  x = basistoalg(nf,x);
  pol = gsub(gpowgs(pol_x(var),n),x);

  return gerepileupto(av,pol);
}

static GEN
get_vecsmall(GEN v)
{
  switch(typ(v))
  {
    case t_VECSMALL: return v;
    case t_VEC: if (RgV_is_ZV(v)) return ZV_to_zv(v);
  }
  pari_err_TYPE("nfgrunwaldwang",v);
  return NULL;/*not reached*/
}
GEN
nfgrunwaldwang(GEN nf0, GEN Lpr, GEN Ld, GEN pl, long var)
{
  ulong n;
  pari_sp av = avma;
  GEN nf, bnf;
  long t, w;
  ulong ell;
  if (typ(Lpr) != t_VEC) pari_err_TYPE("nfgrunwaldwang",Lpr);
  Ld = get_vecsmall(Ld);
  pl = get_vecsmall(pl);
  bnf = get_bnf(nf0,&t);
  nf = get_nf(nf0,&t);
  n = (lg(Ld)==1)? 2: vecsmall_max(Ld);

  (void)uisprimepower(n, &ell);
  w = bnf? bnf_get_tuN(bnf): itos(gel(rootsof1(nf),1));

  /*TODO choice between kummer and generic ? Let user choose between speed
   * and size*/
  if (w%n==0 && lg(Ld)>1)
    return gerepileupto(av,nfgwkummer(nf,Lpr,Ld,pl,var));
  if (ell==n) {
    if (!bnf) bnf = Buchall(nf,0,0);
    return gerepileupto(av,bnfgwgeneric(bnf,Lpr,Ld,pl,var));
  }
  else {av = avma; return gen_0;}
}

/** HASSE INVARIANT **/

/*TODO long -> ulong + uel */
static GEN
hasseconvert(GEN H, long n)
{
  GEN h, c;
  long i, l;
  switch(typ(H)) {
    case t_VEC:
      l = lg(H); h = cgetg(l,t_VECSMALL);
      if (l == 1) return h;
      c = gel(H,1);
      if (typ(c) == t_VEC && l == 3)
        return mkvec2(gel(H,1),hasseconvert(gel(H,2),n));
      for (i=1; i<l; i++)
      {
        c = gel(H,i);
        switch(typ(c)) {
          case t_INT:  break;
          case t_INTMOD:
            c = gel(c,2); break;
          case t_FRAC :
            c = gmulgs(c,n);
            if (typ(c) == t_INT) break;
          default : pari_err_TYPE("Hasse invariant", c);
        }
        h[i] = smodis(c,n);
      }
      return h;
    case t_VECSMALL: return H;
  }
  pari_err_TYPE("Hasse invariant", H); return NULL;
}

/* assume f >= 2 */
static long
cyclicrelfrob0(GEN nf, GEN aut, GEN pr, GEN q, long f, long g)
{
  pari_sp av = avma;
  long s;
  GEN T, p, modpr, a, b;

  modpr = nf_to_Fq_init(nf,&pr,&T,&p);
  a = pol_x(nf_get_varn(nf));
  b = galoisapply(nf, aut, modpr_genFq(modpr));
  b = nf_to_Fq(nf, b, modpr);
  for (s=0; !ZX_equal(a, b); s++) a = Fq_pow(a, q, T, p);
  avma = av;
  return g*Fl_inv(s, f);/*<n*/
}

static GEN
rnfprimedec(GEN rnf, GEN nf2, GEN pr)
{
  GEN pr2;
  pr2 = idealhnf(nf2,gtomat(matalgtobasis(nf2,rnfidealup(rnf, pr))));
  return idealfactor(nf2, pr2);
}

long
cyclicrelfrob(GEN rnf, GEN nf2, GEN auts, GEN pr)
{
  pari_sp av = avma;
  long n,f,g,frob;
  GEN nf, fa, ppr, autabs;
  n = rnf_get_degree(rnf);
  nf = rnf_get_nf(rnf);

  fa = rnfprimedec(rnf, nf2, pr);

  if (cmpis(gcoeff(fa,1,2), 1) > 0)
    pari_err_DOMAIN("cyclicrelfrob","e(PR/pr)",">",gen_1,pr);
  g = nbrows(fa);
  f = n/g;

  if (f <= 2) frob = g%n;
  else {
    ppr = gcoeff(fa,1,1);
    autabs = rnfeltreltoabs(rnf,gel(auts,g));
    autabs = nfadd(nf2, autabs, gmul(rnf_get_k(rnf), rnf_get_alpha(rnf)));
    frob = cyclicrelfrob0(nf2, autabs, ppr, idealnorm(nf,pr), f, g);
  }
  avma = av; return frob;
}

long
localhasse(GEN rnf, GEN nf2, GEN cnd, GEN pl, GEN auts, GEN b, long k)
{
  pari_sp av = avma;
  long v, m, h, lfa, frob, n, i;
  GEN previous, y, pr, nf, q, fa;
  nf = rnf_get_nf(rnf);
  n = rnf_get_degree(rnf);
  pr = gcoeff(cnd,k,1);
  v = nfval(nf, b, pr);
  m = lg(cnd)>1 ? nbrows(cnd) : 0;

  /* add the valuation of b to the conductor... */
  previous = gcoeff(cnd,k,2);
  gcoeff(cnd,k,2) = addis(previous, v);

  y = const_vec(m, gen_1);
  gel(y,k) = b;
  /* find a factored element y congruent to b mod pr^(vpr(b)+vpr(cnd)) and to 1 mod the conductor. */
  y = factoredextchinese(nf, cnd, y, pl, &fa);
  h = 0;
  lfa = nbrows(fa);
  /* sum of all Hasse invariants of (rnf/nf,aut,y) is 0, Hasse invariants at q!=pr are easy, Hasse invariant at pr is the same as for al=(rnf/nf,aut,b). */
  for (i=1; i<=lfa; i++) {
    q = gcoeff(fa,i,1);
    if (cmp_prime_ideal(pr,q)) {
      frob = cyclicrelfrob(rnf, nf2, auts, q);
      frob = Fl_mul(frob,umodiu(gcoeff(fa,i,2),n),n);
      h = Fl_add(h,frob,n);
    }
  }
  /* ...then restore it. */
  gcoeff(cnd,k,2) = previous;

  avma = av; return Fl_neg(h,n);
}

static GEN
allauts(GEN rnf, GEN aut)
{
  long n = rnf_get_degree(rnf), i;
  GEN pol = rnf_get_pol(rnf), vaut;
  if(n==1) n=2;
  vaut = cgetg(n,t_VEC);
  aut = lift(rnfbasistoalg(rnf,aut));
  gel(vaut,1) = aut;
  for (i=1; i<n-1; i++)
    gel(vaut,i+1) = RgX_rem(poleval(gel(vaut,i), aut), pol);
  return vaut;
}

static GEN
clean_factor(GEN fa)
{
  GEN P2,E2, P = gel(fa,1), E = gel(fa,2);
  long l = lg(P), i, j = 1;
  P2 = cgetg(l, t_COL);
  E2 = cgetg(l, t_COL);
  for (i = 1;i < l; i++)
    if (signe(gel(E,i))) {
      gel(P2,j) = gel(P,i);
      gel(E2,j) = gel(E,i); j++;
    }
  setlg(P2,j);
  setlg(E2,j); return mkmat2(P2,E2);
}

/* shallow concat x[1],...x[nx],y[1], ... y[ny], returning a t_COL. To be
 * used when we do not know whether x,y are t_VEC or t_COL */
static GEN
colconcat(GEN x, GEN y)
{
  long i, lx = lg(x), ly = lg(y);
  GEN z=cgetg(lx+ly-1, t_COL);
  for (i=1; i<lx; i++) z[i]     = x[i];
  for (i=1; i<ly; i++) z[lx+i-1]= y[i];
  return z;
}

/* return v(x) at all primes in listpr, replace x by cofactor */
static GEN
nfmakecoprime(GEN nf, GEN *px, GEN listpr)
{
  long j, l = lg(listpr);
  GEN x1, x = *px, L = cgetg(l, t_COL);

  if (typ(x) != t_MAT)
  { /* scalar, divide at the end (fast valuation) */
    x1 = NULL;
    for (j=1; j<l; j++)
    {
      GEN pr = gel(listpr,j), e;
      long v = nfval(nf, x, pr);
      e = stoi(v); gel(L,j) = e;
      if (v) x1 = x1? idealmulpowprime(nf, x1, pr, e)
                    : idealpow(nf, pr, e);
    }
    if (x1) x = idealdivexact(nf, idealhnf(nf,x), x1);
  }
  else
  { /* HNF, divide as we proceed (reduce size) */
    for (j=1; j<l; j++)
    {
      GEN pr = gel(listpr,j);
      long v = idealval(nf, x, pr);
      gel(L,j) = stoi(v);
      if (v) x = idealmulpowprime(nf, x, pr, stoi(-v));
    }
  }
  *px = x; return L;
}

/* Caveat: factorizations are not sorted wrt cmp_prime_ideal: Lpr comes first */
static GEN
computecnd(GEN rnf, GEN Lpr)
{
  GEN id, nf, fa, Le, P,E;
  long n = rnf_get_degree(rnf);

  nf = rnf_get_nf(rnf);
  id = rnf_get_idealdisc(rnf);
  Le = nfmakecoprime(nf, &id, Lpr);
  fa = idealfactor(nf, id); /* part of D_{L/K} coprime with Lpr */
  P =  colconcat(Lpr,gel(fa,1));
  E =  colconcat(Le, gel(fa,2));
  fa = mkmat2(P, gdiventgs(E, eulerphiu(n)));
  return mkvec2(fa, clean_factor(fa));
}

static void
nextgen(GEN gene, long h, GEN* gens, GEN* hgens, long* ngens, long* curgcd) {
  long nextgcd = cgcd(h,*curgcd);
  if (nextgcd == *curgcd) return;
  (*ngens)++;
  gel(*gens,*ngens) = gene;
  gel(*hgens,*ngens) = stoi(h);
  *curgcd = nextgcd;
  return;
}

inline int
dividesmod(long d, long h, long n) { return !(h%cgcd(d,n)); }

/* ramified prime with nontrivial Hasse invariant */
static GEN
localcomplete(GEN rnf, GEN nf2, GEN pl, GEN cnd, GEN auts, long j, long n, long h, long* v)
{
  GEN nf, gens, hgens, pr, modpr, T, p, Np, sol, U, D, b, gene, randg, pu;
  long ngens, i, d, np, k, d1, d2, hg, dnf, vcnd, curgcd;
  nf = rnf_get_nf(rnf);
  pr = gcoeff(cnd,j,1);
  Np = pr_norm(pr);
  np = smodis(Np,n);
  dnf = nf_get_degree(nf);
  vcnd = itos(gcoeff(cnd,j,2));
  ngens = 13+dnf;
  gens = zerovec(ngens);
  hgens = zerovec(ngens);
  *v = 0;
  curgcd = 0;
  ngens = 0;

  if (!uisprime(n)) {
    gene =  pr_get_gen(pr);
    hg = localhasse(rnf, nf2, cnd, pl, auts, gene, j);
    nextgen(gene, hg, &gens, &hgens, &ngens, &curgcd);
  }

  if (cgcd(np,n) != 1) { /* GCD(Np,n) != 1 */
    pu = idealprincipalunits(nf,pr,vcnd);
    pu = abgrp_get_gen(pu);
    for (i=1; i<lg(pu) && !dividesmod(curgcd,h,n); i++) {
      gene = gel(pu,i);
      hg = localhasse(rnf, nf2, cnd, pl, auts, gene, j);
      nextgen(gene, hg, &gens, &hgens, &ngens, &curgcd);
    }
  }

  d = cgcd(np-1,n);
  if (d != 1) { /* GCD(Np-1,n) != 1 */
    modpr = nf_to_Fq_init(nf, &pr, &T, &p);
    while (!dividesmod(curgcd,h,n)) { /*TODO gener_FpXQ_local*/
      if (T==NULL) randg = randomi(p);
      else randg = random_FpX(degpol(T), varn(T),p);

      if (!gequal0(randg) && !gequal1(randg)) {
        gene = Fq_to_nf(randg, modpr);
        hg = localhasse(rnf, nf2, cnd, pl, auts, gene, j);
        nextgen(gene, hg, &gens, &hgens, &ngens, &curgcd);
      }
    }
  }

  setlg(gens,ngens+1);
  setlg(hgens,ngens+1);

  sol = ZV_extgcd(hgens);
  D = gel(sol,1);
  U = gmael(sol,2,ngens);

  b = gen_1;
  d = itos(D);
  d1 = cgcd(d,n);
  d2 = d/d1;
  d = ((h/d1)*Fl_inv(d2,n))%n;
  for (i=1; i<=ngens; i++) {
    k = (itos(gel(U,i))*d)%n;
    if (k<0) k = n-k;
    if (k) b = nfmul(nf, b, nfpow_u(nf, gel(gens,i),k));
    if (i==1) *v = k;
  }
  return b;
}

static int
testsplits(GEN data, GEN b, GEN fa)
{
  GEN rnf, nf2, fapr, pr, forbid, nf;
  long i, g, n;
  rnf = gel(data,1);
  nf2 = gel(data,2);
  forbid = gel(data,3);
  n = rnf_get_degree(rnf);
  nf = rnf_get_nf(rnf);
  if (gequal0(b)) return 0;
  for (i=1; i<lgcols(fa); i++) {
    pr = gcoeff(fa,i,1);
    if (idealval(nf,forbid,pr)) return 0;
    fapr = rnfprimedec(rnf,nf2,pr);
    g = nbrows(fapr);
    if ((itos(gcoeff(fa,i,2))*g)%n) return 0;
  }
  return 1;
}

/* remove entries with Hasse invariant 0 */
static GEN
hassereduce(GEN hf)
{
  GEN pr,h, PR = gel(hf,1), H = gel(hf,2);
  long i, j, l = lg(PR);

  pr= cgetg(l, t_VEC);
  h = cgetg(l, t_VECSMALL);
  for (i = j = 1; i < l; i++)
    if (H[i]) {
      gel(pr,j) = gel(PR,i);
      h[j] = H[i]; j++;
    }
  setlg(pr,j);
  setlg(h,j); return mkvec2(pr,h);
}

/* v vector of prid. Return underlying list of rational primes */
static GEN
pr_primes(GEN v)
{
  long i, l = lg(v);
  GEN w = cgetg(l,t_VEC);
  for (i=1; i<l; i++) gel(w,i) = pr_get_p(gel(v,i));
  return ZV_sort_uniq(w);
}

static GEN
al_complete0(GEN rnf, GEN aut, GEN hf, GEN hi, int maxord)
{
  pari_sp av = avma;
  GEN nf, pl, pl2, cnd, prcnd, cnds, y, Lpr, auts, nf2, b, fa, data, hfe;
  GEN forbid, al;
  long D, n, d, i, j;
  nf = rnf_get_nf(rnf);
  n = rnf_get_degree(rnf);
  d = nf_get_degree(nf);
  D = d*n*n;
  checkhasse(nf,hf,hi,n);
  hf = hassereduce(hf);
  Lpr = gel(hf,1);
  hfe = gel(hf,2);

  auts = allauts(rnf,aut);
  nf2 = nfinit(rnf_get_polabs(rnf), nf_get_prec(rnf_get_nf(rnf)));

  pl = gcopy(hi); /* conditions on the final b */
  pl2 = gcopy(hi); /* conditions for computing local Hasse invariants */
  for (i=1; i<lg(pl); i++) {
    if (hi[i]) {
      pl[i] = -1;
      pl2[i] = 1;
    }
    else if (!rnfrealdec(rnf,i)) {
      pl[i] = 1;
      pl2[i] = 1;
    }
  }

  cnds = computecnd(rnf,Lpr);
  prcnd = gel(cnds,1);
  cnd = gel(cnds,2);
  y = cgetg(lgcols(prcnd),t_VEC);
  forbid = gen_1;
  for (i=j=1; i<lg(Lpr); i++)
  {
    GEN pr = gcoeff(prcnd,i,1);
    long v, e = itos( gcoeff(prcnd,i,2) );
    if (!e) {
      long frob, f1, f2;
      gel(y,i) = gen_0;
      frob = cyclicrelfrob(rnf,nf2,auts,pr);
      f1 = cgcd(frob,n);
      f2 = frob/f1;
      v = ((hfe[i] / f1) * Fl_inv(f2,n)) % n;
      forbid = idealmul(nf,forbid,pr);
    }
    else {
      gel(y,i) = localcomplete(rnf, nf2, pl2, cnd, auts, j, n, hfe[i], &v);
      j++;
    }
    gcoeff(prcnd,i,2) = stoi(e + v);
  }
  for (; i<lgcols(prcnd); i++) gel(y,i) = gen_1;

  data = mkvec3(rnf,nf2,forbid);
  b = factoredextchinesetest(nf,prcnd,y,pl,&fa,data,testsplits);

  al = cgetg(12, t_VEC);
  gel(al,10)= gen_0; /* must be set first */
  gel(al,1) = rnf;
  gel(al,2) = auts;
  gel(al,3) = basistoalg(nf,b);
  gel(al,4) = hi;
  /* add primes | disc or b with trivial Hasse invariant to hf */
  Lpr = gel(prcnd,1); y = b;
  (void)nfmakecoprime(nf, &y, Lpr);
  Lpr = shallowconcat(Lpr, gel(idealfactor(nf,y), 1));
  settyp(Lpr,t_VEC);
  hf = mkvec2(Lpr, shallowconcat(hfe, const_vecsmall(lg(Lpr)-lg(hfe), 0)));
  gel(al,5) = hf;
  gel(al,6) = nf2;
  gel(al,7) = matid(D);
  gel(al,8) = matid(D); /* TODO modify 7, 8 et 9 once LLL added */
  gel(al,9) = alnatmultable(al,D);
  gel(al,11)= altracebasis(al);
  if (maxord) al = al_maximal_primes(al, pr_primes(Lpr));
  return gerepilecopy(av, al);
}

GEN
al_complete(GEN rnf, GEN aut, GEN hf, GEN hi, int maxord)
{
  long n = rnf_get_degree(rnf);
  return al_complete0(rnf,aut,hasseconvert(hf,n),hasseconvert(hi,n), maxord);
}

void
checkhasse(GEN nf, GEN hf, GEN hi, long n)
{
  GEN Lpr, Lh;
  long i, sum;
  if (typ(hf) != t_VEC || lg(hf) != 3) pari_err_TYPE("checkhasse", hf);
  Lpr = gel(hf,1);
  Lh = gel(hf,2);
  if (typ(Lpr) != t_VEC) pari_err_TYPE("checkhasse", Lpr);
  if (typ(Lh) != t_VECSMALL) pari_err_TYPE("checkhasse", Lh);
  if (typ(hi) != t_VECSMALL || (nf && lg(hi) != nf_get_r1(nf)+1))
    pari_err_TYPE("checkhasse", hi);
  if (lg(Lpr) != lg(Lh)) pari_err_TYPE("checkhasse", hf);
  for (i=1; i<lg(Lpr); i++) checkprid(gel(Lpr,i));
  sum = 0;
  for (i=1; i<lg(Lh); i++) sum = (sum+Lh[i])%n;
  for (i=1; i<lg(hi); i++) {
      if(hi[i] && hi[i] != n/2) pari_err_DOMAIN("checkhasse", "nonzero Hasse invariant at infinity", "!=", stoi(n/2), stoi(hi[i]));
      sum = (sum+hi[i])%n;
  }
  if (sum<0) sum = n+sum;
  if (sum != 0)
    pari_err_DOMAIN("checkhasse","sum(Hasse invariants)","!=",gen_0,Lh);
}

GEN
hassecoprime(GEN hf, GEN hi, long n)
{
  pari_sp av = avma;
  long l, i, j, lk, inv;
  GEN fa, P,E, res, hil, hfl;
  hi = hasseconvert(hi, n);
  hf = hasseconvert(hf, n);
  checkhasse(NULL,hf,hi,n);
  fa = factoru(n);
  P = gel(fa,1); l = lg(P);
  E = gel(fa,2);
  res = cgetg(l,t_VEC);
  for (i=1; i<l; i++) {
    lk = upowuu(P[i],E[i]);
    inv = Fl_invsafe((n/lk)%lk, lk);
    hil = gcopy(hi);
    hfl = gcopy(hf);

    if (P[i] == 2)
      for (j=1; j<lg(hil); j++) hil[j] = hi[j]==0 ? 0 : lk/2;
    else
      for (j=1; j<lg(hil); j++) hil[j] = 0;
    for (j=1; j<lgcols(hfl); j++) gel(hfl,2)[j] = (gel(hf,2)[j]*inv)%lk;
    hfl = hassereduce(hfl);
    gel(res,i) = mkvec3(hfl,hil,stoi(lk));
  }

  return gerepilecopy(av, res);
}

static GEN
zv_z_div(GEN z, long k)
{
  long i, l;
  GEN x = cgetg_copy(z,&l);
  for (i = 1; i < l; i++) x[i] = z[i]/k;
  return x;
}

GEN
hassewedderburn(GEN hf, GEN hi, long n)
{
  pari_sp av = avma;
  long ind = 1, denom, i, k;
  GEN hid, hfd;
  hi = hasseconvert(hi,n);
  hf = hasseconvert(hf,n);
  checkhasse(NULL,hf,hi,n);
  for (i=1; i<lg(hi); i++) {
    denom = n/cgcd(hi[i],n);
    ind = clcm(ind,denom);
  }
  for (i=1; i<lgcols(hf); i++) {
    denom = n/cgcd(gel(hf,2)[i],n);
    ind = clcm(ind,denom);
  }
  k = n/ind;
  hid = zv_z_div(hi, k);
  hfd = mkmat2(gel(hf,1), zv_z_div(gel(hf,2),k));
  return gerepilecopy(av, mkvec3(hfd,hid,stoi(k)));
}

static long
alldegmultiple(GEN pr, long d)
{
  long i;
  for (i=1; i<lg(pr); i++)
    if ((pr_get_e(gel(pr,i))*pr_get_f(gel(pr,i))) % d) return 0;
  return 1;
}

/* no garbage collection */
static long
searchprimedeg(GEN nf, long d, GEN forbidden, GEN *pp)
{
  ulong p, n = nf_get_degree(nf);
  GEN b, pr;
  forprime_t T;

  if (n%d) return 0;

  /* replace with a simple bound ? */
  b = glog(nf_get_disc(nf),5);
  b = mulrs(b,n);
  b = mpsqr(b);
  b = ceil_safe(b);
  b = gmin(b, stoi(ULONG_MAX/2));
  if (!u_forprime_init(&T, 0, itos(b))) return 0;

  while ((p=u_forprime_next(&T))) {/* not a comparison : test p!=0 */
    if (tablesearch(forbidden, stoi(p), cmpii)) continue;
    pr = idealprimedec(nf,stoi(p));
    if (alldegmultiple(pr,d)) { *pp = stoi(p); return 1; }
  }
  return 0;
}

/* no garbage collection */
static GEN
sortedp(GEN Lpr)
{
  long i;
  GEN Lp = zerovec(lg(Lpr)-1);
  for (i=1; i<lg(Lp); i++) gel(Lp,i) = pr_get_p(gel(Lpr,i));
  return gen_sort_uniq(Lp, (void*)cmpii, cmp_nodata);
}

static long
solvablecrt(long x1, long N1, long x2, long N2, long *x0, long *N)
{
  long d, a, b, u;
  d = cbezout(N1, N2, &a, &b);
  if ((x1-x2)%d != 0) return 0;
  N1 /= d;
  *N = N1*N2;
  N2 /= d;
  u = a*N1;
  *x0 = smodss(u*x2+(1-u)*x1,*N);
  return 1;
}

static long
hdown(GEN pr, long h, long n, long *nn)
{
  long prdeg, d, u, v;
  prdeg = pr_get_e(pr)*pr_get_f(pr);
  d = cgcd(prdeg,n);
  if (h%d) return 0;
  h /= d;
  prdeg /= d;
  *nn = n/d;
  d = cbezout(prdeg, *nn, &u, &v);
  return (h*u)%(*nn); /* can be <0 */
}

/* Assumes hf contains no prime or all primes above every rational primes */
/* Less efficient (might not find a soution) if a set of primes above p all have Hasse invariant 0. */
static GEN hassedown0(GEN nf, long n, GEN hf, GEN hi)
{
  pari_sp av = avma;
  long totcplx=(lg(hi)==1), hid=0, i, j, h, nn, total, nbp;
  GEN pr, pv, h0v, nnv;
  checkhasse(nf,hf,hi,n);

  /* The Hasse invariant at gel(pv,i) has to be h0v[i] mod nnv[i], where nnv[i] | n. */
  if (!totcplx) {
    hid = hi[1];
    for (i=2;i<lg(hi);i++)
      if (hi[i] != hid) {avma = av; return gen_0;}
  }

  pv = sortedp(gel(hf,1));
  h0v = cgetg(lg(pv),t_VECSMALL);
  nnv = const_vecsmall(lg(pv)-1, 0);

  for (i=1; i<lgcols(hf); i++) {
    pr = gmael(hf,1,i);
    h = gel(hf,2)[i];
    h %= n;
    nn = 0;
    h = hdown(pr, h, n, &nn);
    if (nn==0) {avma = av; return gen_0;}

    j = ZV_search(pv, pr_get_p(pr));
    if (nnv[j]==0) {
      nnv[j] = nn;
      h0v[j] = h;
    }
    else if (!solvablecrt(h0v[j], nnv[j], h, nn, &h0v[j], &nnv[j])) {avma = av; return gen_0;}
  }
  total = (hid + zv_sum(h0v)) % n;
  nbp = lg(pv)-1;
  if (total==n/2 && totcplx)
    hid = n/2;
  else if (total!=0) {
    GEN p;
    nn = n/cgcd(total,n);
    if (!searchprimedeg(nf, nn, pv, &p)) {avma = av; return gen_0;}
    nbp++;
    pv = vec_append(pv, p);
    h0v= vecsmall_append(h0v, (n-total)%n);
  }
  return gerepilecopy(av, mkvec2(mkvec2(pv,h0v),
                                 mkvecsmall(hid)));
}

GEN
hassedown(GEN nf, long n, GEN hf, GEN hi)
{
  return hassedown0(nf,n,hasseconvert(hf,n),hasseconvert(hi,n));
}

/* no garbage collection */
static GEN
genefrob(GEN nf, GEN gal, GEN r)
{
  long i;
  GEN g = identity_perm(nf_get_degree(nf)), fa = Z_factor(r), p, pr, frob;
  for (i=1; i<lgcols(fa); i++) {
    p = gcoeff(fa,i,1);
    pr = idealprimedec(nf, p);
    pr = gel(pr,1);
    frob = idealfrobenius(nf, gal, pr);
    g = perm_mul(g, perm_pow(frob, itos(gcoeff(fa,i,2))));
  }
  return g;
}

static GEN
rnfcycaut(GEN rnf, GEN nf2)
{
  GEN L, alpha, pol, salpha, s, sj, polabs, k, X, pol0, nf;
  long i, d, j;
  d = rnf_get_degree(rnf);
  L = galoisconj(nf2,NULL);
  alpha = lift(rnf_get_alpha(rnf));
  pol = rnf_get_pol(rnf);
  k = rnf_get_k(rnf);
  polabs = rnf_get_polabs(rnf);
  nf = rnf_get_nf(rnf);
  pol0 = nf_get_pol(nf);
  X = RgX_rem(pol_x(varn(pol0)), pol0);

  /* TODO: check mod prime of degree 1 */
  for (i=1; i<lg(L); i++) {
    s = gel(L,i);
    salpha = RgX_RgXQ_eval(alpha,s,polabs);
    if (!gequal(alpha,salpha)) continue;

    s = lift(rnfeltabstorel(rnf,s));
    sj = s = gsub(s, gmul(k,X));
    for (j=1; !gequal0(gsub(sj,pol_x(varn(s)))); j++)
      sj = RgX_RgXQ_eval(sj,s,pol);
    if (j<d) continue;
    return s;
  }
  return NULL; /*not reached*/
}

GEN
al_hasse(GEN nf, long n, GEN hf, GEN hi, long var, long maxord)
{
  pari_sp av = avma;
  GEN primary, al = gen_0, al2, rnf, hil, hfl, Ld, pl, pol, nf2, Lpr, aut;
  long i, lk, j;
  primary = hassecoprime(hf, hi, n); /*contains a checkhasse*/
  if (var < 0) var = 0;
  for (i=1; i<lg(primary); i++) {
    hfl = gmael(primary,i,1);
    hil = gmael(primary,i,2);
    lk = itos(gmael(primary,i,3));
    Lpr = gel(hfl,1);
    Ld = gcopy(gel(hfl,2));
    for (j=1; j<lg(Ld); j++) Ld[j] = lk/cgcd(lk,Ld[j]);
    pl = gcopy(hil);
    for (j=1; j<lg(pl); j++) pl[j] = pl[j] ? -1 : 0;

    pol = nfgrunwaldwang(nf,Lpr,Ld,pl,var);
    rnf = rnfinit(nf,pol);
    nf2 = nfinit(rnf_get_polabs(rnf), nf_get_prec(nf));

    aut = rnfcycaut(rnf,nf2);
    al2 = al_complete0(rnf,aut,hfl,hil,maxord);

    if (i==1) al = al2;
    else      al = altensor(al,al2,maxord);
  }
  return gerepilecopy(av,al);
}

/** CYCLIC ALGEBRA WITH GIVEN HASSE INVARIANTS **/

/* no garbage collection */
static int
linindep(GEN pol, GEN L)
{
  long i;
  GEN fa;
  for (i=1; i<lg(L); i++) {
    fa = nffactor(gel(L,i),pol);
    if (lgcols(fa)>2) return 0;
  }
  return 1;
}

/* no garbage collection */
static GEN
subcycloindep(GEN nf, long n, long v, GEN L, GEN *pr)
{
  pari_sp av;
  forprime_t S;
  ulong p;
  u_forprime_arith_init(&S, 1, ULONG_MAX, 1, n);
  av = avma;
  while ((p = u_forprime_next(&S)))
  {
    ulong r = pgener_Fl(p);
    GEN pol = galoissubcyclo(utoipos(p), utoipos(Fl_powu(r,n,p)), 0, v);
    GEN fa = nffactor(nf, pol);
    if (lgcols(fa) == 2 && linindep(pol,L)) { *pr = utoipos(r); return pol; }
    avma = av;
  }
  pari_err_BUG("subcycloindep (no suitable prime = 1(mod n))");
  *pr = NULL; return NULL;
}

GEN
al_matrix(GEN nf, long n, long v, GEN L, long flag)
{
  pari_sp av = avma;
  GEN pol, gal, rnf, cyclo, g, r, aut;
  pol = subcycloindep(nf, n, v, L, &r);
  rnf = rnfinit(nf, pol);
  cyclo = nfinit(pol, nf_get_prec(nf));
  gal = galoisinit(cyclo, NULL);
  g = genefrob(cyclo,gal,r);
  aut = galoispermtopol(gal,g);
  return gerepileupto(av, al_cyclic(rnf, aut, gen_1, flag));
}

GEN
al_hilbert(GEN nf, GEN a, GEN b, long v, long flag)
{
  pari_sp av = avma;
  GEN C, P, rnf, aut;
  checknf(nf);

  if (v < 0) v = 0;
  C = Rg_col_ei(gneg(a), 3, 3);
  gel(C,1) = gen_1;
  P = gtopoly(C,v);
  rnf = rnfinit(nf, P);
  aut = gneg(pol_x(v));
  return gerepileupto(av, al_cyclic(rnf, aut, b, flag));
}

GEN
alinit(GEN A, GEN B, long v, long flag)
{
  switch(nftyp(A))
  {
    case typ_NF:
      switch(typ(B))
      {
        long nB;
        case t_INT: return al_matrix(A, itos(B), v, cgetg(1,t_VEC), flag);
        case t_VEC:
          nB = lg(B)-1;
          if (nB && typ(gel(B,1)) == t_MAT) return al_csa_table(A, B, v, flag);
          switch(nB)
          {
            case 2: return al_hilbert(A, gel(B,1),gel(B,2), v, flag);
            case 3: return al_hasse(A, itos(gel(B,1)),gel(B,2),gel(B,3),v,flag);
          }
      }
      pari_err_TYPE("alinit1", B); break;

    case typ_RNF:
      if (typ(B) != t_VEC || lg(B) != 3) pari_err_TYPE("alinit2", B);
      return al_cyclic(A,gel(B,1),gel(B,2),flag);
  }
  pari_err_TYPE("alinit3", A);
  return NULL;/*not reached*/
}

static GEN
alnatmultable(GEN al, long D)
{
  GEN res, x;
  long i;
  res = cgetg(D+1,t_VEC);
  for (i=1; i<=D; i++) {
    x = alnattoalg(al,col_ei(D,i));
    gel(res,i) = alZmultable(al,x);
  }
  return res;
}

/* no garbage collection */
static void
alcomputehasse(GEN al)
{
  long r1, k, n, m, m1, m2, m3, i, m23, m123;
  GEN rnf, nf, b, fab, disc2, cnd, fad, auts, nf2, pr, pl, perm;
  GEN hi, PH, H, L;

  rnf = al_get_splitting(al);
  n = rnf_get_degree(rnf);
  nf = rnf_get_nf(rnf);
  b = al_get_b(al);
  r1 = nf_get_r1(nf);
  auts = al_get_auts(al);
  nf2 = al_get_abssplitting(al);

  /* real places where rnf/nf ramifies */
  pl = cgetg(r1+1, t_VECSMALL);
  for (k=1; k<=r1; k++) pl[k] = !rnfrealdec(rnf,k);

  /* infinite Hasse invariants */
  if (odd(n)) hi = const_vecsmall(r1, 0);
  else
  {
    GEN s = nfsign(nf, b);
    hi = cgetg(r1+1, t_VECSMALL);
    for (k = 1; k<=r1; k++) hi[k] = (s[k] && pl[k]) ? (n/2) : 0;
  }

  fab = idealfactor(nf, b);
  disc2 = rnf_get_idealdisc(rnf);
  L = nfmakecoprime(nf, &disc2, gel(fab,1));
  m = lg(L)-1;
  /* m1 = #{pr|b: pr \nmid disc}, m3 = #{pr|b: pr | disc} */
  perm = cgetg(m+1, t_VECSMALL);
  for (i=1, m1=m, k=1; k<=m; k++)
    if (signe(gel(L,k))) perm[m1--] = k; else perm[i++] = k;
  m3 = m - m1;

  /* disc2 : factor of disc coprime to b */
  fad = idealfactor(nf, disc2);
  /* m2 : number of prime factors of disc not dividing b */
  m2 = nbrows(fad);
  m23 = m2+m3;
  m123 = m1+m2+m3;

  /* initialize the possibly ramified primes (hasse) and the factored conductor of rnf/nf (cnd) */
  cnd = zeromatcopy(m23,2);
  PH = cgetg(m123+1, t_VEC); /* ramified primes */
  H = cgetg(m123+1, t_VECSMALL); /* Hasse invariant */
  /* compute Hasse invariant at primes that are unramified in rnf/nf */
  for (k=1; k<=m1; k++) {/* pr | b, pr \nmid disc */
    long frob, e, j = perm[k];
    pr = gcoeff(fab,j,1);
    e = itos(gcoeff(fab,j,2));
    frob = cyclicrelfrob(rnf, nf2, auts, pr);
    gel(PH,k) = pr;
    H[k] = Fl_mul(frob, e, n);
  }
  /* compute Hasse invariant at primes that are ramified in rnf/nf */
  for (k=1; k<=m2; k++) {/* pr \nmid b, pr | disc */
    pr = gcoeff(fad,k,1);
    gel(PH,k+m1) = pr;
    gcoeff(cnd,k,1) = pr;
    gcoeff(cnd,k,2) = gcoeff(fad,k,2);
  }
  for (k=1; k<=m3; k++) { /* pr | (b, disc) */
    long j = perm[k+m1];
    pr = gcoeff(fab,j,1);
    gel(PH,k+m1+m2) = pr;
    gcoeff(cnd,k+m2,1) = pr;
    gcoeff(cnd,k+m2,2) = gel(L,j);
  }
  gel(cnd,2) = gdiventgs(gel(cnd,2), eulerphiu(n));
  for (k=1; k<=m23; k++) H[k+m1] = localhasse(rnf, nf2, cnd, pl, auts, b, k);
  gel(al,4) = hi;
  gel(al,5) = mkvec2(PH,H);
  checkhasse(nf,al_get_hasse_f(al),al_get_hasse_i(al),n);
}

#if 0
static GEN
pr_idem(GEN nf, GEN pr)
{
  pari_sp av = avma;
  GEN p, pri, dec, u;
  long i;

  p = pr_get_p(pr);
  dec = idealprimedec(nf,p);
  pri = gen_1;
  for (i=1; i<lg(dec); i++)
    if (!pr_equal(nf,pr,gel(dec,i))) pri = idealmul(nf,pri,gel(dec,i));
  u = idealaddtoone_i(nf, pr, pri);
  return gerepilecopy(av,u);
}
#endif

static GEN
al_maximal_primes(GEN al, GEN P)
{
  pari_sp av = avma;
  long l = lg(P), i;
  for (i=1; i<l; i++)
  {
    if (i != 1) al = gerepilecopy(av, al);
    al = al_pmaximal(al,gel(P,i));
  }
  return al;
}

GEN
al_cyclic(GEN rnf, GEN aut, GEN b, int maxord)
{
  pari_sp av = avma;
  GEN al, nf;
  long D, n, d;
  checkrnf(rnf);
  nf = rnf_get_nf(rnf);
  n = rnf_get_degree(rnf);
  d = nf_get_degree(nf);
  D = d*n*n;

  al = cgetg(12,t_VEC);
  gel(al,10)= gen_0; /* must be set first */
  gel(al,1) = rnf;
  gel(al,2) = allauts(rnf, aut);
  gel(al,3) = basistoalg(nf,b);
  gel(al,6) = nfinit(rnf_get_polabs(rnf), nf_get_prec(nf));
  gel(al,7) = matid(D);
  gel(al,8) = matid(D); /* TODO modify 7, 8 et 9 once LLL added */
  gel(al,9) = alnatmultable(al,D);
  gel(al,11)= altracebasis(al);

  alcomputehasse(al);

  if (maxord) {
    GEN hf = al_get_hasse_f(al), pr = gel(hf,1);
    al = al_maximal_primes(al, pr_primes(pr));
#if 0
    /* check result */
    GEN h, disc = powiu(nf_get_disc(nf), n*n);
    long i;
    disc = absi(disc);
    h = gel(hf,2);
    for (i=1; i<lg(pr); i++) {
      long dp = cgcd(n,h[i]);
      disc = mulii(disc, powiu(pr_norm(gel(pr,i)), n*(n-dp)));
    }
    disc = mulii(disc, powuu(n,D));
    if (!absi_equal(disc, aldisc(al)))
      pari_err_BUG("al_cyclic (wrong maximal order)");
#endif
  }
  return gerepilecopy(av, al);
}

static int
ismaximalsubfield(GEN al, GEN x, GEN d, long v, GEN *pt_minpol)
{
  GEN cp = albasischarpoly(al, x, v), lead;
  if (!ispower(cp, d, pt_minpol)) return 0;
  lead = leading_term(*pt_minpol);
  if(isintm1(lead)) *pt_minpol = gneg(*pt_minpol);
  return ZX_is_irred(*pt_minpol);
}

static GEN
findmaximalsubfield(GEN al, GEN d, long v)
{
  long count, nb=2, i, N = al_get_absdim(al), n = nf_get_degree(al_get_center(al));
  GEN x, minpol, maxc = gen_1;

  for(i=n+1; i<=N; i+=n) {
    for(count=0; count<2 && i+count<=N; count++) {
      x = col_ei(N,i+count);
      if (ismaximalsubfield(al, x, d, v, &minpol)) return mkvec2(x,minpol);
    }
  }

  while(1) {
    x = zerocol(N);
    for(count=0; count<nb; count++)
    {
      i = random_Fl(N)+1;
      gel(x,i) = addis(randomi(maxc),1);
      if (random_bits(1)) gel(x,i) = negi(gel(x,i));
    }
    if (ismaximalsubfield(al, x, d, v, &minpol)) return mkvec2(x,minpol);
    if (!random_bits(3)) maxc = addis(maxc,1);
    if (nb<N) nb++;
  }

  return NULL; /* not reached */
}

static GEN
frobeniusform(GEN al, GEN x)
{
  GEN M, FP, P, Pi;

  /* /!\ has to be the *right* multiplication table */
  M = albasisrightmultable(al, x);

  FP = matfrobenius(M,2,0); /*M = P^(-1)*F*P*/
  P = gel(FP,2);
  Pi = RgM_inv(P);
  return mkvec2(P, Pi);
}

static void
computesplitting(GEN al, long d, long v)
{
  GEN subf, x, pol, polabs, basis, P, Pi, nf = al_get_center(al), rnf, Lbasis, Lbasisinv, Q, pows;
  long i, n = nf_get_degree(nf), nd = n*d, N = al_get_absdim(al), j, j2;

  subf = findmaximalsubfield(al, utoipos(d), v);
  x = gel(subf, 1);
  polabs = gel(subf, 2);

  /* Frobenius form to obtain L-vector space structure */
  basis = frobeniusform(al, x);
  P = gel(basis, 1);
  Pi = gel(basis, 2);

  /* construct rnf of splitting field */
  pol = nffactor(nf,polabs);
  pol = gcoeff(pol,1,1);
  gel(al,1) = rnf = rnfinit(nf, pol);
  if (!gequal0(rnf_get_k(rnf)))
    pari_err_BUG("computesplitting (k!=0)");
  gel(al,6) = nfinit(polabs, nf_get_prec(nf));

  /* construct splitting data */
  Lbasis = cgetg(d+1, t_MAT);
  for(j=j2=1; j<=d; j++, j2+=nd)
    gel(Lbasis,j) = gel(Pi,j2);

  Q = zeromatcopy(d,N);
  pows = pol_x_powers(nd,v);
  for(i=j=1; j<=N; j+=nd, i++)
  for(j2=0; j2<nd; j2++)
    gcoeff(Q,i,j+j2) = mkpolmod(gel(pows,j2+1),polabs);
  Lbasisinv = RgM_mul(Q,P);

  gel(al,3) = mkvec3(x,Lbasis,Lbasisinv);
  return;
}

/* assumes that mt defines a central simple algebra over nf */
GEN
al_csa_table(GEN nf, GEN mt0, long v, int maxord)
{
  pari_sp av = avma;
  GEN al, mt;
  long n, D, d2 = lg(mt0)-1, d = usqrt(d2);

  nf = checknf(nf);
  mt = check_mt(mt0,NULL);
  if (!mt) pari_err_TYPE("al_csa_table", mt0);
  n = nf_get_degree(nf);
  D = n*d2;
  if (d*d != d2)
    pari_err_DOMAIN("al_csa_table", "(nonsquare) dimension", "!=",stoi(d*d),mt);

  al = cgetg(12, t_VEC);
  gel(al,10) = gen_0; /* must be set first */
  gel(al,1) = zerovec(12); gmael(al,1,10) = nf; gmael(al,1,1) = gpowgs(pol_x(0), d); /* placeholder before actual splitting field */
  gel(al,2) = mt;
  gel(al,3) = gen_0; /* placeholder */
  gel(al,4) = gel(al,5) = gen_0; /* TODO Hasse invariants */
  gel(al,5) = gel(al,6) = gen_0; /* placeholder */
  gel(al,7) = matid(D);
  gel(al,8) = matid(D);
  gel(al,9) = alnatmultable(al,D);
  gel(al,11)= altracebasis(al);

  if(maxord) al = al_maximal(al);
  computesplitting(al, d, v);

  return gerepilecopy(av, al);
}

GEN
altableinit(GEN mt0, GEN p)
{
  pari_sp av = avma;
  GEN al, mt;
  long i, n;

  if (p && typ(p) != t_INT) pari_err_TYPE("altableinit",p);
  if (p && !signe(p)) p = NULL;
  mt = check_mt(mt0,p);
  if (!mt) pari_err_TYPE("altableinit", mt0);
  n = lg(mt)-1;
  al = cgetg(12, t_VEC);
  for (i=1; i<=6; i++) gel(al,i) = gen_0;
  gel(al,7) = matid(n);
  gel(al,8) = matid(n);
  gel(al,9) = mt;
  gel(al,10) = p? p: gen_0;
  gel(al,11)= altracebasis(al);

  return gerepilecopy(av, al);
}

/** MAXIMAL ORDER **/

static GEN
mattocol(GEN M, long n)
{
  GEN C = cgetg(n*n+1, t_COL);
  long i,j,ic;
  ic = 1;
  for (i=1; i<=n; i++)
  for (j=1; j<=n; j++, ic++) gel(C,ic) = gcoeff(M,i,j);
  return C;
}

/*Ip is a lift of a left O/pO-ideal where O is the integral basis of al*/
GEN
alleftordermodp(GEN al, GEN Ip, GEN p)
{
  pari_sp av = avma;
  GEN I, Ii, M, mt, K, imi, p2;
  long n, i;
  n = al_get_absdim(al);
  mt = al_get_multable(al);
  p2 = sqri(p);

  I = ZM_hnfmodid(Ip, p);
  Ii = ZM_inv(I,p);

  M = cgetg(n+1, t_MAT);
  for (i=1; i<=n; i++) {
    imi = FpM_mul(Ii, FpM_mul(gel(mt,i), I, p2), p2);
    imi = ZM_Z_divexact(imi, p);
    gel(M,i) = mattocol(imi, n);
  }

  /*TODO : FpM_invimage superbad documentation (have to read RgM_invimage) Does it really do what it claims if left matrix is not invertible ?*/
  K = FpM_ker(M, p);
  if (lg(K)==1) { avma = av; return matid(n); }
  K = ZM_hnfmodid(K,p);

  return gerepileupto(av, ZM_Z_div(K,p));
}

GEN
al_ordermodp(GEN al, GEN p)
{
  GEN alp;
  long i, N = al_get_absdim(al);
  alp = cgetg(12, t_VEC);
  for (i=1; i<=8; i++) gel(alp,i) = gen_0;
  gel(alp,9) = cgetg(N+1, t_VEC);
  for(i=1; i<=N; i++) gmael(alp,9,i) = FpM_red(gmael(al,9,i), p);
  gel(alp,10) = p;
  gel(alp,11) = cgetg(N+1, t_VEC);
  for(i=1; i<=N; i++) gmael(alp,11,i) = Fp_red(gmael(al,11,i), p);

  return alp;
}

static GEN
alpradical_i(GEN al, GEN p, GEN zprad, GEN projs/*TODO:currently unused*/)
{
  pari_sp av = avma;
  GEN alp = al_ordermodp(al, p), liftrad, alq, alrad, res;
  long n = al_get_absdim(alp);
  (void)projs;
  if(lg(zprad)==1) {
    liftrad = matid(n);
  }
  else {
    alq = al_quotient(alp, zprad, 1);
    alp = gel(alq,1);
    liftrad = gel(alq,3);
  }
  alrad = alradical(alp);
  if(!gequal0(alrad)) {
    alrad = FpM_mul(liftrad, alrad, p);
    res = shallowmatconcat(mkvec2(alrad, zprad));
    res = FpM_image(res,p);
  }
  else res = lg(zprad)==1 ? gen_0 : gcopy(zprad);
  return gerepilecopy(av, res);
}
GEN
alpradical(GEN al, GEN p)
{
  GEN placeholder = cgetg(1,t_MAT); /*left on stack*/
  return alpradical_i(al, p, placeholder, gen_1);
}

static GEN
alpdecompose0(GEN al, GEN prad, GEN p)
{
  pari_sp av = avma;
  GEN alp, quo, ss, liftm = gen_0, dec, res, I;
  long i;

  alp = al_ordermodp(al, p);
  if (!gequal0(prad)) {
    quo = al_quotient(alp,prad,1);
    ss = gel(quo,1);
    liftm = gel(quo,3);
  }
  else ss = alp;

  dec = alsimpledec(ss,1);
  res = cgetg(lg(dec),t_VEC);
  for (i=1; i<lg(dec); i++) {
    I = gmael(dec,i,3);
    if (!gequal0(prad)) I = FpM_mul(liftm,I,p);
    I = shallowmatconcat(mkvec2(I,prad));
    gel(res,i) = I;
  }

  return gerepilecopy(av, res);
}

/*finds a nontrivial ideal of O/prad or gen_0 if there is none.*/
static GEN
alpdecompose_i(GEN al, GEN p, GEN zprad, GEN projs)
{
  pari_sp av = avma;
  GEN prad = alpradical_i(al,p,zprad,projs);
  return gerepileupto(av, alpdecompose0(al, prad, p));
}
GEN
alpdecompose(GEN al, GEN p)
{
  GEN placeholder = cgetg(1,t_MAT); /*left on stack*/
  return alpdecompose_i(al, p, placeholder, gen_1);
}

/*ord is assumed to be in hnf wrt the integral basis of al.*/
GEN
al_change_overorder_shallow(GEN al, GEN ord)
{
  GEN al2, mt, iord, mtx;
  long i, n;
  n = al_get_absdim(al);

  iord = QM_inv(ord,gen_1);
  al2 = shallowcopy(al);
  gel(al2,7) = RgM_mul(gel(al,7), ord);
  gel(al2,8) = RgM_mul(iord, gel(al,8));

  mt = cgetg(n+1,t_VEC);
  gel(mt,1) = matid(n);
  for(i=2; i<=n; i++) {
    mtx = albasismultable(al,gel(ord,i));
    gel(mt,i) = RgM_mul(iord, RgM_mul(mtx, ord));
  }
  gel(al2,9) = mt;

  gel(al2,11)= altracebasis(al2);

  return al2;
}

/*ord is assumed to be in hnf wrt the integral basis of al.*/
GEN
al_changeorder_shallow(GEN al, GEN ord)
{
  GEN al2, mt, iord, mtx;
  long i, n;
  n = al_get_absdim(al);

  iord = RgM_inv_upper(ord);
  al2 = shallowcopy(al);
  gel(al2,7) = RgM_mul(gel(al,7), ord);
  gel(al2,8) = RgM_mul(iord, gel(al,8));

  mt = cgetg(n+1,t_VEC);
  gel(mt,1) = matid(n);
  for(i=2; i<=n; i++) {
    mtx = albasismultable(al,gel(ord,i));
    gel(mt,i) = RgM_mul(iord, RgM_mul(mtx, ord));
  }
  gel(al2,9) = mt;
  gel(al2,11)= altracebasis(al2);

  return al2;
}

GEN
al_changeorder(GEN al, GEN ord)
{
  pari_sp av = avma;
  GEN res = al_changeorder_shallow(al, ord);
  return gerepilecopy(av, res);
}

static GEN
alfromcenter(GEN al, GEN x)
{
  GEN nf = al_get_center(al);
  long n;
  switch(al_type(al)) {
    case al_CYCLIC:
      n = al_get_degree(al);
      break;
    case al_CSA:
      n = al_get_dim(al);
      break;
    default:
      return NULL;
  }
  return alalgtobasis(al, scalarcol(basistoalg(nf, x), n));
}

static GEN
alfromcenterhnf(GEN al, GEN x)
{
  GEN res;
  long i;
  if(x==gen_1) return cgetg(1,t_MAT);
  res = cgetg(lg(x), t_MAT);
  for(i=1; i<lg(x); i++) gel(res,i) = alfromcenter(al, gel(x,i));
  return res;
}

static GEN
alcenter_precompute(GEN al, GEN p)
{
  GEN nf, fa, pdec, nfprad, projs;
  long i, np;
  if(al_type(al)!=al_TABLE) {
    nf = al_get_center(al);
    fa = cgetg(3, t_MAT);
    pdec = idealprimedec(nf, p);
    settyp(pdec, t_COL);
    np = lg(pdec)-1;
    gel(fa,1) = pdec;
    gel(fa,2) = cgetg(np+1, t_COL);
    for(i=1; i<=np; i++) gcoeff(fa,i,2) = gen_1;
    nfprad = idealfactorback(nf,fa,NULL,0);
    projs = cgetg(np+1, t_VEC);
    for(i=1; i<=np; i++) gel(projs, i) = idealchinese(nf, fa, vec_ei(np,i));
  }
  else {
    nfprad = gen_0;
    projs = gen_0;
  }
  return mkvec2(nfprad, projs);
}

static GEN
alcenter_prad(GEN al, GEN p, GEN pre)
{
  GEN nfprad, zprad, mtprad;
  long i;
  nfprad = gel(pre,1);
  if(gequal0(nfprad)) return cgetg(1,t_MAT);
  zprad = alfromcenterhnf(al, nfprad);
  zprad = FpM_image(zprad, p);
  mtprad = cgetg(lg(zprad), t_VEC);
  for(i=1; i<lg(zprad); i++) gel(mtprad, i) = albasismultable(al, gel(zprad,i));
  mtprad = shallowmatconcat(mtprad);
  zprad = FpM_image(mtprad, p);
  return zprad;
}

static GEN
alcenter_p_projs(GEN al, GEN p, GEN pre)
{
  GEN projs, zprojs;
  long i;
  projs = gel(pre,2);
  if(gequal0(projs)) return gen_1;
  zprojs = cgetg(lg(projs), t_VEC);
  for(i=1; i<lg(projs); i++) gel(zprojs,i) = FpC_red(alfromcenter(al, gel(projs,i)),p);
  return zprojs;
}

/*al is assumed to be simple*/
static GEN
al_pmaximal_i(GEN al, GEN p)
{
  GEN al2, prad, lord = gen_0, I, id, dec, zprad, projs, pre;
  long n, i;
  n = al_get_absdim(al);
  id = matid(n);
  al2 = al;

  pre = alcenter_precompute(al,p);

  while (1) {
    zprad = alcenter_prad(al2, p, pre);
    projs = alcenter_p_projs(al2, p, pre);
    prad = alpradical_i(al2,p,zprad,projs);
    if (typ(prad) == t_INT) break;
    lord = alleftordermodp(al2,prad,p);
    if (!cmp_universal(lord,id)) break;
    al2 = al_change_overorder_shallow(al2,lord);
  }

  dec = alpdecompose0(al2,prad,p);/*TODO +zprad, projs*/
  while (lg(dec)>2) {
    for (i=1; i<lg(dec); i++) {
      I = gel(dec,i);
      lord = alleftordermodp(al2,I,p);
      if (cmp_universal(lord,matid(n))) break;
    }
    if (i==lg(dec)) break;
    al2 = al_change_overorder_shallow(al2,lord);
    zprad = alcenter_prad(al2, p, pre);
    projs = alcenter_p_projs(al2, p, pre);
    dec = alpdecompose_i(al2,p,zprad,projs);
  }
  return al2;
}
GEN
al_pmaximal(GEN al, GEN p)
{
  pari_sp av = avma;
  return gerepilecopy(av, al_pmaximal_i(al, p));
}

GEN
altracematrix(GEN al)
{
  GEN M, mt;
  long n, i, j;
  n = al_get_absdim(al);
  mt = al_get_multable(al);
  M = cgetg(n+1, t_MAT);
  for (i=1; i<=n; i++)
  {
    gel(M,i) = cgetg(n+1,t_MAT);
    for (j=1; j<=i; j++)
      gcoeff(M,j,i) = gcoeff(M,i,j) = alabstrace(al,gmael(mt,i,j));
  }
  return M;
}
GEN
aldisc(GEN al)
{
  pari_sp av = avma;
  checkal(al);
  return gerepileuptoint(av, ZM_det(altracematrix(al)));
}
GEN
al_maximal(GEN al)
{
  pari_sp av = avma;
  GEN fa = absi_factor(aldisc(al));
  return gerepilecopy(av, al_maximal_primes(al, gel(fa,1)));
}

/** IDEALS **/

/*
TODO :

lattice :
inter
add
mul
(A:B)
index (ideal from base field)
subset
mul by an ideal from base field

full lattice / ideal ?
leftorder/right
norm (reduced)
norm abs
test (isfulllattice, isideal)
2elt rep
mul with 2elt repr
+ with hnfmod ?
invert
2sidedpart/primitivepart
idealprimedec for two-sided above a prime
factorization : two-sided part + intersection of p-power-norm ideals,
for which we give a loc HNF

approx

orders :
test (isorder)
disc (different ?) (rnfdisc)
pmaximal
connecting ideal
loc splitting
*/

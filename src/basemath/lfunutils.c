/* Copyright (C) 2015  The PARI group.

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
/**                 L-functions: Applications                      **/
/**                                                                **/
/********************************************************************/

#include "pari.h"
#include "paripriv.h"

static GEN
tag(GEN x, long t) { return mkvec2(mkvecsmall(t), x); }

/* v a t_VEC of length > 1 */
static int
is_tagged(GEN v)
{
  GEN T = gel(v,1);
  return (lg(T)==3 && typ(gel(T,1))==t_VECSMALL);
}
static void
checkldata(GEN ldata)
{
  GEN vga, w, N;
#if 0 /* assumed already checked and true */
  long l = lg(ldata);
  if (typ(ldata)!=t_VEC || l < 7 || l > 8 || !is_tagged(ldata))
    pari_err_TYPE("checkldata", ldata);
#endif
  vga = ldata_get_gammavec(ldata);
  if (typ(vga) != t_VEC) pari_err_TYPE("checkldata [gammavec]",vga);
  w = gel(ldata, 4); /* FIXME */
  if (typ(w) != t_INT) pari_err_TYPE("checkldata [weight]",w);
  N = ldata_get_conductor(ldata);
  if (typ(N) != t_INT) pari_err_TYPE("checkldata [conductor]",N);
}

/* data may be either an object (polynomial, elliptic curve, etc...)
 * or a description vector [an,sd,Vga,k,conductor,rootno,{poles}]. */
GEN
lfuncreate(GEN data)
{
  long lx = lg(data);
  if (typ(data)==t_VEC && (lx == 7 || lx == 8))
  {
    GEN ldata;
    if (is_tagged(data)) ldata = gcopy(data);
    else
    { /* tag first component as t_LFUN_GENERIC */
      ldata = gcopy(data);
      gel(ldata, 1) = tag(gel(ldata,1), t_LFUN_GENERIC);
    }
    checkldata(ldata); return ldata;
  }
  return lfunmisc_to_ldata(data);
}

/********************************************************************/
/**                     Simple constructors                        **/
/********************************************************************/
GEN
vecan_mul(GEN an, long n, long prec)
{
  pari_sp ltop = avma;
  GEN p1 = ldata_vecan(gel(an,1), n, prec);
  GEN p2 = ldata_vecan(gel(an,2), n, prec);
  return gerepileupto(ltop, dirmul(p1, p2));
}

GEN
lfunconvol(GEN a1, GEN a2)
{ return tag(mkvec2(a1, a2), t_LFUN_MUL); }

GEN
vecan_div(GEN an, long n, long prec)
{
  pari_sp ltop = avma;
  GEN p1 = ldata_vecan(gel(an,1), n, prec);
  GEN p2 = ldata_vecan(gel(an,2), n, prec);
  return gerepileupto(ltop, dirdiv(p1, p2));
}

static GEN
lfunconvolinv(GEN a1, GEN a2)
{ return tag(mkvec2(a1,a2), t_LFUN_DIV); }

static GEN
lfunmulpoles(GEN ldata1, GEN ldata2, long prec)
{
  long k = ldata_get_k(ldata1), l, j;
  GEN r1 = ldata_get_residue(ldata1);
  GEN r2 = ldata_get_residue(ldata2), r;

  if (r1 && typ(r1) != t_VEC) r1 = mkvec(mkvec2(stoi(k), r1));
  if (r2 && typ(r2) != t_VEC) r2 = mkvec(mkvec2(stoi(k), r2));
  if (!r1)
  {
    if (!r2) return NULL;
    r1 = lfunrtopoles(r2);
  }
  else
  {
    r1 = lfunrtopoles(r1);
    if (r2) r1 = setunion(r1, lfunrtopoles(r2));
  }
  l = lg(r1); r = cgetg(l, t_VEC);
  for (j = 1; j < l; j++)
  {
    GEN be = gel(r1,j);
    GEN z1 = lfun(ldata1,be,prec), z2 = lfun(ldata2,be,prec);
    if (typ(z1) == t_SER && typ(z2) == t_SER)
    { /* pole of both, recompute to needed seriesprecision */
      long e = valp(z1) + valp(z2);
      GEN b = RgX_to_ser(deg1pol_shallow(gen_1, be, 0), 3-e);
      z1 = lfun(ldata1,b,prec);
      z2 = lfun(ldata2,b,prec);
    }
    gel(r,j) = mkvec2(be, gmul(z1, z2));
  }
  return r;
}

GEN
lfunmul(GEN ldata1, GEN ldata2, long prec)
{
  pari_sp ltop = avma;
  GEN r, N, Vga, sd, eno, a1a2, LD;
  long k;
  ldata1 = lfunmisc_to_ldata_shallow(ldata1);
  ldata2 = lfunmisc_to_ldata_shallow(ldata2);
  k = ldata_get_k(ldata1);
  if (ldata_get_k(ldata2) != k)
    pari_err_OP("lfunmul [weight]",ldata1, ldata2);
  r = lfunmulpoles(ldata1, ldata2, prec);
  N = gmul(ldata_get_conductor(ldata1), ldata_get_conductor(ldata2));
  Vga = vecsort0(concat(ldata_get_gammavec(ldata1), ldata_get_gammavec(ldata2)), NULL, 0);
  eno = gmul(ldata_get_rootno(ldata1), ldata_get_rootno(ldata2));
  sd = stoi((ldata_get_selfdual(ldata1) + ldata_get_selfdual(ldata2) + 1)/2);
  a1a2 = lfunconvol(ldata_get_an(ldata1), ldata_get_an(ldata2));
  LD = mkvecn(7, a1a2, sd, Vga, stoi(k), N, eno, r);
  if (!r) setlg(LD,7);
  return gerepilecopy(ltop, LD);
}

static GEN
lfundivpoles(GEN ldata1, GEN ldata2, long prec)
{
  long k = ldata_get_k(ldata1), i, j, l;
  GEN r1 = ldata_get_residue(ldata1);
  GEN r2 = ldata_get_residue(ldata2), r;

  if (r1 && typ(r1) != t_VEC) r1 = mkvec(mkvec2(stoi(k), r1));
  if (r2 && typ(r2) != t_VEC) r2 = mkvec(mkvec2(stoi(k), r2));
  if (!r1) return NULL;
  r1 = lfunrtopoles(r1);
  l = lg(r1); r = cgetg(l, t_VEC);
  r = cgetg(l, t_VEC);
  for (i = j = 1; j < l; j++)
  {
    GEN be = gel(r1,j);
    GEN z = gdiv(lfun(ldata1,be,prec), lfun(ldata2,be,prec));
    if (valp(z) < 0) gel(r,i++) = mkvec2(be, z);
  }
  if (i == 1) return NULL;
  setlg(r, i); return r;
}

GEN
lfundiv(GEN ldata1, GEN ldata2, long prec)
{
  pari_sp ltop = avma;
  GEN r, N, v, v1, v2, sd, eno, a1a2, LD;
  long k, j, j1, j2, l1, l2;
  ldata1 = lfunmisc_to_ldata_shallow(ldata1);
  ldata2 = lfunmisc_to_ldata_shallow(ldata2);
  k = ldata_get_k(ldata1);
  if (ldata_get_k(ldata2) != k)
    pari_err_OP("lfundiv [weight]",ldata1, ldata2);
  r = lfundivpoles(ldata1, ldata2, prec);
  N = gdiv(ldata_get_conductor(ldata1), ldata_get_conductor(ldata2));
  if (typ(N) != t_INT) pari_err_OP("lfundiv [conductor]",ldata1, ldata2);
  a1a2 = lfunconvolinv(ldata_get_an(ldata1), ldata_get_an(ldata2));
  sd = stoi((ldata_get_selfdual(ldata1) + ldata_get_selfdual(ldata2) + 1)/2);
  eno = gdiv(ldata_get_rootno(ldata1), ldata_get_rootno(ldata2));
  v1 = shallowcopy(ldata_get_gammavec(ldata1));
  v2 = ldata_get_gammavec(ldata2);
  l1 = lg(v1); l2 = lg(v2);
  for (j2 = 1; j2 < l2; j2++)
  {
    for (j1 = 1; j1 < l1; j1++)
      if (gel(v1,j1) && gequal(gel(v1,j1), gel(v2,j2)))
      {
        gel(v1,j1) = NULL; break;
      }
    if (j1 == l1) pari_err_OP("lfundiv [Vga]",ldata1, ldata2);
  }
  v = cgetg(l1-l2+1, t_VEC);
  for (j1 = j = 1; j1 < l1; j1++)
    if (gel(v1, j1)) gel(v,j++) = gel(v1,j1);

  LD = mkvecn(7, a1a2, sd, v, stoi(k), N, eno, r);
  if (!r) setlg(LD,7);
  return gerepilecopy(ltop, LD);
}

/*****************************************************************/
/*  L-series of Dirichlet characters.                            */
/*****************************************************************/

static GEN
lfunzeta(void)
{
  GEN zet = mkvecn(7, NULL, gen_0, NULL, gen_1, gen_1, gen_1, gen_1);
  gel(zet,1) = tag(gen_1, t_LFUN_ZETA);
  gel(zet,3) = mkvec(gen_0);
  return zet;
}
static GEN
lfunzetainit_bitprec(GEN dom, long der, long bitprec)
{ return lfuninit_bitprec(lfunzeta(), dom, der, bitprec); }

GEN
vecan_chivec(GEN an, long n, long prec)
{
  pari_sp ltop = avma;
  long N, i;
  ulong ord = itou(gel(an,1));
  GEN c, chi = gel(an,2), z = gpowers(expIr(divru(Pi2n(1,prec), ord)), ord);

  N = lg(chi)-1;
  c = cgetg(n+1, t_VEC);
  for (i = 1; i <= n; ++i)
  {
    if (ugcd(i, N) > 1)
      gel(c,i) = gen_0;
    else
    {
      ulong ind = 1 + itou(gel(chi, (i-1)%N + 1)) % ord;
      gel(c,i) = gel(z,ind);
    }
  }
  return gerepilecopy(ltop, c);
}

static GEN
lfunchivec(GEN CHI)
{
  pari_sp ltop = avma;
  GEN sig = NULL, an, r, chi = gel(CHI,2);
  long n, rn, s, N = lg(chi) - 1;

  if (N == 1) return lfunzeta();
  n = itos(gel(CHI,1)); /* order(chi) */
  s = Fl_double(umodiu(ZV_content(chi), n), n);
  rn = umodiu(gel(chi, N-1), n); /* chi(-1) = zeta^rn */
  if (rn == 0) sig = gen_0;
  else if (2*rn == n) sig = gen_1;
  else pari_err_TYPE("lfunchivec [abs(chi(-1)) != 1]", CHI);
  an = tag(CHI, t_LFUN_CHIVEC);
  r = mkvecn(6, an, (s? gen_1: gen_0), mkvec(sig), gen_1, stoi(N), gen_0);
  return gerepilecopy(ltop, r);
}

GEN
vecan_Kronecker(GEN D, long n)
{
  GEN v = cgetg(n+1, t_VEC);
  long i, d = minss(itou_or_0(D), n);
  for (i = 1; i <= d; i++) gel(v, i) = stoi(krois(D,i));
  for (; i <= n; ++i) gel(v, i) = gel(v, (i-1)%d + 1);
  return v;
}

static GEN
lfunchiquad(GEN D)
{
  GEN r;
  if (equali1(D)) return lfunzeta();
  if (!isfundamental(D)) pari_err_TYPE("lfunchiquad [not primitive]", D);
  r = mkvecn(6, NULL, gen_0, NULL, gen_1, NULL, gen_1);
  gel(r,1) = tag(icopy(D), t_LFUN_KRONECKER);
  gel(r,3) = mkvec(signe(D) < 0? gen_1: gen_0);
  gel(r,5) = mpabs(D);
  return r;
}

/* Quad: 0, Vec: 1, else: -1 */
static long
lfunchitype(GEN CHI)
{
  switch(typ(CHI))
  {
    case t_INT: return 0;
    case t_VEC:
      if (lg(CHI) == 3 && typ(gel(CHI,1)) == t_INT
        && typ(gel(CHI,2)) == t_VEC && RgV_is_ZV(gel(CHI,2))) return 1;
    default: return -1;
  }
}

static GEN
lfunchi(GEN CHI)
{
  switch(lfunchitype(CHI))
  {
    case 0: return lfunchiquad(CHI);
    case 1: return lfunchivec(CHI);
  }
  pari_err_TYPE("lfunchi", CHI);
  return NULL;
}

/* Begin Hecke characters. Here a character is assumed to be given by a
   vector on the generators of the ray class group clgp of CL_m(K).
   If clgp = [h,[d1,...,dk],[g1,...,gk]] with dk|...|d2|d1, a character chi
   is given by [a1,a2,...,ak] such that chi(gi)=\zeta_di^ai. */

/* Is character chi compatible with the group G.
 * Here G can be any finite abelian group [h, cyc, gens]. */
static void
chigencheck(GEN G, GEN chi)
{
  GEN cyc;
  long lcyc, i;
  if (lg(G) < 4) pari_err_TYPE("chigencheck [no generators]", chi);
  cyc = abgrp_get_cyc(G); lcyc = lg(cyc);
  if (typ(chi) != t_VEC || lg(chi) != lcyc) pari_err_TYPE("chigencheck", chi);
  for (i = 1; i < lcyc; ++i)
    if (typ(gel(chi,i)) != t_INT) pari_err_TYPE("chigencheck", chi);
}


static GEN
cyc_get_d1(GEN cyc) {return lg(cyc) == 1 ? gen_1 : gel(cyc, 1);}

/* Value of CHI on x. bnr is either a 6 component vector output by bnrinit(,,1)
   or a 2 component vector [nf, bid] where bid is output by idealstar with
   nonzero flag. */
/* If prec = 0, return exponent of zeta_d1, otherwise complex value. */
/* if ssd < 0, consider that the result is real. */
static GEN
chigeneval(GEN bnr, GEN CHI, GEN x, long ssd, long prec)
{
  pari_sp ltop = avma;
  GEN N, p1, e, nf, G, cyc, d1, res;
  long i;

  nf = bnr_get_nf(bnr);
  G = bnr_get_clgp(bnr);
  N = gel(bnr_get_mod(bnr), 1);
  if (!gequal1(idealnorm(nf, idealadd(nf, x, N))))
  {
    if (!ssd) pari_err_COPRIME("chigeneval",x,N);
    return gen_0;
  }
  cyc = abgrp_get_cyc(G);
  if (lg(cyc) == 1) return ssd ? gen_1 : gen_0;
  d1 = cyc_get_d1(cyc);
  e = isprincipalray(bnr, x);
  p1 = gen_0;
  for (i = 1; i < lg(e); ++i)
    p1 = addii(p1, mulii(mulii(gel(CHI,i), gel(e,i)), divii(d1, gel(cyc,i))));
  if (!prec) res = modii(p1, d1);
  else
  {
    GEN a = divri(mulri(Pi2n(1,prec), p1), d1);
    res = (ssd < 0) ? gcos(a, prec) : expIr(a);
  }
  return gerepileupto(ltop, res);
}

GEN
vecan_chigen(GEN an, long n, long prec)
{
  pari_sp ltop = avma;
  forprime_t iter;
  GEN bnr = gel(an,1), CHI = gel(an,2), gp = cgetipos(3);
  GEN nf = bnr_get_nf(bnr);
  GEN v = vec_ei(n, 1);
  long ssd = itos(gel(an, 3));

  u_forprime_init(&iter, 2, n);
  if (nf_get_degree(nf) == 1)
    while ((gp[2] = u_forprime_next(&iter)))
    {
      GEN ch = chigeneval(bnr, CHI, gp, ssd, prec);
      ulong k, p = gp[2];
      for (k = p; k <= (ulong)n; k += p)
        gel(v, k) = gadd(gel(v, k), gmul(ch, gel(v, k/p)));
    }
  else
  {
    GEN BOUND = stoi(n);
    while ((gp[2] = u_forprime_next(&iter)))
    {
      GEN L = idealprimedec_limit_norm(nf, gp, BOUND);
      long j;
      for (j = 1; j < lg(L); j++)
      {
        GEN pr = gel(L, j), ch = chigeneval(bnr, CHI, pr, ssd, prec);
        ulong k, q = itou(pr_norm(pr));
        for (k = q; k <= (ulong)n; k += q)
          gel(v, k) = gadd(gel(v, k), gmul(ch, gel(v, k/q)));
      }
    }
  }
  return gerepilecopy(ltop, v);
}

static GEN lfunzetak_i(GEN T);
static GEN
vec01(long r1, long r2)
{
  long d = r1+r2, i;
  GEN v = cgetg(d+1,t_VEC);
  for (i = 1; i <= r1; i++) gel(v,i) = gen_0;
  for (     ; i <= d;  i++) gel(v,i) = gen_1;
  return v;
}
/* CHI primitive character */
static GEN
lfunchigen(GEN bnr, GEN CHI)
{
  pari_sp av = avma;
  GEN N, sd, ssd, sig, Ldchi, nf, G, cyc, NN;
  long r1, r2, n1, l, i;
  checkbnrgen(bnr);
  nf = bnr_get_nf(bnr);
  G = bnr_get_clgp(bnr); chigencheck(G, CHI);
  N = bnr_get_mod(bnr);
  n1 = lg(vec01_to_indices(gel(N,2))) - 1; /* vecsum(N[2]) */
  N = gel(N,1);
  NN = mulii(idealnorm(nf, N), absi(nf_get_disc(nf)));
  if (equali1(NN)) return gerepileupto(av, lfunzeta());
  if (gequal0(CHI)) return gerepilecopy(av, lfunzetak_i(bnr));
  nf_get_sign(nf,&r1,&r2);
  sig = vec01(r1+r2-n1,r2+n1);
  cyc = gel(G, 2); l = lg(cyc); sd = gen_0; ssd = gen_m1;
  for (i = 1; i < l; ++i)
    if (signe(modii(shifti(gel(CHI,i), 1), gel(cyc,i))))
    {
      sd = gen_1; ssd = gen_1; break;
    }
  Ldchi = mkvecn(6, tag(mkvec3(bnr,CHI,ssd), t_LFUN_CHIGEN),
                    sd, sig, gen_1, NN, gen_0);
  return gerepilecopy(av, Ldchi);
}

/* HNF of kernel of CHI on clgp. */
static GEN
chigenker(GEN clgp, GEN CHI)
{
  GEN cyc, d1, v, U;
  long lcyc, j;
  chigencheck(clgp, CHI); cyc = gel(clgp, 2); lcyc = lg(cyc);
  if (lcyc == 1) return cgetg(1, t_MAT);
  d1 = gel(cyc,1); v = cgetg(lcyc+1, t_VEC);
  for (j=1; j < lcyc; j++) gel(v,j) = mulii(gel(CHI,j), divii(d1,gel(cyc,j)));
  gel(v, j) = d1;
  U = gel(ZV_extgcd(v), 2); setlg(U, lcyc);
  for (j=1; j < lcyc; j++) setlg(gel(U,j), lcyc);
  return ZM_hnf(shallowconcat(U, scalarmat_shallow(d1,lcyc-1)));
}

/* Find all characters of clgp whose kernel contain group given by HNF HB. */
static GEN
chigenkerfind(GEN G, GEN HB)
{
  GEN cyc, res, cnj, chi, chc;
  long lcyc, i, k, m, h = itos(abgrp_get_no(G));

  if (h == 1) return mkvec2(cgetg(1,t_VEC), cgetg(1,t_VECSMALL));
  cyc = vec_to_vecsmall(abgrp_get_cyc(G));
  lcyc = lg(cyc);
  res = cgetg(h+1, t_VEC);
  cnj = cgetg(h+1, t_VECSMALL);
  chi = cgetg(lcyc, t_VECSMALL);
  chc = cgetg(lcyc, t_VECSMALL);
  for (m = 0, k = 1; m < h; m++)
  {
    long isc, n = m;
    pari_sp av;
    GEN CHI;
    for (i = 1; i < lcyc; ++i)
    {
      long d = cyc[i];
      long n0 = n % d;
      n = n / d;
      chi[i] = n0;
      chc[i] = n0 ? d-n0: 0;
    }
    isc = vecsmall_lexcmp(chc, chi);
    if (isc < 0) continue;
    CHI = vecsmall_to_vec(chi);
    av = avma;
    if (hnfdivide(chigenker(G,CHI), HB))
    {
      gel(res, k) = CHI;
      cnj[k] = isc; k++;
    }
    avma = av;
  }
  setlg(res, k);
  setlg(cnj, k); return mkvec2(res, cnj);
}

/* Compute primitive character equivalent to CHI. */
static GEN
chigenbnrtobnrs(GEN bnr, GEN bnrs)
{
  GEN G, gen, Gs, cycs, A, H, U, U2;
  long l, ls, j;
  G = bnr_get_clgp(bnr);   gen = abgrp_get_gen(G);   l = lg(gen);
  Gs= bnr_get_clgp(bnrs); cycs = abgrp_get_cyc(Gs); ls = lg(cycs);
  A = cgetg(l, t_MAT);
  for (j = 1; j < l; ++j) gel(A,j) = bnrisprincipal(bnrs, gel(gen,j), 0);
  H = ZM_hnfall(shallowconcat(A, diagonal_shallow(cycs)), &U, 1);
  if (!ZM_isidentity(H)) pari_err_BUG("chigenbnrtobnrs [non invertible H]");
  U2 = cgetg(ls, t_MAT);
  for (j = 1; j < ls; ++j)
  {
    GEN c = gel(U, j+l-1); setlg(c, l);
    gel(U2,j) = c;
  }
  return U2;
}

static GEN
chigenprimitive(GEN bnr, GEN CHI)
{
  GEN id, bnf, G, bid, idele, CHIs;
  GEN bnrs, Gs, gens, cycs, cyc, A, B;
  long l, ls, i;

  G = bnr_get_clgp(bnr); cyc = gel(G, 2); l = lg(cyc);
  id = bnrconductorofchar(bnr, CHI);
  bnf = bnr_get_bnf(bnr);
  bid = bnr_get_bid(bnr); idele = gel(bid, 1);
  if (gequal(id, idele)) return mkvec2(bnr, CHI);
  bnrs = Buchray(bnf, id, nf_INIT|nf_GEN);
  Gs = bnr_get_clgp(bnrs);
  cycs = abgrp_get_cyc(Gs);
  gens = abgrp_get_gen(Gs); ls = lg(gens);
  CHIs = cgetg(ls, t_VEC);
  A = cgetg(l, t_VEC);
  for (i = 1; i < l; ++i) gel(A,i) = gdiv(gel(CHI,i), gel(cyc,i));
  B = gmul(A, chigenbnrtobnrs(bnr,bnrs));
  for (i = 1; i < ls; ++i)
  {
    GEN d = gel(cycs, i), c = gmul(d, gel(B,i));
    if (typ(c) != t_INT) pari_err_BUG("chigenprimitive");
    gel(CHIs, i) = modii(c, d);
  }
  return mkvec2(bnrs, CHIs);
}

static GEN
lfunzetak_i(GEN T)
{
  GEN Vga, N, nf, bnf = checkbnf_i(T), r = gen_0/*unknown*/;
  long r1, r2;

  if (bnf)
    nf = bnf_get_nf(bnf);
  else
  {
    nf = checknf_i(T);
    if (!nf) nf = T = nfinit(T, DEFAULTPREC);
  }
  nf_get_sign(nf,&r1,&r2);
  N = absi(nf_get_disc(nf));
  if (bnf)
  {
    GEN h = bnf_get_no(bnf);
    GEN R = bnf_get_reg(bnf);
    long prec = nf_get_prec(nf);
    r = gdiv(gmul(mulir(shifti(h, r1+r2), powru(mppi(prec), r2)), R),
             mulur(bnf_get_tuN(bnf), gsqrt(N, prec)));
  }
  Vga = vec01(r1+r2,r2);
  return mkvecn(7, tag(T,t_LFUN_NF), gen_0, Vga, gen_1, N, gen_1, r);
}
static GEN
lfunzetak(GEN T)
{ pari_sp ltop = avma; return gerepilecopy(ltop, lfunzetak_i(T)); }

/* bnf = NULL: base field = Q */
GEN
lfunabelianrelinit_bitprec(GEN nfabs, GEN bnf, GEN polrel, GEN dom, long der, long bitprec)
{
  pari_sp ltop = avma;
  GEN cond, chi, cnj, res, bnr, M, domain;
  long l, i;
  long v = -1;

  if (bnf) bnf = checkbnf(bnf);
  else
  {
    v = fetch_var();
    bnf = Buchall(pol_x(v), 0, nbits2prec(bitprec));
  }
  if (typ(polrel) != t_POL) pari_err_TYPE("lfunabelianrelinit", polrel);
  cond = rnfconductor(bnf, polrel);
  chi = chigenkerfind(gel(cond,2), gel(cond,3));
  cnj = gel(chi,2);
  chi = gel(chi,1); l = lg(chi);
  bnr = Buchray(bnf, gel(cond,1), nf_INIT|nf_GEN);
  res = cgetg(l, t_VEC);
  for (i = 1; i < l; ++i)
  {
    GEN v = chigenprimitive(bnr, gel(chi, i));
    GEN L = lfunchigen(gel(v,1), gel(v,2));
    gel(res, i) = lfuninit_bitprec(L, dom, der, bitprec);
  }
  if (v >= 0) delete_var();
  M = mkvec3(res, const_vecsmall(l-1, 1), cnj);
  domain = mkvec2(dom, mkvecsmall2(der, bitprec));
  return gerepilecopy(ltop, lfuninit_make(t_LDESC_PRODUCT, lfunzetak_i(nfabs), M, domain));
}

GEN
lfunabelianrelinit(GEN nfabs, GEN bnf, GEN polrel, GEN dom, long der, long prec)
{
  return lfunabelianrelinit_bitprec(nfabs, bnf, polrel, dom, der, prec2nbits(prec));
}

/*****************************************************************/
/*                 Dedekind zeta functions                       */
/*****************************************************************/
static GEN
dirzetak0(GEN nf, ulong N)
{
  GEN vect, c, c2, T = nf_get_pol(nf), index = nf_get_index(nf);
  pari_sp av = avma, av2;
  const ulong SQRTN = (ulong)(sqrt(N) + 1e-3);
  ulong i, p, lx;
  long court[] = {evaltyp(t_INT)|_evallg(3), evalsigne(1)|evallgefint(3),0};
  forprime_t S;

  (void)evallg(N+1);
  c  = cgetalloc(t_VECSMALL, N+1);
  c2 = cgetalloc(t_VECSMALL, N+1);
  c2[1] = c[1] = 1; for (i=2; i<=N; i++) c[i] = 0;
  u_forprime_init(&S, 2, N);
  av2 = avma;
  while ( (p = u_forprime_next(&S)) )
  {
    avma = av2;
    if (umodiu(index, p)) /* p does not divide index */
    {
      vect = gel(Flx_degfact(ZX_to_Flx(T,p), p),1);
      lx = lg(vect);
    }
    else
    {
      GEN P;
      court[2] = p; P = idealprimedec(nf,court);
      lx = lg(P); vect = cgetg(lx,t_VECSMALL);
      for (i=1; i<lx; i++) vect[i] = pr_get_f(gel(P,i));
    }
    if (p <= SQRTN)
      for (i=1; i<lx; i++)
      {
        ulong qn, q = upowuu(p, vect[i]); /* Norm P[i] */
        if (!q || q > N) break;
        memcpy(c2 + 2, c + 2, (N-1)*sizeof(long));
        /* c2[i] <- c[i] + sum_{k = 1}^{v_q(i)} c[i/q^k] for all i <= N */
        for (qn = q; qn <= N; qn *= q)
        {
          ulong k0 = N/qn, k, k2; /* k2 = k*qn */
          for (k = k0, k2 = k*qn; k > 0; k--, k2 -=qn) c2[k2] += c[k];
          if (q > k0) break; /* <=> q*qn > N */
        }
        swap(c, c2);
      }
    else /* p > sqrt(N): simpler */
      for (i=1; i<lx; i++)
      {
        ulong k, k2; /* k2 = k*p */
        if (vect[i] > 1) break;
        /* c2[i] <- c[i] + sum_{k = 1}^{v_q(i)} c[i/q^k] for all i <= N */
        for (k = N/p, k2 = k*p; k > 0; k--, k2 -= p) c[k2] += c[k];
      }
  }
  avma = av;
  pari_free(c2); return c;
}

GEN
dirzetak(GEN nf, GEN b)
{
  GEN z, c;
  long n;

  if (typ(b) != t_INT) pari_err_TYPE("dirzetak",b);
  if (signe(b) <= 0) return cgetg(1,t_VEC);
  nf = checknf(nf);
  n = itou_or_0(b); if (!n) pari_err_OVERFLOW("dirzetak");
  c = dirzetak0(nf, n);
  z = vecsmall_to_vec(c); pari_free(c); return z;
}

static GEN
linit_get_mat(GEN linit)
{
  if (linit_get_type(linit)==t_LDESC_PRODUCT)
    return lfunprod_get_fact(linit_get_tech(linit));
  else
    return mkvec3(mkvec(linit), mkvecsmall(1), mkvecsmall(0));
}

static GEN
lfunproduct(GEN ldata, GEN linit1, GEN linit2, GEN domain)
{
  GEN M1 = linit_get_mat(linit1);
  GEN M2 = linit_get_mat(linit2);
  GEN M3 = mkvec3(shallowconcat(gel(M1, 1), gel(M2, 1)),
                  vecsmall_concat(gel(M1, 2), gel(M2, 2)),
                  vecsmall_concat(gel(M1, 3), gel(M2, 3)));
  return lfuninit_make(t_LDESC_PRODUCT, ldata, M3, domain);
}

/* Initialization without assuming Artin's conjecture. */
static GEN
lfunzetaKinit_bitprec(GEN T, GEN dom, long der, long bitprec)
{
  pari_sp ltop = avma;
  GEN ldata = lfunzetak_i(T);
  return gerepileupto(ltop, lfuninit_bitprec(ldata, dom, der, bitprec));
}

/* From now on we assume the Artin conjecture that z_K(s) is divisible by
* z_k(s) for all subfields k of K. The output is always a d-component
* vector of lfuninits (including d=1), of which we must take the product.
* nf is a true nf */
static GEN
lfunzetaKQinit_bitprec(GEN nf, GEN dom, long der, long bitprec)
{
  pari_sp ltop = avma;
  GEN an, Vga, ldata, N, LKQ, LQ, domain, T = nf_get_pol(nf);
  long r1, r2;

  LQ = lfunzetainit_bitprec(dom, der, bitprec);
  if (degpol(T) == 1) return LQ;
  N = absi(nf_get_disc(nf));
  nf_get_sign(nf,&r1,&r2);
  Vga = vec01(r1+r2-1,r2);
  an = tag(mkvec2(tag(nf, t_LFUN_NF), tag(gen_1, t_LFUN_ZETA)), t_LFUN_DIV);
  ldata = mkvecn(6, an, gen_0, Vga, gen_1, N, gen_1);
  LKQ = lfuninit_bitprec(ldata, dom, der, bitprec); /* zeta_K/zeta */
  domain = mkvec2(dom, mkvecsmall2(der, bitprec));
  return gerepilecopy(ltop, lfunproduct(lfunzetak_i(nf), LKQ, LQ, domain));
}

/* nf is a true nf */
static GEN
lfunzetaKkinit_bitprec(GEN nf, GEN dom, long der, long bitprec)
{
  pari_sp av = avma;
  GEN an, nfs, polk, nfk, Vga, ldata, N, Lk, LKk, domain;
  long r1k, r2k, r1, r2, nsub;

  nfs = nfsubfields(nf, 0);
  nsub = lg(nfs)-1;
  if (nsub <= 2)
    return gerepilecopy(av, lfunzetaKQinit_bitprec(nf, dom, der, bitprec));
  nf_get_sign(nf,&r1,&r2);
  polk = gel(gel(nfs, nsub-1), 1); /* k largest strict subfield, != Q */
  nfk = nfinit(polk, nbits2prec(bitprec));
  Lk = lfunzetakinit_bitprec(nfk, dom, der, 0, bitprec); /* zeta_k */
  nf_get_sign(nfk,&r1k,&r2k);
  Vga = vec01((r1+r2) - (r1k+r2k), r2-r2k);
  N = absi(diviiexact(nf_get_disc(nf), nf_get_disc(nfk)));
  an = tag(mkvec2(tag(nf,t_LFUN_NF), tag(nfk,t_LFUN_NF)), t_LFUN_DIV);
  ldata = mkvecn(6, an, gen_0, Vga, gen_1, N, gen_1);
  LKk = lfuninit_bitprec(ldata, dom, der, bitprec); /* zeta_K/zeta_k */
  domain = mkvec2(dom, mkvecsmall2(der, bitprec));
  return gerepilecopy(av, lfunproduct(lfunzetak_i(nf), Lk, LKk, domain));
}

/* If flag=0 (default), assume zeta_K divisible by zeta_k for all
   subfields k of K. If flag=1, only assume zeta_K divisible by zeta.
   If flag=2, do not assume anything. If flag=4, assume K/Q is abelian.
   If flag<0, do not assume anything and the output is the same as lfuninit,
   so can be used directly. */
GEN
lfunzetakinit_bitprec(GEN NF, GEN dom, long der, long flag, long bitprec)
{
  GEN nf = checknf(NF), T = nf_get_pol(nf);
  if (degpol(T) == 1) return lfunzetainit_bitprec(dom, der, bitprec);
  if (flag < 0)
    flag = 2;
  else if (flag != 4)
  {
    long v = fetch_var();
    if (rnfisabelian(pol_x(v), T)) flag = 4;
    delete_var();
  }
  switch(flag)
  {
    case 0: return lfunzetaKkinit_bitprec(nf, dom, der, bitprec);
    case 1: return lfunzetaKQinit_bitprec(nf, dom, der, bitprec);
    case 2: return lfunzetaKinit_bitprec(NF, dom, der, bitprec);
    case 4: return lfunabelianrelinit_bitprec(nf, NULL, T, dom, der, bitprec);
  }
  pari_err_FLAG("lfunzetakinit");
  return NULL;
}

GEN
lfunzetakinit(GEN pol, GEN dom, long der, long flag, long prec)
{
  return lfunzetakinit_bitprec(pol, dom, der, flag, prec2nbits(prec));
}

/***************************************************************/
/*             Elliptic Curves and Modular Forms               */
/***************************************************************/

static GEN
lfunell(GEN e)
{
  pari_sp av = avma;
  GEN ldata = cgetg(7, t_VEC);
  gel(ldata, 1) = tag(ellanal_globalred(e, NULL), t_LFUN_ELL);
  gel(ldata, 2) = gen_0;
  gel(ldata, 3) = mkvec2(gen_0, gen_1);
  gel(ldata, 4) = gen_2;
  gel(ldata, 5) = icopy(ellQ_get_N(e));
  gel(ldata, 6) = stoi(ellrootno_global(e));
  return gerepilecopy(av, ldata); /* ellanal_globalred not gerepile-safe */
}

GEN
lfunmfspec(GEN lmisc, long prec)
{
  pari_sp ltop = avma;
  GEN Vga, linit, ldataf, veven, vodd, om, op, eps, dom;
  long k, k2, sd, j;

  ldataf = lfunmisc_to_ldata_shallow(lmisc);
  k = ldata_get_k(ldataf);
  dom = mkvec3(dbltor(k/2.), dbltor((k-2)/2.), gen_0);
  if (is_linit(lmisc) && linit_get_type(lmisc) == t_LDESC_INIT
      && sdomain_isincl(dom, lfun_get_dom(linit_get_tech(lmisc))))
    linit = lmisc;
  else
    linit = lfuninit(ldataf, dom, 0, prec);
  sd = ldata_get_selfdual(ldataf);
  Vga = ldata_get_gammavec(ldataf);
  if (sd || !gequal(Vga, mkvec2(gen_0,gen_1)))
    pari_err_TYPE("lfunmfspec", lmisc);
  if (odd(k)) pari_err_IMPL("odd weight in lfunmfspec");
  k2 = k/2;
  vodd = cgetg(k2+1, t_VEC);
  veven = cgetg(k2, t_VEC);
  for (j = 1; j <= k2; ++j) gel(vodd,j) = lfunlambda(linit, stoi(2*j-1), prec);
  for (j = 1; j < k2; ++j) gel(veven,j) = lfunlambda(linit, stoi(2*j), prec);
  if (k > 2)
  {
    om = gel(veven,1);
    veven = gdiv(veven, om);
    op = gel(vodd,2);
  }
  else
  { /* veven empty */
    om = gen_1;
    op = gel(vodd,1);
  }
  vodd = gdiv(vodd, op);
  eps = int2n(prec2nbits(prec)/4);
  veven= bestappr(veven, eps);
  vodd = bestappr(vodd, eps);
  return gerepilecopy(ltop, mkvec4(veven, vodd, om, op));
}

/* Symmetric square of a Hecke eigenform, cuspform. Assume ldata is the ldata
of such a cusp form. Find the ldata of its symmetric square, and in particular
the conductor and bad Euler factors. */
GEN
vecan_symsq(GEN an, long nn, long prec)
{
  pari_sp ltop = avma;
  GEN res = cgetg(nn+1, t_VEC), veceul = gel(an, 1), ldata = gel(an, 2);
  GEN a = ldata_vecan(ldata_get_an(ldata), nn, prec);
  long k = ldata_get_k(ldata), lfa = lg(veceul), j, n;

  for (n = 1; n <= nn; ++n)
  {
    GEN D, S, h = gen_1;
    ulong q = 1;
    long lD;
    for (j = 1; j < lfa; ++j)
    {
      GEN v = gel(veceul,j), p = gel(v,1);
      long vj = u_pval(n, p);
      if (!vj) continue;
      q *= upowuu(itou(p), vj);
      h = gmul(h, gpowgs(gel(v,2), vj));
    }
    D = divisorsu(n/q); lD = lg(D);
    S = gen_0;
    for (j = 1; j < lD; ++j)
    {
      ulong m = D[j], mc = D[lD-j];
      long s = odd(bigomegau(m)) ? -1: 1;
      S = gadd(S, gmul(mulsi(s, powuu(m, k-1)), gsqr(gel(a, mc))));
    }
    gel(res, n) = gmul(h, S);
  }
  return gerepilecopy(ltop, res);
}

static long
ellsymsq_bad2(GEN c4, GEN c6, long e, long *pb2)
{
  switch (e)
  {
    case 2: *pb2 = 1; return 1;
    case 3: *pb2 = 2; return 0;
    case 5: *pb2 = 3; return 0;
    case 7: *pb2 = 4; return 0;
    case 8:
      if (dvdiu(c6,512)) { *pb2 = 4; return 0; }
      *pb2 = 3; return umodiu(c4,128)==32 ? 1 : -1;
    default: *pb2 = 0; return 0;
  }
}
static long
ellsymsq_bad3(GEN c4, GEN c6, long e, long *pb3)
{
  long c6_243, c4_81;
  switch (e)
  {
    case 2: *pb3 = 1; return 1;
    case 3: *pb3 = 2; return 0;
    case 5: *pb3 = 3; return 0;
    case 4: *pb3 = 2;
      c4_81 = umodiu(c4,81);
      if (c4_81 == 27) return -1;
      if (c4_81%27 != 9) return 1;
      c6_243 = umodiu(c6,243);
      return (c6_243==108 || c6_243==135)? -1: 1;
    default: *pb3 = 0; return 0;
  }
}
static int
c4c6_testp(GEN c4, GEN c6, GEN p)
{ GEN p2 = sqri(p); return (dvdii(c6,p2) && !dvdii(c4,p2)); }
/* assume e = v_p(N) >= 2 */
static long
ellsymsq_badp(GEN c4, GEN c6, GEN p, long e, long *pb)
{
  if (equaliu(p, 2)) return ellsymsq_bad2(c4, c6, e, pb);
  if (equaliu(p, 3)) return ellsymsq_bad3(c4, c6, e, pb);
  *pb = 1;
  switch(umodiu(p, 12UL))
  {
    case 1: return -1;
    case 5: return c4c6_testp(c4,c6,p)? -1: 1;
    case 7: return c4c6_testp(c4,c6,p)?  1:-1;
    default:return 1; /* p%12 = 11 */
  }
}
static GEN
ellsymsq(void *D, GEN p)
{
  GEN E = gel((GEN)D, 2);
  GEN T, ap = sqri(ellap(E, p));
  long e = Z_pval(ellQ_get_N(E), p);
  if (e)
  {
    if (e == 1)
      T = deg1pol_shallow(negi(ap),gen_1,0);
    else
    { /* N.B. Could get 'a' from veceul = D[1]: vector of pairs [p,a], e >= 2,
       * but cheaper to rederive */
      GEN c4 = ell_get_c4(E);
      GEN c6 = ell_get_c6(E);
      long junk, a = ellsymsq_badp(c4, c6, p, e, &junk);
      GEN pb = negi(mulis(p,a));
      GEN u1 = negi(addii(ap,pb));
      GEN u2 = mulii(ap,pb);
      T = mkpoln(3,u2,u1,gen_1);
    }
  }
  else
  {
    GEN u1 = subii(ap,p);
    GEN u2 = mulii(p,u1);
    GEN u3 = powiu(p,3);
    T = mkpoln(4,negi(u3),u2,negi(u1),gen_1);
  }
  return mkrfrac(gen_1,T);
}
GEN
vecan_ellsymsq(GEN an, long n)
{ GEN nn = stoi(n); return direuler((void*)an, &ellsymsq, gen_2, nn, nn); }

static GEN
lfunsymsqfind_ell(GEN e)
{
  pari_sp av = avma;
  GEN B, N, Nfa, P, E, V, c4, c6;
  long i, l, k;

  e = ellminimalmodel(e, NULL);
  ellQ_get_Nfa(e, &N, &Nfa);
  c4 = ell_get_c4(e);
  c6 = ell_get_c6(e);
  P = gel(Nfa,1); l = lg(P);
  E = gel(Nfa,2);
  V = cgetg(l, t_VEC);
  B = gen_1;
  for (i=k=1; i<l; i++)
  {
    GEN p = gel(P,i);
    long a, b, e = itos(gel(E,i));
    if (e == 1) { B = mulii(B, p); continue; }
    a = ellsymsq_badp(c4, c6, p, e, &b);
    B = mulii(B, powiu(p, b));
    gel(V,k++) = mkvec2(p, stoi(a));
  }
  setlg(V, k);
  return gerepilecopy(av, mkvec2(sqri(B), V));
}

/* Find conductor and missing Euler factors in symmetric square.
 * If flall is set, output all possibilities, otherwise only the first. */
static GEN
lfunsymsqfind(GEN ldata, long flall/*=0*/, long prec)
{
  pari_sp ltop = avma;
  GEN N, fa, an, D, veceul, vforsig, vforexp, vres, P,P1,P2, E,E2;
  long i1,i2, i, j, k, lmax, lP, bitprec = minss(128, prec2nbits(prec));

  ldata = lfunmisc_to_ldata_shallow(ldata);
  k = ldata_get_k(ldata);
  N = ldata_get_conductor(ldata);
  if (equali1(N)) return gerepilecopy(ltop, mkvec2(gen_1, cgetg(1, t_VEC)));
  fa = Z_factor(N);
  P = gel(fa,1); lP = lg(P);
  E = gel(fa,2);
  P1= cgetg(lP, t_COL);
  P2= cgetg(lP, t_COL);
  E2= cgetg(lP, t_COL);
  for (i1 = i2 = j = 1; j < lP; j++)
  {
    GEN p = gel(P,j);
    if (is_pm1(gel(E,j)))
      gel(P1,i1++) = p;
    else
    {
      gel(P2,i2) = p;
      gel(E2,i2) = gel(E,j); i2++;
    }
  }
  setlg(P1, i1);
  setlg(P2, i2); setlg(E2, i2);
  lmax = i1 > 1 ? itos(vecmax(P1)) : 1;
  an = ldata_vecan(ldata_get_an(ldata), lmax, prec);
  for (j = 1; j < i1; ++j)
  {
    GEN p = gel(P1,j);
    gel(P1,j) = mkvec2(p, gsqr(gel(an, itou(p))));
  }
  if (i2 == 1) return gerepilecopy(ltop, mkvec2(sqri(N), P1));
  vforsig = const_vec(i2-1, mkvec2(gen_m1, gen_1));
  vforexp = cgetg(i2, t_VEC);
  for (j = 1; j < i2; ++j)
  {
    long l, m;
    switch(itou_or_0(gel(P2,j)))
    {
      case 2: l = 6; break;
      case 3: l = 4; break;
      default:l = 2; break;
    }
    m = minss(k-1, l*itos(gel(E2,j)));
    gel(vforexp, j) = mkvec2(gen_0, stoi(m));
  }
  vres = cgetg(1, t_VEC);
  D = divisors(mkmat2(P2,E2));
  for (i = 1; i < lg(D); i++)
  {
    GEN M = gel(D, i), vsig;
    forvec_t iter;

    forvec_init(&iter, vforsig, 0);
    while ((vsig = forvec_next(&iter)))
    {
      GEN vexp, vforexptmp = shallowcopy(vforexp);
      forvec_t iter2;
      long jj;

      for (jj = 1; jj < i2; ++jj)
        if (gequal0(gel(vsig, jj))) gel(vforexptmp, jj) = mkvec2(gen_0, gen_0);
      forvec_init(&iter2, vforexptmp, 0);
      while ((vexp = forvec_next(&iter2)))
      {
        GEN V = cgetg(i2, t_VEC), M2 = sqri(diviiexact(N,M)), L;
        long m;
        for (m = 1; m < i2; m++)
        {
          GEN p = gel(P2,m), vm = mulii(gel(vsig,m), powii(p, gel(vexp,m)));
          gel(V, m) = mkvec2(p, vm);
        }
        veceul = shallowconcat(P1, V);
        L = mkvecn(6, tag(mkvec2(veceul, ldata), t_LFUN_SYMSQ),
              gen_0, mkvec3(stoi(2-k), gen_0, gen_1), stoi(2*k-1), M2, gen_1);
        if (lfuncheckfeq_bitprec(L, NULL, bitprec)  < -bitprec/2)
        {
          GEN z = mkvec2(M2, lexsort(veceul));
          if (!flall) return gerepilecopy(ltop, z);
          vres = concat(vres, mkvec(z));
        }
      }
    }
  }
  if (lg(vres) == 1) pari_err_BUG("lfunsymsqfind [cannot find sym2]");
  if (lg(vres)>2) pari_warn(warner,"several possibilities in lfunsymsqfind\n");
  return gerepilecopy(ltop, vres);
}

GEN
lfunsymsq(GEN ldata, GEN known, long prec)
{
  pari_sp ltop = avma;
  GEN L, N, V;
  long k;
  ldata = lfunmisc_to_ldata_shallow(ldata);
  if (!lfunisvgaell(ldata_get_gammavec(ldata), 0))
    pari_err_TYPE("lfunsymsq", ldata);
  if (known && (!is_vec_t(typ(known)) || lg(known) != 3))
    pari_err_TYPE("lfunsymsq",known);
  if (!known) known = lfunsymsqfind(ldata, 0, prec);
  N = gel(known,1);
  V = gel(known,2);
  k = ldata_get_k(ldata);
  L = mkvecn(6, tag(mkvec2(V, ldata), t_LFUN_SYMSQ), gen_0,
                mkvec3(stoi(2-k), gen_0, gen_1), stoi(2*k-1), N, gen_1);
  return gerepilecopy(ltop, L);
}

static GEN
lfunellsymsq(GEN E)
{
  pari_sp ltop = avma;
  long k = 2;
  GEN ld, known, N, V;
  checkell_Q(E);
  E = ellanal_globalred(E, NULL);
  known = lfunsymsqfind_ell(E);
  N = gel(known,1);
  V = gel(known,2);
  ld = mkvecn(6, tag(mkvec2(V, E), t_LFUN_SYMSQ_ELL), gen_0,
                 mkvec3(stoi(2-k), gen_0, gen_1), stoi(2*k-1), N, gen_1);
  return gerepilecopy(ltop, ld);
}

static long
lfunissymsq(GEN Vga)
{ return (lg(Vga) == 4) && lfunisvgaell(mkvec2(gel(Vga,2), gel(Vga,3)), 0); }

GEN
lfunsymsqspec(GEN lmisc, long prec)
{
  pari_sp ltop = avma;
  GEN veven, vpi, om2, M, Vga, ldata;
  long k, l1, j, fl = 2;
  ldata = lfunmisc_to_ldata_shallow(lmisc);
  Vga = ldata_get_gammavec(ldata);
  /* fl = 0: OK, 1: perform lfuninit, 2: perform lfunsymsq + lfuninit */
  if (is_linit(lmisc) && linit_get_type(lmisc) == t_LDESC_INIT)
  { /* FIXME: should check for prec ! */
    if (lfunissymsq(Vga)) fl = 0;
    else if (!lfunisvgaell(Vga, 0)) pari_err_TYPE("lfunsymsqspec", lmisc);
  }
  else switch(ldata_get_type(ldata))
  {
    case t_LFUN_ETA: break;
    case t_LFUN_SYMSQ:
    case t_LFUN_SYMSQ_ELL: fl = 1; break;
    case t_LFUN_GENERIC:
      if (lfunissymsq(Vga)) { fl = 1; break; }
      if (lfunisvgaell(Vga, 0)) break;
    default: pari_err_TYPE("lfunsymsqspec", lmisc);
  }
  switch(fl)
  {
    GEN dom;
    case 2: ldata = lfunsymsq(ldata, NULL, prec); /* fall through */
    case 1: /* now ldata is a symsq */
      k = ldata_get_k(ldata);
      dom = mkvec3(dbltor((k+1)/2.), dbltor(3*(k+1)/4.), gen_0);
      ldata = lfuninit(ldata, dom, 0, prec);
      break;
    default:
      ldata = lmisc;
      k = ldata_get_k(linit_get_ldata(ldata));
  }
  /* Warning: k is the weight of the symmetric square, not of the form. */
  l1 = (k+1)/4;
  veven = cgetg(l1+1, t_VEC);
  om2 = greal(lfunlambda(ldata, stoi((k+1)/2), prec));
  vpi = gpowers(mppi(prec), l1); /* could be powersshift(,om2) */
  gel(veven,1) = gen_1;
  M = int2n(prec2nbits(prec)/4);
  for (j = 2; j <= l1; ++j)
  {
    GEN Lj = greal(lfunlambda(ldata, stoi(2*j + (k-3)/2), prec));
    Lj = gdiv(Lj, gmul(gel(vpi,j), om2));
    gel(veven, j) = bestappr(Lj, M);
  }
  return gerepilecopy(ltop, mkvec2(veven, om2));
}

static GEN
mfpeters(GEN ldata2, GEN fudge, GEN N, long k, long bitprec)
{
  GEN t, L = greal(lfun_bitprec(ldata2, stoi(k), bitprec));
  long prec = nbits2prec(bitprec);
  t = powrs(mppi(prec), k+1); shiftr_inplace(t, 2*k-1); /* Pi/2 * (4Pi)^k */
  return gmul(gdiv(gmul(mulii(N,mpfact(k-1)), fudge), t), L);
}
/* Petersson square of modular form. ldata must be the
   data of the modular form itself. */
GEN
lfunmfpeters_bitprec(GEN ldata, long bitprec)
{
  pari_sp av = avma;
  GEN ldata2, veceuler, N, fudge = gen_1;
  long k, j;
  long prec = nbits2prec(bitprec);

  ldata = lfunmisc_to_ldata_shallow(ldata);
  if (!lfunisvgaell(ldata_get_gammavec(ldata),0))
    pari_err_TYPE("lfunmfpeters", ldata);
  k = ldata_get_k(ldata);
  N = ldata_get_conductor(ldata);
  ldata2 = lfunsymsq(ldata, NULL, prec);
  veceuler = gmael3(ldata2, 1, 2, 1);
  for (j = 1; j < lg(veceuler); ++j)
  {
    GEN v = gel(veceuler, j), p = gel(v,1), q = powis(p,1-k), s = gel(v,2);
    if (dvdii(N, sqri(p))) fudge = gmul(fudge, gaddsg(1, gmul(s, q)));
  }
  return gerepileupto(av, mfpeters(ldata2,fudge,N,k,bitprec));
}

GEN
lfunmfpeters(GEN ldata, long prec)
{ return lfunmfpeters_bitprec(ldata, prec2nbits(prec)); }

static GEN
lfunellmfpeters_bitprec(GEN E, long bitprec)
{
  pari_sp av = avma;
  GEN ldata2, veceuler, N = ellQ_get_N(E), fudge = gen_1;
  long j, k = 2;

  ldata2 = lfunellsymsq(E);
  veceuler = gmael3(ldata2, 1, 2, 1);
  for (j = 1; j < lg(veceuler); j++)
  {
    GEN v = gel(veceuler,j), p = gel(v,1), q = powis(p,1-k);
    long s = signe(gel(v,2));
    if (s) fudge = gmul(fudge, s==1 ? gaddsg(1, q): gsubsg(1, q));
  }
  return gerepileupto(av, mfpeters(ldata2,fudge,N,k,bitprec));
}

/* From Christophe Delaunay, http://delaunay.perso.math.cnrs.fr/these.pdf */
static GEN
elldiscfix(GEN E, GEN Et, GEN D)
{
  GEN N = ellQ_get_N(E), Nt = ellQ_get_N(Et);
  GEN P = gel(Z_factor(absi(D)), 1);
  GEN f = gen_1;
  long i, l = lg(P);
  for (i=1; i < l; i++)
  {
    GEN r, p = gel(P,i);
    long v = Z_pval(N, p), vt = Z_pval(Nt, p);
    if (v <= vt) continue;
    /* v > vt */
    if (equaliu(p, 2))
    {
      if (vt == 0 && v >= 4)
        r = shifti(subsi(9, sqri(ellap(Et, p))), v-3);  /* 9=(2+1)^2 */
      else if (vt == 1)
        r = gmul2n(utoipos(3), v-3);  /* not in Z if v=2 */
      else if (vt >= 2)
        r = int2n(v-vt);
      else
        r = gen_1; /* vt = 0, 1 <= v <= 3 */
    }
    else if (vt >= 1)
      r = gdiv(subis(sqri(p), 1), p);
    else
      r = gdiv(mulii(subis(p, 1), subii(sqri(addis(p, 1)), sqri(ellap(Et, p)))), p);
    f = gmul(f, r);
  }
  return f;
}

/* Modular degree of elliptic curve e over Q, assuming Manin constant = 1
   (otherwise multiply by square of Manin constant). */
GEN
ellmoddegree(GEN e, long prec)
{
  pari_sp ltop = avma;
  long bitprec = prec2nbits(prec);
  GEN E = ellminimalmodel(e, NULL);
  GEN D = ellminimaltwistcond(E);
  GEN Etr = ellinit(elltwist(E, D), NULL, prec);
  GEN Et = ellminimalmodel(Etr, NULL);
  GEN nor = lfunellmfpeters_bitprec(Et, bitprec);
  GEN degt = gdiv(gmul(nor, sqrr(Pi2n(1,prec))), member_area(E));
  GEN deg = gmul(degt, elldiscfix(E, Et, D));
  GEN degr = bestappr(deg, int2n(bitprec>>1));
  long err = gexpo(gsub(gen_1, gdiv(deg,degr)));
  obj_free(Etr); obj_free(Et); obj_free(E);
  return gerepilecopy(ltop, mkvec2(degr, stoi(err)));
}

/*************************************************************/
/*                        ETA QUOTIENTS                      */
/* An eta quotient is a matrix with 2 columns [m, r_m] with  */
/* m >= 1 representing f(\tau)=\prod_m\eta(m\tau)^{r_m}.     */
/*************************************************************/

static GEN
eta_inflate_ZXn(long m, long v)
{
  long n, k;
  GEN P = cgetg(m+2,t_POL);
  P[1] = 0;
  for(n = 0; n < m; n++) gel(P,n+2) = gen_0;
  for(n = 0;; n++)
  {
    k = v * (((3*n - 1) * n) >> 1);
    if (k >= m) break;
    gel(P, 2+k) = odd(n)? gen_m1: gen_1;
    k += n*v; /* v * (3*n + 1) * n / 2 */;
    if (k >= m) break;
    gel(P, 2+k) = odd(n)? gen_m1: gen_1;
  }
  return RgX_to_ser(P, m+2);
}

GEN
vecan_eta(GEN eta, long L)
{
  pari_sp ltop = avma;
  GEN P, eq, divN = gel(eta, 1), RM = gel(eta, 2);
  long i, ld = lg(divN);
  P = gen_1; eq = gen_0;
  for (i = 1; i < ld; ++i)
  {
    GEN m, rm = gel(RM, i);
    if (!signe(rm)) continue;
    m = gel(divN, i); eq = addii(eq, mulii(m, rm));
    P = gmul(P, gpowgs(eta_inflate_ZXn(L, itos(m)), itos(rm)));
  }
  if (!equalis(eq, 24)) pari_err_IMPL("valuation != 1 in lfunetaquo");
  return gerepileupto(ltop, gtovec0(P, L));
}

/* Check if correct eta quotient. Set canonical form columns */
static void
etaquocheck(GEN eta, GEN *pdivN, GEN *pRM)
{
  GEN M, E, divN, RM;
  long lM, i, ld, j;
  if (typ(eta) != t_MAT || lg(eta) != 3 || !RgM_is_ZM(eta))
    pari_err_TYPE("etaquocheck", eta);
  M = gel(eta, 1); lM = lg(M);
  E = gel(eta, 2);
  *pdivN = divN = divisors(glcm0(M, NULL));
  settyp(divN, t_COL); ld = lg(divN);
  *pRM = RM = cgetg(ld, t_COL);
  for (i = 1; i < ld; ++i)
  {
    GEN S = gen_0, m = gel(divN, i);
    for (j = 1; j < lM; ++j)
      if (equalii(gel(M,j), m)) S = addii(S, gel(E,j));
    gel(RM,i) = S;
  }
}

/* Return etaquotient type:
 * -1: nonholomorphic or not on gamma_0(N)
 * 0: holomorphic noncuspidal
 * 1: cuspidal
 * 2: selfdual noncuspidal
 * 3: selfdual cuspidal
 * Sets conductor, modular weight, canonical matrix */
static long
etaquotype(GEN mateta, GEN *pN, long *pw, GEN *pcan)
{
  GEN divN, RM, S, T, U, N, M;
  long ld, i, j, fl;

  etaquocheck(mateta, &divN, &RM);
  *pcan = mkmat2(divN, RM);
  *pw = 0;
  *pN = gen_1;
  /* divN sorted in increasing order, N = last entry, divN[ld-i] = N/divN[i] */
  ld = lg(divN);
  S = gen_0; T = gen_0; U = gen_0;
  for (i = 1; i < ld; ++i)
  {
    GEN m = gel(divN,i), rm = gel(RM,i);
    if (!signe(rm)) continue;
    S = addii(S, mulii(m, rm));
    T = addii(T, rm);
    U = gadd(U, gdiv(rm, m));
  }
  if (umodiu(S, 24) || umodiu(T, 2)) return -1;
  N = gel(divN, ld-1);
  *pw = itos(shifti(T,-1));
  *pN = M = lcmii(N, denom(gdivgs(U, 24)));
  for (i = 1, fl = 1; i < ld; i++)
  {
    GEN m = gel(divN, i), s = mulii(gel(RM,i), mulii(m,N));
    long t;
    for (j = 1; j < ld; ++j)
      if (j != i && signe(gel(RM,j)))
      {
        GEN mj = gel(divN, j), nj = gel(divN, ld-j); /* nj = N/mj */
        s = addii(s, mulii(mulii(gel(RM,j), sqri(gcdii(mj, m))), nj));
      }
    t = signe(s);
    if (t < 0) return -1;
    if (t == 0) fl = 0;
  }
  for (i = 1; i < ld; ++i)
  {
    GEN m = gel(divN, i), rm = gel(RM, i);
    if (!signe(rm)) continue;
    j = ZV_search(divN, divii(M,m));
    if (!j || !equalii(rm, gel(RM,j))) return fl;
  }
  return fl+2;
}

GEN
lfunetaquo(GEN eta)
{
  pari_sp ltop = avma;
  GEN Ldata, N, can;
  long k;
  if (typ(eta) != t_MAT || !RgM_is_ZM(eta))
    pari_err_TYPE("lfunetaquo", eta);
  if (lg(eta) != 3)
    pari_err_TYPE("lfunetaquo [not a factorization]", eta);
  switch(etaquotype(eta, &N, &k, &can))
  {
    case 3: break;
    case 2: pari_err_IMPL("noncuspidal eta quotient");
    default: pari_err_TYPE("lfunetaquo [non holomorphic]", eta);
  }
  Ldata = mkvecn(6, tag(can, t_LFUN_ETA),
                    gen_0, mkvec2(gen_0, gen_1), stoi(k), N, gen_1);
  return gerepilecopy(ltop, Ldata);
}

GEN
vecan_qf(GEN Q, long L)
{
  return gmul2n(gtovec(qfrep0(Q, utoi(L), 1)), 1);
}

static long
qf_iseven(GEN M)
{
  long i, n = lg(M) - 1;
  for (i=1; i<=n; i++)
    if (mpodd(gcoeff(M,i,i)))
      return 0;
  return 1;
}

GEN
lfunqf(GEN M)
{
  pari_sp ltop = avma;
  long n, k;
  GEN d, Mi;
  GEN Ldata;

  if (typ(M) != t_MAT) pari_err_TYPE("lfunqf", M);
  if (!RgM_is_ZM(M))   pari_err_TYPE("lfunqf [not integral]", M);
  n = lg(M)-1;
  if (odd(n)) pari_err_TYPE("lfunqf [odd dimension]", M);
  k = n >> 1;
  M = gdiv(M, content(M));
  if (!qf_iseven(M)) M = gmul2n(M, 1);
  Mi = ginv(M); d = denom(Mi);
  Mi = gmul(Mi, d);
  if (!qf_iseven(Mi)) d = gmul2n(d,1);
  Ldata = mkvecn(7, tag(M, t_LFUN_QF),
      gen_0, mkvec2(gen_0, gen_1), stoi(k), d, gen_1, gen_0);
  return gerepilecopy(ltop, Ldata);
}

enum { t_LFUNMISC_POL, t_LFUNMISC_CHI, t_LFUNMISC_CHIGEN,
       t_LFUNMISC_ELLINIT, t_LFUNMISC_ETAQUO };
static long
lfundatatype(GEN data)
{
  long l;
  switch(typ(data))
  {
    case t_INT: return t_LFUNMISC_CHI;
    case t_POL: return t_LFUNMISC_POL;
    case t_VEC:
      if (checknf_i(data)) return t_LFUNMISC_POL;
      l = lg(data);
      if (l == 17) return t_LFUNMISC_ELLINIT;
      if (l == 3 && typ(gel(data,2)) == t_VEC)
        switch(typ(gel(data,1)))
        {
          case t_INT: return t_LFUNMISC_CHI;
          case t_VEC: return t_LFUNMISC_CHIGEN;
        }
      break;
  }
  return -1;
}
static GEN
lfunmisc_to_ldata_i(GEN ldata, long shallow)
{
  long lx;
  if (is_linit(ldata)) ldata = linit_get_ldata(ldata);
  lx = lg(ldata);
  if (typ(ldata)==t_VEC && (lx == 7 || lx == 8) && is_tagged(ldata))
  {
    if (!shallow) ldata = gcopy(ldata);
    checkldata(ldata); return ldata;
  }
  switch (lfundatatype(ldata))
  {
    case t_LFUNMISC_POL: return lfunzetak(ldata);
    case t_LFUNMISC_CHI: return lfunchi(ldata);
    case t_LFUNMISC_CHIGEN: return lfunchigen(gel(ldata,1), gel(ldata,2));
    case t_LFUNMISC_ELLINIT: return lfunell(ldata);
  }
  pari_err_TYPE("lfunmisc_to_ldata",ldata);
  return NULL; /* NOT REACHED */
}

GEN
lfunmisc_to_ldata(GEN ldata)
{ return lfunmisc_to_ldata_i(ldata, 0); }

GEN
lfunmisc_to_ldata_shallow(GEN ldata)
{ return lfunmisc_to_ldata_i(ldata, 1); }


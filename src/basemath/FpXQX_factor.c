/* Copyright (C) 2016  The PARI group.

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
/**               Factorisation over finite fields                    **/
/**                                                                   **/
/***********************************************************************/

static GEN
to_Fq(GEN x, GEN T, GEN p)
{
  long i, lx, tx = typ(x);
  GEN y;

  if (tx == t_INT)
    y = mkintmod(x,p);
  else
  {
    if (tx != t_POL) pari_err_TYPE("to_Fq",x);
    lx = lg(x);
    y = cgetg(lx,t_POL); y[1] = x[1];
    for (i=2; i<lx; i++) gel(y,i) = mkintmod(gel(x,i), p);
  }
  return mkpolmod(y, T);
}

static GEN
to_Fq_pol(GEN x, GEN T, GEN p)
{
  long i, lx = lg(x);
  for (i=2; i<lx; i++) gel(x,i) = to_Fq(gel(x,i),T,p);
  return x;
}

static GEN
to_Fq_fact(GEN P, GEN E, GEN T, GEN p, pari_sp av)
{
  GEN y, u, v;
  long j, l = lg(P), nbf = lg(P);

  u = cgetg(nbf,t_COL);
  v = cgetg(nbf,t_COL);
  for (j=1; j<l; j++)
  {
    gel(u,j) = simplify_shallow(gel(P,j)); /* may contain pols of degree 0 */
    gel(v,j) = utoi(uel(E,j));
  }
  y = gerepilecopy(av, mkmat2(u, v));
  u = gel(y,1);
  p = icopy(p);
  T = FpX_to_mod(T, p);
  for (j=1; j<nbf; j++) gel(u,j) = to_Fq_pol(gel(u,j), T,p);
  return y;
}
static GEN
to_FqC(GEN P, GEN T, GEN p, pari_sp av)
{
  GEN u;
  long j, l = lg(P), nbf = lg(P);

  u = cgetg(nbf,t_COL);
  for (j=1; j<l; j++)
    gel(u,j) = simplify_shallow(gel(P,j)); /* may contain pols of degree 0 */
  u = gerepilecopy(av, u);
  p = icopy(p);
  T = FpX_to_mod(T, p);
  for (j=1; j<nbf; j++) gel(u,j) = to_Fq(gel(u,j), T,p);
  return u;
}

GEN
FlxqXQ_halfFrobenius(GEN a, GEN S, GEN T, ulong p)
{
  long vT = get_Flx_var(T);
  GEN xp = Flx_Frobenius(T, p);
  GEN Xp = FlxqXQ_powu(polx_FlxX(get_FlxqX_var(S), vT), p, S, T, p);
  GEN ap2 = FlxqXQ_powu(a,p>>1, S, T, p);
  GEN V = FlxqXQV_autsum(mkvec3(xp, Xp, ap2), get_Flx_degree(T), S, T, p);
  return gel(V,3);
}

GEN
FpXQXQ_halfFrobenius(GEN a, GEN S, GEN T, GEN p)
{
  if (lgefint(p)==3)
  {
    ulong pp = p[2];
    long v = get_FpX_var(T);
    GEN Tp = ZXT_to_FlxT(T,pp), Sp = ZXXT_to_FlxXT(S, pp, v);
    return FlxX_to_ZXX(FlxqXQ_halfFrobenius(ZXX_to_FlxX(a,pp,v),Sp,Tp,pp));
  }
  else
  {
    GEN xp, Xp, ap2, V;
    T = FpX_get_red(T, p);
    S = FpXQX_get_red(S, T, p);
    xp = FpX_Frobenius(T, p);
    Xp = FpXQXQ_pow(pol_x(get_FpXQX_var(S)), p, S, T, p);
    ap2 = FpXQXQ_pow(a,shifti(p,-1), S, T, p);
    V = FpXQXQV_autsum(mkvec3(xp,Xp,ap2), get_FpX_degree(T), S, T, p);
    return gel(V,3);
  }
}

GEN
FlxqX_Frobenius(GEN S, GEN T, ulong p)
{
  pari_sp av = avma;
  long n = get_Flx_degree(T), vT = get_Flx_var(T);
  GEN X  = polx_FlxX(get_FlxqX_var(S), vT);
  GEN xp = Flx_Frobenius(T, p);
  GEN Xp = FlxqXQ_powu(X, p, S, T, p);
  GEN Xq = gel(FlxqXQV_autpow(mkvec2(xp,Xp), n, S, T, p), 2);
  return gerepilecopy(av, Xq);
}

GEN
FpXQX_Frobenius(GEN S, GEN T, GEN p)
{
  pari_sp av = avma;
  long n = get_FpX_degree(T);
  GEN X  = pol_x(get_FpXQX_var(S));
  GEN xp = FpX_Frobenius(T, p);
  GEN Xp = FpXQXQ_pow(X, p, S, T, p);
  GEN Xq = gel(FpXQXQV_autpow(mkvec2(xp,Xp), n, S, T, p), 2);
  return gerepilecopy(av, Xq);
}

static GEN
FqX_Frobenius_powers(GEN S, GEN T, GEN p)
{
  long N = get_FpXQX_degree(S);
  if (lgefint(p)==3)
  {
    ulong pp = p[2];
    GEN Tp = ZXT_to_FlxT(T, pp), Sp = ZXXT_to_FlxXT(S, pp, get_FpX_var(T));
    GEN Xq = FlxqX_Frobenius(Sp, Tp, pp);
    return FlxqXQ_powers(Xq, N-1, Sp, Tp, pp);
  } else
  {
    GEN Xq = FpXQX_Frobenius(S, T, p);
    return FpXQXQ_powers(Xq, N-1, S, T, p);
  }
}

static GEN
FqX_Frobenius_eval(GEN x, GEN V, GEN S, GEN T, GEN p)
{
  if (lgefint(p)==3)
  {
    ulong pp = p[2];
    long v = get_FpX_var(T);
    GEN Tp = ZXT_to_FlxT(T, pp), Sp = ZXXT_to_FlxXT(S, pp, v);
    GEN xp = ZXX_to_FlxX(x, pp, v);
    return FlxX_to_ZXX(FlxqX_FlxqXQV_eval(xp, V, Sp, Tp, pp));
  }
  else
    return FpXQX_FpXQXQV_eval(x, V, S, T, p);
}

static GEN
FpXQX_split_part(GEN f, GEN T, GEN p)
{
  long n = degpol(f);
  GEN z, X = pol_x(varn(f));
  if (n <= 1) return f;
  f = FpXQX_red(f, T, p);
  z = FpXQX_Frobenius(f, T, p);
  z = FpXX_sub(z, X , p);
  return FpXQX_gcd(z, f, T, p);
}

static GEN
FlxqX_split_part(GEN f, GEN T, ulong p)
{
  long n = degpol(f);
  GEN z, Xq, X = polx_FlxX(varn(f),get_Flx_var(T));
  if (n <= 1) return f;
  f = FlxqX_red(f, T, p);
  Xq = FlxqX_Frobenius(f, T, p);
  z = FlxX_sub(Xq, X , p);
  return FlxqX_gcd(z, f, T, p);
}

long
FpXQX_nbroots(GEN f, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN z;
  if(lgefint(p)==3)
  {
    ulong pp=p[2];
    z = FlxqX_split_part(ZXX_to_FlxX(f,pp,varn(T)),ZXT_to_FlxT(T,pp),pp);
  }
  else
    z = FpXQX_split_part(f, T, p);
  avma = av; return degpol(z);
}

long
FqX_nbroots(GEN f, GEN T, GEN p)
{ return T ? FpXQX_nbroots(f, T, p): FpX_nbroots(f, p); }

long
FlxqX_nbroots(GEN f, GEN T, ulong p)
{
  pari_sp av = avma;
  GEN z = FlxqX_split_part(f, T, p);
  avma = av; return degpol(z);
}

GEN
FlxqX_Berlekamp_ker(GEN S, GEN T, ulong p)
{
  pari_sp ltop=avma;
  long j, N = get_FlxqX_degree(S);
  GEN Xq = FlxqX_Frobenius(S,T,p);
  GEN Q  = FlxqXQ_matrix_pow(Xq,N,N,S,T,p);
  for (j=1; j<=N; j++)
    gcoeff(Q,j,j) = Flx_Fl_add(gcoeff(Q,j,j), p-1, p);
  return gerepileupto(ltop, FlxqM_ker(Q,T,p));
}

GEN
FpXQX_Berlekamp_ker(GEN S, GEN T, GEN p)
{
  if (lgefint(p)==3)
  {
    ulong pp=p[2];
    long v = get_FpX_var(T);
    GEN Tp = ZXT_to_FlxT(T,pp), Sp = ZXX_to_FlxX(S,pp,v);
    return FlxM_to_ZXM(FlxqX_Berlekamp_ker(Sp, Tp, pp));
  } else
  {
    pari_sp ltop=avma;
    long j,N = get_FpXQX_degree(S);
    GEN Xq = FpXQX_Frobenius(S,T,p);
    GEN Q  = FpXQXQ_matrix_pow(Xq,N,N,S,T,p);
    for (j=1; j<=N; j++)
      gcoeff(Q,j,j) = Fq_sub(gcoeff(Q,j,j), gen_1, T, p);
    return gerepileupto(ltop, FqM_ker(Q,T,p));
  }
}

long
FpXQX_nbfact(GEN u, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN vker = FpXQX_Berlekamp_ker(u, T, p);
  avma = av; return lg(vker)-1;
}

long
FqX_nbfact(GEN u, GEN T, GEN p)
{
  return T ? FpX_nbfact(u, p): FpXQX_nbfact(u, T, p);
}

#define set_irred(i) { if ((i)>ir) swap(t[i],t[ir]); ir++;}

long
FqX_split_Berlekamp(GEN *t, GEN T, GEN p)
{
  GEN u = *t, a,b,vker,pol;
  long vu = varn(u), vT = varn(T), dT = degpol(T);
  long d, i, ir, L, la, lb;
  T = FpX_get_red(T, p);
  vker = FpXQX_Berlekamp_ker(u,T,p);
  vker = RgM_to_RgXV(vker,vu);
  d = lg(vker)-1;
  ir = 0;
  /* t[i] irreducible for i < ir, still to be treated for i < L */
  for (L=1; L<d; )
  {
    pol= scalarpol(random_FpX(dT,vT,p),vu);
    for (i=2; i<=d; i++)
      pol = FqX_add(pol, FqX_Fq_mul(gel(vker,i),
                                    random_FpX(dT,vT,p), T, p), T, p);
    pol = FpXQX_red(pol,T,p);
    for (i=ir; i<L && L<d; i++)
    {
      a = t[i]; la = degpol(a);
      if (la == 1) { set_irred(i); }
      else
      {
        pari_sp av = avma;
        b = FqX_rem(pol, a, T,p);
        if (degpol(b)<=0) { avma=av; continue; }
        b = FpXQXQ_halfFrobenius(b, a,T,p);
        if (degpol(b)<=0) { avma=av; continue; }
        gel(b,2) = Fq_sub(gel(b,2), gen_1,T,p);
        b = FqX_gcd(a,b, T,p); lb = degpol(b);
        if (lb && lb < la)
        {
          b = FpXQX_normalize(b, T,p);
          t[L] = FqX_div(a,b,T,p);
          t[i]= b; L++;
        }
        else avma = av;
      }
    }
  }
  return d;
}

/* split into r factors of degree d */
static void
FqX_split(GEN *t, long d, GEN q, GEN S, GEN T, GEN p)
{
  GEN u = *t;
  long l, v, is2, cnt, dt = degpol(u), dT = degpol(T);
  pari_sp av;
  pari_timer ti;
  GEN w,w0;

  if (dt == d) return;
  v = varn(*t);
  if (DEBUGLEVEL > 6) timer_start(&ti);
  av = avma; is2 = absequaliu(p, 2);
  for(cnt = 1;;cnt++, avma = av)
  { /* splits *t with probability ~ 1 - 2^(1-r) */
    w = w0 = random_FpXQX(dt,v, T,p);
    if (degpol(w) <= 0) continue;
    for (l=1; l<d; l++) /* sum_{0<i<d} w^(q^i), result in (F_q)^r */
      w = RgX_add(w0, FqX_Frobenius_eval(w, S, u, T, p));
    w = FpXQX_red(w, T,p);
    if (is2)
    {
      w0 = w;
      for (l=1; l<dT; l++) /* sum_{0<i<k} w^(2^i), result in (F_2)^r */
      {
        w = FqX_rem(FqX_sqr(w,T,p), *t, T,p);
        w = FpXX_red(RgX_add(w0,w), p);
      }
    }
    else
    {
      w = FpXQXQ_halfFrobenius(w, *t, T, p);
      /* w in {-1,0,1}^r */
      if (degpol(w) <= 0) continue;
      gel(w,2) = gadd(gel(w,2), gen_1);
    }
    w = FqX_gcd(*t,w, T,p); l = degpol(w);
    if (l && l != dt) break;
  }
  w = gerepileupto(av,FpXQX_normalize(w,T,p));
  if (DEBUGLEVEL > 6)
    err_printf("[FqX_split] splitting time: %ld (%ld trials)\n",
               timer_delay(&ti),cnt);
  l /= d; t[l] = FqX_div(*t,w, T,p); *t = w;
  FqX_split(t+l,d,q,S,T,p);
  FqX_split(t  ,d,q,S,T,p);
}

/*******************************************************************/
/*                                                                 */
/*                  FACTOR USING TRAGER'S TRICK                    */
/*                                                                 */
/*******************************************************************/
static GEN
FqX_frobinv_inplace(GEN F, GEN T, GEN p)
{
  if (T)
  {
    GEN frobinv = powiu(p, degpol(T)-1);
    long i, l = lg(F);
    for (i=2; i<l; i++) gel(F,i) = Fq_pow(gel(F,i), frobinv, T,p);
  }
  return F;
}
static GEN
FqX_frob_deflate(GEN f, GEN T, GEN p)
{ return FqX_frobinv_inplace(RgX_deflate(f, itos(p)), T, p); }

static long
isabsolutepol(GEN f)
{
  long i, l = lg(f);
  for(i=2; i<l; i++)
  {
    GEN c = gel(f,i);
    if (typ(c) == t_POL && degpol(c) > 0) return 0;
  }
  return 1;
}

static void
add(GEN z, GEN g, long d) { vectrunc_append(z, mkvec2(utoipos(d), g)); }
/* return number of roots of u; assume deg u >= 0 */
long
FqX_split_deg1(GEN *pz, GEN u, GEN T, GEN p)
{
  long dg, N = degpol(u);
  GEN v, S, g, X, z = vectrunc_init(N+1);

  *pz = z;
  if (N == 0) return 0;
  if (N == 1) return 1;
  v = X = pol_x(varn(u));
  S = FqX_Frobenius_powers(u, T, p);
  vectrunc_append(z, S);
  v = FqX_Frobenius_eval(v, S, u, T, p);
  g = FqX_gcd(FpXX_sub(v,X,p),u, T,p);
  dg = degpol(g);
  if (dg > 0) add(z, FpXQX_normalize(g,T,p), dg);
  return dg;
}

/* return number of factors; z not properly initialized if deg(u) <= 1 */
long
FqX_split_by_degree(GEN *pz, GEN u, GEN T, GEN p)
{
  long nb = 0, d, dg, N = degpol(u);
  GEN v, S, g, X, z = vectrunc_init(N+1);

  *pz = z;
  if (N <= 1) return 1;
  v = X = pol_x(varn(u));
  S = FqX_Frobenius_powers(u, T, p);
  vectrunc_append(z, S);
  for (d=1; d <= N>>1; d++)
  {
    v = FqX_Frobenius_eval(v, S, u, T, p);
    g = FqX_gcd(FpXX_sub(v,X,p),u, T,p);
    dg = degpol(g); if (dg <= 0) continue;
    /* all factors of g have degree d */
    add(z, FpXQX_normalize(g, T,p), dg / d); nb += dg / d;
    N -= dg;
    if (N)
    {
      u = FqX_div(u,g, T,p);
      v = FqX_rem(v,u, T,p);
    }
  }
  if (N) { add(z, FpXQX_normalize(u, T,p), 1); nb++; }
  return nb;
}

static GEN
FqX_split_equal(GEN L, GEN S, GEN T, GEN p)
{
  long n = itos(gel(L,1));
  GEN u = gel(L,2), z = cgetg(n + 1, t_COL);
  gel(z,1) = u;
  FqX_split((GEN*)(z+1), degpol(u) / n, powiu(p, degpol(T)), S, T, p);
  return z;
}
GEN
FqX_split_roots(GEN z, GEN T, GEN p, GEN pol)
{
  GEN S = gel(z,1), L = gel(z,2), rep = FqX_split_equal(L, S, T, p);
  if (pol) rep = shallowconcat(rep, FqX_div(pol, gel(L,2), T,p));
  return rep;
}
GEN
FqX_split_all(GEN z, GEN T, GEN p)
{
  GEN S = gel(z,1), rep = cgetg(1, t_VEC);
  long i, l = lg(z);
  for (i = 2; i < l; i++)
    rep = shallowconcat(rep, FqX_split_equal(gel(z,i), S, T, p));
  return rep;
}

/* not memory-clean, as Flx_factorff_i, returning only linear factors */
static GEN
Flx_rootsff_i(GEN P, GEN T, ulong p)
{
  GEN V, F = gel(Flx_factor(P,p), 1);
  long i, lfact = 1, nmax = lgpol(P), n = lg(F), dT = get_Flx_degree(T);

  V = cgetg(nmax,t_COL);
  for(i=1;i<n;i++)
  {
    GEN R, Fi = gel(F,i);
    long di = degpol(Fi), j, r;
    if (dT % di) continue;
    R = Flx_factorff_irred(gel(F,i),T,p);
    r = lg(R);
    for (j=1; j<r; j++,lfact++)
      gel(V,lfact) = Flx_neg(gmael(R,j, 2), p);
  }
  setlg(V,lfact);
  gen_sort_inplace(V, (void*) &cmp_Flx, &cmp_nodata, NULL);
  return V;
}
GEN
Flx_rootsff(GEN P, GEN T, ulong p)
{
  pari_sp av = avma;
  return gerepilecopy(av, Flx_rootsff_i(P, T, p));
}

/* dummy implementation */
static GEN
F2x_rootsff_i(GEN P, GEN T)
{
  return FlxC_to_F2xC(Flx_rootsff_i(F2x_to_Flx(P), F2x_to_Flx(T), 2UL));
}

/* not memory-clean, as FpX_factorff_i, returning only linear factors */
static GEN
FpX_rootsff_i(GEN P, GEN T, GEN p)
{
  GEN V, F;
  long i, lfact, nmax, n, dT;
  if (lgefint(p)==3)
  {
    ulong pp = p[2];
    GEN V = Flx_rootsff_i(ZX_to_Flx(P,pp), ZXT_to_FlxT(T,pp), pp);
    return FlxC_to_ZXC(V);
  }
  F = gel(FpX_factor(P,p), 1);
  lfact = 1; nmax = lgpol(P); n = lg(F); dT = get_FpX_degree(T);

  V = cgetg(nmax,t_COL);
  for(i=1;i<n;i++)
  {
    GEN R, Fi = gel(F,i);
    long di = degpol(Fi), j, r;
    if (dT % di) continue;
    R = FpX_factorff_irred(gel(F,i),T,p);
    r = lg(R);
    for (j=1; j<r; j++,lfact++)
      gel(V,lfact) = Fq_to_FpXQ(Fq_neg(gmael(R,j, 2), T, p), T, p);
  }
  setlg(V,lfact);
  gen_sort_inplace(V, (void*) &cmp_RgX, &cmp_nodata, NULL);
  return V;
}
GEN
FpX_rootsff(GEN P, GEN T, GEN p)
{
  pari_sp av = avma;
  return gerepilecopy(av, FpX_rootsff_i(P, T, p));
}

static GEN
F2xqX_quad_roots(GEN P, GEN T)
{
  GEN b= gel(P,3), c = gel(P,2);
  if (lgpol(b))
  {
    GEN z, d = F2xq_div(c, F2xq_sqr(b,T),T);
    if (F2xq_trace(d,T))
      return cgetg(1, t_COL);
    z = F2xq_mul(b, F2xq_Artin_Schreier(d, T), T);
    return mkcol2(z, F2x_add(b, z));
  }
  else
    return mkcol(F2xq_sqrt(c, T));
}

/* Assume p>2 and x monic */
static GEN
FlxqX_quad_roots(GEN x, GEN T, ulong p)
{
  GEN s, D, nb, b = gel(x,3), c = gel(x,2);
  D = Flx_sub(Flxq_sqr(b,T,p), Flx_mulu(c,4,p), p);
  nb = Flx_neg(b,p);
  if (lgpol(D)==0)
    return mkcol(Flx_halve(nb, p));
  s = Flxq_sqrt(D,T,p);
  if (!s) return cgetg(1, t_COL);
  s = Flx_halve(Flx_add(s,nb,p),p);
  return mkcol2(s, Flx_sub(nb,s,p));
}

static GEN
FpXQX_quad_roots(GEN x, GEN T, GEN p)
{
  GEN s, D, nb, b = gel(x,3), c = gel(x,2);
  if (absequaliu(p, 2))
  {
    GEN f2 = ZXX_to_F2xX(x, get_FpX_var(T));
    s = F2xqX_quad_roots(f2, ZX_to_F2x(get_FpX_mod(T)));
    return F2xC_to_ZXC(s);
  }
  D = Fq_sub(Fq_sqr(b,T,p), Fq_Fp_mul(c,utoi(4),T,p), T,p);
  nb = Fq_neg(b,T,p);
  if (signe(D)==0)
    return mkcol(Fq_to_FpXQ(Fq_halve(nb,T, p),T,p));
  s = Fq_sqrt(D,T,p);
  if (!s) return cgetg(1, t_COL);
  s = Fq_halve(Fq_add(s,nb,T,p),T, p);
  return mkcol2(Fq_to_FpXQ(s,T,p), Fq_to_FpXQ(Fq_sub(nb,s,T,p),T,p));
}

static GEN
F2xqX_Frobenius_deflate(GEN S, GEN T)
{
  GEN F = RgX_deflate(S, 2);
  long i, l = lg(F);
  for (i=2; i<l; i++)
    gel(F,i) = F2xq_sqrt(gel(F,i), T);
  return F;
}

static GEN
F2xX_to_F2x(GEN x)
{
  long l=nbits2lg(lgpol(x));
  GEN z=cgetg(l,t_VECSMALL);
  long i,j,k;
  z[1]=x[1];
  for(i=2, k=1,j=BITS_IN_LONG;i<lg(x);i++,j++)
  {
    if (j==BITS_IN_LONG)
    {
      j=0; k++; z[k]=0;
    }
    if (lgpol(gel(x,i)))
      z[k]|=1UL<<j;
  }
  return F2x_renormalize(z,l);
}

static GEN
F2xqX_easyroots(GEN f, GEN T)
{
  if (F2xY_degreex(f) <= 0) return F2x_rootsff_i(F2xX_to_F2x(f), T);
  if (degpol(f)==1) return mkcol(constant_coeff(f));
  if (degpol(f)==2) return F2xqX_quad_roots(f,T);
  return NULL;
}

/* Adapted from Shoup NTL */
static GEN
F2xqX_factor_squarefree(GEN f, GEN T)
{
  pari_sp av = avma;
  GEN r, t, v, tv;
  long q, n = degpol(f);
  GEN u = const_vec(n+1, pol1_F2xX(varn(f),T[1]));
  for(q = 1;;q *= 2)
  {
    r = F2xqX_gcd(f, F2xX_deriv(f), T);
    if (degpol(r) == 0)
    {
      gel(u, q) = F2xqX_normalize(f, T);
      break;
    }
    t = F2xqX_div(f, r, T);
    if (degpol(t) > 0)
    {
      long j;
      for(j = 1;;j++)
      {
        v = F2xqX_gcd(r, t, T);
        tv = F2xqX_div(t, v, T);
        if (degpol(tv) > 0)
          gel(u, j*q) = F2xqX_normalize(tv, T);
        if (degpol(v) <= 0) break;
        r = F2xqX_div(r, v, T);
        t = v;
      }
      if (degpol(r) == 0) break;
    }
    f = F2xqX_Frobenius_deflate(r, T);
  }
  return gerepilecopy(av, u);
}

static void
F2xqX_roots_edf(GEN Sp, GEN xp, GEN Xp, GEN T, GEN V, long idx)
{
  pari_sp btop;
  long n = degpol(Sp);
  GEN S, f, ff;
  GEN R = F2xqX_easyroots(Sp, T);
  if (R)
  {
    long i, l = lg(R)-1;
    for (i=0; i<l; i++)
      gel(V, idx+i) = gel(R,1+i);
    return;
  }
  S = Sp;
  Xp = F2xqX_rem(Xp, S, T);
  btop = avma;
  while (1)
  {
    GEN a = random_F2xqX(degpol(Sp), varn(Sp), T);
    GEN R = gel(F2xqXQV_auttrace(mkvec3(xp, Xp, a), F2x_degree(T), S, T), 3);
    f = F2xqX_gcd(R, Sp, T);
    if (degpol(f) > 0 && degpol(f) < n) break;
    avma = btop;
  }
  f = gerepileupto(btop, F2xqX_normalize(f, T));
  ff = F2xqX_div(Sp, f, T);
  F2xqX_roots_edf(f, xp, Xp, T, V, idx);
  F2xqX_roots_edf(ff,xp, Xp, T, V, idx+degpol(f));
}

static GEN
F2xqXQ_Frobenius(GEN xp, GEN Xp, GEN f, GEN T)
{
  ulong dT = F2x_degree(T), df = degpol(f);
  if (dT >= expu(dT)*usqrt(df))
    return gel(F2xqXQV_autpow(mkvec2(xp, Xp), dT, f, T), 2);
  else
    return F2xqXQ_pow(pol_x(varn(f)), int2n(dT), f, T);
}

static GEN
F2xqX_roots_ddf(GEN f, GEN xp, GEN T)
{
  GEN X, Xp, Xq, g, V;
  long n;
  GEN R = F2xqX_easyroots(f, T);
  if (R) return R;
  X  = pol_x(varn(f));
  Xp = F2xqXQ_sqr(X, f, T);
  Xq = F2xqXQ_Frobenius(xp, Xp, f, T);
  g = F2xqX_gcd(F2xX_add(Xq, X), f, T);
  n = degpol(g);
  if (n==0) return cgetg(1, t_COL);
  g = F2xqX_normalize(g, T);
  V = cgetg(n+1,t_COL);
  F2xqX_roots_edf(g, xp, Xp, T, V, 1);
  return V;
}
static GEN
F2xqX_roots_i(GEN S, GEN T)
{
  GEN xp, F, M, V, R;
  long i, j, l;
  S = F2xqX_red(S, T);
  if (!signe(S)) pari_err_ROOTS0("F2xqX_roots");
  if (degpol(S)==0) return cgetg(1, t_COL);
  S = F2xqX_normalize(S, T);
  R = F2xqX_easyroots(S, T);
  if (R) return gen_sort(R, (void*) &cmp_Flx, &cmp_nodata);
  xp = F2x_Frobenius(T);
  V = F2xqX_factor_squarefree(S, T);
  l = lg(V);
  F = cgetg(l, t_VEC);
  for (i=1, j=1; i < l; i++)
    if (degpol(gel(V,i)))
      gel(F, j++) = F2xqX_roots_ddf(gel(V,i), xp, T);
  setlg(F,j); M = shallowconcat1(F);
  gen_sort_inplace(M, (void*) &cmp_Flx, &cmp_nodata, NULL);
  return M;
}

static GEN
FlxX_to_Flx(GEN f)
{
  long i, l = lg(f);
  GEN V = cgetg(l, t_VECSMALL);
  V[1] = ((ulong)f[1])&VARNBITS;
  for(i=2; i<l; i++)
    V[i] = lgpol(gel(f,i)) ? mael(f,i,2): 0L;
  return V;
}

static GEN
FlxqX_easyroots(GEN f, GEN T, ulong p)
{
  if (FlxY_degreex(f) <= 0) return Flx_rootsff_i(FlxX_to_Flx(f), T, p);
  if (degpol(f)==1) return mkcol(Flx_neg(constant_coeff(f), p));
  if (degpol(f)==2) return FlxqX_quad_roots(f,T,p);
  return NULL;
}

static GEN
FlxqX_invFrobenius(GEN xp, GEN T, ulong p)
{
  return Flxq_autpow(xp, get_Flx_degree(T)-1, T, p);
}

static GEN
FlxqX_Frobenius_deflate(GEN S, GEN ixp, GEN T, ulong p)
{
  GEN F = RgX_deflate(S, p);
  long i, l = lg(F);
  if (typ(ixp)==t_INT)
    for (i=2; i<l; i++)
      gel(F,i) = Flxq_pow(gel(F,i), ixp, T, p);
  else
  {
    long n = brent_kung_optpow(get_Flx_degree(T)-1, l-2, 1);
    GEN V = Flxq_powers(ixp, n, T, p);
    for (i=2; i<l; i++)
      gel(F,i) = Flx_FlxqV_eval(gel(F,i), V, T, p);
  }
  return F;
}

/* Adapted from Shoup NTL */
static GEN
FlxqX_factor_squarefree(GEN f, GEN xp, GEN T, ulong p)
{
  pari_sp av = avma;
  GEN r, t, v, tv;
  long q, n = degpol(f);
  GEN u = const_vec(n+1, pol1_FlxX(varn(f),get_Flx_var(T)));
  GEN ixp = NULL;
  for(q = 1;;q *= p)
  {
    r = FlxqX_gcd(f, FlxX_deriv(f, p), T, p);
    if (degpol(r) == 0)
    {
      gel(u, q) = FlxqX_normalize(f, T, p);
      break;
    }
    t = FlxqX_div(f, r, T, p);
    if (degpol(t) > 0)
    {
      long j;
      for(j = 1;;j++)
      {
        v = FlxqX_gcd(r, t, T, p);
        tv = FlxqX_div(t, v, T, p);
        if (degpol(tv) > 0)
          gel(u, j*q) = FlxqX_normalize(tv, T, p);
        if (degpol(v) <= 0) break;
        r = FlxqX_div(r, v, T, p);
        t = v;
      }
      if (degpol(r) == 0) break;
    }
    if (!ixp) ixp = FlxqX_invFrobenius(xp, T, p);
    f = FlxqX_Frobenius_deflate(r, ixp, T, p);
  }
  return gerepilecopy(av, u);
}

static void
FlxqX_roots_edf(GEN Sp, GEN xp, GEN Xp, GEN T, ulong p, GEN V, long idx)
{
  pari_sp btop;
  long n = degpol(Sp);
  GEN S, f, ff;
  long vT = get_Flx_var(T), dT = get_Flx_degree(T);
  GEN R = FlxqX_easyroots(Sp, T, p);
  if (R)
  {
    long i, l = lg(R)-1;
    for (i=0; i<l; i++)
      gel(V, idx+i) = gel(R,1+i);
    return;
  }
  S = FlxqX_get_red(Sp, T, p);
  Xp = FlxqX_rem(Xp, S, T, p);
  btop = avma;
  while (1)
  {
    GEN a = deg1pol(pol1_Flx(vT), random_Flx(dT, vT, p), varn(Sp));
    GEN ap2 = FlxqXQ_powu(a, p>>1, S, T, p);
    GEN R = gel(FlxqXQV_autsum(mkvec3(xp, Xp, ap2), get_Flx_degree(T), S, T, p), 3);
    f = FlxqX_gcd(FlxX_Flx_add(R, Flx_neg(pol1_Flx(vT), p), p), Sp, T, p);
    if (degpol(f) > 0 && degpol(f) < n) break;
    avma = btop;
  }
  f = gerepileupto(btop, FlxqX_normalize(f, T, p));
  ff = FlxqX_div(Sp, f, T, p);
  FlxqX_roots_edf(f, xp, Xp, T, p, V, idx);
  FlxqX_roots_edf(ff,xp, Xp, T, p, V, idx+degpol(f));
}

static GEN
FlxqX_roots_ddf(GEN f, GEN xp, GEN T, ulong p)
{
  GEN X, Xp, Xq, g, V;
  long n, dT = get_Flx_degree(T);
  GEN R = FlxqX_easyroots(f, T, p);
  if (R) return R;
  X  = pol_x(varn(f));
  Xp = FlxqXQ_powu(X, p, f, T, p);
  Xq = gel(FlxqXQV_autpow(mkvec2(xp, Xp), dT, f, T, p), 2);
  g = FlxqX_gcd(FlxX_sub(Xq, X, p), f, T, p);
  n = degpol(g);
  if (n==0) return cgetg(1, t_COL);
  g = FlxqX_normalize(g, T, p);
  V = cgetg(n+1,t_COL);
  FlxqX_roots_edf(g, xp, Xp, T, p, V, 1);
  return V;
}

/* do not handle p==2 */
static GEN
FlxqX_roots_i(GEN S, GEN T, ulong p)
{
  GEN xp, F, M, V, R;
  long i, j, l;
  S = FlxqX_red(S, T, p);
  if (!signe(S)) pari_err_ROOTS0("FlxqX_roots");
  if (degpol(S)==0) return cgetg(1, t_COL);
  S = FlxqX_normalize(S, T, p);
  R = FlxqX_easyroots(S, T, p);
  if (R) return gen_sort(R, (void*) &cmp_Flx, &cmp_nodata);
  xp = Flx_Frobenius(T, p);
  V = FlxqX_factor_squarefree(S, xp, T, p);
  l = lg(V);
  F = cgetg(l, t_VEC);
  for (i=1, j=1; i < l; i++)
    if (degpol(gel(V,i)))
      gel(F, j++) = FlxqX_roots_ddf(gel(V,i), xp, T, p);
  setlg(F,j); M = shallowconcat1(F);
  gen_sort_inplace(M, (void*) &cmp_Flx, &cmp_nodata, NULL);
  return M;
}

static GEN
FpXQX_easyroots(GEN f, GEN T, GEN p)
{
  if (isabsolutepol(f)) return FpX_rootsff_i(simplify_shallow(f), T, p);
  if (degpol(f)==1) return mkcol(Fq_to_FpXQ(Fq_neg(constant_coeff(f),T,p),T,p));
  if (degpol(f)==2) return FpXQX_quad_roots(f,T,p);
  return NULL;
}

/* Adapted from Shoup NTL */
static GEN
FpXQX_factor_squarefree(GEN f, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN r, t, v, tv;
  long j, n = degpol(f);
  GEN u = const_vec(n+1, pol_1(varn(f)));
  r = FpXQX_gcd(f, FpXX_deriv(f, p), T, p);
  t = FpXQX_div(f, r, T, p);
  for (j = 1;;j++)
  {
    v = FpXQX_gcd(r, t, T, p);
    tv = FpXQX_div(t, v, T, p);
    if (degpol(tv) > 0)
      gel(u, j) = FpXQX_normalize(tv, T, p);
    if (degpol(v) <= 0) break;
    r = FpXQX_div(r, v, T, p);
    t = v;
  }
  return gerepilecopy(av, u);
}

static void
FpXQX_roots_edf(GEN Sp, GEN xp, GEN Xp, GEN T, GEN p, GEN V, long idx)
{
  pari_sp btop;
  long n = degpol(Sp);
  GEN S, f, ff;
  long vT = get_FpX_var(T), dT = get_FpX_degree(T);
  GEN R = FpXQX_easyroots(Sp, T, p);
  if (R)
  {
    long i, l = lg(R)-1;
    for (i=0; i<l; i++)
      gel(V, idx+i) = gel(R,1+i);
    return;
  }
  S = FpXQX_get_red(Sp, T, p);
  Xp = FpXQX_rem(Xp, S, T, p);
  btop = avma;
  while (1)
  {
    GEN a = deg1pol(pol_1(vT), random_FpX(dT, vT, p), varn(Sp));
    GEN ap2 = FpXQXQ_pow(a, shifti(p,-1), S, T, p);
    GEN R = gel(FpXQXQV_autsum(mkvec3(xp, Xp, ap2), get_FpX_degree(T), S, T, p), 3);
    f = FpXQX_gcd(FqX_Fq_add(R, FpX_neg(pol_1(vT), p), T, p), Sp, T, p);
    if (degpol(f) > 0 && degpol(f) < n) break;
    avma = btop;
  }
  f = gerepileupto(btop, FpXQX_normalize(f, T, p));
  ff = FpXQX_div(Sp, f, T, p);
  FpXQX_roots_edf(f, xp, Xp, T, p, V, idx);
  FpXQX_roots_edf(ff,xp, Xp, T, p, V, idx+degpol(f));
}

static GEN
FpXQX_roots_ddf(GEN f, GEN xp, GEN T, GEN p)
{
  GEN X, Xp, Xq, g, V;
  long n, dT = get_FpX_degree(T);
  GEN R = FpXQX_easyroots(f, T, p);
  if (R) return R;
  X  = pol_x(varn(f));
  Xp = FpXQXQ_pow(X, p, f, T, p);
  Xq = gel(FpXQXQV_autpow(mkvec2(xp, Xp), dT, f, T, p), 2);
  g = FpXQX_gcd(FpXX_sub(Xq, X, p), f, T, p);
  n = degpol(g);
  if (n==0) return cgetg(1, t_COL);
  g = FpXQX_normalize(g, T, p);
  V = cgetg(n+1,t_COL);
  FpXQX_roots_edf(g, xp, Xp, T, p, V, 1);
  return V;
}

/* do not handle small p */
static GEN
FpXQX_roots_i(GEN S, GEN T, GEN p)
{
  GEN xp, F, M, V, R;
  long i, j, l;
  if (lgefint(p)==3)
  {
    ulong pp = p[2];
    if (pp == 2)
    {
      GEN V = F2xqX_roots_i(ZXX_to_F2xX(S,get_FpX_var(T)), ZX_to_F2x(get_FpX_mod(T)));
      return F2xC_to_ZXC(V);
    }
    else
    {
      GEN V = FlxqX_roots_i(ZXX_to_FlxX(S,pp,get_FpX_var(T)), ZXT_to_FlxT(T,pp), pp);
      return FlxC_to_ZXC(V);
    }
  }
  S = FpXQX_red(S, T, p);
  if (!signe(S)) pari_err_ROOTS0("FpXQX_roots");
  if (degpol(S)==0) return cgetg(1, t_COL);
  S = FpXQX_normalize(S, T, p);
  R = FpXQX_easyroots(S, T, p);
  if (R) return gen_sort(R, (void*) &cmp_RgX, &cmp_nodata);
  xp = FpX_Frobenius(T, p);
  V = FpXQX_factor_squarefree(S, T, p);
  l = lg(V);
  F = cgetg(l, t_VEC);
  for (i=1, j=1; i < l; i++)
    if (degpol(gel(V,i)))
      gel(F, j++) = FpXQX_roots_ddf(gel(V,i), xp, T, p);
  setlg(F,j); M = shallowconcat1(F);
  gen_sort_inplace(M, (void*) &cmp_RgX, &cmp_nodata, NULL);
  return M;
}

GEN
F2xqX_roots(GEN x, GEN T)
{
  pari_sp av = avma;
  return gerepilecopy(av, F2xqX_roots_i(x, T));
}

GEN
FlxqX_roots(GEN x, GEN T, ulong p)
{
  pari_sp av = avma;
  if (p==2)
  {
    GEN V = F2xqX_roots_i(FlxX_to_F2xX(x), Flx_to_F2x(get_Flx_mod(T)));
    return gerepileupto(av, F2xC_to_FlxC(V));
  }
  return gerepilecopy(av, FlxqX_roots_i(x, T, p));
}

GEN
FpXQX_roots(GEN x, GEN T, GEN p)
{
  pari_sp av = avma;
  return gerepilecopy(av, FpXQX_roots_i(x, T, p));
}

static long
FqX_sqf_split(GEN *t0, GEN q, GEN T, GEN p)
{
  GEN *t = t0, u = *t, v, S, g, X;
  long d, dg, N = degpol(u);

  if (N == 1) return 1;
  v = X = pol_x(varn(u));
  S = FqX_Frobenius_powers(u, T, p);
  for (d=1; d <= N>>1; d++)
  {
    v = FqX_Frobenius_eval(v, S, u, T, p);
    g = FpXQX_normalize(FqX_gcd(FpXX_sub(v,X,p),u, T,p),T,p);
    dg = degpol(g); if (dg <= 0) continue;

    /* all factors of g have degree d */
    *t = g;
    FqX_split(t, d, q, S, T, p);
    t += dg / d;
    N -= dg;
    if (N)
    {
      u = FqX_div(u,g, T,p);
      v = FqX_rem(v,u, T,p);
    }
  }
  if (N) *t++ = u;
  return t - t0;
}

/* not memory-clean */
static GEN
FpX_factorff_i(GEN P, GEN T, GEN p)
{
  GEN V, E, F = FpX_factor(P,p);
  long i, lfact = 1, nmax = lgpol(P), n = lgcols(F);

  V = cgetg(nmax,t_VEC);
  E = cgetg(nmax,t_VECSMALL);
  for(i=1;i<n;i++)
  {
    GEN R = FpX_factorff_irred(gmael(F,1,i),T,p), e = gmael(F,2,i);
    long j, r = lg(R);
    for (j=1; j<r; j++,lfact++)
    {
      gel(V,lfact) = gel(R,j);
      gel(E,lfact) = e;
    }
  }
  setlg(V,lfact);
  setlg(E,lfact); return sort_factor_pol(mkvec2(V,E), cmp_RgX);
}
GEN
FpX_factorff(GEN P, GEN T, GEN p)
{
  pari_sp av = avma;
  return gerepilecopy(av, FpX_factorff_i(P, T, p));
}

static GEN
FpXQX_factor_2(GEN f, GEN T, GEN p)
{
  long v = varn(f);
  GEN r = FpXQX_quad_roots(f,T,p);
  switch(lg(r)-1)
  {
  case 0:
    return mkvec2(mkcolcopy(f), mkvecsmall(1));
  case 1:
    return mkvec2(mkcol(deg1pol_shallow(gen_1, Fq_neg(gel(r,1), T, p), v)),
        mkvecsmall(2));
  default: /* 2 */
    {
      GEN f1 = deg1pol_shallow(gen_1, Fq_neg(gel(r,1), T, p), v);
      GEN f2 = deg1pol_shallow(gen_1, Fq_neg(gel(r,2), T, p), v);
      GEN t = mkcol2(f1, f2), E = mkvecsmall2(1, 1);
      sort_factor_pol(mkvec2(t, E), cmp_RgX);
      return mkvec2(t, E);
    }
  }
}

/* assumes varncmp (varn(T), varn(f)) > 0 */
static GEN
FpXQX_factor_i(GEN f, GEN T, GEN p)
{
  long pg, j, k, e, N, lfact, pk, d = degpol(f);
  GEN E, f2, f3, df1, df2, g1, u, q, t;

  switch(d)
  {
    case -1: retmkmat2(mkcolcopy(f), mkvecsmall(1));
    case 0: return trivial_fact();
  }
  T = FpX_normalize(T, p);
  f = FpXQX_normalize(f, T, p);
  if (isabsolutepol(f)) return FpX_factorff_i(simplify_shallow(f), T, p);
  if (degpol(f)==2) return FpXQX_factor_2(f, T, p);

  pg = itos_or_0(p);
  df2  = NULL; /* gcc -Wall */
  t = cgetg(d+1,t_VEC);
  E = cgetg(d+1, t_VECSMALL);

  q = powiu(p, degpol(T));
  e = lfact = 1;
  pk = 1;
  f3 = NULL;
  df1 = FqX_deriv(f, T, p);
  for(;;)
  {
    long nb0;
    while (!signe(df1))
    { /* needs d >= p: pg = 0 can't happen  */
      pk *= pg; e = pk;
      f = FqX_frob_deflate(f, T, p);
      df1 = FqX_deriv(f, T, p); f3 = NULL;
    }
    f2 = f3? f3: FqX_gcd(f,df1, T,p);
    if (!degpol(f2)) u = f;
    else
    {
      g1 = FqX_div(f,f2, T,p);
      df2 = FqX_deriv(f2, T,p);
      if (gequal0(df2)) { u = g1; f3 = f2; }
      else
      {
        f3 = FqX_gcd(f2,df2, T,p);
        u = degpol(f3)? FqX_div(f2, f3, T,p): f2;
        u = FqX_div(g1, u, T,p);
      }
    }
    /* u is square-free (product of irreducibles of multiplicity e) */
    N = degpol(u);
    if (N) {
      nb0 = lfact;
      gel(t,lfact) = FpXQX_normalize(u, T,p);
      if (N == 1) lfact++;
      else
      {
        if (!absequaliu(p,2))
          lfact += FqX_split_Berlekamp(&gel(t,lfact), T, p);
        else
          lfact += FqX_sqf_split(&gel(t,lfact), q, T, p);
      }
      for (j = nb0; j < lfact; j++) E[j] = e;
    }

    if (!degpol(f2)) break;
    f = f2; df1 = df2; e += pk;
  }
  setlg(t, lfact);
  setlg(E, lfact);
  for (j=1; j<lfact; j++) gel(t,j) = FpXQX_normalize(gel(t,j), T,p);
  (void)sort_factor_pol(mkvec2(t, E), cmp_RgX);
  k = 1;
  for (j = 2; j < lfact; j++)
  {
    if (RgX_equal(gel(t,j), gel(t,k)))
      E[k] += E[j];
    else
    { /* new factor */
      k++;
      E[k] = E[j];
      gel(t,k) = gel(t,j);
    }
  }
  setlg(t, k+1);
  setlg(E, k+1); return mkvec2(t, E);
}

long
FqX_ispower(GEN f, ulong k, GEN T, GEN p, GEN *pt)
{
  pari_sp av = avma;
  long v, w;
  ulong pp;
  GEN lc, F;

  if (degpol(f) % k) return 0;
  lc = leading_coeff(f);
  lc = Fq_sqrtn(lc, stoi(k), T, p, NULL);
  if (!lc) { av = avma; return 0; }
  pp = itou_or_0(p);
  f = FqX_normalize(f, T, p);
  v = pp? u_lvalrem(k,pp,&k): 0;
  if (v)
  {
    long i;
    w = u_lval(RgX_deflate_order(f), pp);
    if (w < v) { avma = av; return 0; }
    /* deflate as much as possible using frobenius, unless k reduced to 1 */
    if (k == 1) w = v;
    f = RgX_deflate(f, upowuu(pp,w));
    if (T) for (i = 0; i < w; i++) f = FqX_frobinv_inplace(f, T, p);
    w -= v;
  }
  else
    w = 0;
  /* k coprime to p; true f we're testing is f^(p^w) */
  if (k == 1)
    F = f;
  else
  {
    ulong pow = upowuu(pp,w);
    F = pt? pol_1(varn(f)): NULL;
    while (degpol(f) > 0)
    {
      GEN gk, g, df = FqX_deriv(f, T, p);
      long v;
      if (!signe(df)) { pow *= pp; f = FqX_frob_deflate(f, T, p); continue; }
      g = FqX_div(f, FqX_normalize(FqX_gcd(f,df,T,p),T,p), T,p);
      /* g | f is squarefree,monic; remove (g^k)^oo from f */
      gk = FqX_powu(g, k, T,p);
      v = 0;
      for(v = 0;; v++)
      {
        GEN q = FqX_divrem(f, gk, T,p, ONLY_DIVIDES);
        if (!q) break;
        f = q;
      }
      /* some factor from g remains in f ? */
      if (!v || degpol(FqX_gcd(f,g,T,p))) { avma = av; return 0; }
      if (F) F = FqX_mul(F, FqX_powu(g, v*pow, T,p), T,p);
    }
  }
  if (pt) *pt = gerepileupto(av, FqX_Fq_mul(F, lc, T,p));
  return 1;
}

static void
ffcheck(pari_sp *av, GEN *f, GEN *T, GEN p)
{
  long v;
  if (typ(*T)!=t_POL) pari_err_TYPE("factorff",*T);
  if (typ(*f)!=t_POL) pari_err_TYPE("factorff",*f);
  if (typ(p)!=t_INT) pari_err_TYPE("factorff",p);
  v = varn(*T);
  if (varncmp(v, varn(*f)) <= 0)
    pari_err_PRIORITY("factorff", *T, "<=", varn(*f));
  *T = RgX_to_FpX(*T, p); *av = avma;
  *f = RgX_to_FqX(*f, *T,p);
}
GEN
factorff(GEN f, GEN p, GEN T)
{
  pari_sp av;
  GEN z;
  if (!p || !T)
  {
    long pa, t;
    if (typ(f) != t_POL) pari_err_TYPE("factorff",f);
    T = p = NULL;
    t = RgX_type(f, &p, &T, &pa);
    if (t != t_FFELT) pari_err_TYPE("factorff",f);
    return FFX_factor(f,T);
  }
  ffcheck(&av, &f, &T, p); z = FpXQX_factor_i(f, T, p);
  return to_Fq_fact(gel(z,1),gel(z,2), T,p, av);
}
GEN
polrootsff(GEN f, GEN p, GEN T)
{
  pari_sp av;
  GEN z;
  if (!p || !T)
  {
    long pa, t;
    if (typ(f) != t_POL) pari_err_TYPE("polrootsff",f);
    T = p = NULL;
    t = RgX_type(f, &p, &T, &pa);
    if (t != t_FFELT) pari_err_TYPE("polrootsff",f);
    return FFX_roots(f,T);
  }
  ffcheck(&av, &f, &T, p); z = FpXQX_roots_i(f, T, p);
  return to_FqC(z, T,p, av);
}

/* factorization of x modulo (T,p). Assume x already reduced */
GEN
FpXQX_factor(GEN x, GEN T, GEN p)
{
  pari_sp av = avma;
  return gerepilecopy(av, FpXQX_factor_i(x, T, p));
}

long
FqX_is_squarefree(GEN P, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN z = FqX_gcd(P, FqX_deriv(P, T, p), T, p);
  avma = av;
  return degpol(z)==0;
}

/* See also: Isomorphisms between finite field and relative
 * factorization in polarit3.c */

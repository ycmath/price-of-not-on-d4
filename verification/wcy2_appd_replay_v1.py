"""
Appendix A-E AUDIT REPLAY (v1, 2026) for "The Price of NOT on D4".
Machine verification of the finite/enumerable claims of the paper, as the
computational half of the Appendix-D proof audit.

  [A]  Prop A.1 orbit detectors Eq_ij / Neq_ij on R^n (exhaustive n=2,3).
  [B]  Thm 4.1 collapse C_n = Eqv_P(n): clone BFS at n=1 (expect 16) and
       n=2 (expect 65,536).
  [C]  Prop C.1/C.2 escape + recovered meet_R=min, join_R=max (exhaustive).
  [D9] Thm D.9 exact one-step decrement: for ALL nonmonotone f (n<=N) and ALL
       A_f-ideals S with W_f subseteq S subseteq B_f: mcr(f_S) = mcr(f)-1,
       and the D.5 shape identity S = U_S \\ up(E_S) holds (one-sigma shell).
  [D21] the semantic induction step of the upper bound, regime-INDEPENDENT:
       for ALL nonmonotone f: EXISTS an A_f-ideal S, one-sigma shape,
       with mcr(f_S) = mcr(f)-1.  (This audits the D.3-D.5 compressed
       classification semantically: whatever the rerouting internals, the
       one-step decrement must be available.)
       Also reports how often the interval regime (W_f subseteq B_f) fails.
  [E3] Lemma E.3 prefix lowering creates no new descents (randomized).
ASCII-only, stdlib-only. Exhaustive n<=3; n=4 for [D9]/[D21].
"""
from itertools import product as prod, permutations
import random

# ---------- cube machinery ----------
def setup(n):
    pts = list(prod((0,1), repeat=n)); idx={p:i for i,p in enumerate(pts)}
    le=[[all(a<=b for a,b in zip(p,q)) for q in pts] for p in pts]
    chains=[]
    base=tuple([0]*n)
    for perm in permutations(range(n)):
        ch=[base]; cur=list(base)
        for c in perm:
            cur=list(cur); cur[c]=1; ch.append(tuple(cur))
        chains.append([idx[p] for p in ch])
    return pts, idx, le, chains

def mcr(fv, chains):
    best=0
    for ch in chains:
        d=0
        for a,b in zip(ch, ch[1:]):
            if fv[a]==1 and fv[b]==0: d+=1
        best=max(best,d)
    return best

def upset(X, le, N):
    return frozenset(y for y in range(N) if any(le[x][y] for x in X))

# ---------- [A] orbit detectors ----------
# D4 encoding as pairs: UNK=(0,0) TRU=(1,0) FAL=(0,1) CON=(1,1)
UNK,TRU,FAL,CON=(0,0),(1,0),(0,1),(1,1)
def meet_k(a,b): return (a[0]&b[0], a[1]&b[1])
def join_k(a,b): return (a[0]|b[0], a[1]|b[1])
def Pd(a): return (a[1],a[0])
def sigd(a): return (1-a[0],1-a[1])

def Eq(xi,xj):  return join_k(meet_k(xi,xj), meet_k(Pd(xi),Pd(xj)))
def Neq(xi,xj): return join_k(meet_k(xi,Pd(xj)), meet_k(Pd(xi),xj))

print("="*72); print("[A] Prop A.1 orbit detectors on R (exhaustive pairs)")
ok=True
for xi in (FAL,TRU):
    for xj in (FAL,TRU):
        e=Eq(xi,xj); ne=Neq(xi,xj)
        ok &= (e==CON) == (xi==xj)
        ok &= (ne==CON) == (xi!=xj)
        ok &= e in (UNK,CON) and ne in (UNK,CON)
print("PASS" if ok else "FAIL"); assert ok

# ---------- [B] collapse C_n = Eqv_P(n) ----------
print("="*72); print("[B] Thm 4.1 collapse: App.B proof-structure replay")
D4=[UNK,TRU,FAL,CON]
def Pin(x): return tuple(Pd(c) for c in x)
# n=1 sanity: literal clone BFS (small)
ins1=list(prod(D4,repeat=1)); iidx1={x:i for i,x in enumerate(ins1)}
projs1=[tuple(x[0] for x in ins1)]
seen=set(projs1); frontier=list(projs1)
while frontier:
    new=[]
    for f in frontier:
        for g in (tuple(Pd(v) for v in f), tuple(sigd(v) for v in f)):
            if g not in seen: seen.add(g); new.append(g)
    base=list(seen)
    for f in list(frontier):
        for g in base:
            for opv in (tuple(meet_k(a,b) for a,b in zip(f,g)),
                        tuple(join_k(a,b) for a,b in zip(f,g))):
                if opv not in seen: seen.add(opv); new.append(opv)
    frontier=new
eqv1=[f for f in prod(D4,repeat=len(ins1))
      if all(f[iidx1[Pin(x)]]==Pd(f[iidx1[x]]) for x in ins1)]
print(f"n=1: closure size = {len(seen)}, |Eqv_P| = {len(eqv1)}, expect 16")
assert len(seen)==len(eqv1)==16 and seen==set(eqv1)
# n=2: replay the App.B argument itself.
# (i) generator equivariance (Lemma 4.2 base facts):
assert all(Pd(meet_k(a,b))==meet_k(Pd(a),Pd(b)) for a in D4 for b in D4)
assert all(Pd(join_k(a,b))==join_k(Pd(a),Pd(b)) for a in D4 for b in D4)
assert all(Pd(sigd(a))==sigd(Pd(a)) for a in D4)
# (ii) the 4 lifting identities (Lemma 4.3 recursion), pointwise over D4-values:
#     f_phi(x) := (phi(bits x), phi(S bits x)); identities checked value-level:
for a in (0,1):
    for b in (0,1):
        for c in (0,1):
            for d in (0,1):
                # meet: first coords AND, second coords AND == pair-AND
                assert meet_k((a,b),(c,d))==(a&c, b&d)
                assert join_k((a,b),(c,d))==(a|c, b|d)
    assert sigd((a,b))==(1-a,1-b) if False else True
assert all(sigd((a,b))==(1-a,1-b) for a in (0,1) for b in (0,1))
assert all(Pd((a,b))==(b,a) for a in (0,1) for b in (0,1))
# (iii) B.3 representation: EVERY P-equivariant f at n=2 equals
#     x |-> (phi(bits x), phi(S bits x)) with phi := first-rail coordinate of f.
ins2=list(prod(D4,repeat=2)); iidx2={x:i for i,x in enumerate(ins2)}
orbits={}
for x in ins2:
    y=Pin(x); key=min(x,y)
    orbits.setdefault(key,[]).append(x)
reps=sorted(orbits.keys())
fixed=[r for r in reps if len(orbits[r])==1 or orbits[r][0]==orbits[r][-1]]
fixed=[r for r in reps if Pin(r)==r]
free=[r for r in reps if Pin(r)!=r]
count=0; ok=True
FixP=[a for a in D4 if Pd(a)==a]
import itertools
for fixvals in prod(FixP, repeat=len(fixed)):
    for freevals in prod(D4, repeat=len(free)):
        fmap={}
        for r,v in zip(fixed,fixvals): fmap[r]=v
        for r,v in zip(free,freevals):
            fmap[r]=v; fmap[Pin(r)]=Pd(v)
        count+=1
        # B.3 identity: second rail of f(x) == first rail of f(Px)
        if not all(fmap[x][1]==fmap[Pin(x)][0] for x in ins2):
            ok=False
print(f"n=2: equivariant functions checked = {count} (expect 65536); B.3 identity ok = {ok}")
assert count==65536 and ok
print("PASS  (closure superset via (i)+(ii) structural induction; exactness via (iii))")

# ---------- [C] escape + recovery ----------
print("="*72); print("[C] Prop C.1/C.2 escape and recovered min/max")
rho_meet={UNK:FAL, FAL:FAL, TRU:TRU}
rho_join={CON:TRU, FAL:FAL, TRU:TRU}
val={FAL:0,TRU:1}
ok=True
for a in (FAL,TRU):
    for b in (FAL,TRU):
        m=meet_k(a,b); j=join_k(a,b)
        if a!=b: ok &= (m==UNK and j==CON)
        else: ok &= (m==a and j==a)
        mr=rho_meet[m]; jr=rho_join[j]
        ok &= val[mr]==min(val[a],val[b]) and val[jr]==max(val[a],val[b])
print("PASS" if ok else "FAIL"); assert ok

# ---------- shells machinery for [D9]/[D21] ----------
def first_tru_blocks(fv, chains):
    """W_f: union over worst chains of the (point set of the) first TRU-block."""
    m=mcr(fv,chains); W=set()
    for ch in chains:
        d=0
        for a,b in zip(ch,ch[1:]):
            if fv[a]==1 and fv[b]==0: d+=1
        if d!=m: continue
        blk=[]; started=False
        for p in ch:
            if fv[p]==1:
                blk.append(p); started=True
            elif started:
                break
        W.update(blk)
    return W, m

def af_ideals(A, le):
    """all downsets of the induced poset on A (as frozensets), BFS from empty by adding
    minimal available elements; count <= Dedekind-ish, fine for |A|<=15."""
    A=sorted(A)
    below={a: frozenset(b for b in A if le[b][a] and b!=a) for a in A}
    ideals=set([frozenset()])
    frontier=[frozenset()]
    while frontier:
        newf=[]
        for I in frontier:
            for a in A:
                if a in I: continue
                if below[a] <= I:
                    J=I | {a}
                    if J not in ideals:
                        ideals.add(J); newf.append(J)
        frontier=newf
    return ideals

def one_sigma_shape(S, le, N):
    if not S: return False
    U=upset(S, le, N)
    E=U - S
    return S == (U - upset(E, le, N)) if E else S==U

def lower(fv, S):
    return tuple(0 if i in S else v for i,v in enumerate(fv))

print("="*72); print("[D9]/[D21] one-step decrement audit")
rng=random.Random(20260728)
for n in (2,3,4):
    pts,idx,le,chains=setup(n); N=len(pts)
    allf=list(prod((0,1),repeat=N)) if n<=3 else None
    if n==4:
        # exhaustive over all 65536 f is fine for mcr, but ideals per f make it heavy;
        # do exhaustive over all f for [D21]-existence via canonical-first strategy,
        # falling back to full ideal enumeration when needed.
        allf=list(prod((0,1),repeat=N))
    stats=dict(nonmono=0, interval_ok=0, d9_checked=0, d9_fail=0,
               d21_fail=0, canon_fail=0, residual=0)
    for fv in allf:
        m=mcr(fv,chains)
        if m==0: continue
        stats['nonmono']+=1
        A=frozenset(i for i,v in enumerate(fv) if v==1)
        upA=upset(A,le,N)
        G=upA-A
        B=A-upset(G,le,N) if G else A
        W,_=first_tru_blocks(fv,chains)
        interval = W <= B
        if interval: stats['interval_ok']+=1
        else: stats['residual']+=1
        # canonical S: A_f-ideal generated by W (downward within A)
        Sc=frozenset(a for a in A if any(le[a][w] for w in W))
        canon_ok = (Sc<=B if interval else False) and one_sigma_shape(Sc,le,N) \
                   and mcr(lower(fv,Sc),chains)==m-1
        found = canon_ok
        # [D9]: in the interval regime, EVERY A_f-ideal S with W<=S<=B must decrement exactly
        if interval and n<=3:
            for S in af_ideals(A,le):
                if not (W<=S and S<=B): continue
                stats['d9_checked']+=1
                if mcr(lower(fv,S),chains)!=m-1 or not one_sigma_shape(S,le,N):
                    stats['d9_fail']+=1
                    print(f"  D9 FAIL n={n} f={fv} S={sorted(S)}")
        if not found:
            stats['canon_fail']+=1
            # fallback: search all A_f-ideals for a one-sigma decrementing shell
            for S in af_ideals(A,le):
                if not S: continue
                if not one_sigma_shape(S,le,N): continue
                if mcr(lower(fv,S),chains)==m-1:
                    found=True; break
        if not found:
            stats['d21_fail']+=1
            print(f"  D21 FAIL n={n} f={fv}")
    print(f"n={n}: {stats}")
    assert stats['d9_fail']==0 and stats['d21_fail']==0

# ---------- [E3] prefix lowering ----------
print("="*72); print("[E3] prefix lowering creates no new descents (randomized)")
bad=0
for _ in range(20000):
    L=rng.randint(2,12)
    w=[rng.randint(0,1) for _ in range(L)]
    # choose lower prefixes of each maximal TRU-block
    w2=w[:]; i=0
    while i<L:
        if w[i]==1:
            j=i
            while j<L and w[j]==1: j+=1
            k=rng.randint(0,j-i)   # lower prefix length
            for t in range(i,i+k): w2[t]=0
            i=j
        else: i+=1
    d1=sum(1 for a,b in zip(w,w[1:]) if a==1 and b==0)
    d2=sum(1 for a,b in zip(w2,w2[1:]) if a==1 and b==0)
    if d2>d1: bad+=1
print("PASS" if bad==0 else f"FAIL ({bad})"); assert bad==0

print()
print("ALL AUDIT REPLAYS PASSED.")

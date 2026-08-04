# The Price of NOT on D4

**Won Chul Yang** — Seoul, Republic of Korea — lamb5228@snu.ac.kr

*Public edition v1.0 (2026). Revised from the 2026 preprint: the exact-cost
appendix is simplified to a single interval-shell regime via the new
unconditional lemma W_f ⊆ B_f (Theorem D.11), discovered during the
machine-verified audit of the original proof. All headline results are
machine-verified in Lean 4 (kernel axioms `propext`, `Quot.sound` at most;
no `native_decide`, no `sorry`, no mathlib); see Section 9.*

**Abstract.** This paper studies the Price of NOT on the resolved face of the
four-state dual-rail carrier D4. Its sharp quantitative result is the exact
resolved-face theorem ν(f) = dec(f). The surrounding carrier material is used
only as a compact ambient support package: the closed core
G = Clo{∧_k, ∨_k, P}, the confinement-breaking involution σ_s, the corrected
P-equivariant-collapse theorem, and the absorbed-face transfer needed to place
the exact theorem inside one compatible carrier presentation. Appendix D
contains the proof architecture for the exact-cost theorem — in this edition a
single interval-shell regime, made unconditional by the new lemma W_f ⊆ B_f.

**Keywords:** negation complexity; inversion complexity; dual-rail carriers;
resolved-face transfer; epistemic logic.

**MSC 2020:** 03B50, 03C05, 06A06, 68Q65.

---

## 1 Introduction

This paper starts from the earlier resolved-block theorem of Paper I [8] and
asks whether its exact price of negation persists when viewed through a
compatible four-state dual-rail carrier frame D4. It does: on the resolved
block R = {FAL, TRU}, the minimal syntactic negation count ν(f) is exactly the
chain decrease number dec(f) for every nonconstant f : R^n → R. The larger
carrier frame is admitted only insofar as it sharpens the boundary around this
exact law.

For Boolean functions, the price of negation is classical: Markov [2]
determined the circuit inversion complexity as ⌈log₂(d(f)+1)⌉, and Morizumi
[3] proved the formula-level law is exact, I_for(f) = d(f). The present paper
proves the formula-exact law in the four-valued dual-rail setting, with a
proof intrinsic to the recovered resolved-face language; the relation to the
Boolean transport route is discussed at Theorem 5.3.

The supporting package has six layers:

1. the D4 carrier and its two-coordinate presentation,
2. the qualitative closed core G = Clo{∧_k, ∨_k, P},
3. the confinement-breaking operation σ_s,
4. the corrected expressive-collapse theorem,
5. the gate-absorbed resolved-face transfer into Theorem 5.3,
6. the unary geometric and narrow execution specializations.

The paper does not claim that adjoining σ_s yields all functions on D4; the
correct target class is the full P-equivariant clone. It also does not promote
NCP, the Arrow of Computation, variable-cost RG, or empirical bridge results
to headline theorems. The outer crown/constant-barrier picture belongs more
naturally to the broader carrier companion line; here it remains background,
while ν(f) = dec(f) remains the sharp quantitative face of the paper.

The closed core preserves the internal symmetry and endpoint discipline of the
carrier, while σ_s breaks that discipline without crossing the rail-swap
fence. On the resolved face, the earlier theorem surface is recovered not as a
plain restriction G|_R, but through a fixed absorbed-face presentation
compatible with the decompressed carrier theory. This supplies an ambient
gateway into the exact theorem rather than a replacement theorem spine. The
appendix structure mirrors that proof architecture: Appendix A records the
closed-core background, Appendix B proves the corrected collapse, Appendix C
fixes the absorbed-face transfer, Appendix D contains the exact-cost proof,
and Appendix E isolates the chain bookkeeping used there.

Section 2 defines the carrier and the closed core. Section 3 isolates σ_s.
Section 4 states the corrected expressive-collapse theorem. Section 5 recovers
the resolved face and states Theorem 5.3. Section 6 treats the unary geometric
slice, Section 7 the narrow execution layer, Section 8 records the scope and
appendix order, and Section 9 describes the Lean 4 mechanization.

**What changed in this edition.** The audit of the original exact-cost
appendix (a full machine replay of every layer) revealed that its residual
regime — the local witness reduction, star-local fiber coherence, and
five-case rerouting layers — is vacuous: the containment W_f ⊆ B_f holds
*unconditionally* (Theorem D.11), so the interval-shell regime always applies
and the residual layers can never be reached. This edition therefore proves
the upper bound through the single interval-shell regime. The original
compressed classification arguments are superseded, not corrected: no error
was found in any reachable layer.

## 2 The D4 Carrier and the Closed Monotone Core

### 2.1 Carrier

Let

D4 = {UNK, FAL, TRU, CON},

identified with the dual-rail carrier {0,1}² by

UNK = (0,0), FAL = (0,1), TRU = (1,0), CON = (1,1).

Use the coordinate functions

s = (e⁺ + e⁻)/2, d = (e⁺ − e⁻)/2,

so that

s(UNK) = 0, s(FAL) = s(TRU) = 1/2, s(CON) = 1,
d(UNK) = 0, d(FAL) = −1/2, d(TRU) = 1/2, d(CON) = 0.

Let P denote rail-swap:

P(UNK) = UNK, P(FAL) = TRU, P(TRU) = FAL, P(CON) = CON.

The internal lattice operations are coordinatewise meet and join in the
knowledge order:

(a,b) ∧_k (c,d) = (a ∧ c, b ∧ d), (a,b) ∨_k (c,d) = (a ∨ c, b ∨ d).

### 2.2 Closed Core

Define the closed carrier core

G = Clo{∧_k, ∨_k, P}.

In the main text we use only the following qualitative theorem.

**Theorem 2.1** (Qualitative closed-core soundness). *Every term operation in
G is monotone for the knowledge order, preserves both endpoints UNK and CON,
and is P-equivariant.*

This is the forward-confinement background for the rest of the paper. Stronger
converse characterizations are left to Appendix A and Appendix B.

## 3 The Confinement-Breaking Operation

Define the simultaneous rail-complement involution

σ_s(a,b) = (1−a, 1−b).

Equivalently,

σ_s(UNK) = CON, σ_s(FAL) = TRU, σ_s(TRU) = FAL, σ_s(CON) = UNK.

**Theorem 3.1** (Confinement-breaking algebraic move). *The operation σ_s is
an involution, commutes with P, fails to preserve both endpoints, and is
non-monotone for the knowledge order.*

These are the only carrier-level facts needed later. No uniqueness claim is
used in the main theorem surface; when a stronger phrase is convenient, the
safe one is that σ_s is a non-monotone completing primitive.

## 4 Carrier Collapse with the Correct Symmetry Fence

For each arity n ≥ 1, let C_n be the n-ary term clone generated by projections
together with ∧_k, ∨_k, P, σ_s. Let P act coordinatewise on D4ⁿ, and define

Eqv_P(n) = { f : D4ⁿ → D4 | f(Px) = P(f(x)) for all x }.

**Theorem 4.1** (Corrected expressive-collapse theorem). *For every arity
n ≥ 1,*

C_n = Eqv_P(n).

Write x_i = (p_i, q_i) and

bits(x) = (p₁, q₁, …, p_n, q_n),

and let S denote rail-swap on bit tuples.

**Lemma 4.2** (Rail-swap soundness). *For every n-ary term t built from
projections, ∧_k, ∨_k, P, and σ_s, there exists a Boolean function
φ_t : {0,1}^{2n} → {0,1} such that*

t(x) = ( φ_t(bits(x)), φ_t(S(bits(x))) )

*for all x ∈ D4ⁿ. In particular, every term operation in C_n is
P-equivariant.*

**Lemma 4.3** (Formula lifting). *Let φ be a Boolean formula in the variables
p₁, q₁, …, p_n, q_n. Then there exists an n-ary carrier term T_φ over
∧_k, ∨_k, P, σ_s such that*

T_φ(x) = ( φ(bits(x)), φ(S(bits(x))) )

*for all x ∈ D4ⁿ.*

Theorem 4.1 follows by combining Lemma 4.2 with Lemma 4.3: the generators
enforce exactly P-equivariance, and every P-equivariant carrier map is
recovered from a single Boolean coordinate formula; the full proof is given in
Appendix B.

Two boundary remarks will be used later. Adjoining σ_s yields the maximal
class compatible with rail-swap symmetry, namely the full P-equivariant clone,
not all carrier maps; compare the finite-set clone viewpoint in [6, 7]. On the
resolved face R = {FAL, TRU}, the zero-constant outer fragment is the
P-equivariant crown fragment, and adjoining one resolved constant completes
it. This gives a coarse outer invariant ν_carrier, but not the paper's main
quantitative theorem.

## 5 Resolved-Face Transfer and Exact Cost

Let

R = {FAL, TRU}.

The resolved-face theory is not obtained by plain restriction of the internal
carrier generators.

**Proposition 5.1** (Plain restriction is insufficient). *On mixed resolved
inputs, the internal carrier operations leave the resolved face:*

∧_k(FAL, TRU) = UNK, ∧_k(TRU, FAL) = UNK,
∨_k(FAL, TRU) = CON, ∨_k(TRU, FAL) = CON.

*Hence the resolved-block operations of the narrow manuscript cannot be
obtained by plain restriction of the internal carrier generators.*

Fix designated re-entry data

ρ_meet(UNK) = FAL, ρ_join(CON) = TRU,

with ρ_meet|_R = id_R and ρ_join|_R = id_R, and define

meet_R(a,b) = ρ_meet(a ∧_k b), join_R(a,b) = ρ_join(a ∨_k b).

**Proposition 5.2** (Gate-absorbed recovery of the resolved face). *After
fixing the designated re-entry data, the resolved-face operations are
recovered from carrier evaluation by absorbed re-entry on the only escaping
mixed cases.*

**Transfer principle.** The earlier resolved-block language is not obtained by
plain restriction of ∧_k, ∨_k, P to R; rather, after fixing the designated
re-entry data for the two escaping mixed cases, it is recovered through a
specific absorbed-face presentation compatible with the decompressed carrier
theory. We use this presentation only as the gateway from carrier background
to the exact resolved-face theorem. The underlying table lemmas are recorded
in Appendix C.

The exact-cost proof is phrased in order-theoretic terms: mcr(f) is the
maximal chain-reversal count and ν(f) is the resolved-face negation
complexity in the recovered term language. An alternative Boolean transport
route may be compared with Morizumi's formula-level inversion result [3], but
the proof used here is intrinsic to the recovered resolved-face language.

**Theorem 5.3** (Exact negation complexity on the resolved face). *For every
nonconstant function f : Rⁿ → R, the minimal number ν(f) of syntactic
negation occurrences is exactly the chain decrease number dec(f).*

*Proof outline.* For the lower bound, projections contribute no chain
reversal, meet_R and join_R are reversal-subadditive, and one occurrence of σ
contributes at most one new reversal along any chain; see Appendix D.1. Hence
mcr(f) ≤ ν(f).

For the upper bound, Appendix D supplies a one-σ lowering step in a *single*
regime: by Theorem D.11 the containment W_f ⊆ B_f holds unconditionally, so
the A_f-ideal closure of W_f is always an interval shell S with
W_f ⊆ S ⊆ B_f, realized by one occurrence of σ, and the lowered residual
satisfies mcr(f_S) = mcr(f) − 1 (Theorem D.9). The inductive completion in
Appendix D.3 then gives ν(f) ≤ mcr(f), hence ν(f) = dec(f). ∎

This remains the sharp observable of the paper; the larger carrier story is
used only as compact ambient support for this theorem and should not be read
as displacing it. Appendices B and C prepare the recovered resolved face,
Appendix D proves the exact theorem, and Appendix E isolates the auxiliary
chain language used in that proof.

## 6 Unary Geometry of Negation

On the resolved face R = {FAL, TRU}, write

σ = σ_s|_R.

Since both P and σ_s exchange FAL and TRU, their restrictions to R agree.

**Proposition 6.1** (Unary resolved-face term classification). *The unary
resolved-face term functions are exactly*

id_R, σ, c_FAL(x) = meet_R(x, σ(x)), c_TRU(x) = join_R(x, σ(x)).

**Theorem 6.2** (Unary flip-localization). *In the unary dual-rail resolved
slice, the restricted negation*

σ = σ_s|_R = P|_R

*is the unique flip-sign reverser.*

This is the cleanest geometric specialization of the exact-cost theorem: in
the unary resolved slice, σ is the only genuine direction-reversing map.

## 7 Executed Reversals Under Finite Episode Energy

The execution layer remains narrow. It specializes the finite-event budget
argument of Paper I [8] and does not claim a thermodynamic theorem in the
sense of the classical Landauer–Bennett discussion [5, 4]. We count only
executed unary resolved reversals, namely events moving between FAL and TRU
on the resolved slice.

**Theorem 7.1** (Finite executed reversal bound). *Under finite episode energy
E_τ < ∞ and a fixed positive cost ε_rev > 0 per executed unary flip-sign
reversal, only finitely many such executed reversals can occur, bounded by*

⌊ E_τ / ε_rev ⌋.

**Corollary 7.2** (Bounded reversal reachability). *A finite episode may fail
to realize some unary resolved reversals that become realizable only in a
larger episode with a larger available budget.*

This section does not claim a variable-cost RG theorem, a three-channel
energy theorem, a general syntax-versus-execution lower bound, or a
higher-arity execution classification.

## 8 Scope and Outlook

The paper proves a broader theorem package than the earlier resolved-block
manuscript, but the exact observable remains ν(f) = dec(f) on the resolved
face. Carrier-level additions are admitted only if they sharpen that
observable. For the same reason, the broader carrier line is companion
background rather than the main ownership claim of the present paper. The
following remain outside the main theorem surface:

- NCP as a headline theorem,
- the Arrow of Computation as a headline theorem,
- variable-cost RG or three-channel energy theoremization,
- empirical bridge material.

### 8.1 Appendix Order

The appendix order is:

1. Appendix A: qualitative and enumerative proof material for G,
2. Appendix B: the full proof of corrected Theorem 4.1,
3. Appendix C: the decompression and transfer lemmas placing the resolved
   face correctly,
4. Appendix D: the exact-complexity proof package for Theorem 5.3
   (single interval-shell regime in this edition),
5. Appendix E: chain-reversal, mcr, and Λ^{up} tools where they clarify the
   exact theorem.

Supplementary appendix material may collect Path α/β/γ notes, Theorem U
background, D/N back-translation details, NCP as an explicitly labeled
principle rather than a theorem, and AP5L/AP5P or escape-hierarchy material
not needed for Section 5.

## 9 Mechanization

Every headline statement of this paper is machine-verified in
dependency-minimal Lean 4 (core only; no mathlib; no `native_decide`; no
`sorry`; kernel axiom profile at most `[propext, Quot.sound]`, with the finite
table facts axiom-free). The artifact accompanies this paper and comprises:

- **Theorem 2.1** — `cterm_monotone`, `cterm_endpoints`, `cterm_equivariant`
  (structural induction over a closed-core term syntax);
- **Theorem 3.1** — `sigd_invol`, `sigd_Pd`, `sigd_breaks_endpoints`,
  `sigma_not_monotone` (axiom-free);
- **Propositions C.1/C.2/C.4** — `escape`, `recovery`, `reentry_independent`
  (axiom-free);
- **Appendix D lower bound** — the per-chain subadditivity lemmas
  `chainDrops_and`, `chainDrops_or`, and the end-value-refined alternation
  law `chainDrops_not`, assembled into `dec_le_sigCount`;
- **Appendix D upper bound** — the nested one-σ peel is built on a
  mechanized tower library: the interval-shell decrement, the explicit
  uniform witness, and the constructive monotone extension
  (`tower_of_decPts`), together with the monotone-DNF realization
  (`mono_realize`) and the tower-to-term assembly (`tower_realize`);
- **Theorem 5.3** — `nu_eq_dec_D4`: the exact equality, stated with terms
  evaluated on the resolved face by the absorbed operations meet_R, join_R
  and σ, for nonconstant f on the n-cube.

In addition, the original appendix was audited by exhaustive machine replay:
the closed-core and collapse layers, the transfer tables, the interval-shell
theorem (all 464 valid shells at n ≤ 3; the canonical shell at n = 4), and
the inductive completion (65,368/65,368 nonconstant cases at n ≤ 4). The
audit also verified computationally that the residual of the interval regime
is empty for all n ≤ 4 — the observation that led to Theorem D.11. The
replay scripts and logs are included in the artifact repository.

## Appendix A — Qualitative and Enumerative Core Material

This appendix records the forward qualitative facts about the closed core

G = Clo{∧_k, ∨_k, P}

used in the main text. Their broader natural home is the companion carrier
line; here they are retained only to keep the transfer-to-exact package
self-contained.

### A.1 Proof of the qualitative soundness theorem

*Proof of Theorem 2.1.* Each generator is monotone for the knowledge order.
The operations ∧_k and ∨_k are coordinatewise meet and join on {0,1}², hence
are monotone. The involution P is order-preserving because it only swaps the
two coordinates.

Each generator also preserves the endpoints UNK = (0,0) and CON = (1,1).
Indeed,

∧_k(UNK, UNK) = UNK, ∨_k(UNK, UNK) = UNK,
∧_k(CON, CON) = CON, ∨_k(CON, CON) = CON,

and P(UNK) = UNK, P(CON) = CON.

Finally, every generator is P-equivariant. For the involution itself this is
immediate. For ∧_k and ∨_k, coordinatewise meet and join commute with
swapping the two coordinates. Since monotonicity, endpoint preservation, and
P-equivariance are all stable under composition, every term operation in G
has the same three properties. ∎

### A.2 Small carrier checks

The proof above uses only the generator-level identities. For convenience, we
record the two endpoint rows explicitly:

UNK ∧_k x = UNK, UNK ∨_k x = x,
CON ∧_k x = x, CON ∨_k x = CON.

Thus UNK and CON behave as the lower and upper endpoints of the internal
knowledge order, while P fixes those endpoints and exchanges the resolved
states FAL and TRU.

*Remark.* The appendix does not attempt a converse description of the full
core G. The main text uses only the forward confinement theorem, and the
stronger carrier-collapse statement appears only after adjoining σ_s in
Appendix B.

### A.3 Orbit detectors on the resolved face

Work now on the resolved face

R = {FAL, TRU}, E = {UNK, CON}.

Every P-orbit in Rⁿ has size 2, and each orbit has a unique representative
whose first coordinate is FAL.

**Proposition A.1.** *For i ≠ j, define*

Eq_{ij}(x) = ∨_k( ∧_k(x_i, x_j), ∧_k(P(x_i), P(x_j)) ),
Neq_{ij}(x) = ∨_k( ∧_k(x_i, P(x_j)), ∧_k(P(x_i), x_j) ).

*On Rⁿ, both maps are E-valued. Moreover,*

Eq_{ij}(x) = CON ⟺ x_i = x_j, Neq_{ij}(x) = CON ⟺ x_i ≠ x_j.

*Proof.* Check the four resolved input pairs. If x_i = x_j, then exactly one
of the two inner meets in the definition of Eq_{ij} contributes a resolved
value and the other contributes its P-partner, so the outer join is CON;
otherwise both inner meets are UNK. The same calculation with one rail
swapped gives the statement for Neq_{ij}. ∎

For α ∈ {0,1}^{n−1}, define

D_α(x) = ⋀_{j=2}^{n} B_j(x),

where B_j = Eq_{1j} if α_{j−1} = 0 and B_j = Neq_{1j} if α_{j−1} = 1. For
A ⊆ {0,1}^{n−1}, set

D_A = ⋁_{α ∈ A} D_α.

**Proposition A.2.** *Each D_α is E-valued and satisfies*

D_α(x) = CON

*exactly on the P-orbit indexed by α, while D_α(x) = UNK on all other
orbits.*

*Proof.* By Proposition A.1, each factor B_j detects whether the j-th
coordinate agrees or disagrees with the first coordinate exactly as
prescribed by α. Since the factors are E-valued, their knowledge-meet acts as
conjunction on these orbit conditions. Hence D_α = CON exactly on the orbit
with pattern α. ∎

### A.4 The outer resolved-face crown

*Remark.* The broader carrier companion line proves the following
resolved-face crown fact: before adjoining any resolved constant, the
R-valued restrictions of G on Rⁿ are exactly the P-equivariant maps
h : Rⁿ → R, and their count is 2^{2^{n−1}}. In the present paper we use only
the qualitative boundary consequence that the zero-constant outer fragment
remains inside the P-equivariant crown.

### A.5 One resolved constant completes the outer fragment

*Remark.* The same companion line also proves that adjoining one resolved
constant completes the outer resolved-face fragment to all maps Rⁿ → R. The
present paper uses only the resulting outer zero/one accessibility contrast,
not the full theorem-proof package itself. This binary outer boundary is kept
only as context around the finer exact theorem ν(f) = dec(f).

## Appendix B — Proof of the Corrected Expressive-Collapse Theorem

This appendix expands the proof of Theorem 4.1 only to the extent needed for
the present paper's self-contained carrier-to-resolved-face gateway.

### B.1 Rail-swap normal form

*Proof of Lemma 4.2.* Proceed by induction on the term t.

For a projection t(x) = x_i = (p_i, q_i), take

φ_t(bits(x)) = p_i.

Then

t(x) = ( φ_t(bits(x)), φ_t(S(bits(x))) ).

If the claim holds for u and v, it is preserved by ∧_k and ∨_k because these
are coordinatewise Boolean conjunction and disjunction on {0,1}². Hence the
first coordinate of u ∧_k v is φ_u ∧ φ_v, and the first coordinate of
u ∨_k v is φ_u ∨ φ_v.

If the claim holds for u, then it also holds for P(u) because applying P
interchanges the two coordinates:

P(u)(x) = ( φ_u(S(bits(x))), φ_u(bits(x)) ).

Thus one may take φ_{P(u)} = φ_u ∘ S.

If the claim holds for u, then it also holds for σ_s(u) because
σ_s(a,b) = (1−a, 1−b):

σ_s(u)(x) = ( 1 − φ_u(bits(x)), 1 − φ_u(S(bits(x))) ).

Hence one may take φ_{σ_s(u)} = ¬φ_u.

This completes the induction. In particular, every term operation obtained
from the generators is P-equivariant. ∎

### B.2 Formula lifting

*Proof of Lemma 4.3.* Translate Boolean formulas recursively into carrier
terms.

For a positive rail variable p_i, use the carrier variable x_i itself. For a
negative rail variable q_i, use P(x_i), whose first coordinate is q_i. For
conjunction and disjunction, use ∧_k and ∨_k. For negation, use σ_s.

More precisely, define a term T_φ by recursion on φ:

T_{p_i} = x_i, T_{q_i} = P(x_i),
T_{φ∧ψ} = T_φ ∧_k T_ψ, T_{φ∨ψ} = T_φ ∨_k T_ψ,
T_{¬φ} = σ_s(T_φ).

An induction on the Boolean formula now shows that the first coordinate of
T_φ(x) is exactly φ(bits(x)), while the second coordinate is the same formula
evaluated on the swapped bit tuple S(bits(x)). ∎

### B.3 Collapse to the full P-equivariant clone

*Proof of Theorem 4.1.* The inclusion C_n ⊆ Eqv_P(n) is exactly the final
sentence of Lemma 4.2.

For the converse, let f ∈ Eqv_P(n). Define the Boolean coordinate function

φ_f(bits(x)) = π₁(f(x)),

where π₁ denotes the first rail coordinate. Since f is P-equivariant, the
second rail coordinate is determined by the same function on the swapped
tuple:

f(x) = ( φ_f(bits(x)), φ_f(S(bits(x))) ).

Lemma 4.3 therefore produces a carrier term T_{φ_f} with exactly this value,
so f ∈ C_n. ∎

## Appendix C — Decompression and Transfer Lemmas

This appendix records the table-level lemmas behind the absorbed recovered
resolved-face operations.

### C.1 Escaping mixed cases

**Proposition C.1.** *For a, b ∈ R = {FAL, TRU}, the internal carrier
operations stay in R except on the mixed inputs, where they escape in exactly
one way:*

∧_k(FAL, TRU) = ∧_k(TRU, FAL) = UNK,
∨_k(FAL, TRU) = ∨_k(TRU, FAL) = CON.

*Proof.* This is an immediate coordinatewise calculation in the dual-rail
model FAL = (0,1), TRU = (1,0). Taking coordinatewise meet produces
(0,0) = UNK, while taking coordinatewise join produces (1,1) = CON. On the
unmixed inputs, one obtains the original resolved state again. ∎

### C.2 Recovered resolved-face operations

**Proposition C.2.** *With the designated re-entry data*

ρ_meet(UNK) = FAL, ρ_join(CON) = TRU,

*and ρ_meet|_R = id_R, ρ_join|_R = id_R, the absorbed recovered operations
satisfy*

meet_R(a,b) = min(a,b), join_R(a,b) = max(a,b)

*for all a, b ∈ R.*

*Proof.* On unmixed pairs, Proposition C.1 shows that the internal operation
already lands in R, so the re-entry maps act trivially. On the two mixed
pairs, the meet case lands in UNK and is sent back to FAL, while the join
case lands in CON and is sent back to TRU. This is exactly the two-point
chain minimum and maximum on R = {FAL, TRU}. ∎

**Corollary C.3.** *The resolved-face term language used in Section 5 is not
the plain restriction of the internal carrier generators. It is the absorbed
R-face obtained by evaluating ∧_k and ∨_k in the carrier and then applying
the designated re-entry data on the two escaping mixed cases.*

*Proof.* The failure of plain restriction is Proposition 5.1. The recovered
operations are Proposition C.2. ∎

### C.3 Witness-independence at the resolved endpoints

**Proposition C.4.** *Suppose ρ′_meet and ρ′_join are alternative designated
re-entry maps with the same endpoint values:*

ρ′_meet|_R = id_R, ρ′_meet(UNK) = FAL,
ρ′_join|_R = id_R, ρ′_join(CON) = TRU.

*Then the induced binary operations on R agree with meet_R and join_R on all
inputs from R².*

*Proof.* Proposition C.1 shows that the only possible outputs of ∧_k on R²
are FAL, TRU, UNK, and the only possible outputs of ∨_k on R² are FAL, TRU,
CON. The two re-entry systems agree on exactly these values. Hence they
induce identical binary operations on the resolved face. ∎

*Remark.* This extensional agreement does not imply uniqueness of the
surrounding carrier realization. Different decompressed witness systems may
still behave differently away from the endpoint values used here. The paper
does not count or classify that ambient witness dependence.

### C.4 Transport to the recovered resolved-face language

**Proposition C.5.** *Let σ = P|_R. Then the term language generated on R by*

meet_R, join_R, σ

*is exactly the recovered resolved-face language used in Section 5.*

*Proof.* Proposition C.2 identifies meet_R and join_R with the two-point
minimum and maximum on R = {FAL, TRU}. The unary map σ = P|_R exchanges the
two resolved endpoints. These are precisely the operations used in the
recovered resolved-face term algebra. ∎

*Remark* (Safe transfer principle). The appendix proves only the narrow
statement needed in the main text: the resolved-face language is not obtained
by plain restriction, but by absorbed re-entry on the two escaping mixed
cases. It does not prove a quotient theorem, a congruence-image theorem, or
any theorem counting ambient witness use.

## Appendix D — Exact Negation Complexity on the Resolved Face

This appendix gives the proof of Theorem 5.3. In this edition the exact-cost
argument has three layers: lower-bound charging, the interval-shell decrement
made unconditional by the new lemma W_f ⊆ B_f, and inductive completion.

*Comparison with the original preprint.* The original appendix carried three
further layers — local witness reduction, star-local fiber coherence, and a
five-case rerouting package — to handle a residual family of shells assumed
to fall outside the interval regime. Theorem D.11 below shows that this
residual family is empty: the containment W_f ⊆ B_f holds for every
nonconstant f, so the interval-shell regime already covers every inductive
step. The removed layers were never reachable; no error in them was
implicated. This simplification was found during the machine-verified audit
of the appendix.

### D.1 Lower-Bound Charging

Let R = {FAL, TRU} with the chain order FAL < TRU, and let Rⁿ carry the
componentwise order. For a maximal chain

C = (c₀ < ⋯ < c_n)

define desc(f, C) to be the number of indices i such that

f(c_i) = TRU, f(c_{i+1}) = FAL.

Set

mcr(f) = max_C desc(f, C).

On the two-point chain one has mcr(f) = dec(f).

**Lemma D.1.** *If t is a projection, then desc(t, C) = 0 for every maximal
chain C.*

*Proof.* A projection is monotone on Rⁿ, so along any increasing chain it can
change only from FAL to TRU, never from TRU to FAL. ∎

**Lemma D.2.** *For resolved-face terms u and v, and every maximal chain C,*

desc(meet_R(u,v), C) ≤ desc(u, C) + desc(v, C),
desc(join_R(u,v), C) ≤ desc(u, C) + desc(v, C).

*Proof.* If meet_R(u,v) descends at a step of C, then both inputs are TRU
below and at least one is FAL above, so that descent is charged to an input
descent. If join_R(u,v) descends, then both inputs are FAL above and at least
one is TRU below, so again the descent is charged to an input descent.
Summing over all steps gives the inequalities. ∎

**Lemma D.3.** *For every resolved-face term u and maximal chain C,*

desc(σ(u), C) ≤ desc(u, C) + 1.

*Proof.* Along a fixed chain, applying σ exchanges FAL and TRU, so descents
of σ(u) are ascents of u. In any binary word, the number of ascents exceeds
the number of descents by at most one. ∎

**Proposition D.4** (Lower-bound charging). *If a resolved-face term t
computes f : Rⁿ → R, then*

mcr(f) ≤ ν(t).

*In particular,*

dec(f) = mcr(f) ≤ ν(f).

*Proof.* Proceed by structural induction on t. Lemma D.1 handles projections.
Lemma D.2 handles meet_R and join_R. Lemma D.3 handles one occurrence of σ,
which can add at most one new descent along any chain. Therefore any term
computing f has at least mcr(f) occurrences of σ. Taking the minimum over all
such terms gives mcr(f) ≤ ν(f), and mcr(f) = dec(f) on the two-point
chain. ∎

### D.2 Interval-Shell Decrement

Assume now that f : Rⁿ → R is nonconstant and non-monotone. Define

A_f = { x : f(x) = TRU }, G_f = ↑A_f \ A_f, B_f = A_f \ ↑G_f.

Let W_f be the union of the first TRU-blocks over all worst chains of f. For
S ⊆ Rⁿ, define the lowered residual f_S by

f_S(x) = FAL for x ∈ S, f_S(x) = f(x) otherwise.

**Proposition D.5** (One-σ realization for interval shells). *Let S be an
A_f-ideal with W_f ⊆ S ⊆ B_f. Then χ_S is definable with at most one
occurrence of σ.*

*Proof.* Set

U_S = ↑S, E_S = U_S \ S.

Then S = U_S \ ↑(E_S). If E_S = ∅, then S = U_S is an upset and χ_S is
negation-free. Otherwise,

χ_S = meet_R( χ_{U_S}, σ(χ_{↑(E_S)}) ),

so one occurrence of σ suffices. ∎

**Lemma D.6** (Worst-chain shell identity). *If C is a worst chain for f,
then B_f ∩ C is exactly the first TRU-block of f on C.*

*Proof.* Let the first descent on C occur at c_j → c_{j+1}. Then
c_{j+1} ∈ G_f, so every point strictly above the first TRU-block lies in
↑G_f and hence outside B_f. Points below that block are outside A_f, so they
are also outside B_f. The first TRU-block itself lies in B_f. ∎

**Lemma D.7** (Chain-prefix property). *Let S be an A_f-ideal with S ⊆ B_f.
Then on every maximal chain C, the set S ∩ C is a lower prefix of each
TRU-block of f on C.*

*Proof.* If x < y lie in the same TRU-block on C and y ∈ S, then y ∈ B_f.
Lemma D.6 implies that x also lies in B_f. Since x ∈ A_f and S is downward
closed inside A_f, it follows that x ∈ S. ∎

**Corollary D.8** (No new descents). *Under the hypotheses of Lemma D.7, for
every maximal chain C,*

desc(f_S, C) ≤ desc(f, C).

*Proof.* Lowering only shortens lower prefixes of existing TRU-blocks, so it
cannot create a new TRU → FAL boundary. ∎

**Theorem D.9** (Exact one-step decrement for interval shells). *Let S be an
A_f-ideal with W_f ⊆ S ⊆ B_f. Then*

mcr(f_S) = mcr(f) − 1.

*Proof.* Fix a worst chain C for f. Since W_f ⊆ S, the first TRU-block on C
lies in S. Since S ⊆ B_f, Lemma D.6 forces S ∩ C to lie inside that same
first block. Hence S ∩ C is exactly the first TRU-block, and deleting it
lowers the descent count on C by exactly one.

For any other maximal chain D, Corollary D.8 gives
desc(f_S, D) ≤ desc(f, D). If D is non-worst, then desc(f, D) ≤ mcr(f) − 1.
If D is worst, the same first-block argument gives
desc(f_S, D) = mcr(f) − 1. Thus all chains have at most mcr(f) − 1 descents
after lowering, and at least one worst chain has exactly that many. ∎

**Corollary D.10** (Forward interval-shell safety). *Every A_f-ideal S with
W_f ⊆ S ⊆ B_f gives a one-step safe shell: it is realized by one occurrence
of σ, and lowering along it decreases mcr by exactly one.*

*Proof.* Combine Proposition D.5 with Theorem D.9. ∎

**Theorem D.11** (★ Unconditional containment W_f ⊆ B_f). *For every
nonconstant, non-monotone f : Rⁿ → R,*

W_f ⊆ B_f.

*Proof.* Suppose not: some w ∈ W_f lies outside B_f. Since w ∈ W_f ⊆ A_f,
this means w ∈ ↑G_f, so there is a gap point g ∈ G_f with g ≤ w, and by the
definition of G_f a point a ∈ A_f with a ≤ g, f(a) = TRU, f(g) = FAL. Both
containments are strict: a ≠ g because f(a) ≠ f(g), and g ≠ w because
f(g) = FAL while f(w) = TRU. So a < g < w.

Since w ∈ W_f, there is a worst chain C for f whose first TRU-block contains
w. On C, no descent occurs before the first TRU-block, so all mcr(f)
descents of C occur on the segment of C from w upward.

Build an increasing chain X: ascend to a, then to g, then to w, then follow
C upward from w. The segment through a < g < w contributes at least one
descent (its f-word passes from TRU at a to FAL at g), and the tail from w
contributes mcr(f) descents. By the refinement lemma (Lemma E.4), some
maximal chain has at least as many descents as X, so

mcr(f) ≥ desc(f, X) ≥ 1 + mcr(f),

a contradiction. ∎

**Corollary D.12** (Canonical shell — the interval regime is total). *For
every nonconstant, non-monotone f, the A_f-ideal closure of W_f,*

S_f = A_f ∩ ↓W_f,

*satisfies W_f ⊆ S_f ⊆ B_f. Hence the interval-shell decrement of Corollary
D.10 applies at every inductive step: every nonconstant non-monotone f admits
a one-σ shell whose lowering decreases mcr by exactly one.*

*Proof.* S_f is an A_f-ideal containing W_f by construction. For S_f ⊆ B_f,
let x ∈ S_f, so x ∈ A_f and x ≤ w for some w ∈ W_f. If x were outside B_f,
there would be a gap point g ∈ G_f with g ≤ x ≤ w, contradicting
w ∈ B_f (Theorem D.11). ∎

### D.3 Inductive Completion

**Proposition D.13** (Monotone base case). *Let f : Rⁿ → R be nonconstant.
If mcr(f) = 0, then f is monotone and therefore has a negation-free
resolved-face term.*

*Proof.* If mcr(f) = 0, then no increasing chain contains a descent
TRU → FAL, so f is monotone. Hence A_f is an upset. Since f is nonconstant,
the usual monotone formula

f = ⋁_{a ∈ Min(A_f)} ⋀_{i : a_i = TRU} x_i

computes f using only meet_R and join_R. ∎

**Theorem D.14** (Upper bound). *For every nonconstant function
f : Rⁿ → R,*

ν(f) ≤ mcr(f).

*Proof.* We induct on mcr(f). If mcr(f) = 0, Proposition D.13 gives
ν(f) = 0.

Assume mcr(f) > 0 and the claim already holds for all nonconstant functions
of smaller mcr. Since mcr(f) > 0, f is non-monotone, so by Corollary D.12
the canonical shell S_f is an A_f-ideal with W_f ⊆ S_f ⊆ B_f, and Corollary
D.10 gives a one-σ lowering step whose residual f₁ = f_{S_f} satisfies

mcr(f₁) = mcr(f) − 1.

One occurrence of σ realizes the first step and reconstruction uses only
monotone context. Hence

ν(f) ≤ 1 + ν(f₁).

By the induction hypothesis,

ν(f₁) ≤ mcr(f₁) = mcr(f) − 1.

Therefore ν(f) ≤ mcr(f). ∎

**Corollary D.15** (Exact equality). *For every nonconstant f : Rⁿ → R,*

ν(f) = mcr(f) = dec(f).

*Proof.* The lower bound is Proposition D.4 and the upper bound is Theorem
D.14. Since mcr(f) = dec(f) on the two-point chain, all three quantities are
equal. ∎

## Appendix E — Auxiliary Chain-Reversal Tools

This appendix records a small amount of chain notation used as bookkeeping
for Appendix D.

### E.1 Upward edges and descending edges

Let

X = (x⁽⁰⁾ < x⁽¹⁾ < ⋯ < x⁽ᵐ⁾)

be an increasing chain in Rⁿ. Write

Λ^{up}(X) = { (x⁽ʲ⁾, x⁽ʲ⁺¹⁾) : 0 ≤ j < m }

for its set of adjacent upward edges. For f : Rⁿ → R, define the descending
edge set

Δ_f(X) = { (u,v) ∈ Λ^{up}(X) : f(u) > f(v) }.

Then

mcr_X(f) := |Δ_f(X)|

is the chainwise reversal count, and

mcr(f) = max_X mcr_X(f)

is the global maximum over increasing chains.

### E.2 Ascents and descents in binary chain words

Let

w = (w₀, …, w_m) ∈ R^{m+1}

be a binary word. Write asc(w) for the number of indices j with w_j = FAL
and w_{j+1} = TRU, and desc(w) for the number of indices j with w_j = TRU
and w_{j+1} = FAL.

**Lemma E.1.** *For every binary word w,*

asc(w) ≤ desc(w) + 1.

*Proof.* Read the word from left to right and decompose it into maximal
constant blocks. Every ascent starts a TRU-block, and every descent ends
one. At most one TRU-block can fail to be preceded by a descent, namely the
initial TRU-block if the word begins at TRU. Hence the number of ascents
exceeds the number of descents by at most one. ∎

**Corollary E.2.** *Let X be an increasing chain and let σ exchange FAL and
TRU. Then*

mcr_X(σ ∘ f) ≤ mcr_X(f) + 1.

*Proof.* Along the chain X, descents of σ ∘ f are ascents of the binary word
defined by f. Apply Lemma E.1. ∎

### E.3 Prefix lowering lemma

**Lemma E.3.** *Fix a binary word along an increasing chain, and lower some
TRU-entries to FAL. If the lowered set is a lower prefix inside each maximal
TRU-block, then no new descending edge is created.*

*Proof.* Inside a single maximal TRU-block, lowering a lower prefix changes
a block of the form

TRU ⋯ TRU

into

FAL ⋯ FAL TRU ⋯ TRU.

This creates at most one new ascent inside the block and never a new
descent. At the block boundaries, the left boundary can only move from
FAL TRU to FAL FAL, and the right boundary can only move from TRU FAL to
either TRU FAL or FAL FAL. Hence the number of descents does not
increase. ∎

### E.4 Subchain refinement lemma

**Lemma E.4.** *Every increasing chain X in Rⁿ extends to a maximal chain C
with desc(f, C) ≥ mcr_X(f). Hence the maximum over increasing chains in the
definition of mcr agrees with the maximum over maximal chains.*

*Proof.* Refine each upward edge u < v of X into a saturated cover path from
u to v and concatenate, extending below the bottom of X and above its top to
a maximal chain C. If (u, v) is a descending edge of X, the f-word along the
inserted cover path starts at TRU and ends at FAL, so it contains at least
one descending cover step. Distinct edges of X refine to disjoint segments
of C, so desc(f, C) ≥ |Δ_f(X)| = mcr_X(f). ∎

*Remark.* Appendix D uses Lemmas E.3 and E.4 in the interval-shell argument
and in Theorem D.11. They are recorded separately here only to keep the main
exact-cost appendix shorter.

## References

1. Won Chul Yang. *The cohomological price of NOT.* Zenodo, 2026.
   DOI: 10.5281/zenodo.21775055. (Companion note; cites the present paper as
   [10] and mechanizes the nested tower used in Appendix D's Lean artifact.)
2. A. A. Markov. *On the inversion complexity of a system of functions.*
   J. ACM 5(4), 331–334, 1958. (Russian original: Doklady AN SSSR 116(6),
   917–919, 1957.)
3. Hiroki Morizumi. *Limiting Negations in Formulas.* ICALP 2009, LNCS 5555,
   701–712. (Preliminary version: arXiv:0811.0699, 2008.)
4. Charles H. Bennett. *Logical reversibility of computation.* IBM Journal
   of Research and Development, 17(6):525–532, 1973.
5. Rolf Landauer. *Irreversibility and heat generation in the computing
   process.* IBM Journal of Research and Development, 5(3):183–191, 1961.
6. Dietlinde Lau. *Function Algebras on Finite Sets.* Springer, 2006.
7. Emil L. Post. *The Two-Valued Iterative Systems of Mathematical Logic.*
   Princeton University Press, 1941.
8. Won Chul Yang. *Finite-Energy Epistemic Logic with Conservative Pointed
   Extension and Negation Geometry.* 2026. (Paper I; companion release:
   https://github.com/ycmath/finite-energy-epistemic-logic. An earlier draft
   circulated as "Finite-energy epistemic logic with T0-preserving open
   updates".)

---

## Authorship & provenance

Won Chul Yang, independent researcher. This paper and its companion Lean
artifact were produced in collaboration with an AI research loop operated by
the author (frontier language models — Anthropic Claude family — for
discovery, formalization, and adversarial verification), **with the Lean 4
kernel as the final acceptance gate**. The interval single-regime
simplification of Appendix D (Theorem D.11) was found during a machine
audit of the original proof. The author directed the research programme and
verified the pipeline; in line with the author's research-ethics policy, no
claim of academic priority is made beyond full disclosure of how the work
was produced. Corrections are invited.

Licenses: Apache-2.0 (Lean artifacts and verification scripts),
CC BY 4.0 (text).

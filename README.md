# The Price of NOT on D4

**Won Chul Yang** — public edition v1.0 (2026)

The exact price of negation on the resolved face of the four-state dual-rail
carrier D4: for every nonconstant `f : Rⁿ → R` on the resolved face
`R = {FAL, TRU}`,

> **ν(f) = dec(f)** — the minimal number of syntactic negation occurrences
> equals the chain decrease number.

This is the four-valued, formula-exact counterpart of the classical
Markov/Morizumi inversion-complexity line, proved intrinsically in the
recovered resolved-face language `{meet_R, join_R, σ}`.

This edition simplifies the original preprint's proof architecture to a
**single interval-shell regime** via the new unconditional containment
**W_f ⊆ B_f** (Theorem D.11), discovered during a machine-verified audit of
the original appendix. Every headline statement is machine-verified in
dependency-minimal Lean 4.

## Contents

```
paper/            the paper (public edition v1.0)
lean/dec_bridge/  DecBridge — the nested negation-tower library
                  (alternation, subadditivity, three-zone witness, cube
                  omega, both tower directions; kernel-only)
lean/wcy2/        Wcy2 — the D4 layer on top of DecBridge:
                  D4.lean        Theorem 2.1 (closed-core soundness),
                                 Theorem 3.1 (sigma facts)
                  Transfer.lean  Props C.1/C.2/C.4 (escape / recovery /
                                 witness-independence)
                  RTerm.lean     the recovery-face term language, dual
                                 (D4 / Boolean) semantics
                  NuLower.lean   word-level subadditivity; dec <= nu
                  NuUpper.lean   monotone-DNF + tower-peel realization;
                                 nu <= dec
                  PriceOfNot.lean  nu_eq_dec_D4 — the exact equality
verification/     exhaustive machine replay of the original appendix
                  (all layers; includes the n <= 4 evidence behind
                  Theorem D.11)
```

## Verification status

- **Lean**: core Lean 4 only (no mathlib), no `native_decide`, no `sorry`.
  Kernel axiom profile at most `[propext, Quot.sound]`; the finite table
  facts are axiom-free. See `lean/wcy2/axcheck.log` for the per-theorem
  `#print axioms` output of a clean build.
- **Replay**: `verification/wcy2_appd_replay_v1.py` exhaustively replays the
  proof structure of the original appendix — closed-core, collapse,
  transfer, interval-shell (all 464 valid shells at n ≤ 3), inductive
  completion (65,368/65,368 at n ≤ 4), and the residual-regime emptiness
  check that led to Theorem D.11.

To rebuild:

```
cd lean/wcy2
lake build
```

(Requires `elan`; the toolchain is pinned by `lean-toolchain`. Building
`wcy2` builds `dec_bridge` automatically.)

## Companion

- *The cohomological price of NOT* — the companion note that places dec in
  its cohomological address and mechanizes the nested χ_σ-tower:
  https://github.com/ycmath/cohomological-price-of-not
  (DOI: 10.5281/zenodo.21775055)
- *Finite-Energy Epistemic Logic with Conservative Pointed Extension and
  Negation Geometry* — Paper I; companion release:
  https://github.com/ycmath/finite-energy-epistemic-logic
  (an earlier draft circulated as "Finite-energy epistemic logic with
  T0-preserving open updates").

## Authorship & provenance

Won Chul Yang, independent researcher. **This paper is the author's own
research**: the mathematical content — definitions, theorems, proofs,
including the original preprint this edition revises — is the author's
original work. AI assistance (Anthropic Claude family) was used **only for
the machine-verification layer**: the Lean 4 mechanization and the machine
audit/replay of the author's proofs, with the Lean 4 kernel as the
acceptance gate for that layer; the interval single-regime simplification
(Theorem D.11) emerged from that audit and was adopted by the author. This
differs from the author's two earlier AI-collaborative releases
(cohomological-price-of-not, inversion-wilf-spi), which were produced in an
AI research loop and are labeled accordingly. Corrections are invited.

## License

- Lean artifacts and verification scripts: Apache-2.0 (`LICENSE`)
- Text (paper, README): CC BY 4.0 (`LICENSE-text`)

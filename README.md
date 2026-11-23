# Lean Formalization of Equal Opportunity

A Lean 4 + Mathlib formalization of the ordering analysis in
*Equal Opportunity: A Correctness Condition for Ordered Consensus* (OSDI '26):
§3.5 (Theorems 3.1–3.4) and the appendix results for continuous uniform noise.

## Status

Every statement in scope is machine-checked: `lake build --wfail` passes and each theorem
depends only on Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

| Paper | Lean (`EqualOpportunity.Paper`) | Proved in |
|---|---|---|
| Thm 3.1 (Δ-Ordering Separation) | `thm_3_1` | `Separation.lean` |
| Thm 3.2 (ε(2) ≥ 1/(2(k+1)) for every D) | `thm_3_2` | `Equality/LowerBound.lean` |
| Corollary (ε(2) = Pr[x − y < Δnet] − 1/2 for every D) | `cor_eps2` | `Equality/Two.lean` |
| Thm 3.3 (discrete D attains it) | `thm_3_3` | `Equality/Discrete.lean` |
| Thm 3.4 (ε(n), discrete D) | `thm_3_4`, `thm_3_4_upper`, `thm_3_4_lower`, `thm_3_4_degenerate` | `Equality/Discrete.lean` |
| App. Thm 3.3 (ε(2) = α − α²/2, uniform D) | `app_thm_3_3` | `Equality/Uniform.lean` |
| App. Thm 3.4, lower bound and its tightness | `app_thm_3_4_lower`, `app_thm_3_4_lower_tight` | `Equality/Uniform.lean` |
| App. Thm 3.4, upper bound and ε(n) guarantee | `app_thm_3_4_upper`, `app_thm_3_4` | `Equality/UniformUpper.lean` |

## What to read

Lean checks proofs, not statements. If these five files say what the paper means, the rest
is machine-checked:

1. `EqualOpportunity/Basic.lean` — `Params`, `Admissible`, `NoiseLaw`, `WeakOut`/`StrictOut`.
2. `EqualOpportunity/Separation.lean` — `OrderingSeparation`.
3. `EqualOpportunity/Equality/Defs.lean` — `TieBreak`, `outProb`, `OrderingEquality`.
4. `EqualOpportunity/Equality/Noise.lean` — `discreteNoise`, `uniformNoise`.
5. `EqualOpportunity/Paper.lean` — every theorem, by paper number.

Proof files, in dependency order:

| File | Content |
|---|---|
| `Equality/Envelope.lean` | Adversarial tie-breaking reduces to two events: `π` consistent with the timestamps (best case) and `π` forced by them (worst case). |
| `Equality/Combinatorics.lean` | Counting weakly/strictly increasing maps; the dominance inequality for Thm 3.4. |
| `Equality/Discrete.lean` | Thms 3.3 and 3.4. |
| `Equality/LowerBound.lean` | Thm 3.2: buckets, Cauchy–Schwarz, and the limit of offsets approaching `Δnet`. |
| `Equality/Two.lean` | For any D, ε(2) = Pr[x − y < Δnet] − 1/2. |
| `Equality/OrderVolume.lean` | Inside a cube, each ordering of the coordinates has volume `1/n!` of the cube. |
| `Equality/Uniform.lean` | Uniform noise as Lebesgue measure on a box; App. Thm 3.3; App. Thm 3.4 lower bound. |
| `Equality/UniformUpper.lean` | App. Thm 3.4 upper bound, by induction on the number of commands. |

## Modelling decisions

- **Non-adaptive adversary.** Assigned timestamps are chosen in `[T, T + Δnet)` before any
  noise is revealed (Assumption 3.1 + Lemma 3.1 are hypotheses, not proved).
- **The adversary orders ties.** Commands with equal modified timestamps are ordered by the
  adversary, and the choice may depend on the realized noise.
- **Ideal SRO.** Each command's noise is an independent sample from `D`.
- Out of scope: the §2.2 axiomatic model, SRO cryptographic guarantees, Pompē itself.

## What the formalization found

1. **Thm 3.2: the proof needs a limit.** The window is half-open and the adversary cannot
   react to the noise, so no single offset lets it "decide" every same-bucket pair. The bound
   holds because offsets approaching `Δnet` capture every pair whose noise differs by less
   than `Δnet` (`pair_sup`). The statement is read as "every valid ε is at least
   1/(2(k+1))"; the paper's literal "for all i₁, i₂" fails for an honest execution.
2. **Thm 3.4 needs no assumption relating n and k.** The step "the upper deviation dominates
   the lower one" is the inequality C(k+n,n) + C(k+1,n) ≥ 2(k+1)ⁿ/n!, which the paper does not
   prove; it holds for all n and k (`two_div_factorial_le`). When n > k+1 the adversary can
   make any chosen order impossible (`thm_3_4_degenerate`), and the formula still holds.
3. **The window must be half-open.** With a closed window and adversarial ties, adjacent
   discrete noise points could tie and Thm 3.3 would fail.
4. **App. Thm 3.4 upper bound: sound, but tight only for an adaptive adversary.**
   `((1+α)ⁿ − n αⁿ)/n!` is proved as a bound against the non-adaptive adversary. The paper's
   tightness argument lets the adversary see each modified timestamp before choosing the next
   assigned one. Non-adaptively, the bound is tight for n = 2 but appears not to be for n ≥ 3:
   numerically the n = 3 optimum is `1/6 + α/2 + α²/4 − α³/6` at offsets
   `(0, Δnet/2, Δnet)` (`scripts/check_bounds.py`). This last claim is **not** formalized.
5. **A general formula for two commands.** For every noise law, the least valid ε(2) is
   exactly `Pr[x − y < Δnet] − 1/2` (`cor_eps2`). Thm 3.2, Thm 3.3 and App. Thm 3.3 are
   all instances.
6. **Side conditions made explicit.** The uniform-noise results need `0 < Δnoise` and
   `Δnet ≤ Δnoise` (α ≤ 1). Tightness of the App. Thm 3.4 lower bound needs n ≥ 2 and is an
   infimum, not attained; `ε(2) = α − α²/2` is likewise a supremum.

## Building and checking

```sh
lake exe cache get                 # prebuilt Mathlib, ~7 GB under .lake/ (once per clone)
lake build                         # type-check everything
lake build --wfail                 # strict: fails on any warning, hence on any `sorry`
lake env lean scripts/axioms.lean  # axioms each paper theorem depends on
python3 scripts/check_bounds.py    # numeric cross-checks of the closed forms
```

Toolchain and Mathlib are pinned to `v4.36.0` (`lean-toolchain`, `lakefile.toml`).

## Conventions

- No `sorry`, no `axiom`, no `native_decide`.
- `#print axioms` on each theorem in `Paper.lean` lists only `propext`, `Classical.choice`,
  `Quot.sound`.

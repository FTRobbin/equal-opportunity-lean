# Lean Formalization of Equal Opportunity

A Lean 4 + Mathlib formalization of the ordering analysis in
[Equal Opportunity: A Correctness Condition for Ordered Consensus (OSDI '26)](https://www.usenix.org/conference/osdi26/presentation/zhang-yunhao):
§3.5 (Theorems 3.1–3.4) and Appendix A (Theorems A.1 and A.2, continuous uniform noise).

> Yunhao Zhang, Haobin Ni, Soumya Basu, Shir Cohen, Maofan Yin, Lorenzo Alvisi,
> Robbert van Renesse, Qi Chen, and Lidong Zhou.
> **Equal Opportunity: A Correctness Condition for Ordered Consensus.**
> In *20th USENIX Symposium on Operating Systems Design and Implementation (OSDI 26)*,
> pages 1283–1298, Seattle, WA, July 2026. USENIX Association.

Appendix A is part of the extended version, [arxiv:2509.09868](https://arxiv.org/abs/2509.09868).

## Summary

Every statement in scope is machine-checked: `lake build --wfail` passes and each theorem
depends only on Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

| Paper | Lean (`EqualOpportunity.Paper`) | Proved in |
|---|---|---|
| Thm 3.1 (Δ-Ordering Separation) | `thm_3_1` | `Separation.lean` |
| Thm 3.2 (ε(2) ≥ 1/(2(k+1)) for every D) | `thm_3_2` | `Equality/LowerBound.lean` |
| Corollary (ε(2) = Pr[x − y < Δnet] − 1/2 for every D) | `cor_eps2` | `Equality/Two.lean` |
| Thm 3.3 (discrete D attains it) | `thm_3_3` | `Equality/Discrete.lean` |
| Thm 3.4 (ε(n), discrete D; proof in Appendix A.4) | `thm_3_4`, `thm_3_4_upper`, `thm_3_4_lower`, `thm_3_4_degenerate` | `Equality/Discrete.lean` |
| Thm A.1 (ε(2) = α − α²/2, uniform D) | `thm_A_1` | `Equality/Uniform.lean` |
| Thm A.2 (ε(n) = ((1+α)ⁿ − 1 − nαⁿ)/n! for n ≥ 2, uniform D) | `thm_A_2` | `Equality/UniformUpper.lean` |
| Thm A.2, bounds on Pr[≻] from its proof | `thm_A_2_lower`, `thm_A_2_lower_tight`, `thm_A_2_upper` | `Equality/Uniform.lean`, `Equality/UniformUpper.lean` |
| Thm A.2, upper bound holds for every adaptive strategy | `thm_A_2_adaptive_upper` | `Equality/Adaptive.lean` |
| Thm A.2, upper bound is tight for the adaptive adversary | `thm_A_2_adaptive_tight` | `Equality/Adaptive.lean` |
| The adaptive model extends the non-adaptive one | `adaptive_extends_nonadaptive` | `Equality/UniformUpper.lean` |

The adversary is non-adaptive by default, as in the paper. Theorem A.2 is a guarantee against
that adversary; its value is tight only for the adaptive adversary, which is what the last
three rows are about.

## Building

```sh
lake exe cache get                 # prebuilt Mathlib, ~7 GB under .lake/ (once per clone)
lake build                         # type-check everything
lake build --wfail                 # strict: fails on any warning, hence on any `sorry`
lake env lean scripts/axioms.lean  # axioms each paper theorem depends on
python3 scripts/check_bounds.py    # numeric cross-checks of the closed forms
```

Toolchain and Mathlib are pinned to `v4.36.0` (`lean-toolchain`, `lakefile.toml`).

## What to read

Lean checks proofs, not statements. If these six files say what the paper means, the rest
is machine-checked.

1. `EqualOpportunity/Basic.lean` — the timing model.
   - `Params`: the two time constants, `Δnet > 0` and `Δnoise ≥ 0`, with `k = ⌊Δnoise/Δnet⌋`
     and `α = Δnet/Δnoise` derived from them.
   - `Admissible`: the adversary may give a command invoked at time `T` any assigned
     timestamp in `[T, T + Δnet)`, chosen before the noise is revealed.
   - `NoiseLaw`: a probability distribution `D` on `[0, Δnoise]`; each command's noise is an
     independent sample from it.
   - `WeakOut π ts`: the order `π` is consistent with the modified timestamps `ts`, i.e. they
     never decrease along `π`.
   - `StrictOut π ts`: the order `π` is forced by `ts`, i.e. they strictly increase along `π`,
     so there are no ties.
2. `EqualOpportunity/Separation.lean` — Δ-Ordering Separation.
   - `OrderingSeparation p Δ`: whatever the adversary and the noise do, a command invoked at
     least `Δ` before another gets a strictly smaller modified timestamp.
3. `EqualOpportunity/Equality/Defs.lean` — ε-Ordering Equality.
   - `TieBreak`: the adversary's rule for ordering commands whose modified timestamps tie; it
     may output any order consistent with the timestamps.
   - `outProb N ats tb π`: the probability that the output order is `π`, given assigned
     timestamps `ats`, noise law `N` and tie-breaking `tb`.
   - `OrderingEquality p N n ε`: for `n` commands invoked at the same time,
     `|Pr[π] − 1/n!| ≤ ε` for every order `π`, every admissible timestamp assignment and every
     tie-breaking.
4. `EqualOpportunity/Equality/Noise.lean` — the two distributions the paper analyses.
   - `discreteNoise`: uniform on the `k + 1` points `0, Δnet, …, kΔnet`.
   - `uniformNoise`: the continuous uniform distribution on `[0, Δnoise]`.
5. `EqualOpportunity/Equality/AdaptiveDefs.lean` — the adaptive adversary, used only for the
   tightness of Theorem A.2.
   - `Strategy n`: fixes the assigned timestamps of `n` commands one at a time, in the order of
     the target permutation, seeing each command's modified timestamp before choosing the next.
   - `Strategy.win p σ x`: the probability that, playing `σ`, the remaining commands all get
     modified timestamps at least `x` and come out in the target order.
   - `Strategy.Admissible p σ`: every timestamp `σ` can choose lies in `[0, Δnet)`, measured
     from the invocation time.
   - `Strategy.winProb p σ`: the probability that `σ` produces the target order.
   - `Strategy.const t`: the non-adaptive strategy with fixed offsets `t`.
6. `EqualOpportunity/Paper.lean` — every theorem, by paper number.

Proof files, in dependency order:

| File | Content |
|---|---|
| `Equality/Envelope.lean` | Adversarial tie-breaking reduces to two events: `π` consistent with the timestamps (best case) and `π` forced by them (worst case). |
| `Equality/Combinatorics.lean` | Counting weakly/strictly increasing maps; the dominance inequality for Thm 3.4. |
| `Equality/Discrete.lean` | Thms 3.3 and 3.4. |
| `Equality/LowerBound.lean` | Thm 3.2: buckets, Cauchy–Schwarz, and the limit of offsets approaching `Δnet`. |
| `Equality/Two.lean` | For any D, ε(2) = Pr[x − y < Δnet] − 1/2. |
| `Equality/OrderVolume.lean` | Inside a cube, each ordering of the coordinates has volume `1/n!` of the cube. |
| `Equality/Uniform.lean` | Uniform noise as Lebesgue measure on a box; Thm A.1; the lower bound in Thm A.2. |
| `Equality/TailRegion.lean` | The region of increasing timestamp vectors above a threshold, its slicing along the first command, and the two polynomials that bound its volume. |
| `Equality/Adaptive.lean` | The upper bound in Thm A.2 for every adaptive strategy, by induction on the number of commands; the greedy strategy that attains it. |
| `Equality/UniformUpper.lean` | The non-adaptive adversary as a constant strategy; Thm A.2 itself. |

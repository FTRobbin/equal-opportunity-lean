# Lean Formalization of Equal Opportunity

A Lean 4 + Mathlib formalization of the ordering analysis in
*Equal Opportunity: A Correctness Condition for Ordered Consensus* (OSDI '26):
§3.5 (Theorems 3.1–3.4) and the appendix results for continuous uniform noise.

> Yunhao Zhang, Haobin Ni, Soumya Basu, Shir Cohen, Maofan Yin, Lorenzo Alvisi,
> Robbert van Renesse, Qi Chen, and Lidong Zhou.
> **Equal Opportunity: A Correctness Condition for Ordered Consensus.**
> In *Proceedings of the USENIX Symposium on Operating Systems Design and Implementation
> (OSDI '26)*, 2026.
> <https://www.usenix.org/conference/osdi26/presentation/zhang-yunhao>
>
> The appendix is part of the extended version, arXiv:2509.09868.

## Summary

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

Lean checks proofs, not statements. If these five files say what the paper means, the rest
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

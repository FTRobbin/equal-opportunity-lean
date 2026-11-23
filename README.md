# Lean Formalization of Equal Opportunity

A Lean 4 + Mathlib formalization of the ordering analysis in
*Equal Opportunity: A Correctness Condition for Ordered Consensus* (OSDI '26):
§3.5 (Theorems 3.1–3.4) and the appendix results for continuous uniform noise.

## Status

**Phase 1: statements only.** The definitions and theorem statements are written and
type-check; most proofs are `sorry`. Nothing marked `sorry` has been verified.

| Paper | Lean (`EqualOpportunity.Paper`) | Status |
|---|---|---|
| Thm 3.1 (Δ-Ordering Separation) | `thm_3_1` | proved |
| Thm 3.2 (ε(2) lower bound, any D) | `thm_3_2` | stated |
| Thm 3.3 (discrete D optimal for ε(2)) | `thm_3_3` | stated |
| Thm 3.4 (ε(n), discrete D) | `thm_3_4`, `thm_3_4_upper`, `thm_3_4_lower`, `thm_3_4_degenerate` | stated |
| App. Thm 3.3 (ε(2), uniform D) | `app_thm_3_3` | stated |
| App. Thm 3.4 (ε(n), uniform D) | `app_thm_3_4`, `app_thm_3_4_lower`, `app_thm_3_4_lower_tight`, `app_thm_3_4_upper` | stated |

## What to read

The audit surface is small:

1. `EqualOpportunity/Basic.lean` — `Params`, `Admissible`, `NoiseLaw`, `WeakOut`/`StrictOut`.
2. `EqualOpportunity/Separation.lean` — `OrderingSeparation`.
3. `EqualOpportunity/Equality/Defs.lean` — `TieBreak`, `outProb`, `OrderingEquality`.
4. `EqualOpportunity/Equality/Noise.lean` — `discreteNoise`, `uniformNoise`.
5. `EqualOpportunity/Paper.lean` — every theorem, by paper number.

Lean checks proofs, not statements: if these five files say what the paper means, the rest is
machine-checked.

## Modelling decisions

- **Non-adaptive adversary.** Assigned timestamps are chosen in `[T, T + Δnet)` before any
  noise is revealed (Assumption 3.1 + Lemma 3.1 are hypotheses, not proved).
- **The adversary orders ties.** Commands with equal modified timestamps are ordered by the
  adversary, and the choice may depend on the realized noise.
- **Ideal SRO.** Each command's noise is an independent sample from `D`.
- Out of scope: the §2.2 axiomatic model, SRO cryptographic guarantees, Pompē itself.

## Where the Lean statements differ from the paper's wording

- *Thm 3.2* is stated as "every valid ε is at least 1/(2(k+1))". The paper's "for all i₁, i₂"
  would be false for an honest execution.
- *Thm 3.4* carries no assumption relating `n` and `k`. The regime `n > k + 1`, where the
  adversary can make an order impossible, is stated separately (`thm_3_4_degenerate`).
- *App. Thm 3.4* (uniform noise, general `n`): the upper bound is stated as sound, not tight.
  The paper's tightness argument uses an adversary that sees each modified timestamp before
  choosing the next assigned timestamp; against the non-adaptive adversary the bound appears
  not to be tight for `n ≥ 3` (`scripts/check_bounds.py`).

## Building and checking

```sh
lake exe cache get                 # prebuilt Mathlib, ~7 GB under .lake/ (once per clone)
lake build                         # type-check everything; unfinished proofs show as `sorry` warnings
lake build --wfail                 # strict: fails while any warning (hence any `sorry`) remains
lake env lean scripts/axioms.lean  # axioms each paper theorem depends on; `sorryAx` = not yet proved
python3 scripts/check_bounds.py    # numeric cross-checks of the closed forms
```

Toolchain and Mathlib are pinned to `v4.36.0` (`lean-toolchain`, `lakefile.toml`).

## Conventions

- No `axiom`, no `native_decide`. `sorry` is allowed only while a phase is in progress.
- Once the proofs are done, `#print axioms` on each theorem in `Paper.lean` must list only
  `propext`, `Classical.choice`, `Quot.sound`.

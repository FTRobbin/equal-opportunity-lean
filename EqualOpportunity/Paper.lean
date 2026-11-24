import EqualOpportunity.Separation
import EqualOpportunity.Equality.Defs
import EqualOpportunity.Equality.Noise
import EqualOpportunity.Equality.Discrete
import EqualOpportunity.Equality.LowerBound
import EqualOpportunity.Equality.Two
import EqualOpportunity.Equality.Uniform
import EqualOpportunity.Equality.UniformUpper
import EqualOpportunity.Equality.AdaptiveDefs
import EqualOpportunity.Equality.Adaptive

/-!
# The paper's theorems, by number

This file is the **audit surface**: each theorem of "Equal Opportunity: A Correctness Condition
for Ordered Consensus" (OSDI '26) that is in scope, stated in terms of the definitions in
`Basic`, `Separation`, `Equality/Defs`, `Equality/Noise` and, for the last section only,
`Equality/AdaptiveDefs`.

Reading guide.

* `p : Params` carries `Δnet > 0` and `Δnoise ≥ 0`; `p.k = ⌊Δnoise / Δnet⌋`, `p.α = Δnet / Δnoise`.
* `OrderingEquality p N n ε` : ε-Ordering Equality for `n` simultaneous commands under noise
  law `N`, against a non-adaptive adversary that also controls ties.
* `IsLeast S ε` means `ε ∈ S` and every element of `S` is `≥ ε`.  So
  `IsLeast {ε | OrderingEquality p N n ε} ε₀` reads "the protocol satisfies ε₀-Ordering Equality
  and no smaller ε": the paper's "achieves ε(n) = ε₀".
* `outProb N ats tb π` is `Pr[π]` for assigned timestamps `ats` and tie-breaking `tb`.
* Every theorem here is fully proved; `lake env lean scripts/axioms.lean` lists the axioms each
  one depends on.
-/

open scoped Nat

namespace EqualOpportunity.Paper

/-! ## Main text, §3.5 -/

/-- **Theorem 3.1** (Δ-Ordering Separation).  If `i₁` is invoked at least `Δnet + Δnoise`
before `i₂`, then `i₁` appears before `i₂` in the output. -/
theorem thm_3_1 (p : Params) : OrderingSeparation p (p.Δnet + p.Δnoise) :=
  orderingSeparation p

/-- **Theorem 3.2** (ε(2) lower bound).  For *every* distribution `D` on `[0, Δnoise]`, any ε
for which 2-command Ordering Equality holds is at least `1 / (2(k+1))`. -/
theorem thm_3_2 (p : Params) (N : NoiseLaw p) {ε : ℝ} (h : OrderingEquality p N 2 ε) :
    1 / (2 * ((p.k : ℝ) + 1)) ≤ ε :=
  eps2_lower_bound N h

/-- **Corollary** (exact ε(2) for any distribution).  For two commands and *every* noise
distribution `D`, the least valid ε is `Pr[x − y < Δnet] − 1/2`, where `x, y` are independent
samples from `D`.  Theorem 3.2 is the lower bound `Pr[x − y < Δnet] ≥ 1/2 + 1/(2(k+1))` on
this quantity; Theorem 3.3 and Theorem A.1 evaluate it for the discrete and the
uniform distribution. -/
theorem cor_eps2 (p : Params) (N : NoiseLaw p) :
    IsLeast {ε : ℝ | OrderingEquality p N 2 ε}
      ((N.D.prod N.D).real {q : ℝ × ℝ | q.1 - q.2 < p.Δnet} - 1 / 2) :=
  eps2_isLeast N

/-- **Theorem 3.3** (discrete distribution is optimal for ε(2)).  The discrete distribution
achieves exactly `ε(2) = 1 / (2(k+1))`, the lower bound of Theorem 3.2. -/
theorem thm_3_3 (p : Params) :
    IsLeast {ε : ℝ | OrderingEquality p (discreteNoise p) 2 ε} (1 / (2 * ((p.k : ℝ) + 1))) :=
  discrete_isLeast_two p

/-- **Theorem 3.4** (ε(n) for the discrete distribution).
`ε(n) = C(k+n, n) / (k+1)ⁿ − 1/n!`, for every `n` and `k` (no relation between them assumed). -/
theorem thm_3_4 (p : Params) (n : ℕ) :
    IsLeast {ε : ℝ | OrderingEquality p (discreteNoise p) n ε}
      (((p.k + n).choose n : ℝ) / ((p.k : ℝ) + 1) ^ n - 1 / (n ! : ℝ)) :=
  discrete_isLeast p n

/-- **Theorem 3.4, upper bound** (from its proof in Appendix A.4).
`Pr[π] ≤ C(k+n, n) / (k+1)ⁿ` (multisets of size `n`). -/
theorem thm_3_4_upper (p : Params) {n : ℕ} {T : ℝ} {ats : Fin n → ℝ}
    (hats : Admissible p (fun _ => T) ats) (tb : TieBreak n) (π : Equiv.Perm (Fin n)) :
    outProb (discreteNoise p) ats tb π ≤ ((p.k + n).choose n : ℝ) / ((p.k : ℝ) + 1) ^ n :=
  discrete_outProb_le p hats tb π

/-- **Theorem 3.4, lower bound** (from its proof in Appendix A.4).
`Pr[π] ≥ C(k+1, n) / (k+1)ⁿ` (subsets of size `n`).
Positive iff `n ≤ k + 1`. -/
theorem thm_3_4_lower (p : Params) {n : ℕ} {T : ℝ} {ats : Fin n → ℝ}
    (hats : Admissible p (fun _ => T) ats) (tb : TieBreak n) (π : Equiv.Perm (Fin n)) :
    ((p.k + 1).choose n : ℝ) / ((p.k : ℝ) + 1) ^ n ≤ outProb (discreteNoise p) ats tb π :=
  discrete_le_outProb p hats tb π

/-- **Degenerate regime `n > k + 1`** (not in the paper; spelled out at Haobin's request).
With more commands than noise points, two commands always share a noise value, and the
adversary can make any chosen order `π` impossible.  Theorem 3.4's formula still holds here. -/
theorem thm_3_4_degenerate (p : Params) {n : ℕ} (hn : p.k + 1 < n) (π : Equiv.Perm (Fin n)) :
    ∃ (T : ℝ) (ats : Fin n → ℝ), Admissible p (fun _ => T) ats ∧
      ∀ tb : TieBreak n, outProb (discreteNoise p) ats tb π = 0 :=
  discrete_degenerate p hn π

/-! ## Appendix A.5: continuous uniform noise on `[0, Δnoise]`

All statements assume `0 < Δnoise` (so the distribution exists) and `Δnet ≤ Δnoise`, i.e.
`α ≤ 1`.  (If `Δnoise < Δnet` then `k = 0` and Theorem 3.2 already gives `ε(2) ≥ 1/2`.) -/

/-- **Theorem A.1** (ε(2) for the uniform continuous distribution).  Uniform noise achieves
exactly `ε(2) = α − α²/2`. -/
theorem thm_A_1 (p : Params) (h0 : 0 < p.Δnoise) (hα : p.Δnet ≤ p.Δnoise) :
    IsLeast {ε : ℝ | OrderingEquality p (uniformNoise p h0) 2 ε} (p.α - p.α ^ 2 / 2) :=
  uniform_isLeast_two p h0 hα

/-- **Theorem A.2** (ε(n) for the uniform continuous distribution).  For `n ≥ 2`, uniform noise
satisfies ε(n)-Ordering Equality with `ε(n) = ((1 + α)ⁿ − 1 − n αⁿ) / n!`.

This is the guarantee.  As the paper notes, the value is tight only for an adaptive adversary;
against the non-adaptive adversary modelled here it is tight for `n = 2` (Theorem A.1) and is
not claimed to be tight for `n ≥ 3`. -/
theorem thm_A_2 (p : Params) (h0 : 0 < p.Δnoise) (hα : p.Δnet ≤ p.Δnoise) {n : ℕ} (hn : 2 ≤ n) :
    OrderingEquality p (uniformNoise p h0) n
      (((1 + p.α) ^ n - 1 - n * p.α ^ n) / (n ! : ℝ)) :=
  uniform_orderingEquality p h0 hα hn

/-- **Theorem A.2, lower bound** (from its proof).  `Pr[π] ≥ (1 − α)ⁿ / n!`. -/
theorem thm_A_2_lower (p : Params) (h0 : 0 < p.Δnoise) (hα : p.Δnet ≤ p.Δnoise)
    {n : ℕ} {T : ℝ} {ats : Fin n → ℝ} (hats : Admissible p (fun _ => T) ats)
    (tb : TieBreak n) (π : Equiv.Perm (Fin n)) :
    (1 - p.α) ^ n / (n ! : ℝ) ≤ outProb (uniformNoise p h0) ats tb π :=
  (uniform_strictProb_ge p h0 hα hats π).trans (strictProb_le_outProb _ ats tb π)

/-- **Theorem A.2, the lower bound is tight** (from its proof): it is approached as the first
command's assigned timestamp approaches `T + Δnet`.  Needs `n ≥ 2`. -/
theorem thm_A_2_lower_tight (p : Params) (h0 : 0 < p.Δnoise) (hα : p.Δnet ≤ p.Δnoise)
    {n : ℕ} (hn : 2 ≤ n) (π : Equiv.Perm (Fin n)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (T : ℝ) (ats : Fin n → ℝ), Admissible p (fun _ => T) ats ∧
      ∀ tb : TieBreak n,
        outProb (uniformNoise p h0) ats tb π < (1 - p.α) ^ n / (n ! : ℝ) + δ := by
  obtain ⟨T, ats, hadm, h⟩ := uniform_weakProb_lt p h0 hα hn π hδ
  exact ⟨T, ats, hadm, fun tb => lt_of_le_of_lt (outProb_le_weakProb _ ats tb π) h⟩

/-- **Theorem A.2, upper bound** (from its proof).  `Pr[π] ≤ ((1 + α)ⁿ − n αⁿ) / n!`, for
every `n`.  Proved as a sound bound against the non-adaptive adversary. -/
theorem thm_A_2_upper (p : Params) (h0 : 0 < p.Δnoise) (hα : p.Δnet ≤ p.Δnoise)
    {n : ℕ} {T : ℝ} {ats : Fin n → ℝ} (hats : Admissible p (fun _ => T) ats)
    (tb : TieBreak n) (π : Equiv.Perm (Fin n)) :
    outProb (uniformNoise p h0) ats tb π ≤ ((1 + p.α) ^ n - n * p.α ^ n) / (n ! : ℝ) :=
  (outProb_le_weakProb _ ats tb π).trans (uniform_weakProb_le p h0 hα hats π)

/-! ## Adaptive adversary: the upper bound of Theorem A.2 is tight

The paper states that Theorem A.2's value is tight only for an adaptive adversary.  The model
is in `Equality/AdaptiveDefs.lean`: a `Strategy n` fixes the assigned timestamps of the `n`
commands one at a time, in the order of the target permutation, seeing each command's modified
timestamp before choosing the next; `σ.Admissible p` says every timestamp stays in the window;
`σ.winProb p` is the probability that `σ` produces the target order. -/

/-- **Theorem A.2, upper bound, adaptive adversary.**  Every admissible adaptive strategy
produces the target order with probability at most `((1 + α)ⁿ − n αⁿ) / n!`. -/
theorem thm_A_2_adaptive_upper (p : Params) (h0 : 0 < p.Δnoise) (hα : p.Δnet ≤ p.Δnoise)
    {n : ℕ} (σ : Strategy n) (hσ : σ.Admissible p) :
    σ.winProb p ≤ ((1 + p.α) ^ n - n * p.α ^ n) / (n ! : ℝ) :=
  Strategy.winProb_le p h0 hα σ hσ

/-- **Theorem A.2, the upper bound is tight for the adaptive adversary.**  Admissible adaptive
strategies produce the target order with probability arbitrarily close to
`((1 + α)ⁿ − n αⁿ) / n!`.  (Approached, not attained: the window is half-open.)

Hence no `ε` below `((1 + α)ⁿ − 1 − n αⁿ) / n!` bounds `Pr[π] − 1/n!` against this adversary:
Theorem A.2's `ε(n)` cannot be improved in the adaptive model. -/
theorem thm_A_2_adaptive_tight (p : Params) (h0 : 0 < p.Δnoise) (hα : p.Δnet ≤ p.Δnoise)
    (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ σ : Strategy n, σ.Admissible p ∧
      ((1 + p.α) ^ n - n * p.α ^ n) / (n ! : ℝ) - δ < σ.winProb p :=
  Strategy.exists_winProb_gt p h0 hα n hδ

/-- **The adaptive model extends the non-adaptive one.**  A non-adaptive timestamp assignment
is the constant strategy with the same offsets (listed in the target order `π`); it is
admissible, and its `winProb` is the probability that `π` is a possible output in the
non-adaptive model (`weakProb`: the adversary's best case for `π` over all tie-breaking). -/
theorem adaptive_extends_nonadaptive (p : Params) (h0 : 0 < p.Δnoise) {n : ℕ} {T : ℝ}
    {ats : Fin n → ℝ} (hats : Admissible p (fun _ => T) ats) (π : Equiv.Perm (Fin n)) :
    (Strategy.const fun i => ats (π i) - T).Admissible p ∧
      weakProb (uniformNoise p h0) ats π = (Strategy.const fun i => ats (π i) - T).winProb p :=
  ⟨Strategy.const_admissible p fun i =>
      ⟨by linarith [(hats (π i)).1], by linarith [(hats (π i)).2]⟩,
    weakProb_eq_winProb_const p h0 hats π⟩

end EqualOpportunity.Paper

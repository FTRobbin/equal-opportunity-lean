import EqualOpportunity.Equality.LowerBound

/-!
# ε(2) for an arbitrary noise distribution

For two commands and any noise law `D`, the best achievable `ε(2)` is exactly
`Pr[x − y < Δnet] − 1/2`, where `x, y` are independent samples from `D` (`eps2_isLeast`).

Theorem 3.2 bounds this quantity from below for every `D`; Theorem A.1 computes
it for uniform noise.
-/

open MeasureTheory
open scoped Nat

namespace EqualOpportunity

variable {p : Params}

/-- `Pr[x − y < Δnet]` for two independent noise samples `x, y`. -/
noncomputable def nearProb (N : NoiseLaw p) : ℝ := (N.D.prod N.D).real p.nearLt

theorem prod_swap_nearLt (N : NoiseLaw p) :
    (N.D.prod N.D).real (Prod.swap ⁻¹' p.nearLt) = (N.D.prod N.D).real p.nearLt := by
  have h := (Measure.measurePreserving_swap (μ := N.D) (ν := N.D)).measure_preimage
    p.measurableSet_nearLt.nullMeasurableSet
  rw [measureReal_def, measureReal_def, h]

/-- In the two-command noise space, "sample `a` exceeds sample `b` by less than `Δnet`" has
probability `nearProb`, whichever of the two commands `a` is. -/
theorem joint_two_near (N : NoiseLaw p) {a b : Fin 2} (hab : a ≠ b) :
    (N.joint 2).real {η | η a - η b < p.Δnet} = nearProb N := by
  have hmp := measurePreserving_finTwoArrow N.D
  have hcases : (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by
    revert a b
    decide
  unfold NoiseLaw.joint nearProb
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hset : {η : Fin 2 → ℝ | η 0 - η 1 < p.Δnet} =
        MeasurableEquiv.finTwoArrow ⁻¹' p.nearLt := by
      ext η
      simp [Params.nearLt]
    rw [hset, measureReal_def, hmp.measure_preimage p.measurableSet_nearLt.nullMeasurableSet,
      measureReal_def]
  · have hset : {η : Fin 2 → ℝ | η 1 - η 0 < p.Δnet} =
        MeasurableEquiv.finTwoArrow ⁻¹' (Prod.swap ⁻¹' p.nearLt) := by
      ext η
      simp [Params.nearLt]
    rw [hset, measureReal_def, hmp.measure_preimage
      (p.measurableSet_nearLt.preimage measurable_swap).nullMeasurableSet, ← measureReal_def,
      prod_swap_nearLt]

theorem weakProb_two_le (N : NoiseLaw p) {T : ℝ} {ats : Fin 2 → ℝ}
    (hats : Admissible p (fun _ => T) ats) (π : Equiv.Perm (Fin 2)) :
    weakProb N ats π ≤ nearProb N := by
  rw [← joint_two_near N (a := π 0) (b := π 1) (π.injective.ne (by decide))]
  refine measureReal_mono (fun η hη => ?_) (measure_ne_top _ _)
  have h := hη (show (0 : Fin 2) ≤ 1 by decide)
  have h1 := (hats (π 0)).1
  have h2 := (hats (π 1)).2
  simp only [Function.comp, Pi.add_apply] at h
  simp only [Set.mem_ofPred_eq]
  linarith

theorem one_sub_le_strictProb_two (N : NoiseLaw p) {T : ℝ} {ats : Fin 2 → ℝ}
    (hats : Admissible p (fun _ => T) ats) (π : Equiv.Perm (Fin 2)) :
    1 - nearProb N ≤ strictProb N ats π := by
  have hm : MeasurableSet {η : Fin 2 → ℝ | η (π 1) - η (π 0) < p.Δnet} :=
    measurableSet_lt ((measurable_pi_apply (π 1)).sub (measurable_pi_apply (π 0)))
      measurable_const
  rw [← joint_two_near N (a := π 1) (b := π 0) (π.injective.ne (by decide)),
    ← probReal_compl_eq_one_sub hm]
  refine measureReal_mono (fun η hη => ?_) (measure_ne_top _ _)
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at hη
  have h1 := (hats (π 1)).1
  have h2 := (hats (π 0)).2
  show StrictMono ((ats + η) ∘ π)
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  fin_cases i
  simp only [Function.comp, Pi.add_apply]
  show ats (π 0) + η (π 0) < ats (π 1) + η (π 1)
  linarith

/-- **ε(2) for any noise law**: the least valid `ε` is `Pr[x − y < Δnet] − 1/2`. -/
theorem eps2_isLeast (N : NoiseLaw p) :
    IsLeast {ε : ℝ | OrderingEquality p N 2 ε} (nearProb N - 1 / 2) := by
  have h2 : ((2 ! : ℕ) : ℝ) = 2 := by norm_num [Nat.factorial]
  constructor
  · show OrderingEquality p N 2 _
    rw [orderingEquality_iff]
    intro T ats hats π
    have h1 := weakProb_two_le N hats π
    have h3 := one_sub_le_strictProb_two N hats π
    rw [h2]
    constructor <;> linarith
  · intro ε hε
    have h := pair_sup N hε
    unfold nearProb
    linarith

end EqualOpportunity

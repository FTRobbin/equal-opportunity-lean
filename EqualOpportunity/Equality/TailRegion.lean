import EqualOpportunity.Equality.Uniform

/-!
# The tail region and its bounding polynomials

Shared prerequisites for the upper bound in Theorem A.2, in both adversary models.

Work in the window `[0, a]` (`a = Δnet`), noise range `L = Δnoise ≥ a`.  For offsets
`t₀, …, t_{m−1}` and a threshold `x`, `tailRegion L x t` is the set of timestamp vectors `y`
with `tᵢ ≤ yᵢ ≤ tᵢ + L`, all `≥ x`, weakly increasing.  Slicing along the first coordinate:
`vol (tailRegion x (t₀, t')) = ∫_{max(t₀, x)}^{t₀ + L} vol (tailRegion y t') dy`.

The two polynomials that bound these volumes are

* `B_m(v) = ((L + v)ᵐ − m vᵐ) / m!`  (threshold inside the window, `v = a − x`),
* `A_m(u) = uᵐ / m!`                 (threshold beyond the window, `u = L + a − x`).
-/

open MeasureTheory
open scoped Nat ENNReal

namespace EqualOpportunity

/-! ### The region and its slices -/

/-- Timestamp vectors `y` with `tᵢ ≤ yᵢ ≤ tᵢ + L`, all at least `x`, weakly increasing. -/
def tailRegion (L : ℝ) {m : ℕ} (x : ℝ) (t : Fin m → ℝ) : Set (Fin m → ℝ) :=
  {y | (∀ i, t i ≤ y i ∧ y i ≤ t i + L) ∧ (∀ i, x ≤ y i) ∧ Monotone y}

theorem measurableSet_tailRegion (L x : ℝ) {m : ℕ} (t : Fin m → ℝ) :
    MeasurableSet (tailRegion L x t) := by
  have h1 : MeasurableSet {y : Fin m → ℝ | ∀ i, t i ≤ y i ∧ y i ≤ t i + L} := by
    have e : {y : Fin m → ℝ | ∀ i, t i ≤ y i ∧ y i ≤ t i + L} =
        Set.pi Set.univ fun i => Set.Icc (t i) (t i + L) := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_univ_pi, Set.mem_Icc]
    rw [e]
    exact MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have h2 : MeasurableSet {y : Fin m → ℝ | ∀ i, x ≤ y i} := by
    have e : {y : Fin m → ℝ | ∀ i, x ≤ y i} = Set.pi Set.univ fun _ => Set.Ici x := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_univ_pi, Set.mem_Ici]
    rw [e]
    exact MeasurableSet.univ_pi fun _ => measurableSet_Ici
  have h3 : MeasurableSet {y : Fin m → ℝ | Monotone y} := by
    simpa [WeakOut] using measurableSet_weakOut (1 : Equiv.Perm (Fin m))
  exact h1.inter (h2.inter h3)

theorem monotone_cons_iff {m : ℕ} (y0 : ℝ) (z : Fin m → ℝ) :
    Monotone (Fin.cons y0 z : Fin (m + 1) → ℝ) ↔ (∀ j, y0 ≤ z j) ∧ Monotone z := by
  constructor
  · intro h
    refine ⟨fun j => ?_, fun i j hij => ?_⟩
    · have := h (Fin.zero_le j.succ)
      simpa using this
    · have := h (Fin.succ_le_succ_iff.mpr hij)
      simpa using this
  · rintro ⟨h1, h2⟩ i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => simp
      | succ j => simpa using h1 j
    | succ i =>
      induction j using Fin.cases with
      | zero => exact absurd hij (by simp)
      | succ j => simpa using h2 (Fin.succ_le_succ_iff.mp hij)

theorem cons_mem_tailRegion {L x : ℝ} {m : ℕ} (t : Fin (m + 1) → ℝ) (y0 : ℝ) (z : Fin m → ℝ) :
    (Fin.cons y0 z : Fin (m + 1) → ℝ) ∈ tailRegion L x t ↔
      y0 ∈ Set.Icc (max (t 0) x) (t 0 + L) ∧ z ∈ tailRegion L y0 (fun j => t j.succ) := by
  simp only [tailRegion, Set.mem_ofPred_eq, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ,
    monotone_cons_iff, Set.mem_Icc, max_le_iff]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, ⟨h4, _⟩, h6, h7⟩
    exact ⟨⟨⟨h1, h4⟩, h2⟩, h3, h6, h7⟩
  · rintro ⟨⟨⟨h1, h4⟩, h2⟩, h3, h6, h7⟩
    exact ⟨⟨⟨h1, h2⟩, h3⟩, ⟨h4, fun j => h4.trans (h6 j)⟩, h6, h7⟩

/-- **Slicing along the first coordinate.** -/
theorem volume_tailRegion_succ (L x : ℝ) {m : ℕ} (t : Fin (m + 1) → ℝ) :
    volume (tailRegion L x t) =
      ∫⁻ y in Set.Icc (max (t 0) x) (t 0 + L), volume (tailRegion L y fun j => t j.succ) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0 with he
  have hmp : MeasurePreserving e volume volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
  have hS := measurableSet_tailRegion L x t
  have h1 : volume (e.symm ⁻¹' tailRegion L x t) = volume (tailRegion L x t) :=
    (hmp.symm e).measure_preimage_equiv _
  have hsym : ∀ (y0 : ℝ) (z : Fin m → ℝ), e.symm (y0, z) = (Fin.cons y0 z : Fin (m + 1) → ℝ) :=
    fun y0 z => Fin.insertNth_zero' y0 z
  have hsec : ∀ y0 : ℝ, volume (Prod.mk y0 ⁻¹' (e.symm ⁻¹' tailRegion L x t)) =
      (Set.Icc (max (t 0) x) (t 0 + L)).indicator
        (fun y => volume (tailRegion L y fun j => t j.succ)) y0 := by
    intro y0
    have hset : Prod.mk y0 ⁻¹' (e.symm ⁻¹' tailRegion L x t) =
        {z | (Fin.cons y0 z : Fin (m + 1) → ℝ) ∈ tailRegion L x t} := by
      ext z
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, hsym]
    rw [hset]
    by_cases hy : y0 ∈ Set.Icc (max (t 0) x) (t 0 + L)
    · rw [Set.indicator_of_mem hy]
      congr 1
      ext z
      simp only [Set.mem_ofPred_eq, cons_mem_tailRegion, hy, true_and]
    · rw [Set.indicator_of_notMem hy]
      have hempty : {z : Fin m → ℝ | (Fin.cons y0 z : Fin (m + 1) → ℝ) ∈ tailRegion L x t} = ∅ := by
        ext z
        simp only [Set.mem_ofPred_eq, cons_mem_tailRegion, hy, false_and, Set.mem_empty_iff_false]
      rw [hempty, measure_empty]
  rw [← h1, Measure.volume_eq_prod, Measure.prod_apply (e.symm.measurable hS)]
  simp_rw [hsec]
  rw [lintegral_indicator measurableSet_Icc]

/-! ### The two bounding polynomials -/

/-- `A_m(u) = uᵐ / m!`. -/
noncomputable def polyA (m : ℕ) (u : ℝ) : ℝ := u ^ m / (m ! : ℝ)

/-- `B_m(v) = ((L + v)ᵐ − m vᵐ) / m!`. -/
noncomputable def polyB (L : ℝ) (m : ℕ) (v : ℝ) : ℝ := ((L + v) ^ m - m * v ^ m) / (m ! : ℝ)

theorem polyA_nonneg {m : ℕ} {u : ℝ} (hu : 0 ≤ u) : 0 ≤ polyA m u :=
  div_nonneg (pow_nonneg hu m) (by positivity)

/-- `(m + 1) vᵐ ≤ (L + v)ᵐ` for `0 ≤ v ≤ L`. -/
theorem succ_mul_pow_le {L v : ℝ} (hv : 0 ≤ v) (hvL : v ≤ L) :
    ∀ m : ℕ, ((m : ℝ) + 1) * v ^ m ≤ (L + v) ^ m := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    have hvm : 0 ≤ v ^ m := pow_nonneg hv m
    have h1 : (L + v) * (((m : ℝ) + 1) * v ^ m) ≤ (L + v) * (L + v) ^ m :=
      mul_le_mul_of_nonneg_left ih (by linarith)
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have h2 : 0 ≤ (((m : ℝ) + 1) * L - v) * v ^ m :=
      mul_nonneg (by nlinarith) hvm
    have e : (L + v) * (((m : ℝ) + 1) * v ^ m) - (((m : ℝ) + 1) + 1) * v ^ (m + 1) =
        (((m : ℝ) + 1) * L - v) * v ^ m := by ring
    push_cast
    rw [pow_succ (L + v)]
    nlinarith

/-- The numerator of `B_m` is monotone on `[0, L]`. -/
theorem polyB_num_mono {L v v' : ℝ} (hv : 0 ≤ v) (hvv' : v ≤ v') (hv'L : v' ≤ L) :
    ∀ m : ℕ, (L + v) ^ m - m * v ^ m ≤ (L + v') ^ m - m * v' ^ m := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
      have hF : 0 ≤ v' ^ m - v ^ m := sub_nonneg.mpr (pow_le_pow_left₀ hv hvv' m)
      have hE : 0 ≤ ((L + v') ^ m - (L + v) ^ m) - m * (v' ^ m - v ^ m) := by linarith
      have hP := succ_mul_pow_le hv (hvv'.trans hv'L) m
      have t1 : 0 ≤ (L + v') * (((L + v') ^ m - (L + v) ^ m) - m * (v' ^ m - v ^ m)) :=
        mul_nonneg (by linarith) hE
      have t2 : 0 ≤ (v' ^ m - v ^ m) * (m * L - v') := mul_nonneg hF (by nlinarith)
      have t3 : 0 ≤ (v' - v) * ((L + v) ^ m - ((m : ℝ) + 1) * v ^ m) :=
        mul_nonneg (by linarith) (by linarith)
      have e : (L + v') ^ (m + 1) - ((m : ℝ) + 1) * v' ^ (m + 1) -
          ((L + v) ^ (m + 1) - ((m : ℝ) + 1) * v ^ (m + 1)) =
          (L + v') * (((L + v') ^ m - (L + v) ^ m) - m * (v' ^ m - v ^ m)) +
            (v' ^ m - v ^ m) * (m * L - v') +
            (v' - v) * ((L + v) ^ m - ((m : ℝ) + 1) * v ^ m) := by ring
      push_cast
      linarith

theorem polyB_nonneg {L v : ℝ} (hv : 0 ≤ v) (hvL : v ≤ L) (m : ℕ) : 0 ≤ polyB L m v := by
  have h := succ_mul_pow_le hv hvL m
  have hvm : 0 ≤ v ^ m := pow_nonneg hv m
  exact div_nonneg (by nlinarith) (by positivity)

/-- The inequality that closes the induction step, on numerators. -/
theorem step_num_le (L : ℝ) (m : ℕ) {v w u : ℝ} (hv : 0 ≤ v) (hu : u ≤ L)
    (h : (v = u ∧ u ≤ w) ∨ (v = w ∧ v ≤ u)) :
    (L + v) ^ (m + 1) - m * v ^ (m + 1) - w ^ (m + 1) ≤
      (L + u) ^ (m + 1) - ((m : ℝ) + 1) * u ^ (m + 1) := by
  rcases h with ⟨rfl, huw⟩ | ⟨rfl, hvu⟩
  · have := pow_le_pow_left₀ hv huw (m + 1)
    linarith
  · have := polyB_num_mono hv hvu hu (m + 1)
    push_cast at this
    linarith

/-! ### Integrals of the bounding polynomials -/

theorem integral_polyA (K c d : ℝ) (m : ℕ) :
    ∫ y in c..d, polyA m (K - y) = polyA (m + 1) (K - c) - polyA (m + 1) (K - d) := by
  unfold polyA
  rw [intervalIntegral.integral_div, intervalIntegral.integral_comp_sub_left (fun u => u ^ m) K,
    integral_pow, Nat.factorial_succ]
  push_cast
  field_simp

theorem continuous_polyA (K : ℝ) (m : ℕ) : Continuous fun y : ℝ => polyA m (K - y) := by
  unfold polyA
  fun_prop

theorem continuous_polyB (L a : ℝ) (m : ℕ) : Continuous fun y : ℝ => polyB L m (a - y) := by
  unfold polyB
  fun_prop

theorem integral_polyB (L a c : ℝ) (m : ℕ) :
    ∫ y in c..a, polyB L m (a - y) =
      (polyA (m + 1) (L + a - c) - polyA (m + 1) L) - m * polyA (m + 1) (a - c) := by
  have hfun : (fun y : ℝ => polyB L m (a - y)) =
      fun y => polyA m (L + a - y) - m * polyA m (a - y) := by
    funext y
    unfold polyB polyA
    rw [show L + (a - y) = L + a - y by ring]
    ring
  rw [hfun, intervalIntegral.integral_sub ((continuous_polyA _ m).intervalIntegrable _ _)
    (((continuous_polyA _ m).const_mul _).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, integral_polyA, integral_polyA]
  have h0 : polyA (m + 1) (a - a) = 0 := by simp [polyA]
  rw [h0, show L + a - a = L by ring]
  ring

/-- Set-integral of a nonnegative continuous function as an interval integral. -/
theorem lintegral_Icc_ofReal {f : ℝ → ℝ} (hf : Continuous f) {c d : ℝ} (hcd : c ≤ d)
    (hnn : ∀ y ∈ Set.Icc c d, 0 ≤ f y) :
    ∫⁻ y in Set.Icc c d, ENNReal.ofReal (f y) = ENNReal.ofReal (∫ y in c..d, f y) := by
  rw [intervalIntegral.integral_of_le hcd, ← integral_Icc_eq_integral_Ioc,
    ofReal_integral_eq_lintegral_ofReal hf.integrableOn_Icc
      ((ae_restrict_iff' measurableSet_Icc).mpr (ae_of_all _ hnn))]


theorem volume_univ_fin_zero : volume (Set.univ : Set (Fin 0 → ℝ)) = 1 := by
  rw [← Set.pi_univ (Set.univ : Set (Fin 0)), volume_pi_pi]
  simp

/-- `B_n(a) / Lⁿ` in terms of `α = a / L`: the paper's `((1 + α)ⁿ − n αⁿ) / n!`. -/
theorem polyB_div_pow {L : ℝ} (hL : L ≠ 0) (a : ℝ) (n : ℕ) :
    polyB L n a / L ^ n = ((1 + a / L) ^ n - n * (a / L) ^ n) / (n ! : ℝ) := by
  have h1 : (1 + a / L) ^ n = (L + a) ^ n / L ^ n := by
    rw [← div_pow]
    congr 1
    field_simp
  rw [h1, div_pow]
  simp only [polyB]
  field_simp

end EqualOpportunity

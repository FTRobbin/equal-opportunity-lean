import EqualOpportunity.Equality.Uniform

/-!
# Appendix Theorem 3.4, upper bound: `Pr[π] ≤ ((1 + α)ⁿ − n αⁿ) / n!`

The paper obtains this value for an adversary that sees each modified timestamp before choosing
the next assigned one.  Here it is proved as a *sound bound against the non-adaptive
adversary*, by an induction that peels off the first command of `π`.

Work in the window `[0, a]` (`a = Δnet`), noise range `L = Δnoise ≥ a`.  For offsets
`t₀, …, t_{m−1} ∈ [0, a]` and a threshold `x`, let `tailRegion L x t` be the set of timestamp
vectors `y` with `tᵢ ≤ yᵢ ≤ tᵢ + L`, all `≥ x`, weakly increasing.  Its volume is at most

* `B_m(a − x) = ((L + a − x)ᵐ − m (a − x)ᵐ) / m!`  if `0 ≤ x ≤ a`,
* `A_m(L + a − x) = (L + a − x)ᵐ / m!`             if `a ≤ x ≤ a + L`.

Slicing along the first coordinate gives
`vol (tailRegion x (t₀, t')) = ∫_{max(t₀, x)}^{t₀ + L} vol (tailRegion y t') dy`, and the two
bounds reproduce themselves under this integral.  At `x = 0`, `m = n` the bound is
`((L + a)ⁿ − n aⁿ)/n!`.
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

/-! ### The induction -/

theorem volume_univ_fin_zero : volume (Set.univ : Set (Fin 0 → ℝ)) = 1 := by
  rw [← Set.pi_univ (Set.univ : Set (Fin 0)), volume_pi_pi]
  simp

/-- **Volume bound for the tail region**, by induction on the number of commands. -/
theorem volume_tailRegion_le {L a : ℝ} (haL : a ≤ L) :
    ∀ (m : ℕ) (t : Fin m → ℝ), (∀ i, t i ∈ Set.Icc 0 a) →
      (∀ x ∈ Set.Icc 0 a, volume (tailRegion L x t) ≤ ENNReal.ofReal (polyB L m (a - x))) ∧
      (∀ x ∈ Set.Icc a (a + L),
        volume (tailRegion L x t) ≤ ENNReal.ofReal (polyA m (L + a - x))) := by
  intro m
  induction m with
  | zero =>
    intro t _
    have h1 : ∀ x, volume (tailRegion L x t) ≤ 1 := fun x =>
      (measure_mono (Set.subset_univ _)).trans_eq volume_univ_fin_zero
    constructor
    · intro x _
      simpa [polyB] using h1 x
    · intro x _
      simpa [polyA] using h1 x
  | succ m ih =>
    intro t ht
    obtain ⟨ih1, ih2⟩ := ih (fun j => t j.succ) (fun j => ht j.succ)
    have ht0 := ht 0
    constructor
    · -- threshold inside the window
      intro x hx
      rw [volume_tailRegion_succ]
      set c := max (t 0) x with hc
      set d := t 0 + L with hd
      have hc0 : 0 ≤ c := le_max_of_le_left ht0.1
      have hca : c ≤ a := max_le ht0.2 hx.2
      have had : a ≤ d := by simp only [hd]; linarith [ht0.1]
      rw [← Set.Icc_union_Icc_eq_Icc hca had]
      refine (lintegral_union_le _ _ _).trans ?_
      have nnB : ∀ y ∈ Set.Icc c a, 0 ≤ polyB L m (a - y) := fun y hy =>
        polyB_nonneg (by linarith [hy.2]) (by linarith [hy.1]) m
      have nnA : ∀ y ∈ Set.Icc a d, 0 ≤ polyA m (L + a - y) := fun y hy =>
        polyA_nonneg (by simp only [hd] at hy; linarith [hy.2, ht0.2])
      have b1 : ∫⁻ y in Set.Icc c a, volume (tailRegion L y fun j => t j.succ) ≤
          ENNReal.ofReal (∫ y in c..a, polyB L m (a - y)) := by
        rw [← lintegral_Icc_ofReal (continuous_polyB L a m) hca nnB]
        exact setLIntegral_mono' measurableSet_Icc fun y hy =>
          ih1 y ⟨hc0.trans hy.1, hy.2⟩
      have b2 : ∫⁻ y in Set.Icc a d, volume (tailRegion L y fun j => t j.succ) ≤
          ENNReal.ofReal (∫ y in a..d, polyA m (L + a - y)) := by
        rw [← lintegral_Icc_ofReal (continuous_polyA (L + a) m) had nnA]
        exact setLIntegral_mono' measurableSet_Icc fun y hy =>
          ih2 y ⟨hy.1, by simp only [hd] at hy; linarith [hy.2, ht0.2]⟩
      refine (add_le_add b1 b2).trans ?_
      rw [← ENNReal.ofReal_add
        (intervalIntegral.integral_nonneg hca nnB) (intervalIntegral.integral_nonneg had nnA)]
      apply ENNReal.ofReal_le_ofReal
      rw [integral_polyB, integral_polyA]
      -- numerators
      have hnum := step_num_le L m (v := a - c) (w := a - t 0) (u := a - x)
        (by linarith) (by linarith [hx.1]) (by
          rcases le_total (t 0) x with h | h
          · have hc' : c = x := by simp only [hc, max_eq_right h]
            left
            exact ⟨by rw [hc'], by linarith⟩
          · have hc' : c = t 0 := by simp only [hc, max_eq_left h]
            right
            exact ⟨by rw [hc'], by rw [hc']; linarith⟩)
      have hfac : (0 : ℝ) < ((m + 1) ! : ℝ) := by positivity
      have hdiv := div_le_div_of_nonneg_right hnum hfac.le
      have e1 : polyA (m + 1) (L + a - c) - polyA (m + 1) L - m * polyA (m + 1) (a - c) +
          (polyA (m + 1) (L + a - a) - polyA (m + 1) (L + a - d)) =
          ((L + (a - c)) ^ (m + 1) - m * (a - c) ^ (m + 1) - (a - t 0) ^ (m + 1)) /
            ((m + 1) ! : ℝ) := by
        simp only [polyA, hd]
        rw [show L + a - a = L by ring, show L + a - (t 0 + L) = a - t 0 by ring,
          show L + a - c = L + (a - c) by ring]
        ring
      have e2 : polyB L (m + 1) (a - x) =
          ((L + (a - x)) ^ (m + 1) - ((m : ℝ) + 1) * (a - x) ^ (m + 1)) / ((m + 1) ! : ℝ) := by
        simp only [polyB]
        push_cast
        ring
      rw [e1, e2]
      exact hdiv
    · -- threshold beyond the window
      intro x hx
      rw [volume_tailRegion_succ]
      have hc : max (t 0) x = x := max_eq_right (ht0.2.trans hx.1)
      rw [hc]
      by_cases hxd : x ≤ t 0 + L
      · have nnA : ∀ y ∈ Set.Icc x (t 0 + L), 0 ≤ polyA m (L + a - y) := fun y hy =>
          polyA_nonneg (by linarith [hy.2, ht0.2])
        have b : ∫⁻ y in Set.Icc x (t 0 + L), volume (tailRegion L y fun j => t j.succ) ≤
            ENNReal.ofReal (∫ y in x..(t 0 + L), polyA m (L + a - y)) := by
          rw [← lintegral_Icc_ofReal (continuous_polyA (L + a) m) hxd nnA]
          exact setLIntegral_mono' measurableSet_Icc fun y hy =>
            ih2 y ⟨hx.1.trans hy.1, by linarith [hy.2, ht0.2]⟩
        refine b.trans (ENNReal.ofReal_le_ofReal ?_)
        rw [integral_polyA]
        have : 0 ≤ polyA (m + 1) (L + a - (t 0 + L)) := polyA_nonneg (by linarith [ht0.2])
        linarith
      · rw [Set.Icc_eq_empty hxd, setLIntegral_empty]
        exact bot_le

/-! ### Back to probabilities -/

variable {n : ℕ} (p : Params) (h0 : 0 < p.Δnoise)

/-- Shifting all assigned timestamps by a constant does not change any order. -/
theorem weakProb_sub_const (N : NoiseLaw p) (ats : Fin n → ℝ) (T : ℝ) (π : Equiv.Perm (Fin n)) :
    weakProb N ats π = weakProb N (fun j => ats j - T) π := by
  unfold weakProb
  congr 1
  ext η
  simp only [Set.mem_ofPred_eq, WeakOut]
  constructor
  · intro h i j hij
    have := h hij
    simp only [Function.comp, Pi.add_apply] at this ⊢
    linarith
  · intro h i j hij
    have := h hij
    simp only [Function.comp, Pi.add_apply] at this ⊢
    linarith

/-- **Appendix Theorem 3.4, upper bound** (sound against the non-adaptive adversary). -/
theorem uniform_weakProb_le (hα : p.Δnet ≤ p.Δnoise) {T : ℝ} {ats : Fin n → ℝ}
    (hats : Admissible p (fun _ => T) ats) (π : Equiv.Perm (Fin n)) :
    weakProb (uniformNoise p h0) ats π ≤ ((1 + p.α) ^ n - n * p.α ^ n) / (n ! : ℝ) := by
  set ats' : Fin n → ℝ := fun j => ats j - T with hats'
  have hats0 : ∀ j, ats' j ∈ Set.Icc 0 p.Δnet := fun j =>
    ⟨by simp only [hats']; linarith [(hats j).1], by simp only [hats']; linarith [(hats j).2]⟩
  rw [weakProb_sub_const p _ ats T π, uniform_weakProb]
  have hset : {ts | WeakOut π ts} ∩ shiftBox p.Δnoise ats' =
      reorder π ⁻¹' tailRegion p.Δnoise 0 (ats' ∘ π) := by
    ext ts
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, mem_shiftBox, Set.mem_preimage, reorder_apply,
      tailRegion, WeakOut, Function.comp]
    constructor
    · rintro ⟨hw, hb⟩
      exact ⟨fun i => hb (π i), fun i => (hats0 (π i)).1.trans (hb (π i)).1, hw⟩
    · rintro ⟨hb, _, hw⟩
      exact ⟨hw, fun j => by simpa using hb (π.symm j)⟩
  have hvol : volume ({ts | WeakOut π ts} ∩ shiftBox p.Δnoise ats') ≤
      ENNReal.ofReal (polyB p.Δnoise n (p.Δnet - 0)) := by
    rw [hset, volume_preimage_reorder]
    exact (volume_tailRegion_le hα n (ats' ∘ π) (fun i => hats0 (π i))).1 0
      ⟨le_rfl, p.net_pos.le⟩
  have hB : 0 ≤ polyB p.Δnoise n (p.Δnet - 0) :=
    polyB_nonneg (by linarith [p.net_pos]) (by linarith) n
  have hreal : volume.real ({ts | WeakOut π ts} ∩ shiftBox p.Δnoise ats') ≤
      polyB p.Δnoise n (p.Δnet - 0) :=
    ENNReal.toReal_le_of_le_ofReal hB hvol
  have hLn : 0 < p.Δnoise ^ n := pow_pos h0 n
  have hLne : p.Δnoise ≠ 0 := h0.ne'
  have e : ((1 + p.α) ^ n - n * p.α ^ n) / (n ! : ℝ) =
      polyB p.Δnoise n (p.Δnet - 0) / p.Δnoise ^ n := by
    have h1 : (1 + p.α) ^ n = (p.Δnoise + p.Δnet) ^ n / p.Δnoise ^ n := by
      rw [← div_pow]
      congr 1
      simp only [Params.α]
      field_simp
    have h2 : p.α ^ n = p.Δnet ^ n / p.Δnoise ^ n := by
      simp only [Params.α]
      rw [div_pow]
    rw [h1, h2]
    simp only [polyB, sub_zero]
    field_simp
  rw [e]
  exact div_le_div_of_nonneg_right hreal hLn.le

/-- **Appendix Theorem 3.4** as a guarantee: the paper's `ε(n)` is valid for uniform noise. -/
theorem uniform_orderingEquality (hα : p.Δnet ≤ p.Δnoise) (n : ℕ) :
    OrderingEquality p (uniformNoise p h0) n
      (max ((1 - (1 - p.α) ^ n) / (n ! : ℝ)) (((1 + p.α) ^ n - 1 - n * p.α ^ n) / (n ! : ℝ))) := by
  rw [orderingEquality_iff]
  intro T ats hats π
  have h1 := uniform_weakProb_le p h0 hα hats π
  have h2 := uniform_strictProb_ge p h0 hα hats π
  constructor
  · refine le_trans ?_ (le_max_right _ _)
    have e : ((1 + p.α) ^ n - 1 - n * p.α ^ n) / (n ! : ℝ) =
        ((1 + p.α) ^ n - n * p.α ^ n) / (n ! : ℝ) - 1 / (n ! : ℝ) := by ring
    rw [e]
    linarith
  · refine le_trans ?_ (le_max_left _ _)
    have e : (1 - (1 - p.α) ^ n) / (n ! : ℝ) =
        1 / (n ! : ℝ) - (1 - p.α) ^ n / (n ! : ℝ) := by ring
    rw [e]
    linarith

end EqualOpportunity

import EqualOpportunity.Equality.AdaptiveDefs
import EqualOpportunity.Equality.TailRegion

/-!
# The upper bound of Theorem A.2 is tight for the adaptive adversary

For the adaptive strategies of `AdaptiveDefs.lean`:

* `Strategy.vol_le`, `Strategy.winProb_le` — every strategy wins with probability at most
  `((1 + α)ⁿ − n αⁿ) / n!`.  The proof is the paper's induction: peel off the first command,
  and check that the two bounding polynomials reproduce themselves under the integral over its
  modified timestamp.
* `Strategy.vol_greedy` — the greedy strategy "give the next command the previous modified
  timestamp, clamped into the window" attains the bound exactly, for a closed window `[0, a]`.
* `Strategy.exists_winProb_gt` — since the real window `[0, Δnet)` is half-open, take
  `a = Δnet − h`: the bound is approached but not attained.

`Strategy.vol` is `Strategy.win` without the `1/Δnoise` factors (a volume instead of a
probability); the non-adaptive tail region is the volume of a constant strategy
(`Strategy.vol_const`).
-/

open MeasureTheory
open scoped Nat ENNReal

namespace EqualOpportunity

namespace Strategy

/-! ### Volumes instead of probabilities -/

/-- `win` without the normalising factors: the Lebesgue volume of the winning outcomes. -/
noncomputable def vol (L : ℝ) : {m : ℕ} → Strategy m → ℝ → ℝ≥0∞
  | _, nil, _ => 1
  | _, cons t next, x => ∫⁻ y in Set.Icc (max t x) (t + L), (next y).vol L y

/-- Every timestamp the strategy can choose lies in the closed window `[0, a]`. -/
def Within (a : ℝ) : {m : ℕ} → Strategy m → Prop
  | _, nil => True
  | _, cons t next => t ∈ Set.Icc 0 a ∧ ∀ y, (next y).Within a

theorem win_eq (p : Params) (h0 : 0 < p.Δnoise) {m : ℕ} (σ : Strategy m) :
    ∀ x, σ.win p x = (ENNReal.ofReal p.Δnoise)⁻¹ ^ m * σ.vol p.Δnoise x := by
  induction σ with
  | nil =>
    intro x
    simp [win, vol]
  | @cons m t next ih =>
    intro x
    have hne : (ENNReal.ofReal p.Δnoise)⁻¹ ^ m ≠ ∞ :=
      ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr h0).ne')
    simp only [win, vol]
    simp_rw [ih]
    rw [lintegral_const_mul' _ _ hne, ← mul_assoc, ← pow_succ']

theorem winProb_eq (p : Params) (h0 : 0 < p.Δnoise) {m : ℕ} (σ : Strategy m) :
    σ.winProb p = (σ.vol p.Δnoise 0).toReal / p.Δnoise ^ m := by
  unfold winProb
  rw [win_eq p h0, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal h0.le, inv_pow, div_eq_mul_inv, mul_comm]

theorem Admissible.within {p : Params} {m : ℕ} {σ : Strategy m} :
    σ.Admissible p → σ.Within p.Δnet := by
  induction σ with
  | nil => intro _; trivial
  | cons t next ih =>
    intro h
    simp only [Admissible] at h
    simp only [Within]
    exact ⟨⟨h.1.1, h.1.2.le⟩, fun y => ih y (h.2.2 y)⟩

/-! ### The bound holds for every strategy -/

/-- **Upper bound for every adaptive strategy**, in volume form.  With all timestamps in
`[0, a]` and `a ≤ L`, the winning volume above a threshold `x` is at most `B_m(a − x)` if `x` is
inside the window and `A_m(L + a − x)` if it is beyond. -/
theorem vol_le {L a : ℝ} (haL : a ≤ L) {m : ℕ} (σ : Strategy m) :
    σ.Within a →
      (∀ x ∈ Set.Icc 0 a, σ.vol L x ≤ ENNReal.ofReal (polyB L m (a - x))) ∧
      (∀ x ∈ Set.Icc a (a + L), σ.vol L x ≤ ENNReal.ofReal (polyA m (L + a - x))) := by
  induction σ with
  | nil =>
    intro _
    constructor <;> intro x _ <;> simp [vol, polyB, polyA]
  | @cons m t next ih =>
    intro hw
    simp only [Within] at hw
    obtain ⟨ht0, hnext⟩ := hw
    have ih1 : ∀ y ∈ Set.Icc 0 a, (next y).vol L y ≤ ENNReal.ofReal (polyB L m (a - y)) :=
      fun y hy => (ih y (hnext y)).1 y hy
    have ih2 : ∀ y ∈ Set.Icc a (a + L),
        (next y).vol L y ≤ ENNReal.ofReal (polyA m (L + a - y)) :=
      fun y hy => (ih y (hnext y)).2 y hy
    constructor
    · -- threshold inside the window
      intro x hx
      simp only [vol]
      set c := max t x with hc
      set d := t + L with hd
      have hc0 : 0 ≤ c := le_max_of_le_left ht0.1
      have hca : c ≤ a := max_le ht0.2 hx.2
      have had : a ≤ d := by simp only [hd]; linarith [ht0.1]
      rw [← Set.Icc_union_Icc_eq_Icc hca had]
      refine (lintegral_union_le _ _ _).trans ?_
      have nnB : ∀ y ∈ Set.Icc c a, 0 ≤ polyB L m (a - y) := fun y hy =>
        polyB_nonneg (by linarith [hy.2]) (by linarith [hy.1]) m
      have nnA : ∀ y ∈ Set.Icc a d, 0 ≤ polyA m (L + a - y) := fun y hy =>
        polyA_nonneg (by simp only [hd] at hy; linarith [hy.2, ht0.2])
      have b1 : ∫⁻ y in Set.Icc c a, (next y).vol L y ≤
          ENNReal.ofReal (∫ y in c..a, polyB L m (a - y)) := by
        rw [← lintegral_Icc_ofReal (continuous_polyB L a m) hca nnB]
        exact setLIntegral_mono' measurableSet_Icc fun y hy =>
          ih1 y ⟨hc0.trans hy.1, hy.2⟩
      have b2 : ∫⁻ y in Set.Icc a d, (next y).vol L y ≤
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
      have hnum := step_num_le L m (v := a - c) (w := a - t) (u := a - x)
        (by linarith) (by linarith [hx.1]) (by
          rcases le_total t x with h | h
          · have hc' : c = x := by simp only [hc, max_eq_right h]
            left
            exact ⟨by rw [hc'], by linarith⟩
          · have hc' : c = t := by simp only [hc, max_eq_left h]
            right
            exact ⟨by rw [hc'], by rw [hc']; linarith⟩)
      have hfac : (0 : ℝ) < ((m + 1) ! : ℝ) := by positivity
      have hdiv := div_le_div_of_nonneg_right hnum hfac.le
      have e1 : polyA (m + 1) (L + a - c) - polyA (m + 1) L - m * polyA (m + 1) (a - c) +
          (polyA (m + 1) (L + a - a) - polyA (m + 1) (L + a - d)) =
          ((L + (a - c)) ^ (m + 1) - m * (a - c) ^ (m + 1) - (a - t) ^ (m + 1)) /
            ((m + 1) ! : ℝ) := by
        simp only [polyA, hd]
        rw [show L + a - a = L by ring, show L + a - (t + L) = a - t by ring,
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
      simp only [vol]
      have hc : max t x = x := max_eq_right (ht0.2.trans hx.1)
      rw [hc]
      by_cases hxd : x ≤ t + L
      · have nnA : ∀ y ∈ Set.Icc x (t + L), 0 ≤ polyA m (L + a - y) := fun y hy =>
          polyA_nonneg (by linarith [hy.2, ht0.2])
        have b : ∫⁻ y in Set.Icc x (t + L), (next y).vol L y ≤
            ENNReal.ofReal (∫ y in x..(t + L), polyA m (L + a - y)) := by
          rw [← lintegral_Icc_ofReal (continuous_polyA (L + a) m) hxd nnA]
          exact setLIntegral_mono' measurableSet_Icc fun y hy =>
            ih2 y ⟨hx.1.trans hy.1, by linarith [hy.2, ht0.2]⟩
        refine b.trans (ENNReal.ofReal_le_ofReal ?_)
        rw [integral_polyA]
        have : 0 ≤ polyA (m + 1) (L + a - (t + L)) := polyA_nonneg (by linarith [ht0.2])
        linarith
      · rw [Set.Icc_eq_empty hxd, setLIntegral_empty]
        exact bot_le

/-- **Upper bound for every adaptive strategy**: `Pr[target order] ≤ ((1 + α)ⁿ − n αⁿ) / n!`. -/
theorem winProb_le_of_within (p : Params) (h0 : 0 < p.Δnoise) (hα : p.Δnet ≤ p.Δnoise) {n : ℕ}
    (σ : Strategy n) (hσ : σ.Within p.Δnet) :
    σ.winProb p ≤ ((1 + p.α) ^ n - n * p.α ^ n) / (n ! : ℝ) := by
  have hvol := (vol_le hα σ hσ).1 0 ⟨le_rfl, p.net_pos.le⟩
  rw [sub_zero] at hvol
  have hB : 0 ≤ polyB p.Δnoise n p.Δnet := polyB_nonneg p.net_pos.le hα n
  have hreal := ENNReal.toReal_le_of_le_ofReal hB hvol
  have e := polyB_div_pow h0.ne' p.Δnet n
  rw [winProb_eq p h0]
  unfold Params.α
  rw [← e]
  exact div_le_div_of_nonneg_right hreal (pow_pos h0 n).le

theorem winProb_le (p : Params) (h0 : 0 < p.Δnoise) (hα : p.Δnet ≤ p.Δnoise) {n : ℕ}
    (σ : Strategy n) (hσ : σ.Admissible p) :
    σ.winProb p ≤ ((1 + p.α) ^ n - n * p.α ^ n) / (n ! : ℝ) :=
  winProb_le_of_within p h0 hα σ hσ.within

/-! ### Constant strategies are the non-adaptive adversary -/

theorem const_within {a : ℝ} : ∀ {m : ℕ} {t : Fin m → ℝ}, (∀ i, t i ∈ Set.Icc 0 a) →
    (const t).Within a
  | 0, _, _ => by simp [const, Within]
  | m + 1, t, ht => by
    simp only [const, Within]
    exact ⟨ht 0, fun _ => const_within fun j => ht j.succ⟩

/-- The winning volume of a constant strategy is the volume of the tail region. -/
theorem vol_const (L : ℝ) : ∀ {m : ℕ} (t : Fin m → ℝ) (x : ℝ),
    (const t).vol L x = volume (tailRegion L x t)
  | 0, t, x => by
    have hset : tailRegion L x t = Set.univ := by
      ext y
      simp [tailRegion, Subsingleton.monotone]
    simp [const, vol, hset, volume_univ_fin_zero]
  | m + 1, t, x => by
    simp only [const, vol]
    rw [volume_tailRegion_succ]
    exact setLIntegral_congr_fun measurableSet_Icc fun y _ => vol_const L _ y

theorem winProb_const (p : Params) (h0 : 0 < p.Δnoise) {n : ℕ} (t : Fin n → ℝ) :
    (const t).winProb p = volume.real (tailRegion p.Δnoise 0 t) / p.Δnoise ^ n := by
  rw [winProb_eq p h0, vol_const, measureReal_def]

/-- For a fixed strategy, raising the threshold can only lower the winning probability. -/
theorem win_antitone (p : Params) {m : ℕ} (σ : Strategy m) : Antitone (σ.win p) := by
  cases σ with
  | nil => intro x y _; simp [win]
  | cons t next =>
    intro x y hxy
    simp only [win]
    gcongr

theorem const_admissible (p : Params) : ∀ {m : ℕ} {t : Fin m → ℝ},
    (∀ i, t i ∈ Set.Ico 0 p.Δnet) → (const t).Admissible p
  | 0, _, _ => by simp [const, Admissible]
  | m + 1, t, ht => by
    simp only [const, Admissible]
    exact ⟨ht 0, (win_antitone p _).measurable, fun _ => const_admissible p fun j => ht j.succ⟩

/-! ### The greedy strategy attains the bound -/

/-- The greedy strategy for the closed window `[0, a]`: give the next command the current
threshold (the previous command's modified timestamp), clamped into the window. -/
def greedy (a : ℝ) : (m : ℕ) → ℝ → Strategy m
  | 0, _ => nil
  | m + 1, x => cons (max 0 (min x a)) fun y => greedy a m y

theorem greedy_within {a : ℝ} (ha : 0 ≤ a) : ∀ (m : ℕ) (x : ℝ), (greedy a m x).Within a
  | 0, _ => by simp [greedy, Within]
  | m + 1, x => by
    simp only [greedy, Within]
    exact ⟨⟨le_max_left _ _, max_le ha (min_le_right _ _)⟩, fun y => greedy_within ha m y⟩

/-- **The greedy strategy's winning volume, exactly.** -/
theorem vol_greedy {L a : ℝ} (ha : 0 ≤ a) (haL : a ≤ L) : ∀ m : ℕ,
    (∀ x ∈ Set.Icc 0 a, (greedy a m x).vol L x = ENNReal.ofReal (polyB L m (a - x))) ∧
    (∀ x ∈ Set.Icc a (a + L),
      (greedy a m x).vol L x = ENNReal.ofReal (polyA m (L + a - x))) := by
  intro m
  induction m with
  | zero =>
    constructor <;> intro x _ <;> simp [greedy, vol, polyB, polyA]
  | succ m ih =>
    obtain ⟨ih1, ih2⟩ := ih
    constructor
    · -- threshold inside the window: the next command gets timestamp `x`
      intro x hx
      have ht : max 0 (min x a) = x := by rw [min_eq_left hx.2, max_eq_right hx.1]
      simp only [greedy, vol, ht, max_self]
      have hxa : x ≤ a := hx.2
      have hax : a ≤ x + L := by linarith [hx.1]
      have hdisj : Disjoint (Set.Icc x a) (Set.Ioc a (x + L)) := by
        rw [Set.disjoint_left]
        intro y hy hy'
        exact absurd hy.2 (not_le.mpr hy'.1)
      have nnB : ∀ y ∈ Set.Icc x a, 0 ≤ polyB L m (a - y) := fun y hy =>
        polyB_nonneg (by linarith [hy.2]) (by linarith [hy.1, hx.1]) m
      have nnA : ∀ y ∈ Set.Icc a (x + L), 0 ≤ polyA m (L + a - y) := fun y hy =>
        polyA_nonneg (by linarith [hy.2])
      have e1 : ∫⁻ y in Set.Icc x a, (greedy a m y).vol L y =
          ENNReal.ofReal (∫ y in x..a, polyB L m (a - y)) := by
        rw [← lintegral_Icc_ofReal (continuous_polyB L a m) hxa nnB]
        exact setLIntegral_congr_fun measurableSet_Icc fun y hy =>
          ih1 y ⟨hx.1.trans hy.1, hy.2⟩
      have e2 : ∫⁻ y in Set.Ioc a (x + L), (greedy a m y).vol L y =
          ENNReal.ofReal (∫ y in a..(x + L), polyA m (L + a - y)) := by
        rw [← lintegral_Icc_ofReal (continuous_polyA (L + a) m) hax nnA,
          ← setLIntegral_congr (f := fun y => ENNReal.ofReal (polyA m (L + a - y))) Ioc_ae_eq_Icc]
        exact setLIntegral_congr_fun measurableSet_Ioc fun y hy =>
          ih2 y ⟨hy.1.le, by linarith [hy.2]⟩
      rw [← Set.Icc_union_Ioc_eq_Icc hxa hax, lintegral_union measurableSet_Ioc hdisj, e1, e2,
        ← ENNReal.ofReal_add (intervalIntegral.integral_nonneg hxa nnB)
          (intervalIntegral.integral_nonneg hax nnA),
        integral_polyB, integral_polyA]
      congr 1
      simp only [polyA, polyB]
      rw [show L + a - a = L by ring, show L + a - (x + L) = a - x by ring,
        show L + a - x = L + (a - x) by ring]
      push_cast
      ring
    · -- threshold beyond the window: the next command gets timestamp `a`
      intro x hx
      have ht : max 0 (min x a) = a := by rw [min_eq_right hx.1, max_eq_right ha]
      simp only [greedy, vol, ht]
      rw [max_eq_right hx.1]
      have nnA : ∀ y ∈ Set.Icc x (a + L), 0 ≤ polyA m (L + a - y) := fun y hy =>
        polyA_nonneg (by linarith [hy.2])
      have e : ∫⁻ y in Set.Icc x (a + L), (greedy a m y).vol L y =
          ENNReal.ofReal (∫ y in x..(a + L), polyA m (L + a - y)) := by
        rw [← lintegral_Icc_ofReal (continuous_polyA (L + a) m) hx.2 nnA]
        exact setLIntegral_congr_fun measurableSet_Icc fun y hy =>
          ih2 y ⟨hx.1.trans hy.1, hy.2⟩
      rw [e, integral_polyA, show L + a - (a + L) = 0 by ring]
      congr 1
      simp [polyA]

theorem measurable_win_greedy (p : Params) (a : ℝ) :
    ∀ m : ℕ, Measurable fun y => (greedy a m y).win p y := by
  intro m
  induction m with
  | zero =>
    simp only [greedy, win]
    exact measurable_const
  | succ m ih =>
    simp only [greedy, win]
    apply Measurable.const_mul
    set lo : ℝ → ℝ := fun y => max (max 0 (min y a)) y with hlo_def
    set hi : ℝ → ℝ := fun y => max 0 (min y a) + p.Δnoise with hhi_def
    have hlo : Measurable lo :=
      (measurable_const.max (measurable_id.min measurable_const)).max measurable_id
    have hhi : Measurable hi :=
      (measurable_const.max (measurable_id.min measurable_const)).add_const _
    set S : Set (ℝ × ℝ) := {q | lo q.1 ≤ q.2 ∧ q.2 ≤ hi q.1} with hS_def
    have hS : MeasurableSet S :=
      (measurableSet_le (hlo.comp measurable_fst) measurable_snd).inter
        (measurableSet_le measurable_snd (hhi.comp measurable_fst))
    have hF : Measurable fun q : ℝ × ℝ =>
        S.indicator (fun q : ℝ × ℝ => (greedy a m q.2).win p q.2) q :=
      (ih.comp measurable_snd).indicator hS
    have e : (fun y => ∫⁻ z in Set.Icc (lo y) (hi y), (greedy a m z).win p z) =
        fun y => ∫⁻ z, S.indicator (fun q : ℝ × ℝ => (greedy a m q.2).win p q.2) (y, z) := by
      funext y
      rw [← lintegral_indicator measurableSet_Icc]
      refine lintegral_congr fun z => ?_
      by_cases hz : z ∈ Set.Icc (lo y) (hi y)
      · have hz' : (y, z) ∈ S := hz
        rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz']
      · have hz' : (y, z) ∉ S := hz
        rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz']
    have hmeas := hF.lintegral_prod_right' (ν := (volume : Measure ℝ))
    rw [← e] at hmeas
    exact hmeas

theorem greedy_admissible (p : Params) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < p.Δnet) :
    ∀ (m : ℕ) (x : ℝ), (greedy a m x).Admissible p
  | 0, _ => by simp [greedy, Admissible]
  | m + 1, x => by
    simp only [greedy, Admissible]
    exact ⟨⟨le_max_left _ _, lt_of_le_of_lt (max_le ha0 (min_le_right _ _)) ha1⟩,
      measurable_win_greedy p a m, fun y => greedy_admissible p ha0 ha1 m y⟩

/-- **The upper bound is tight for the adaptive adversary**: admissible strategies win with
probability arbitrarily close to `((1 + α)ⁿ − n αⁿ) / n!`. -/
theorem exists_winProb_gt (p : Params) (h0 : 0 < p.Δnoise) (hα : p.Δnet ≤ p.Δnoise) (n : ℕ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ σ : Strategy n, σ.Admissible p ∧
      ((1 + p.α) ^ n - n * p.α ^ n) / (n ! : ℝ) - δ < σ.winProb p := by
  set f : ℝ → ℝ := fun h => polyB p.Δnoise n (p.Δnet - h) / p.Δnoise ^ n with hf
  have hcont : Continuous f := by
    simp only [hf, polyB]
    fun_prop
  have hf0 : f 0 = ((1 + p.α) ^ n - n * p.α ^ n) / (n ! : ℝ) := by
    simp only [hf, sub_zero]
    unfold Params.α
    exact polyB_div_pow h0.ne' _ n
  have hev : ∀ᶠ h in nhds (0 : ℝ), f 0 - δ < f h :=
    continuousAt_const.eventually_lt hcont.continuousAt (by linarith)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hev
  set h : ℝ := min (r / 2) (p.Δnet / 2) with hh
  have hpos : 0 < h := lt_min (by linarith) (by linarith [p.net_pos])
  have hlt : h < p.Δnet := lt_of_le_of_lt (min_le_right _ _) (by linarith [p.net_pos])
  have hfh : f 0 - δ < f h := by
    apply hball
    rw [Real.dist_eq, sub_zero, abs_of_pos hpos]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have ha0 : 0 ≤ p.Δnet - h := by linarith
  have ha1 : p.Δnet - h < p.Δnet := by linarith
  have haL : p.Δnet - h ≤ p.Δnoise := by linarith
  refine ⟨greedy (p.Δnet - h) n 0, greedy_admissible p ha0 ha1 n 0, ?_⟩
  rw [← hf0, winProb_eq p h0, (vol_greedy ha0 haL n).1 0 ⟨le_rfl, ha0⟩, sub_zero,
    ENNReal.toReal_ofReal (polyB_nonneg ha0 haL n)]
  exact hfh

end Strategy

end EqualOpportunity

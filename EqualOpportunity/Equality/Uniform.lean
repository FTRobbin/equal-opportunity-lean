import EqualOpportunity.Equality.Two
import EqualOpportunity.Equality.Noise
import EqualOpportunity.Equality.OrderVolume

/-!
# Continuous uniform noise (appendix §3.2)

With `η` uniform on `[0, Δnoise]ⁿ`, the modified timestamps `ats + η` are uniform on the
shifted box `∏ᵢ [atsᵢ, atsᵢ + Δnoise]`.  So every probability is a Lebesgue volume divided by
`Δnoiseⁿ` (`uniform_weakProb`, `uniform_strictProb`), and the order-volume lemma
(`volume_real_strictCube`) evaluates the volumes that matter:

* appendix Theorem 3.3: `ε(2) = α − α²/2`;
* appendix Theorem 3.4, lower bound: `Pr[π] ≥ (1 − α)ⁿ / n!`, and it is tight.
-/

open MeasureTheory
open scoped Nat ENNReal

namespace EqualOpportunity

variable {n : ℕ} (p : Params) (h0 : 0 < p.Δnoise)

/-! ### The joint law is rescaled Lebesgue measure on a cube -/

theorem uniform_joint (n : ℕ) :
    (uniformNoise p h0).joint n =
      (ENNReal.ofReal p.Δnoise)⁻¹ ^ n • (volume.restrict (cube n 0 p.Δnoise)) := by
  unfold NoiseLaw.joint
  refine Measure.pi_eq fun s hs => ?_
  have hD : ∀ i, (uniformNoise p h0).D (s i) =
      (ENNReal.ofReal p.Δnoise)⁻¹ * volume (s i ∩ Set.Icc 0 p.Δnoise) := by
    intro i
    show ProbabilityTheory.cond volume (Set.Icc 0 p.Δnoise) (s i) = _
    rw [ProbabilityTheory.cond_apply measurableSet_Icc, Real.volume_Icc, sub_zero, Set.inter_comm]
  simp only [hD, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [_root_.smul_apply, Measure.restrict_apply (MeasurableSet.univ_pi hs), smul_eq_mul]
  congr 1
  unfold cube
  rw [← Set.pi_inter_distrib, volume_pi_pi]

theorem uniform_joint_real {S : Set (Fin n → ℝ)} (hS : MeasurableSet S) :
    ((uniformNoise p h0).joint n).real S =
      volume.real (S ∩ cube n 0 p.Δnoise) / p.Δnoise ^ n := by
  rw [measureReal_def, uniform_joint, _root_.smul_apply, Measure.restrict_apply hS, smul_eq_mul,
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofReal h0.le,
    ← measureReal_def, div_eq_mul_inv, mul_comm, inv_pow]

/-- The box in which the modified timestamps live: `∏ᵢ [atsᵢ, atsᵢ + L]`. -/
def shiftBox (L : ℝ) (ats : Fin n → ℝ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ fun i => Set.Icc (ats i) (ats i + L)

theorem mem_shiftBox {L : ℝ} {ats ts : Fin n → ℝ} :
    ts ∈ shiftBox L ats ↔ ∀ i, ats i ≤ ts i ∧ ts i ≤ ats i + L := by
  unfold shiftBox
  simp only [Set.mem_univ_pi, Set.mem_Icc]

theorem volume_shiftBox_ne_top (L : ℝ) (ats : Fin n → ℝ) : volume (shiftBox L ats) ≠ ∞ := by
  unfold shiftBox
  rw [volume_pi_pi]
  exact ENNReal.prod_ne_top fun i _ => by simp [Real.volume_Icc]

/-- A probability about the modified timestamps is a volume inside the shifted box. -/
theorem uniform_prob_shift (ats : Fin n → ℝ) {A : Set (Fin n → ℝ)} (hA : MeasurableSet A) :
    ((uniformNoise p h0).joint n).real {η | ats + η ∈ A} =
      volume.real (A ∩ shiftBox p.Δnoise ats) / p.Δnoise ^ n := by
  have hpre : MeasurableSet {η : Fin n → ℝ | ats + η ∈ A} :=
    hA.preimage (measurable_const_add_pi ats)
  have hset : {η : Fin n → ℝ | ats + η ∈ A} ∩ cube n 0 p.Δnoise =
      (fun η => ats + η) ⁻¹' (A ∩ shiftBox p.Δnoise ats) := by
    ext η
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, mem_cube, mem_shiftBox,
      Set.mem_Icc, Pi.add_apply]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun i => ⟨by linarith [(h2 i).1], by linarith [(h2 i).2]⟩⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun i => ⟨by linarith [(h2 i).1], by linarith [(h2 i).2]⟩⟩
  rw [uniform_joint_real p h0 hpre, hset, measureReal_def, measure_preimage_add,
    ← measureReal_def]

theorem uniform_weakProb (ats : Fin n → ℝ) (π : Equiv.Perm (Fin n)) :
    weakProb (uniformNoise p h0) ats π =
      volume.real ({ts | WeakOut π ts} ∩ shiftBox p.Δnoise ats) / p.Δnoise ^ n :=
  uniform_prob_shift p h0 ats (measurableSet_weakOut π)

theorem uniform_strictProb (ats : Fin n → ℝ) (π : Equiv.Perm (Fin n)) :
    strictProb (uniformNoise p h0) ats π =
      volume.real ({ts | StrictOut π ts} ∩ shiftBox p.Δnoise ats) / p.Δnoise ^ n :=
  uniform_prob_shift p h0 ats (measurableSet_strictOut π)

/-! ### Appendix Theorem 3.4, lower bound -/

include h0 in
/-- `(1 − α)ⁿ / n!` written as a cube volume over `Δnoiseⁿ`. -/
theorem one_sub_alpha_pow (n : ℕ) :
    (1 - p.α) ^ n / (n ! : ℝ) = (p.Δnoise - p.Δnet) ^ n / (n ! : ℝ) / p.Δnoise ^ n := by
  have hne : p.Δnoise ≠ 0 := h0.ne'
  have h : 1 - p.α = (p.Δnoise - p.Δnet) / p.Δnoise := by
    unfold Params.α
    field_simp
  rw [h, div_pow]
  field_simp

/-- **Appendix Theorem 3.4, lower bound**: whatever the adversary does, with probability
`(1 − α)ⁿ` all modified timestamps land in `[T + Δnet, T + Δnoise]`, where they are iid uniform,
and then each order has probability `1/n!`. -/
theorem uniform_strictProb_ge (hα : p.Δnet ≤ p.Δnoise) {T : ℝ} {ats : Fin n → ℝ}
    (hats : Admissible p (fun _ => T) ats) (π : Equiv.Perm (Fin n)) :
    (1 - p.α) ^ n / (n ! : ℝ) ≤ strictProb (uniformNoise p h0) ats π := by
  rw [uniform_strictProb, one_sub_alpha_pow p h0]
  have hsub : strictCube (T + p.Δnet) (T + p.Δnoise) π ⊆
      {ts | StrictOut π ts} ∩ shiftBox p.Δnoise ats := by
    rintro ts ⟨hc, hs⟩
    refine ⟨hs, mem_shiftBox.mpr fun i => ?_⟩
    have h1 := mem_cube.mp hc i
    have h2 := (hats i).1
    have h3 := (hats i).2
    exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
  have hvol := volume_real_strictCube (n := n) (a := T + p.Δnet) (b := T + p.Δnoise)
    (by linarith) π
  have hmono : volume.real (strictCube (T + p.Δnet) (T + p.Δnoise) π) ≤
      volume.real ({ts | StrictOut π ts} ∩ shiftBox p.Δnoise ats) :=
    measureReal_mono hsub (ne_top_of_le_ne_top (volume_shiftBox_ne_top _ _)
      (measure_mono Set.inter_subset_right))
  have e : T + p.Δnoise - (T + p.Δnet) = p.Δnoise - p.Δnet := by ring
  rw [hvol, e] at hmono
  exact div_le_div_of_nonneg_right hmono (pow_pos h0 n).le

/-- **The lower bound is tight** (`n ≥ 2`): put the first command of `π` at the very end of the
window and the last one at its start.  Then `π` needs every modified timestamp inside
`[T + Δnet − h, T + Δnoise]`, for an arbitrarily small `h > 0`. -/
theorem uniform_weakProb_lt (hα : p.Δnet ≤ p.Δnoise) (hn : 2 ≤ n) (π : Equiv.Perm (Fin n))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (T : ℝ) (ats : Fin n → ℝ), Admissible p (fun _ => T) ats ∧
      weakProb (uniformNoise p h0) ats π < (1 - p.α) ^ n / (n ! : ℝ) + δ := by
  -- choose `h` small
  set f : ℝ → ℝ := fun h => (p.Δnoise - p.Δnet + h) ^ n / (n ! : ℝ) / p.Δnoise ^ n with hf
  have hcont : Continuous f := by
    simp only [hf]
    fun_prop
  have hf0 : f 0 = (1 - p.α) ^ n / (n ! : ℝ) := by
    simp only [hf, add_zero]
    rw [one_sub_alpha_pow p h0]
  have hev : ∀ᶠ h in nhds (0 : ℝ), f h < f 0 + δ :=
    hcont.continuousAt.eventually_lt continuousAt_const (by linarith)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hev
  set h : ℝ := min (r / 2) (p.Δnet / 2) with hh
  have hpos : 0 < h := lt_min (by linarith) (by linarith [p.net_pos])
  have hlt : h < p.Δnet := lt_of_le_of_lt (min_le_right _ _) (by linarith [p.net_pos])
  have hfh : f h < f 0 + δ := by
    apply hball
    rw [Real.dist_eq, sub_zero, abs_of_pos hpos]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  -- the assignment
  have hn0 : 0 < n := by omega
  set i0 : Fin n := ⟨0, hn0⟩ with hi0
  set il : Fin n := ⟨n - 1, by omega⟩ with hil
  have hne : π il ≠ π i0 := π.injective.ne (by
    intro e
    have := congrArg Fin.val e
    simp only [hi0, hil] at this
    omega)
  set ats : Fin n → ℝ := fun j => if j = π i0 then p.Δnet - h else 0 with hats_def
  have hadm : Admissible p (fun _ => (0 : ℝ)) ats := by
    intro j
    simp only [hats_def]
    split_ifs
    · exact ⟨by linarith, by linarith⟩
    · exact ⟨le_rfl, by linarith [p.net_pos]⟩
  refine ⟨0, ats, hadm, ?_⟩
  rw [uniform_weakProb, ← hf0]
  have hsub : {ts | WeakOut π ts} ∩ shiftBox p.Δnoise ats ⊆
      weakCube (p.Δnet - h) p.Δnoise π := by
    rintro ts ⟨hw, hb⟩
    refine ⟨mem_cube.mpr fun j => ?_, hw⟩
    have hb0 := (mem_shiftBox.mp hb (π i0)).1
    have hbl := (mem_shiftBox.mp hb (π il)).2
    have ha0 : ats (π i0) = p.Δnet - h := by simp [hats_def]
    have hal : ats (π il) = 0 := by simp [hats_def, hne]
    have h1 : ts (π i0) ≤ ts j := by
      have := hw (show i0 ≤ π.symm j from Fin.mk_le_of_le_val (Nat.zero_le _))
      simpa using this
    have h2 : ts j ≤ ts (π il) := by
      have hle : π.symm j ≤ il := by
        rw [Fin.le_def]
        have := (π.symm j).isLt
        simp only [hil]
        omega
      have := hw hle
      simpa using this
    exact ⟨by linarith, by linarith⟩
  have hvol := volume_real_weakCube (n := n) (a := p.Δnet - h) (b := p.Δnoise) (by linarith) π
  have hmono : volume.real ({ts | WeakOut π ts} ∩ shiftBox p.Δnoise ats) ≤
      volume.real (weakCube (p.Δnet - h) p.Δnoise π) :=
    measureReal_mono hsub (ne_top_of_le_ne_top (volume_cube_ne_top _ _)
      (measure_mono Set.inter_subset_left))
  have e : p.Δnoise - (p.Δnet - h) = p.Δnoise - p.Δnet + h := by ring
  rw [hvol, e] at hmono
  calc volume.real ({ts | WeakOut π ts} ∩ shiftBox p.Δnoise ats) / p.Δnoise ^ n
      ≤ f h := div_le_div_of_nonneg_right hmono (pow_pos h0 n).le
    _ < f 0 + δ := hfh

/-! ### Appendix Theorem 3.3: `ε(2) = α − α²/2` -/

/-- For uniform noise, `Pr[x − y < Δnet] = 1 − (1 − α)²/2`. -/
theorem uniform_nearProb (hα : p.Δnet ≤ p.Δnoise) :
    nearProb (uniformNoise p h0) = 1 - (1 - p.α) ^ 2 / 2 := by
  set σ : Equiv.Perm (Fin 2) := Equiv.swap 0 1 with hσ
  have hm : MeasurableSet {η : Fin 2 → ℝ | η 0 - η 1 < p.Δnet} :=
    measurableSet_lt ((measurable_pi_apply 0).sub (measurable_pi_apply 1)) measurable_const
  have hweak : ∀ ts : Fin 2 → ℝ, WeakOut σ ts ↔ ts 1 ≤ ts 0 := by
    intro ts
    unfold WeakOut
    rw [Fin.monotone_iff_le_succ]
    simp [Fin.forall_fin_one, hσ]
  have hcompl : {η : Fin 2 → ℝ | η 0 - η 1 < p.Δnet}ᶜ =
      {η | WeakOut σ (![0, p.Δnet] + η)} := by
    ext η
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt, hweak]
    simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, zero_add]
    constructor <;> intro h <;> linarith
  have h1 : weakProb (uniformNoise p h0) ![0, p.Δnet] σ =
      1 - ((uniformNoise p h0).joint 2).real {η : Fin 2 → ℝ | η 0 - η 1 < p.Δnet} := by
    unfold weakProb
    rw [← hcompl, probReal_compl_eq_one_sub hm]
  have h2 : weakProb (uniformNoise p h0) ![0, p.Δnet] σ = (1 - p.α) ^ 2 / 2 := by
    rw [uniform_weakProb]
    have hset : {ts | WeakOut σ ts} ∩ shiftBox p.Δnoise ![0, p.Δnet] =
        weakCube p.Δnet p.Δnoise σ := by
      ext ts
      simp only [weakCube, Set.mem_inter_iff, Set.mem_ofPred_eq, mem_cube, mem_shiftBox, hweak,
        Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one, Set.mem_Icc, zero_add]
      constructor
      · rintro ⟨hw, ⟨h00, h01⟩, h10, h11⟩
        exact ⟨⟨⟨by linarith, h01⟩, h10, by linarith⟩, hw⟩
      · rintro ⟨⟨⟨h00, h01⟩, h10, h11⟩, hw⟩
        exact ⟨hw, ⟨by linarith [p.net_pos], h01⟩, h10, by linarith [p.net_pos]⟩
    rw [hset, volume_real_weakCube hα]
    have e := one_sub_alpha_pow p h0 2
    have h2 : ((2 ! : ℕ) : ℝ) = 2 := by norm_num [Nat.factorial]
    rw [h2] at e ⊢
    rw [e]
  rw [← joint_two_near (uniformNoise p h0) (a := 0) (b := 1) (by decide)]
  linarith

/-- **Appendix Theorem 3.3.** -/
theorem uniform_isLeast_two (hα : p.Δnet ≤ p.Δnoise) :
    IsLeast {ε : ℝ | OrderingEquality p (uniformNoise p h0) 2 ε} (p.α - p.α ^ 2 / 2) := by
  have h := eps2_isLeast (uniformNoise p h0)
  rw [uniform_nearProb p h0 hα] at h
  have e : 1 - (1 - p.α) ^ 2 / 2 - 1 / 2 = p.α - p.α ^ 2 / 2 := by ring
  rwa [e] at h

end EqualOpportunity

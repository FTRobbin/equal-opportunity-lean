import EqualOpportunity.Equality.Adaptive

/-!
# Theorem A.2 against the non-adaptive adversary

A non-adaptive timestamp assignment is the constant strategy of the adaptive model, so the
upper bound `Pr[π] ≤ ((1 + α)ⁿ − n αⁿ) / n!` proved there for every adaptive strategy
(`Strategy.vol_le`) applies.  As the paper notes, the bound is tight only for the adaptive
adversary (`Strategy.exists_winProb_gt`); here it is a sound guarantee.

The last section derives Theorem A.2's `ε(n)` from the upper and lower bounds.
-/

open MeasureTheory
open scoped Nat ENNReal

namespace EqualOpportunity

/-- **Volume bound for the tail region**: the bound for adaptive strategies, applied to the
constant strategy. -/
theorem volume_tailRegion_le {L a : ℝ} (haL : a ≤ L) (m : ℕ) (t : Fin m → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc 0 a) :
    (∀ x ∈ Set.Icc 0 a, volume (tailRegion L x t) ≤ ENNReal.ofReal (polyB L m (a - x))) ∧
    (∀ x ∈ Set.Icc a (a + L),
      volume (tailRegion L x t) ≤ ENNReal.ofReal (polyA m (L + a - x))) := by
  have h := Strategy.vol_le haL (Strategy.const t) (Strategy.const_within ht)
  simp only [Strategy.vol_const] at h
  exact h

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
/-- For uniform noise, the probability that `π` is a possible output is the volume of a tail
region, divided by `Δnoiseⁿ`. -/
theorem uniform_weakProb_eq_tailRegion {T : ℝ} {ats : Fin n → ℝ}
    (hats : Admissible p (fun _ => T) ats) (π : Equiv.Perm (Fin n)) :
    weakProb (uniformNoise p h0) ats π =
      volume.real (tailRegion p.Δnoise 0 fun i => ats (π i) - T) / p.Δnoise ^ n := by
  set ats' : Fin n → ℝ := fun j => ats j - T with hats'
  have hats0 : ∀ j, 0 ≤ ats' j := fun j => by simp only [hats']; linarith [(hats j).1]
  rw [weakProb_sub_const p _ ats T π, uniform_weakProb]
  have hset : {ts | WeakOut π ts} ∩ shiftBox p.Δnoise ats' =
      reorder π ⁻¹' tailRegion p.Δnoise 0 (fun i => ats (π i) - T) := by
    ext ts
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, mem_shiftBox, Set.mem_preimage, reorder_apply,
      tailRegion, WeakOut, Function.comp]
    constructor
    · rintro ⟨hw, hb⟩
      exact ⟨fun i => hb (π i), fun i => (hats0 (π i)).trans (hb (π i)).1, hw⟩
    · rintro ⟨hb, _, hw⟩
      exact ⟨hw, fun j => by simpa [hats'] using hb (π.symm j)⟩
  rw [hset, measureReal_def, volume_preimage_reorder, ← measureReal_def]

/-- **The adaptive model extends the non-adaptive one**: a non-adaptive assignment has the same
probability of producing `π` as the constant strategy with the same offsets. -/
theorem weakProb_eq_winProb_const {T : ℝ} {ats : Fin n → ℝ}
    (hats : Admissible p (fun _ => T) ats) (π : Equiv.Perm (Fin n)) :
    weakProb (uniformNoise p h0) ats π =
      (Strategy.const fun i => ats (π i) - T).winProb p := by
  rw [uniform_weakProb_eq_tailRegion p h0 hats π, Strategy.winProb_const p h0]

/-- **Theorem A.2, upper bound** (sound against the non-adaptive adversary). -/
theorem uniform_weakProb_le (hα : p.Δnet ≤ p.Δnoise) {T : ℝ} {ats : Fin n → ℝ}
    (hats : Admissible p (fun _ => T) ats) (π : Equiv.Perm (Fin n)) :
    weakProb (uniformNoise p h0) ats π ≤ ((1 + p.α) ^ n - n * p.α ^ n) / (n ! : ℝ) := by
  rw [weakProb_eq_winProb_const p h0 hats π]
  refine Strategy.winProb_le p h0 hα _ (Strategy.const_admissible p fun i => ?_)
  exact ⟨by linarith [(hats (π i)).1], by linarith [(hats (π i)).2]⟩

/-! ### Theorem A.2: the upper deviation dominates for `n ≥ 2` -/

/-- `(1 + α)ⁿ + (1 − α)ⁿ ≥ 2 + n(n − 1)α²` for `α ≥ 0`, together with the two auxiliary facts
that make the induction go through. -/
theorem two_add_le_pow_add_pow {α : ℝ} (hα : 0 ≤ α) :
    ∀ n : ℕ, 2 + (n : ℝ) * ((n : ℝ) - 1) * α ^ 2 ≤ (1 + α) ^ n + (1 - α) ^ n ∧
      2 * (n : ℝ) * α ≤ (1 + α) ^ n - (1 - α) ^ n ∧ 2 ≤ (1 + α) ^ n + (1 - α) ^ n := by
  intro n
  induction n with
  | zero => norm_num
  | succ n ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have eS : (1 + α) ^ (n + 1) + (1 - α) ^ (n + 1) =
        ((1 + α) ^ n + (1 - α) ^ n) + α * ((1 + α) ^ n - (1 - α) ^ n) := by ring
    have eD : (1 + α) ^ (n + 1) - (1 - α) ^ (n + 1) =
        ((1 + α) ^ n - (1 - α) ^ n) + α * ((1 + α) ^ n + (1 - α) ^ n) := by ring
    have h1 : α * (2 * (n : ℝ) * α) ≤ α * ((1 + α) ^ n - (1 - α) ^ n) :=
      mul_le_mul_of_nonneg_left ih2 hα
    have h2 : α * 2 ≤ α * ((1 + α) ^ n + (1 - α) ^ n) := mul_le_mul_of_nonneg_left ih3 hα
    have h3 : 0 ≤ α * (2 * (n : ℝ) * α) := by positivity
    rw [eS, eD]
    push_cast
    refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

/-- For `n ≥ 2` and `0 ≤ α ≤ 1`, the lower deviation `1 − (1 − α)ⁿ` is at most the upper
deviation `(1 + α)ⁿ − 1 − n αⁿ` (last step of the proof of Theorem A.2). -/
theorem lower_dev_le_upper_dev {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {n : ℕ} (hn : 2 ≤ n) :
    1 - (1 - α) ^ n ≤ (1 + α) ^ n - 1 - n * α ^ n := by
  have h1 := (two_add_le_pow_add_pow hα0 n).1
  have h2 : α ^ n ≤ α ^ 2 := pow_le_pow_of_le_one hα0 hα1 hn
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hsq : 0 ≤ α ^ 2 := sq_nonneg α
  have h3 : (n : ℝ) * α ^ n ≤ (n : ℝ) * ((n : ℝ) - 1) * α ^ 2 := by
    have h4 : (n : ℝ) * α ^ n ≤ (n : ℝ) * α ^ 2 := mul_le_mul_of_nonneg_left h2 (by linarith)
    have h5 : (n : ℝ) * α ^ 2 ≤ (n : ℝ) * ((n : ℝ) - 1) * α ^ 2 :=
      mul_le_mul_of_nonneg_right (by nlinarith) hsq
    linarith
  linarith

/-- **Theorem A.2**: for `n ≥ 2`, uniform noise satisfies ε(n)-Ordering Equality with
`ε(n) = ((1 + α)ⁿ − 1 − n αⁿ) / n!`. -/
theorem uniform_orderingEquality (hα : p.Δnet ≤ p.Δnoise) {n : ℕ} (hn : 2 ≤ n) :
    OrderingEquality p (uniformNoise p h0) n (((1 + p.α) ^ n - 1 - n * p.α ^ n) / (n ! : ℝ)) := by
  have hα0 : 0 ≤ p.α := div_nonneg p.net_pos.le h0.le
  have hα1 : p.α ≤ 1 := (div_le_one h0).mpr hα
  have hdev := lower_dev_le_upper_dev hα0 hα1 hn
  have hfac : (0 : ℝ) < (n ! : ℝ) := by positivity
  rw [orderingEquality_iff]
  intro T ats hats π
  have h1 := uniform_weakProb_le p h0 hα hats π
  have h2 := uniform_strictProb_ge p h0 hα hats π
  have e1 : ((1 + p.α) ^ n - 1 - n * p.α ^ n) / (n ! : ℝ) =
      ((1 + p.α) ^ n - n * p.α ^ n) / (n ! : ℝ) - 1 / (n ! : ℝ) := by ring
  have e2 : (1 - (1 - p.α) ^ n) / (n ! : ℝ) =
      1 / (n ! : ℝ) - (1 - p.α) ^ n / (n ! : ℝ) := by ring
  have h3 : (1 - (1 - p.α) ^ n) / (n ! : ℝ) ≤ ((1 + p.α) ^ n - 1 - n * p.α ^ n) / (n ! : ℝ) :=
    div_le_div_of_nonneg_right hdev hfac.le
  constructor
  · rw [e1]
    linarith
  · rw [e2] at h3
    linarith

end EqualOpportunity

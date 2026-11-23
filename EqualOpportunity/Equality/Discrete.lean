import EqualOpportunity.Equality.Envelope
import EqualOpportunity.Equality.Noise
import EqualOpportunity.Equality.Combinatorics

/-!
# The discrete distribution (Theorems 3.3 and 3.4)

Noise is `j * Δnet` for a uniformly random bucket index `j ∈ {0, …, k}`.  Because assigned
timestamps of simultaneous commands differ by less than `Δnet`:

* commands in different buckets are ordered by bucket, whatever the adversary does;
* commands in the same bucket are ordered by the adversary.

So `π` is a possible output only if the bucket indices are weakly increasing along `π`
(`C(k+n, n)` cases out of `(k+1)ⁿ`), and it is forced whenever they are strictly increasing
(`C(k+1, n)` cases).
-/

open MeasureTheory
open scoped Nat ENNReal

namespace EqualOpportunity

variable {n : ℕ} (p : Params)

/-! ### The joint noise law is a uniform count over bucket assignments -/

/-- The noise vector determined by a bucket assignment. -/
noncomputable def Params.points (s : Fin n → Fin (p.k + 1)) : Fin n → ℝ := fun i => p.point (s i)

theorem Params.measurable_points : Measurable (p.points (n := n)) :=
  measurable_pi_iff.mpr fun i => Measurable.of_discrete.comp (measurable_pi_apply i)

theorem discrete_joint (n : ℕ) :
    (discreteNoise p).joint n = (Measure.pi fun _ : Fin n => bucketLaw p.k).map p.points :=
  (Measure.pi_map_pi (μ := fun _ : Fin n => bucketLaw p.k) (f := fun _ => p.point)
    fun _ => Measurable.of_discrete.aemeasurable).symm

theorem bucketLaw_singleton (k : ℕ) (j : Fin (k + 1)) :
    bucketLaw k {j} = ((k : ℝ≥0∞) + 1)⁻¹ := by
  rw [bucketLaw, Measure.uniformOfFinset_apply_singleton_of_mem (Finset.mem_univ j)]
  simp

theorem bucket_pi_real (k n : ℕ) (F : Finset (Fin n → Fin (k + 1))) :
    (Measure.pi fun _ : Fin n => bucketLaw k).real (F : Set (Fin n → Fin (k + 1))) =
      (F.card : ℝ) / ((k : ℝ) + 1) ^ n := by
  rw [measureReal_def, ← sum_measure_singleton]
  simp only [Measure.pi_singleton, bucketLaw_singleton, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Finset.sum_const, nsmul_eq_mul]
  have hk : ((k : ℝ≥0∞) + 1).toReal = (k : ℝ) + 1 := by
    rw [ENNReal.toReal_add (by simp) (by simp)]
    simp
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv, hk]
  simp [div_eq_mul_inv]

theorem bucket_pi_real_setOf (k n : ℕ) (P : (Fin n → Fin (k + 1)) → Prop) [DecidablePred P] :
    (Measure.pi fun _ : Fin n => bucketLaw k).real {s | P s} =
      ((Finset.univ.filter P).card : ℝ) / ((k : ℝ) + 1) ^ n := by
  rw [← bucket_pi_real]
  congr 1
  ext s
  simp

open Classical in
theorem discrete_weakProb (ats : Fin n → ℝ) (π : Equiv.Perm (Fin n)) :
    weakProb (discreteNoise p) ats π =
      ((Finset.univ.filter fun s : Fin n → Fin (p.k + 1) =>
        WeakOut π (ats + p.points s)).card : ℝ) / ((p.k : ℝ) + 1) ^ n := by
  unfold weakProb
  have hm : MeasurableSet {η : Fin n → ℝ | WeakOut π (ats + η)} :=
    (measurableSet_weakOut π).preimage (measurable_const_add_pi ats)
  rw [discrete_joint, map_measureReal_apply p.measurable_points hm]
  exact bucket_pi_real_setOf p.k n _

open Classical in
theorem discrete_strictProb (ats : Fin n → ℝ) (π : Equiv.Perm (Fin n)) :
    strictProb (discreteNoise p) ats π =
      ((Finset.univ.filter fun s : Fin n → Fin (p.k + 1) =>
        StrictOut π (ats + p.points s)).card : ℝ) / ((p.k : ℝ) + 1) ^ n := by
  unfold strictProb
  have hm : MeasurableSet {η : Fin n → ℝ | StrictOut π (ats + η)} :=
    (measurableSet_strictOut π).preimage (measurable_const_add_pi ats)
  rw [discrete_joint, map_measureReal_apply p.measurable_points hm]
  exact bucket_pi_real_setOf p.k n _

/-! ### Timestamps versus bucket indices -/

theorem Params.point_add_net_le {a b : Fin (p.k + 1)} (h : a < b) :
    p.point a + p.Δnet ≤ p.point b := by
  unfold Params.point
  have h' : ((a : ℕ) : ℝ) + 1 ≤ ((b : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (Fin.lt_def.mp h)
  nlinarith [p.net_pos]

theorem Params.point_mono {a b : Fin (p.k + 1)} (h : a ≤ b) : p.point a ≤ p.point b := by
  unfold Params.point
  have h' : ((a : ℕ) : ℝ) ≤ ((b : ℕ) : ℝ) := by exact_mod_cast Fin.le_def.mp h
  exact mul_le_mul_of_nonneg_right h' p.net_pos.le

variable {p}

/-- If `π` is a possible output then bucket indices weakly increase along `π`:
a later bucket can never be overtaken, since assigned timestamps differ by less than `Δnet`. -/
theorem monotone_of_weakOut {T : ℝ} {ats : Fin n → ℝ} (hats : Admissible p (fun _ => T) ats)
    {π : Equiv.Perm (Fin n)} {s : Fin n → Fin (p.k + 1)} (h : WeakOut π (ats + p.points s)) :
    Monotone (s ∘ π) := by
  intro i j hij
  by_contra hlt
  rw [not_le] at hlt
  have h1 := h hij
  have h2 := p.point_add_net_le hlt
  have h3 := (hats (π i)).1
  have h4 := (hats (π j)).2
  simp only [Function.comp, Pi.add_apply, Params.points] at h1 h2
  linarith

/-- If bucket indices strictly increase along `π` then `π` is forced. -/
theorem strictOut_of_strictMono {T : ℝ} {ats : Fin n → ℝ} (hats : Admissible p (fun _ => T) ats)
    {π : Equiv.Perm (Fin n)} {s : Fin n → Fin (p.k + 1)} (h : StrictMono (s ∘ π)) :
    StrictOut π (ats + p.points s) := by
  intro i j hij
  have h2 := p.point_add_net_le (h hij)
  have h3 := (hats (π j)).1
  have h4 := (hats (π i)).2
  simp only [Function.comp, Pi.add_apply, Params.points] at h2 ⊢
  linarith

/-- With equal assigned timestamps, weakly increasing bucket indices make `π` possible. -/
theorem weakOut_const_of_monotone (c : ℝ) {π : Equiv.Perm (Fin n)} {s : Fin n → Fin (p.k + 1)}
    (h : Monotone (s ∘ π)) : WeakOut π ((fun _ => c) + p.points s) := by
  intro i j hij
  have h1 := p.point_mono (h hij)
  simp only [Function.comp, Pi.add_apply, Params.points] at h1 ⊢
  linarith

/-! ### Counting along a permutation -/

theorem card_monotone_comp (π : Equiv.Perm (Fin n)) (k : ℕ) :
    (Finset.univ.filter fun s : Fin n → Fin (k + 1) => Monotone (s ∘ π)).card =
      (k + n).choose n := by
  rw [← card_monotone n k]
  refine Finset.card_nbij' (fun s => s ∘ π) (fun s => s ∘ π.symm) ?_ ?_ ?_ ?_
  · intro s hs
    simpa using hs
  · intro s hs
    have hcomp : (s ∘ π.symm) ∘ π = s := by funext x; simp
    simpa [hcomp] using hs
  · intro s _
    funext x
    simp
  · intro s _
    funext x
    simp

theorem card_strictMono_comp (π : Equiv.Perm (Fin n)) (k : ℕ) :
    (Finset.univ.filter fun s : Fin n → Fin (k + 1) => StrictMono (s ∘ π)).card =
      (k + 1).choose n := by
  rw [← card_strictMono n (k + 1)]
  refine Finset.card_nbij' (fun s => s ∘ π) (fun s => s ∘ π.symm) ?_ ?_ ?_ ?_
  · intro s hs
    simpa using hs
  · intro s hs
    have hcomp : (s ∘ π.symm) ∘ π = s := by funext x; simp
    simpa [hcomp] using hs
  · intro s _
    funext x
    simp
  · intro s _
    funext x
    simp

/-! ### Bounds on the probability of an order -/

variable (p)

theorem discrete_weakProb_le {T : ℝ} {ats : Fin n → ℝ} (hats : Admissible p (fun _ => T) ats)
    (π : Equiv.Perm (Fin n)) :
    weakProb (discreteNoise p) ats π ≤ ((p.k + n).choose n : ℝ) / ((p.k : ℝ) + 1) ^ n := by
  classical
  rw [discrete_weakProb, ← card_monotone_comp π p.k]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card fun s hs => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    exact monotone_of_weakOut hats hs

theorem discrete_strictProb_ge {T : ℝ} {ats : Fin n → ℝ} (hats : Admissible p (fun _ => T) ats)
    (π : Equiv.Perm (Fin n)) :
    ((p.k + 1).choose n : ℝ) / ((p.k : ℝ) + 1) ^ n ≤ strictProb (discreteNoise p) ats π := by
  classical
  rw [discrete_strictProb, ← card_strictMono_comp π p.k]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card fun s hs => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    exact strictOut_of_strictMono hats hs

/-- The upper bound is attained when all assigned timestamps are equal. -/
theorem discrete_weakProb_const_ge (c : ℝ) (π : Equiv.Perm (Fin n)) :
    ((p.k + n).choose n : ℝ) / ((p.k : ℝ) + 1) ^ n ≤
      weakProb (discreteNoise p) (fun _ => c) π := by
  classical
  rw [discrete_weakProb, ← card_monotone_comp π p.k]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card fun s hs => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    exact weakOut_const_of_monotone c hs

theorem admissible_const (T : ℝ) : Admissible p (fun _ : Fin n => T) (fun _ => T) :=
  fun _ => ⟨le_rfl, by linarith [p.net_pos]⟩

/-! ### Theorems 3.4 and 3.3 -/

theorem discrete_outProb_le {T : ℝ} {ats : Fin n → ℝ} (hats : Admissible p (fun _ => T) ats)
    (tb : TieBreak n) (π : Equiv.Perm (Fin n)) :
    outProb (discreteNoise p) ats tb π ≤ ((p.k + n).choose n : ℝ) / ((p.k : ℝ) + 1) ^ n :=
  (outProb_le_weakProb _ ats tb π).trans (discrete_weakProb_le p hats π)

theorem discrete_le_outProb {T : ℝ} {ats : Fin n → ℝ} (hats : Admissible p (fun _ => T) ats)
    (tb : TieBreak n) (π : Equiv.Perm (Fin n)) :
    ((p.k + 1).choose n : ℝ) / ((p.k : ℝ) + 1) ^ n ≤ outProb (discreteNoise p) ats tb π :=
  (discrete_strictProb_ge p hats π).trans (strictProb_le_outProb _ ats tb π)

/-- **Theorem 3.4.** -/
theorem discrete_isLeast (n : ℕ) :
    IsLeast {ε : ℝ | OrderingEquality p (discreteNoise p) n ε}
      (((p.k + n).choose n : ℝ) / ((p.k : ℝ) + 1) ^ n - 1 / (n ! : ℝ)) := by
  constructor
  · show OrderingEquality p (discreteNoise p) n _
    rw [orderingEquality_iff]
    intro T ats hats π
    have h1 := discrete_weakProb_le p hats π
    have h2 := discrete_strictProb_ge p hats π
    have h3 := two_div_factorial_le p.k n
    have h4 : 2 / (n ! : ℝ) = 1 / (n ! : ℝ) + 1 / (n ! : ℝ) := by ring
    constructor <;> linarith
  · intro ε hε
    have h := ((orderingEquality_iff _ ε).mp hε 0 (fun _ => 0) (admissible_const p 0) 1).1
    have h2 := discrete_weakProb_const_ge p 0 (1 : Equiv.Perm (Fin n))
    linarith

/-- **Theorem 3.3**: the case `n = 2` of Theorem 3.4. -/
theorem discrete_isLeast_two :
    IsLeast {ε : ℝ | OrderingEquality p (discreteNoise p) 2 ε} (1 / (2 * ((p.k : ℝ) + 1))) := by
  have h := discrete_isLeast p 2
  have hk : ((p.k : ℝ) + 1) ≠ 0 := by positivity
  have e : ((p.k + 2).choose 2 : ℝ) / ((p.k : ℝ) + 1) ^ 2 - 1 / ((2 ! : ℕ) : ℝ) =
      1 / (2 * ((p.k : ℝ) + 1)) := by
    rw [Nat.cast_choose_two, Nat.factorial_two]
    push_cast
    field_simp
    ring
  rwa [e] at h

/-- **Degenerate regime `n > k + 1`.**  Give the commands strictly decreasing assigned
timestamps along `π`.  Then `π` needs strictly increasing bucket indices, and there are not
enough buckets. -/
theorem discrete_degenerate (hn : p.k + 1 < n) (π : Equiv.Perm (Fin n)) :
    ∃ (T : ℝ) (ats : Fin n → ℝ), Admissible p (fun _ => T) ats ∧
      ∀ tb : TieBreak n, outProb (discreteNoise p) ats tb π = 0 := by
  classical
  set ats : Fin n → ℝ := fun j => p.Δnet / (((π.symm j : ℕ) : ℝ) + 2) with hats_def
  have hadm : Admissible p (fun _ => (0 : ℝ)) ats := by
    intro j
    have hpos : (0 : ℝ) < ((π.symm j : ℕ) : ℝ) + 2 := by positivity
    refine ⟨div_nonneg p.net_pos.le hpos.le, ?_⟩
    rw [zero_add]
    exact div_lt_self p.net_pos (by linarith [Nat.cast_nonneg (α := ℝ) (π.symm j : ℕ)])
  have hdec : ∀ i j : Fin n, i < j → ats (π j) < ats (π i) := by
    intro i j hij
    simp only [hats_def, Equiv.symm_apply_apply]
    apply div_lt_div_of_pos_left p.net_pos (by positivity)
    have : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast Fin.lt_def.mp hij
    linarith
  have hempty : ∀ s : Fin n → Fin (p.k + 1), ¬WeakOut π (ats + p.points s) := by
    intro s h
    have hstrict : StrictMono (s ∘ π) := by
      intro i j hij
      by_contra hle
      rw [not_lt] at hle
      have h1 := h hij.le
      have h2 := p.point_mono hle
      have h3 := hdec i j hij
      simp only [Function.comp, Pi.add_apply, Params.points] at h1 h2
      linarith
    have := Fintype.card_le_of_injective _ hstrict.injective
    simp only [Fintype.card_fin] at this
    omega
  have hzero : weakProb (discreteNoise p) ats π = 0 := by
    rw [discrete_weakProb]
    have : (Finset.univ.filter fun s : Fin n → Fin (p.k + 1) =>
        WeakOut π (ats + p.points s)) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun s _ => hempty s
    rw [this]
    simp
  refine ⟨0, ats, hadm, fun tb => ?_⟩
  exact le_antisymm ((outProb_le_weakProb _ ats tb π).trans_eq hzero) measureReal_nonneg

end EqualOpportunity

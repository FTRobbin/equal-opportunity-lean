import EqualOpportunity.Equality.Envelope

/-!
# Theorem 3.2: every noise distribution has `ε(2) ≥ 1 / (2(k+1))`

Two commands, noise `(x, y)` drawn independently from `D`.  Give the first command assigned
timestamp `T` and the second `T + d` with `0 ≤ d < Δnet`.  The first command can be output
first exactly when `x ≤ y + d`.

1. `pair_sup` (the paper's "the adversary decides the order of two commands whose noise
   differs by less than `Δnet`"): letting `d ↑ Δnet`, any valid `ε` satisfies
   `Pr[x − y < Δnet] ≤ ε + 1/2`.  The window is half-open, so this is a limit.
2. By symmetry of `(x, y)`, `2 · Pr[x − y < Δnet] ≥ 1 + Pr[|x − y| < Δnet]
   ≥ 1 + Pr[same bucket]`.
3. `Pr[same bucket] = Σᵢ D(Bᵢ)² ≥ 1/(k+1)` by Cauchy–Schwarz over the `k+1` buckets.
-/

open MeasureTheory
open scoped Nat ENNReal

namespace EqualOpportunity

variable (p : Params)

/-! ### Buckets -/

/-- Bucket `i` is `[i·Δnet, (i+1)·Δnet)`. -/
def Params.bucket (i : ℕ) : Set ℝ := Set.Ico ((i : ℝ) * p.Δnet) (((i : ℝ) + 1) * p.Δnet)

theorem Params.measurableSet_bucket (i : ℕ) : MeasurableSet (p.bucket i) := measurableSet_Ico

theorem Params.bucket_disjoint_of_lt {i j : ℕ} (h : i < j) :
    Disjoint (p.bucket i) (p.bucket j) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  have h1 : ((i : ℝ) + 1) ≤ (j : ℝ) := by exact_mod_cast h
  have h2 := mul_le_mul_of_nonneg_right h1 p.net_pos.le
  have h3 := hx.2
  have h4 := hx'.1
  linarith

theorem Params.bucket_pairwiseDisjoint (s : Set ℕ) : s.PairwiseDisjoint p.bucket := by
  intro i _ j _ hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact p.bucket_disjoint_of_lt h
  · exact (p.bucket_disjoint_of_lt h).symm

/-- The buckets `0, …, k` cover `[0, Δnoise]`. -/
theorem Params.Icc_subset_iUnion_bucket :
    Set.Icc 0 p.Δnoise ⊆ ⋃ i ∈ Finset.range (p.k + 1), p.bucket i := by
  intro x hx
  simp only [Set.mem_iUnion, Finset.mem_range, exists_prop]
  refine ⟨⌊x / p.Δnet⌋₊, ?_, ?_, ?_⟩
  · exact Nat.lt_succ_of_le (Nat.floor_le_floor (div_le_div_of_nonneg_right hx.2 p.net_pos.le))
  · exact (le_div_iff₀ p.net_pos).mp (Nat.floor_le (div_nonneg hx.1 p.net_pos.le))
  · exact (div_lt_iff₀ p.net_pos).mp (Nat.lt_floor_add_one _)

variable {p}

theorem sum_bucket (N : NoiseLaw p) :
    ∑ i ∈ Finset.range (p.k + 1), N.D.real (p.bucket i) = 1 := by
  rw [← measureReal_biUnion_finset (p.bucket_pairwiseDisjoint _)
    (fun i _ => p.measurableSet_bucket i)]
  have h1 : N.D (Set.Icc 0 p.Δnoise) = 1 := (prob_compl_eq_zero_iff measurableSet_Icc).mp N.supp
  have h2 : N.D.real (Set.Icc 0 p.Δnoise) = 1 := by simp [measureReal_def, h1]
  apply le_antisymm measureReal_le_one
  rw [← h2]
  exact measureReal_mono p.Icc_subset_iUnion_bucket (measure_ne_top _ _)

/-- Cauchy–Schwarz over the `k + 1` buckets. -/
theorem sum_sq_bucket_ge (N : NoiseLaw p) :
    1 / ((p.k : ℝ) + 1) ≤ ∑ i ∈ Finset.range (p.k + 1), N.D.real (p.bucket i) ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := Finset.range (p.k + 1))
    (f := fun i => N.D.real (p.bucket i))
  rw [sum_bucket, Finset.card_range] at h
  push_cast at h
  rw [div_le_iff₀ (by positivity)]
  linarith

/-! ### Pairs of noise samples -/

variable (p)

/-- Both samples fall in the same bucket. -/
def Params.sameBucket : Set (ℝ × ℝ) := ⋃ i ∈ Finset.range (p.k + 1), p.bucket i ×ˢ p.bucket i

/-- The first sample exceeds the second by less than `Δnet` (or is smaller). -/
def Params.nearLt : Set (ℝ × ℝ) := {q | q.1 - q.2 < p.Δnet}

theorem Params.measurableSet_nearLt : MeasurableSet p.nearLt :=
  measurableSet_lt (measurable_fst.sub measurable_snd) measurable_const

variable {p}

theorem prod_sameBucket (N : NoiseLaw p) :
    (N.D.prod N.D).real p.sameBucket =
      ∑ i ∈ Finset.range (p.k + 1), N.D.real (p.bucket i) ^ 2 := by
  unfold Params.sameBucket
  rw [measureReal_biUnion_finset ?_
    (fun i _ => (p.measurableSet_bucket i).prod (p.measurableSet_bucket i))]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [measureReal_prod_prod, sq]
  · intro i hi j hj hij
    exact Set.disjoint_prod.mpr (Or.inl (p.bucket_pairwiseDisjoint _ hi hj hij))

/-- Symmetry step: `2·Pr[x − y < Δnet] ≥ 1 + Pr[same bucket]`. -/
theorem one_add_sameBucket_le (N : NoiseLaw p) :
    1 + (N.D.prod N.D).real p.sameBucket ≤ 2 * (N.D.prod N.D).real p.nearLt := by
  set μ := N.D.prod N.D with hμ
  have hW := p.measurableSet_nearLt
  have hswap : μ.real (Prod.swap ⁻¹' p.nearLt) = μ.real p.nearLt := by
    have h := (Measure.measurePreserving_swap (μ := N.D) (ν := N.D)).measure_preimage
      hW.nullMeasurableSet
    rw [measureReal_def, measureReal_def, hμ, h]
  have hunion : p.nearLt ∪ Prod.swap ⁻¹' p.nearLt = Set.univ := by
    ext ⟨x, y⟩
    simp only [Params.nearLt, Set.mem_union, Set.mem_ofPred_eq, Set.mem_preimage, Prod.swap_prod_mk,
      Set.mem_univ, iff_true]
    by_contra h
    push Not at h
    linarith [p.net_pos, h.1, h.2]
  have hsub : p.sameBucket ⊆ p.nearLt ∩ Prod.swap ⁻¹' p.nearLt := by
    rintro ⟨x, y⟩ h
    simp only [Params.sameBucket, Set.mem_iUnion, Set.mem_prod, Params.bucket, Set.mem_Ico,
      exists_prop] at h
    obtain ⟨i, _, ⟨hx1, hx2⟩, hy1, hy2⟩ := h
    simp only [Params.nearLt, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage,
      Prod.swap_prod_mk]
    constructor <;> linarith
  have h := measureReal_union_add_inter (μ := μ) (s := p.nearLt) (hW.preimage measurable_swap)
  rw [hunion, probReal_univ, hswap] at h
  have h2 := measureReal_mono (μ := μ) hsub
  linarith

/-! ### From the protocol to a pair of samples -/

theorem admissible_pair (p : Params) {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < p.Δnet) :
    Admissible p (fun _ : Fin 2 => (0 : ℝ)) ![0, d] := by
  intro i
  fin_cases i
  · simpa using p.net_pos
  · simpa using ⟨hd0, hd1⟩

/-- With assigned timestamps `(0, d)`, command 0 can be output first iff `x ≤ y + d`. -/
theorem weakProb_two (N : NoiseLaw p) (d : ℝ) :
    weakProb N ![0, d] (1 : Equiv.Perm (Fin 2)) =
      (N.D.prod N.D).real {q : ℝ × ℝ | q.1 ≤ q.2 + d} := by
  have hmp := measurePreserving_finTwoArrow N.D
  have hm : MeasurableSet {q : ℝ × ℝ | q.1 ≤ q.2 + d} :=
    measurableSet_le measurable_fst (measurable_snd.add measurable_const)
  have hset : {η : Fin 2 → ℝ | WeakOut 1 (![0, d] + η)} =
      MeasurableEquiv.finTwoArrow ⁻¹' {q : ℝ × ℝ | q.1 ≤ q.2 + d} := by
    ext η
    simp only [WeakOut, Set.mem_ofPred_eq, Set.mem_preimage, Equiv.Perm.coe_one,
      Function.comp_id, Fin.monotone_iff_le_succ, Fin.forall_fin_one]
    simp [add_comm]
  unfold weakProb NoiseLaw.joint
  rw [hset, measureReal_def, hmp.measure_preimage hm.nullMeasurableSet, measureReal_def]

/-- **The adversary decides near-ties** (`n = 2`).  If `ε`-Ordering Equality holds for two
commands, then `Pr[x − y < Δnet] ≤ ε + 1/2`: by taking the offset `d` arbitrarily close to
`Δnet`, the adversary gets its preferred order whenever the noise differs by less than `Δnet`
in the unfavourable direction. -/
theorem pair_sup (N : NoiseLaw p) {ε : ℝ} (h : OrderingEquality p N 2 ε) :
    (N.D.prod N.D).real p.nearLt ≤ ε + 1 / 2 := by
  rw [orderingEquality_iff] at h
  set μ := N.D.prod N.D with hμ
  have hd : ∀ d, 0 ≤ d → d < p.Δnet → μ.real {q : ℝ × ℝ | q.1 ≤ q.2 + d} ≤ ε + 1 / 2 := by
    intro d hd0 hd1
    have h1 := (h 0 ![0, d] (admissible_pair p hd0 hd1) 1).1
    rw [weakProb_two] at h1
    have h2 : ((2 ! : ℕ) : ℝ) = 2 := by norm_num [Nat.factorial]
    rw [h2] at h1
    linarith
  have hnonneg : 0 ≤ ε + 1 / 2 := le_trans measureReal_nonneg (hd 0 le_rfl p.net_pos)
  -- offsets increasing to `Δnet`
  set dseq : ℕ → ℝ := fun m => p.Δnet - p.Δnet * (1 / ((m : ℝ) + 1)) with hdseq
  have hdlt : ∀ m, dseq m < p.Δnet := by
    intro m
    have : 0 < p.Δnet * (1 / ((m : ℝ) + 1)) := mul_pos p.net_pos (by positivity)
    simp only [hdseq]
    linarith
  have hd0 : ∀ m, 0 ≤ dseq m := by
    intro m
    have h1 : 1 / ((m : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [Nat.cast_nonneg (α := ℝ) m]
    have := mul_le_mul_of_nonneg_left h1 p.net_pos.le
    simp only [hdseq]
    linarith
  have hmono : Monotone fun m => {q : ℝ × ℝ | q.1 ≤ q.2 + dseq m} := by
    intro m m' hmm' q hq
    have h1 : 1 / ((m' : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hmm')
    have h2 := mul_le_mul_of_nonneg_left h1 p.net_pos.le
    simp only [Set.mem_ofPred_eq, hdseq] at hq ⊢
    linarith
  have hU : (⋃ m, {q : ℝ × ℝ | q.1 ≤ q.2 + dseq m}) = p.nearLt := by
    ext q
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Params.nearLt]
    constructor
    · rintro ⟨m, hm⟩
      linarith [hdlt m]
    · intro hq
      have hδ : 0 < (p.Δnet - (q.1 - q.2)) / p.Δnet := div_pos (by linarith) p.net_pos
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
      refine ⟨m, ?_⟩
      have h1 := mul_lt_mul_of_pos_left hm p.net_pos
      rw [mul_div_cancel₀ _ p.net_pos.ne'] at h1
      simp only [hdseq]
      linarith
  have hle : μ p.nearLt ≤ ENNReal.ofReal (ε + 1 / 2) := by
    rw [← hU, hmono.measure_iUnion]
    refine iSup_le fun m => ?_
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (hd (dseq m) (hd0 m) (hdlt m))
  exact ENNReal.toReal_le_of_le_ofReal hnonneg hle

/-- **Theorem 3.2.** -/
theorem eps2_lower_bound (N : NoiseLaw p) {ε : ℝ} (h : OrderingEquality p N 2 ε) :
    1 / (2 * ((p.k : ℝ) + 1)) ≤ ε := by
  have h1 := pair_sup N h
  have h2 := one_add_sameBucket_le N
  have h3 := prod_sameBucket N
  have h4 := sum_sq_bucket_ge N
  have h5 : 1 / (2 * ((p.k : ℝ) + 1)) = 1 / ((p.k : ℝ) + 1) / 2 := by
    field_simp
  rw [h5]
  linarith

end EqualOpportunity

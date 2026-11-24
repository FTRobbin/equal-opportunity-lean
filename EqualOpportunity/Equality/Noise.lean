import EqualOpportunity.Basic

/-!
# The two concrete noise distributions analysed in the paper

* `discreteNoise p` — uniform on the `k + 1` points `0, Δnet, 2Δnet, …, kΔnet` (Theorem 3.3);
* `uniformNoise p`  — the continuous uniform distribution on `[0, Δnoise]` (Appendix A.5).
-/

open MeasureTheory

namespace EqualOpportunity

/-- Uniform distribution on the bucket indices `{0, …, k}`. -/
noncomputable def bucketLaw (k : ℕ) : Measure (Fin (k + 1)) :=
  Measure.uniformOfFinset Finset.univ

instance (k : ℕ) : IsProbabilityMeasure (bucketLaw k) := by
  constructor
  classical
  rw [bucketLaw, Measure.uniformOfFinset_apply]
  simp only [Set.mem_univ, Finset.filter_true, Finset.card_univ, Fintype.card_fin]
  exact ENNReal.div_self (by simp) (by simp)

/-- The point `j * Δnet` carried by bucket index `j`. -/
noncomputable def Params.point (p : Params) (j : Fin (p.k + 1)) : ℝ := ((j : ℕ) : ℝ) * p.Δnet

theorem Params.point_mem (p : Params) (j : Fin (p.k + 1)) : p.point j ∈ Set.Icc 0 p.Δnoise := by
  have hj : ((j : ℕ) : ℝ) ≤ p.k := by exact_mod_cast Nat.lt_succ_iff.mp j.isLt
  constructor
  · exact mul_nonneg (Nat.cast_nonneg _) p.net_pos.le
  · exact (mul_le_mul_of_nonneg_right hj p.net_pos.le).trans p.k_mul_le

/-- **Discrete distribution** of Theorem 3.3: pick `j ∈ {0, …, k}` uniformly, output `j * Δnet`. -/
noncomputable def discreteNoise (p : Params) : NoiseLaw p where
  D := (bucketLaw p.k).map p.point
  supp := by
    rw [Measure.map_apply Measurable.of_discrete measurableSet_Icc.compl]
    convert measure_empty (μ := bucketLaw p.k)
    ext j
    simpa using p.point_mem j

/-- **Continuous uniform distribution** on `[0, Δnoise]`: Lebesgue measure restricted to the
interval and rescaled to total mass 1 (`ProbabilityTheory.cond volume s` is
`(volume s)⁻¹ • volume.restrict s`).  Needs `0 < Δnoise`. -/
noncomputable def uniformNoise (p : Params) (h : 0 < p.Δnoise) : NoiseLaw p where
  D := ProbabilityTheory.cond volume (Set.Icc 0 p.Δnoise)
  prob := ProbabilityTheory.cond_isProbabilityMeasure_of_finite
    (by simp [Real.volume_Icc, h]) (by simp [Real.volume_Icc])
  supp := by
    simp [ProbabilityTheory.cond, Measure.restrict_apply measurableSet_Icc.compl]

end EqualOpportunity

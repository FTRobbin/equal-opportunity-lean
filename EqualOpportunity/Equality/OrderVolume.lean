import EqualOpportunity.Equality.Envelope

/-!
# Each ordering takes `1/n!` of a cube

For `n` points drawn uniformly and independently from an interval `[a, b]`, every order is
equally likely.  In Lebesgue terms: inside the cube `[a, b]ⁿ`, the region where the
coordinates are (weakly or strictly) increasing along a given permutation `π` has volume
`(b − a)ⁿ / n!`.

Proof: the `n!` strict regions are disjoint, are images of one another under coordinate
permutations (which preserve volume), and cover the cube up to the set of ties, which lies in
finitely many hyperplanes and so has volume zero.
-/

open MeasureTheory
open scoped Nat ENNReal

namespace EqualOpportunity

variable {n : ℕ}

/-- The cube `[a, b]ⁿ`. -/
def cube (n : ℕ) (a b : ℝ) : Set (Fin n → ℝ) := Set.pi Set.univ fun _ => Set.Icc a b

theorem mem_cube {a b : ℝ} {ts : Fin n → ℝ} : ts ∈ cube n a b ↔ ∀ i, ts i ∈ Set.Icc a b := by
  unfold cube
  simp only [Set.mem_univ_pi]

theorem measurableSet_cube (a b : ℝ) : MeasurableSet (cube n a b) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Icc

theorem volume_cube (a b : ℝ) : volume (cube n a b) = ENNReal.ofReal (b - a) ^ n := by
  unfold cube
  rw [volume_pi_pi]
  simp [Real.volume_Icc]

theorem volume_cube_ne_top (a b : ℝ) : volume (cube n a b) ≠ ∞ := by
  rw [volume_cube]
  exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top

theorem volume_real_cube {a b : ℝ} (hab : a ≤ b) : volume.real (cube n a b) = (b - a) ^ n := by
  rw [measureReal_def, volume_cube, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by linarith)]

/-! ### Permuting coordinates preserves volume -/

/-- Reorder the coordinates of a vector along `π`. -/
noncomputable def reorder (π : Equiv.Perm (Fin n)) : (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ => ℝ) π.symm

theorem reorder_apply (π : Equiv.Perm (Fin n)) (g : Fin n → ℝ) : reorder π g = g ∘ π := by
  funext i
  have h := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin n => ℝ) π.symm g (π i)
  simpa [reorder] using h

theorem volume_preimage_reorder (π : Equiv.Perm (Fin n)) (S : Set (Fin n → ℝ)) :
    volume (reorder π ⁻¹' S) = volume S :=
  (volume_measurePreserving_piCongrLeft (fun _ : Fin n => ℝ) π.symm).measure_preimage_equiv S

/-! ### Ties have volume zero -/

/-- Vectors with two equal coordinates. -/
def ties (n : ℕ) : Set (Fin n → ℝ) := ⋃ i : Fin n, ⋃ j : Fin n, ⋃ (_ : i ≠ j), {ts | ts i = ts j}

theorem volume_eq_coord {i j : Fin n} (hij : i ≠ j) :
    volume {ts : Fin n → ℝ | ts i = ts j} = 0 := by
  let L : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    (LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ) - (LinearMap.proj j : (Fin n → ℝ) →ₗ[ℝ] ℝ)
  have hset : {ts : Fin n → ℝ | ts i = ts j} = (LinearMap.ker L : Set (Fin n → ℝ)) := by
    ext ts
    simp [L, sub_eq_zero]
  rw [hset]
  apply Measure.addHaar_submodule
  intro htop
  have hmem : Pi.single i (1 : ℝ) ∈ LinearMap.ker L := by
    rw [htop]
    trivial
  simp [L, hij.symm] at hmem

theorem volume_ties : volume (ties n) = 0 := by
  unfold ties
  simp only [measure_iUnion_null_iff]
  intro i j hij
  exact volume_eq_coord hij

theorem strictOut_of_weakOut_of_notMem_ties {π : Equiv.Perm (Fin n)} {ts : Fin n → ℝ}
    (hw : WeakOut π ts) (ht : ts ∉ ties n) : StrictOut π ts := by
  apply Monotone.strictMono_of_injective hw
  intro i j hij
  by_contra hne
  apply ht
  simp only [ties, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
  exact ⟨π i, π j, fun h => hne (π.injective h), hij⟩

/-! ### The strict regions -/

/-- The part of the cube whose coordinates strictly increase along `π`. -/
def strictCube (a b : ℝ) (π : Equiv.Perm (Fin n)) : Set (Fin n → ℝ) :=
  cube n a b ∩ {ts | StrictOut π ts}

/-- The part of the cube whose coordinates weakly increase along `π`. -/
def weakCube (a b : ℝ) (π : Equiv.Perm (Fin n)) : Set (Fin n → ℝ) :=
  cube n a b ∩ {ts | WeakOut π ts}

theorem strictCube_eq_preimage (a b : ℝ) (π : Equiv.Perm (Fin n)) :
    strictCube a b π = reorder π ⁻¹' strictCube a b 1 := by
  ext ts
  simp only [strictCube, Set.mem_inter_iff, Set.mem_preimage, reorder_apply, mem_cube,
    Set.mem_ofPred_eq, StrictOut, Equiv.Perm.coe_one, Function.comp_id]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i => h1 (π i), h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i => by simpa using h1 (π.symm i), h2⟩

theorem volume_strictCube (a b : ℝ) (π : Equiv.Perm (Fin n)) :
    volume (strictCube a b π) = volume (strictCube a b (1 : Equiv.Perm (Fin n))) := by
  rw [strictCube_eq_preimage, volume_preimage_reorder]

/-- **Each strict order takes `1/n!` of the cube.** -/
theorem volume_real_strictCube {a b : ℝ} (hab : a ≤ b) (π : Equiv.Perm (Fin n)) :
    volume.real (strictCube a b π) = (b - a) ^ n / (n ! : ℝ) := by
  have hfin : ∀ σ : Equiv.Perm (Fin n), volume (strictCube a b σ) ≠ ∞ := fun σ =>
    ne_top_of_le_ne_top (volume_cube_ne_top a b) (measure_mono Set.inter_subset_left)
  have hdisj : Pairwise (Function.onFun Disjoint fun σ : Equiv.Perm (Fin n) =>
      strictCube a b σ) := by
    intro σ τ hστ
    rw [Function.onFun, Set.disjoint_left]
    rintro ts ⟨_, h1⟩ ⟨_, h2⟩
    exact hστ (eq_of_strictOut_of_weakOut h2 (StrictOut.weakOut h1))
  have hmeas : ∀ σ : Equiv.Perm (Fin n), MeasurableSet (strictCube a b σ) := fun σ =>
    (measurableSet_cube a b).inter (measurableSet_strictOut σ)
  have hsum := measureReal_iUnion_fintype (μ := volume) hdisj hmeas hfin
  have hU : volume (⋃ σ : Equiv.Perm (Fin n), strictCube a b σ) = volume (cube n a b) := by
    apply le_antisymm
    · exact measure_mono (Set.iUnion_subset fun σ => Set.inter_subset_left)
    · have hsub : cube n a b ⊆ (⋃ σ : Equiv.Perm (Fin n), strictCube a b σ) ∪ ties n := by
        intro ts hts
        by_cases ht : ts ∈ ties n
        · exact Or.inr ht
        · exact Or.inl (Set.mem_iUnion.mpr ⟨Tuple.sort ts, hts,
            strictOut_of_weakOut_of_notMem_ties (Tuple.monotone_sort ts) ht⟩)
      calc volume (cube n a b)
          ≤ volume ((⋃ σ : Equiv.Perm (Fin n), strictCube a b σ) ∪ ties n) := measure_mono hsub
        _ ≤ volume (⋃ σ : Equiv.Perm (Fin n), strictCube a b σ) + volume (ties n) :=
            measure_union_le _ _
        _ = volume (⋃ σ : Equiv.Perm (Fin n), strictCube a b σ) := by
            rw [volume_ties, add_zero]
  have hconst : ∀ σ : Equiv.Perm (Fin n),
      volume.real (strictCube a b σ) = volume.real (strictCube a b π) := fun σ => by
    rw [measureReal_def, measureReal_def, volume_strictCube a b σ, volume_strictCube a b π]
  rw [measureReal_def, hU, ← measureReal_def, volume_real_cube hab] at hsum
  simp only [hconst, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul] at hsum
  rw [eq_div_iff (by positivity)]
  linarith

theorem volume_weakCube (a b : ℝ) (π : Equiv.Perm (Fin n)) :
    volume (weakCube a b π) = volume (strictCube a b π) := by
  apply le_antisymm
  · have hsub : weakCube a b π ⊆ strictCube a b π ∪ ties n := by
      rintro ts ⟨hts, hw⟩
      by_cases ht : ts ∈ ties n
      · exact Or.inr ht
      · exact Or.inl ⟨hts, strictOut_of_weakOut_of_notMem_ties hw ht⟩
    calc volume (weakCube a b π) ≤ volume (strictCube a b π ∪ ties n) := measure_mono hsub
      _ ≤ volume (strictCube a b π) + volume (ties n) := measure_union_le _ _
      _ = volume (strictCube a b π) := by rw [volume_ties, add_zero]
  · exact measure_mono fun ts hts => ⟨hts.1, StrictOut.weakOut hts.2⟩

/-- **Each weak order takes `1/n!` of the cube** (ties do not matter). -/
theorem volume_real_weakCube {a b : ℝ} (hab : a ≤ b) (π : Equiv.Perm (Fin n)) :
    volume.real (weakCube a b π) = (b - a) ^ n / (n ! : ℝ) := by
  rw [measureReal_def, volume_weakCube, ← measureReal_def, volume_real_strictCube hab]

end EqualOpportunity

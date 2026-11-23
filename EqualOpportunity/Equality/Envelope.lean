import EqualOpportunity.Equality.Defs

/-!
# What adversarial tie-breaking amounts to

For every tie-breaking rule, `StrictOut π ⊆ {output = π} ⊆ WeakOut π`, and both ends are
attained by some rule.  Hence `OrderingEquality` only depends on `weakProb` and `strictProb`
(`orderingEquality_iff`), which is the form every later proof uses.
-/

open MeasureTheory
open scoped Nat

namespace EqualOpportunity

variable {n : ℕ} {p : Params}

/-! ### Measurability of the basic events -/

theorem measurableSet_weakOut (π : Equiv.Perm (Fin n)) :
    MeasurableSet {ts : Fin n → ℝ | WeakOut π ts} := by
  have h : {ts : Fin n → ℝ | WeakOut π ts} = ⋂ i, ⋂ j, {ts | i ≤ j → ts (π i) ≤ ts (π j)} := by
    ext ts
    simp [WeakOut, Monotone]
  rw [h]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
  by_cases hij : i ≤ j
  · simpa [hij] using measurableSet_le (measurable_pi_apply (π i)) (measurable_pi_apply (π j))
  · simp [hij]

theorem measurableSet_strictOut (π : Equiv.Perm (Fin n)) :
    MeasurableSet {ts : Fin n → ℝ | StrictOut π ts} := by
  have h : {ts : Fin n → ℝ | StrictOut π ts} = ⋂ i, ⋂ j, {ts | i < j → ts (π i) < ts (π j)} := by
    ext ts
    simp [StrictOut, StrictMono]
  rw [h]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
  by_cases hij : i < j
  · simpa [hij] using measurableSet_lt (measurable_pi_apply (π i)) (measurable_pi_apply (π j))
  · simp [hij]

theorem measurable_const_add_pi (ats : Fin n → ℝ) : Measurable fun η : Fin n → ℝ => ats + η :=
  measurable_pi_iff.mpr fun i => by
    have h : Measurable fun η : Fin n → ℝ => ats i + η i :=
      (measurable_pi_apply (X := fun _ : Fin n => ℝ) i).const_add (ats i)
    exact h

/-! ### Forced orders are unique; non-forced consistent orders are not -/

theorem StrictOut.weakOut {π : Equiv.Perm (Fin n)} {ts : Fin n → ℝ} (h : StrictOut π ts) :
    WeakOut π ts :=
  StrictMono.monotone h

/-- If `π` is forced, it is the only consistent order. -/
theorem eq_of_strictOut_of_weakOut {π σ : Equiv.Perm (Fin n)} {ts : Fin n → ℝ}
    (hπ : StrictOut π ts) (hσ : WeakOut σ ts) : σ = π := by
  have h : ts ∘ σ = ts ∘ π := Tuple.unique_monotone hσ hπ.weakOut
  have hinj : Function.Injective ts := by
    intro a b hab
    have := StrictMono.injective hπ (a₁ := π.symm a) (a₂ := π.symm b) (by simpa using hab)
    simpa using this
  exact Equiv.ext fun i => hinj (congrFun h i)

/-- If `π` is consistent but not forced, some other order is consistent too (swap a tie). -/
theorem exists_ne_weakOut {π : Equiv.Perm (Fin n)} {ts : Fin n → ℝ}
    (hw : WeakOut π ts) (hs : ¬StrictOut π ts) : ∃ σ, σ ≠ π ∧ WeakOut σ ts := by
  unfold StrictOut StrictMono at hs
  push Not at hs
  obtain ⟨i, j, hij, hle⟩ := hs
  have heq : ts (π i) = ts (π j) := le_antisymm (hw hij.le) hle
  refine ⟨(Equiv.swap i j).trans π, ?_, ?_⟩
  · intro h
    have h' := congrArg (fun e : Equiv.Perm (Fin n) => e i) h
    simp only [Equiv.trans_apply, Equiv.swap_apply_left, EmbeddingLike.apply_eq_iff_eq] at h'
    exact hij.ne' h'
  · have hcomp : ts ∘ ((Equiv.swap i j).trans π) = ts ∘ π := by
      funext x
      simp only [Function.comp, Equiv.trans_apply]
      by_cases hx : x = i
      · subst hx
        simp [heq]
      · by_cases hx' : x = j
        · subst hx'
          simp [heq]
        · rw [Equiv.swap_apply_of_ne_of_ne hx hx']
    unfold WeakOut
    rw [hcomp]
    exact hw

/-! ### Tie-breaking by a priority list -/

open Classical in
/-- Output the first permutation of the list that is consistent with the timestamps. -/
noncomputable def firstConsistent :
    List (Equiv.Perm (Fin n)) → (Fin n → ℝ) → Equiv.Perm (Fin n)
  | [], _ => Equiv.refl _
  | σ :: L, ts => if WeakOut σ ts then σ else firstConsistent L ts

theorem firstConsistent_weakOut :
    ∀ (L : List (Equiv.Perm (Fin n))) (ts : Fin n → ℝ),
      (∃ σ ∈ L, WeakOut σ ts) → WeakOut (firstConsistent L ts) ts
  | [], ts, h => by simp at h
  | σ :: L, ts, h => by
    unfold firstConsistent
    split_ifs with hσ
    · exact hσ
    · apply firstConsistent_weakOut L ts
      obtain ⟨τ, hτ, hτw⟩ := h
      rcases List.mem_cons.mp hτ with rfl | hτ
      · exact absurd hτw hσ
      · exact ⟨τ, hτ, hτw⟩

theorem measurableSet_firstConsistent :
    ∀ (L : List (Equiv.Perm (Fin n))) (π : Equiv.Perm (Fin n)),
      MeasurableSet {ts : Fin n → ℝ | firstConsistent L ts = π}
  | [], π => by simp [firstConsistent]
  | σ :: L, π => by
    have h : {ts : Fin n → ℝ | firstConsistent (σ :: L) ts = π} =
        ({ts | WeakOut σ ts} ∩ {_ts | σ = π}) ∪
          ({ts | WeakOut σ ts}ᶜ ∩ {ts | firstConsistent L ts = π}) := by
      ext ts
      simp only [firstConsistent, Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff,
        Set.mem_compl_iff]
      split_ifs with hσ <;> simp [hσ]
    rw [h]
    exact ((measurableSet_weakOut σ).inter (MeasurableSet.const _)).union
      ((measurableSet_weakOut σ).compl.inter (measurableSet_firstConsistent L π))

theorem not_weakOut_of_firstConsistent_append {π : Equiv.Perm (Fin n)} :
    ∀ (L : List (Equiv.Perm (Fin n))) (ts : Fin n → ℝ), π ∉ L →
      firstConsistent (L ++ [π]) ts = π → ∀ σ ∈ L, ¬WeakOut σ ts
  | [], _, _, _ => by simp
  | τ :: L, ts, hπ, h => by
    have hτπ : τ ≠ π := fun e => hπ (e ▸ List.mem_cons_self)
    simp only [List.cons_append, firstConsistent] at h
    split_ifs at h with hτ
    · exact absurd h hτπ
    · intro σ hσ
      rcases List.mem_cons.mp hσ with rfl | hσ
      · exact hτ
      · exact not_weakOut_of_firstConsistent_append L ts
          (fun h' => hπ (List.mem_cons_of_mem _ h')) h σ hσ

/-- The tie-breaking rule "first consistent permutation of `L`", for a list containing every
permutation. -/
noncomputable def TieBreak.ofList (L : List (Equiv.Perm (Fin n))) (hL : ∀ σ, σ ∈ L) :
    TieBreak n where
  out := firstConsistent L
  consistent ts :=
    firstConsistent_weakOut L ts ⟨Tuple.sort ts, hL _, Tuple.monotone_sort ts⟩
  measurable := measurableSet_firstConsistent L

/-- A rule that outputs `π` whenever `π` is consistent. -/
noncomputable def TieBreak.favor (π : Equiv.Perm (Fin n)) : TieBreak n :=
  TieBreak.ofList (π :: Finset.univ.toList) fun σ =>
    List.mem_cons_of_mem _ (Finset.mem_toList.mpr (Finset.mem_univ σ))

/-- A rule that outputs `π` only when `π` is forced. -/
noncomputable def TieBreak.avoid (π : Equiv.Perm (Fin n)) : TieBreak n :=
  TieBreak.ofList ((Finset.univ.erase π).toList ++ [π]) fun σ => by
    by_cases h : σ = π
    · simp [h]
    · simp [h]

theorem TieBreak.favor_out {π : Equiv.Perm (Fin n)} {ts : Fin n → ℝ} (h : WeakOut π ts) :
    (TieBreak.favor π).out ts = π := by
  simp [TieBreak.favor, TieBreak.ofList, firstConsistent, h]

theorem TieBreak.strictOut_of_avoid_out {π : Equiv.Perm (Fin n)} {ts : Fin n → ℝ}
    (h : (TieBreak.avoid π).out ts = π) : StrictOut π ts := by
  by_contra hs
  have hw : WeakOut π ts := h ▸ (TieBreak.avoid π).consistent ts
  obtain ⟨σ, hσ, hσw⟩ := exists_ne_weakOut hw hs
  have hnot := not_weakOut_of_firstConsistent_append (π := π) (Finset.univ.erase π).toList ts
    (by simp) h σ (by simp [hσ])
  exact hnot hσw

/-! ### The envelope -/

theorem strictProb_le_outProb (N : NoiseLaw p) (ats : Fin n → ℝ) (tb : TieBreak n)
    (π : Equiv.Perm (Fin n)) : strictProb N ats π ≤ outProb N ats tb π :=
  measureReal_mono fun _η hη => eq_of_strictOut_of_weakOut hη (tb.consistent _)

theorem outProb_le_weakProb (N : NoiseLaw p) (ats : Fin n → ℝ) (tb : TieBreak n)
    (π : Equiv.Perm (Fin n)) : outProb N ats tb π ≤ weakProb N ats π :=
  measureReal_mono fun η hη => by
    have h := tb.consistent (ats + η)
    rw [Set.mem_ofPred_eq] at hη
    rwa [hη] at h

theorem weakProb_le_outProb_favor (N : NoiseLaw p) (ats : Fin n → ℝ) (π : Equiv.Perm (Fin n)) :
    weakProb N ats π ≤ outProb N ats (TieBreak.favor π) π :=
  measureReal_mono fun _η hη => TieBreak.favor_out hη

theorem outProb_avoid_le_strictProb (N : NoiseLaw p) (ats : Fin n → ℝ)
    (π : Equiv.Perm (Fin n)) : outProb N ats (TieBreak.avoid π) π ≤ strictProb N ats π :=
  measureReal_mono fun _η hη => TieBreak.strictOut_of_avoid_out hη

/-- `OrderingEquality` unfolded: the adversary's best case for `π` is `weakProb`, its worst
case is `strictProb`. -/
theorem orderingEquality_iff (N : NoiseLaw p) (ε : ℝ) :
    OrderingEquality p N n ε ↔
      ∀ (T : ℝ) (ats : Fin n → ℝ), Admissible p (fun _ => T) ats → ∀ π : Equiv.Perm (Fin n),
        weakProb N ats π - 1 / (n ! : ℝ) ≤ ε ∧ 1 / (n ! : ℝ) - strictProb N ats π ≤ ε := by
  constructor
  · intro h T ats hats π
    have h1 := (abs_le.mp (h T ats hats (TieBreak.favor π) π)).2
    have h2 := (abs_le.mp (h T ats hats (TieBreak.avoid π) π)).1
    have h3 := weakProb_le_outProb_favor N ats π
    have h4 := outProb_avoid_le_strictProb N ats π
    constructor <;> linarith
  · intro h T ats hats tb π
    obtain ⟨h1, h2⟩ := h T ats hats π
    have h3 := strictProb_le_outProb N ats tb π
    have h4 := outProb_le_weakProb N ats tb π
    rw [abs_le]
    constructor <;> linarith

end EqualOpportunity

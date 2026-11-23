import EqualOpportunity.Basic

/-!
# Δ-Ordering Separation (paper §2.3, Theorem 3.1)
-/

namespace EqualOpportunity

/-- **Δ-Ordering Separation** (§2.3).  Whatever the adversary does within its power and whatever
noise is drawn, if `i` is invoked at least `Δ` before `j` then `i`'s modified timestamp is
strictly smaller than `j`'s, so `i` precedes `j` in the output (no tie-breaking involved).

Quantifies over every index type `ι`, i.e. every set of commands, with arbitrary invocation
times `inv`. -/
def OrderingSeparation (p : Params) (Δ : ℝ) : Prop :=
  ∀ {ι : Type} (inv ats η : ι → ℝ),
    Admissible p inv ats → (∀ i, η i ∈ Set.Icc 0 p.Δnoise) →
    ∀ i j, inv i + Δ ≤ inv j → ats i + η i < ats j + η j

/-- **Theorem 3.1.**  Pompē-SRO achieves `(Δnet + Δnoise)`-Ordering Separation. -/
theorem orderingSeparation (p : Params) : OrderingSeparation p (p.Δnet + p.Δnoise) := by
  intro ι inv ats η hats hη i j hij
  have hi := (hats i).2
  have hj := (hats j).1
  have hηi := (hη i).2
  have hηj := (hη j).1
  linarith

end EqualOpportunity

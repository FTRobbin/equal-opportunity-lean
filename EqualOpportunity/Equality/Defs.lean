import EqualOpportunity.Basic

/-!
# ε-Ordering Equality (paper §2.3) in the Pompē-SRO timing model

The adversary has two powers, both from the paper:

1. it picks each command's assigned timestamp inside the window (`Admissible`), before any
   noise is revealed;
2. it orders ties: commands whose modified timestamps coincide are placed in any order it
   likes, and that choice may depend on the realized noise (`TieBreak`).

`OrderingEquality p N n ε` says: for `n` commands invoked at the same time, whatever the
adversary does, every total order `π` has `|Pr[π] − 1/n!| ≤ ε`.
-/

open MeasureTheory
open scoped Nat

namespace EqualOpportunity

variable {n : ℕ} {p : Params}

/-- **Adversary's power over ties.**  A rule that turns modified timestamps into an output
order.  The only constraint is `consistent`: the output never places a larger timestamp before
a smaller one.  Hence the rule is free exactly where timestamps tie.  (`measurable` is a
technical condition so that "the output is `π`" is an event.) -/
structure TieBreak (n : ℕ) where
  out : (Fin n → ℝ) → Equiv.Perm (Fin n)
  consistent : ∀ ts, WeakOut (out ts) ts
  measurable : ∀ π, MeasurableSet {ts | out ts = π}

/-- `Pr[π]`: probability that the output order is `π`, given assigned timestamps `ats`, noise
law `N` and tie-breaking `tb`.  The modified timestamps are `ats + η` with `η ∼ N.joint n`. -/
noncomputable def outProb (N : NoiseLaw p) (ats : Fin n → ℝ) (tb : TieBreak n)
    (π : Equiv.Perm (Fin n)) : ℝ :=
  (N.joint n).real {η | tb.out (ats + η) = π}

/-- **ε-Ordering Equality** for `n` commands invoked at the same time `T`:
`|Pr[π] − 1/n!| ≤ ε` for every order `π`, against every admissible assignment of timestamps
and every tie-breaking. -/
def OrderingEquality (p : Params) (N : NoiseLaw p) (n : ℕ) (ε : ℝ) : Prop :=
  ∀ (T : ℝ) (ats : Fin n → ℝ), Admissible p (fun _ => T) ats →
    ∀ (tb : TieBreak n) (π : Equiv.Perm (Fin n)), |outProb N ats tb π - 1 / (n ! : ℝ)| ≤ ε

/-! ### Working form

With adversarial tie-breaking, the largest probability the adversary can give `π` is the
probability that `π` is *consistent* with the timestamps, and the smallest is the probability
that `π` is *forced*.  All proofs go through these two quantities. -/

/-- Probability that `π` is consistent with the modified timestamps. -/
noncomputable def weakProb (N : NoiseLaw p) (ats : Fin n → ℝ) (π : Equiv.Perm (Fin n)) : ℝ :=
  (N.joint n).real {η | WeakOut π (ats + η)}

/-- Probability that `π` is forced by the modified timestamps. -/
noncomputable def strictProb (N : NoiseLaw p) (ats : Fin n → ℝ) (π : Equiv.Perm (Fin n)) : ℝ :=
  (N.joint n).real {η | StrictOut π (ats + η)}

/-- `OrderingEquality` unfolded: the adversary's best case for `π` is `weakProb`, its worst
case is `strictProb`. -/
theorem orderingEquality_iff (N : NoiseLaw p) (ε : ℝ) :
    OrderingEquality p N n ε ↔
      ∀ (T : ℝ) (ats : Fin n → ℝ), Admissible p (fun _ => T) ats → ∀ π : Equiv.Perm (Fin n),
        weakProb N ats π - 1 / (n ! : ℝ) ≤ ε ∧ 1 / (n ! : ℝ) - strictProb N ats π ≤ ε := by
  sorry

/-! ### Sanity: the definition is neither vacuous nor unsatisfiable -/

theorem OrderingEquality.mono {N : NoiseLaw p} {ε ε' : ℝ} (h : OrderingEquality p N n ε)
    (hε : ε ≤ ε') : OrderingEquality p N n ε' :=
  fun T ats hats tb π => (h T ats hats tb π).trans hε

/-- `ε = 1` always works (probabilities lie in `[0, 1]`), so some `ε` is always valid. -/
theorem orderingEquality_one (N : NoiseLaw p) : OrderingEquality p N n 1 := by
  intro T ats _ tb π
  have h0 : 0 ≤ outProb N ats tb π := measureReal_nonneg
  have h1 : outProb N ats tb π ≤ 1 := measureReal_le_one
  have h2 : 0 < 1 / (n ! : ℝ) := by positivity
  have h3 : 1 / (n ! : ℝ) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero n)
  rw [abs_le]
  constructor <;> linarith

end EqualOpportunity

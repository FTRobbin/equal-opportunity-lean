import Mathlib

/-!
# Timing model of Pompē-SRO (paper §3.5)

Everything the paper's ordering analysis needs, and nothing about the protocol itself:

* `Params`      — the two time constants `Δnet` and `Δnoise`;
* `Admissible`  — what the adversary may do to assigned timestamps
                  (Assumption 3.1 + Lemma 3.1 of the paper, taken as a hypothesis);
* `NoiseLaw`    — the distribution `D` the SRO-seeded noise is drawn from
                  (an ideal SRO: the noise of different commands is iid from `D`);
* `WeakOut`, `StrictOut` — when a permutation is a possible / the forced output order.

Conventions.  Commands are indexed by `Fin n`.  A permutation `π : Equiv.Perm (Fin n)` is read
as an output order: `π i` is the command placed at position `i`.
-/

open MeasureTheory

namespace EqualOpportunity

/-- The two time constants of the model.  `Δnet` bounds network + processing delay + clock
drift after GST; `Δnoise` is the width of the noise range, a protocol parameter. -/
structure Params where
  Δnet : ℝ
  Δnoise : ℝ
  net_pos : 0 < Δnet
  noise_nonneg : 0 ≤ Δnoise

namespace Params

/-- The paper's `k`: the natural number with `k * Δnet ≤ Δnoise < (k + 1) * Δnet`
(see `k_mul_le` and `lt_k_succ_mul`). -/
noncomputable def k (p : Params) : ℕ := ⌊p.Δnoise / p.Δnet⌋₊

/-- The appendix's `α = Δnet / Δnoise`.  (Lean's `x / 0 = 0`: only meaningful if `0 < Δnoise`.) -/
noncomputable def α (p : Params) : ℝ := p.Δnet / p.Δnoise

theorem k_mul_le (p : Params) : (p.k : ℝ) * p.Δnet ≤ p.Δnoise := by
  have h := Nat.floor_le (div_nonneg p.noise_nonneg p.net_pos.le)
  exact (le_div_iff₀ p.net_pos).mp h

theorem lt_k_succ_mul (p : Params) : p.Δnoise < ((p.k : ℝ) + 1) * p.Δnet := by
  have h := Nat.lt_floor_add_one (p.Δnoise / p.Δnet)
  exact (div_lt_iff₀ p.net_pos).mp h

end Params

variable {ι : Type*}

/-- **Adversary's power over assigned timestamps** (Assumption 3.1 + Lemma 3.1).
A command invoked at time `inv i` receives an assigned timestamp in `[inv i, inv i + Δnet)`;
the adversary may choose any value in that window.  The choice is a plain function, i.e. it is
made without knowledge of the noise (*non-adaptive* adversary). -/
def Admissible (p : Params) (inv ats : ι → ℝ) : Prop :=
  ∀ i, ats i ∈ Set.Ico (inv i) (inv i + p.Δnet)

/-- A noise distribution `D` on `[0, Δnoise]`. -/
structure NoiseLaw (p : Params) where
  /-- The distribution of one command's noise. -/
  D : Measure ℝ
  [prob : IsProbabilityMeasure D]
  /-- `D` puts no mass outside `[0, Δnoise]`. -/
  supp : D (Set.Icc 0 p.Δnoise)ᶜ = 0

attribute [instance] NoiseLaw.prob

/-- Joint law of the noise of `n` commands: independent samples from `D` (ideal SRO). -/
noncomputable def NoiseLaw.joint {p : Params} (N : NoiseLaw p) (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ => N.D

instance {p : Params} (N : NoiseLaw p) (n : ℕ) : IsProbabilityMeasure (N.joint n) := by
  unfold NoiseLaw.joint; infer_instance

variable {n : ℕ}

/-- `π` is *consistent with* the modified timestamps `ts`: reading the commands in the order
`π`, timestamps never decrease.  Every output order of the protocol satisfies this. -/
def WeakOut (π : Equiv.Perm (Fin n)) (ts : Fin n → ℝ) : Prop := Monotone (ts ∘ π)

/-- `π` is *forced by* the modified timestamps `ts`: timestamps strictly increase along `π`,
so there are no ties and `π` is the only possible output order. -/
def StrictOut (π : Equiv.Perm (Fin n)) (ts : Fin n → ℝ) : Prop := StrictMono (ts ∘ π)

end EqualOpportunity

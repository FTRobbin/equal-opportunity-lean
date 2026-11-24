import EqualOpportunity.Basic

/-!
# The adaptive adversary (used only for the tightness of Theorem A.2)

Everywhere else the adversary is non-adaptive: it fixes all assigned timestamps before any
noise is revealed.  The paper's tightness claim for Theorem A.2 is about a stronger adversary,
which this file models:

* the adversary fixes the commands' assigned timestamps one at a time, **in the order of the
  target permutation** (first command of the target order first);
* after fixing a command's assigned timestamp it sees that command's modified timestamp, and
  may use it to choose the timestamps of the remaining commands.

The noise is continuous uniform on `[0, Δnoise]`, so a command with assigned timestamp `t` gets
a modified timestamp uniform on `[t, t + Δnoise]`, independently of the past.

Timestamps are measured from the common invocation time `T`: a strategy's timestamps are
offsets in `[0, Δnet)`.
-/

open MeasureTheory
open scoped ENNReal

namespace EqualOpportunity

/-- **An adaptive strategy for `m` commands**, listed in the target order.
`cons t next`: give the next command assigned timestamp `t`; once its modified timestamp `y`
is revealed, continue with the strategy `next y` for the remaining commands. -/
inductive Strategy : ℕ → Type
  | nil : Strategy 0
  | cons {m : ℕ} (t : ℝ) (next : ℝ → Strategy m) : Strategy (m + 1)

namespace Strategy

/-- `σ.win p x`: the probability that, playing `σ`, the remaining commands all get modified
timestamps at least `x` and come out in the target order (each at least the previous one).

For `cons t next`: the next command's modified timestamp `y` is uniform on `[t, t + Δnoise]`
(density `1 / Δnoise`); it must be at least `x`, and then the rest must succeed above `y`. -/
noncomputable def win (p : Params) : {m : ℕ} → Strategy m → ℝ → ℝ≥0∞
  | _, nil, _ => 1
  | _, cons t next, x =>
      (ENNReal.ofReal p.Δnoise)⁻¹ *
        ∫⁻ y in Set.Icc (max t x) (t + p.Δnoise), (next y).win p y

/-- **What the adaptive adversary may do**: every assigned timestamp lies in the window
`[0, Δnet)`, whatever has been observed.  (The measurability clause is a technical condition
making the integral in `win` an ordinary Lebesgue integral.) -/
def Admissible (p : Params) : {m : ℕ} → Strategy m → Prop
  | _, nil => True
  | _, cons t next =>
      t ∈ Set.Ico 0 p.Δnet ∧ Measurable (fun y => (next y).win p y) ∧
        ∀ y, (next y).Admissible p

/-- The probability that the adaptive strategy `σ` produces the target order. -/
noncomputable def winProb (p : Params) {m : ℕ} (σ : Strategy m) : ℝ := (σ.win p 0).toReal

/-- The non-adaptive strategy with fixed offsets `t₀, …, t_{m−1}`: it ignores what it sees. -/
def const : {m : ℕ} → (Fin m → ℝ) → Strategy m
  | 0, _ => nil
  | _ + 1, t => cons (t 0) fun _ => const fun j => t j.succ

end Strategy

end EqualOpportunity

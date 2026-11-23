import Mathlib

/-!
# Counting lemmas for the discrete distribution

* `card_strictMono` — strictly increasing maps `Fin n → Fin m` are counted by `C(m, n)`
  (subsets of size `n`);
* `card_monotone`   — weakly increasing maps `Fin n → Fin (k+1)` are counted by `C(k+n, n)`
  (multisets of size `n`; stars and bars);
* `two_div_factorial_le` — the inequality behind "the upper deviation dominates the lower one"
  in Theorem 3.4, for every `n` and `k`.
-/

open scoped Nat

namespace EqualOpportunity

/-- The number of strictly increasing maps `Fin n → Fin m` is `C(m, n)`. -/
theorem card_strictMono (n m : ℕ) :
    (Finset.univ.filter fun s : Fin n → Fin m => StrictMono s).card = m.choose n := by
  classical
  have hcard := Finset.card_powersetCard n (Finset.univ : Finset (Fin m))
  rw [Finset.card_univ, Fintype.card_fin] at hcard
  rw [← hcard]
  refine Finset.card_bij (fun s _ => Finset.univ.image s) ?_ ?_ ?_
  · intro s hs
    rw [Finset.mem_filter] at hs
    rw [Finset.mem_powersetCard]
    refine ⟨Finset.subset_univ _, ?_⟩
    rw [Finset.card_image_of_injective _ hs.2.injective, Finset.card_univ, Fintype.card_fin]
  · intro s hs s' hs' h
    rw [Finset.mem_filter] at hs hs'
    have hc : (Finset.univ.image s).card = n := by
      rw [Finset.card_image_of_injective _ hs.2.injective, Finset.card_univ, Fintype.card_fin]
    have e1 := Finset.orderEmbOfFin_unique hc (f := s)
      (fun x => Finset.mem_image_of_mem _ (Finset.mem_univ x)) hs.2
    have e2 := Finset.orderEmbOfFin_unique hc (f := s')
      (fun x => by rw [h]; exact Finset.mem_image_of_mem _ (Finset.mem_univ x)) hs'.2
    rw [e1, e2]
  · intro t ht
    rw [Finset.mem_powersetCard] at ht
    refine ⟨t.orderEmbOfFin ht.2, ?_, ?_⟩
    · simp [(t.orderEmbOfFin ht.2).strictMono]
    · exact Finset.image_orderEmbOfFin_univ t ht.2

/-- A strictly increasing `ℕ`-valued map on `Fin n` grows by at least one per step. -/
theorem strictMono_add_le {n : ℕ} {t : Fin n → ℕ} (ht : StrictMono t) :
    ∀ (d : ℕ) (i j : Fin n), (j : ℕ) = i + d → t i + d ≤ t j := by
  intro d
  induction d with
  | zero =>
    intro i j h
    have hij : i = j := Fin.ext (by omega)
    subst hij
    simp
  | succ d ih =>
    intro i j h
    have hjlt := j.isLt
    have hj' : (i : ℕ) + d < n := by omega
    have h1 := ih i ⟨i + d, hj'⟩ rfl
    have h2 : t ⟨i + d, hj'⟩ < t j := ht (by rw [Fin.lt_def]; simp only; omega)
    omega

/-- Stars and bars: the number of weakly increasing maps `Fin n → Fin (k+1)` is `C(k+n, n)`. -/
theorem card_monotone (n k : ℕ) :
    (Finset.univ.filter fun s : Fin n → Fin (k + 1) => Monotone s).card = (k + n).choose n := by
  rw [← card_strictMono n (k + n)]
  refine Finset.card_nbij'
    (fun s i => ⟨s i + i, by have := (s i).isLt; have := i.isLt; omega⟩)
    (fun s i => ⟨min ((s i : ℕ) - i) k, by omega⟩) ?_ ?_ ?_ ?_
  · intro s hs
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hs ⊢
    intro i j hij
    have h1 : (s i : ℕ) ≤ s j := hs hij.le
    have h2 : (i : ℕ) < j := hij
    rw [Fin.lt_def]
    simp only
    omega
  · intro s hs
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hs ⊢
    have ht : StrictMono fun i => (s i : ℕ) := fun a b hab => hs hab
    intro i j hij
    have h1 : (i : ℕ) ≤ j := hij
    have h2 := strictMono_add_le ht ((j : ℕ) - i) i j (by omega)
    rw [Fin.le_def]
    simp only
    omega
  · intro s _
    funext i
    apply Fin.ext
    have := (s i).isLt
    simp only
    omega
  · intro s hs
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hs
    have ht : StrictMono fun i => (s i : ℕ) := fun a b hab => hs hab
    funext i
    apply Fin.ext
    have hi := i.isLt
    have h0 := strictMono_add_le ht (i : ℕ) ⟨0, by omega⟩ i (by simp)
    have h1 := strictMono_add_le ht (n - 1 - i) i ⟨n - 1, by omega⟩ (by simp only; omega)
    have h2 := (s ⟨n - 1, by omega⟩).isLt
    simp only at h0 h1 ⊢
    omega

/-- Rising plus falling factorial dominates twice the power, with no condition on `n`. -/
theorem two_mul_pow_le_ascFactorial_add_descFactorial (m : ℕ) :
    ∀ n : ℕ, 2 * m ^ n ≤ m.ascFactorial n + m.descFactorial n ∧
      m.descFactorial n ≤ m.ascFactorial n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [Nat.ascFactorial_succ, Nat.descFactorial_succ]
    set A := m.ascFactorial n
    set B := m.descFactorial n
    refine ⟨?_, Nat.mul_le_mul (by omega) ih2⟩
    have key : m * (A + B) ≤ (m + n) * A + (m - n) * B := by
      rcases le_total n m with h | h
      · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
        rw [Nat.add_sub_cancel_left]
        nlinarith [Nat.mul_le_mul_left n ih2]
      · rw [Nat.sub_eq_zero_of_le h]
        nlinarith [Nat.mul_le_mul h ih2]
    calc 2 * m ^ (n + 1) = m * (2 * m ^ n) := by ring
      _ ≤ m * (A + B) := Nat.mul_le_mul_left _ ih1
      _ ≤ (m + n) * A + (m - n) * B := key

/-- **Dominance inequality for Theorem 3.4**: `C(k+n,n)/(k+1)ⁿ + C(k+1,n)/(k+1)ⁿ ≥ 2/n!`,
i.e. the upper deviation from `1/n!` is at least the lower deviation.  Holds for all `n`, `k`. -/
theorem two_div_factorial_le (k n : ℕ) :
    2 / (n ! : ℝ) ≤
      ((k + n).choose n : ℝ) / ((k : ℝ) + 1) ^ n + ((k + 1).choose n : ℝ) / ((k : ℝ) + 1) ^ n := by
  have h := (two_mul_pow_le_ascFactorial_add_descFactorial (k + 1) n).1
  rw [Nat.ascFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose] at h
  have h' : (2 : ℝ) * ((k : ℝ) + 1) ^ n ≤
      (n ! : ℝ) * ((k + n).choose n : ℝ) + (n ! : ℝ) * ((k + 1).choose n : ℝ) := by
    exact_mod_cast h
  have hf : (0 : ℝ) < (n ! : ℝ) := by positivity
  have hk : (0 : ℝ) < ((k : ℝ) + 1) ^ n := by positivity
  rw [← add_div, div_le_div_iff₀ hf hk]
  nlinarith

end EqualOpportunity

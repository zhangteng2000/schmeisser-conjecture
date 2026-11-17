import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic

open scoped BigOperators

namespace Schmeisser

theorem pow_le_choose_mul_pow (m k : ℕ) (hkm : k ≤ m) :
    m ^ k ≤ m.choose k * k ^ k := by
  have hprod : (∏ j ∈ Finset.range k, m * (k - j)) ≤
      ∏ j ∈ Finset.range k, k * (m - j) := by
    apply Finset.prod_le_prod
    intro j hj
    have hjk : j ≤ k := (Finset.mem_range.mp hj).le
    have hjm : j ≤ m := hjk.trans hkm
    have hk := Nat.sub_add_cancel hjk
    have hm := Nat.sub_add_cancel hjm
    nlinarith [Nat.mul_le_mul_left j hkm]
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
    ← Nat.descFactorial_eq_prod_range, Nat.descFactorial_self,
    Nat.descFactorial_eq_factorial_mul_choose] at hprod
  have hfac := Nat.factorial_pos k
  nlinarith

theorem choose_square_mul_powers_ge (m k : ℕ) (hkm : k ≤ m) :
    m ^ m ≤ (m.choose k) ^ 2 * k ^ k * (m - k) ^ (m - k) := by
  have h₁ := pow_le_choose_mul_pow m k hkm
  have h₂ := pow_le_choose_mul_pow m (m - k) (Nat.sub_le m k)
  rw [Nat.choose_symm hkm] at h₂
  have h := Nat.mul_le_mul h₁ h₂
  rw [← pow_add, Nat.add_sub_of_le hkm] at h
  nlinarith

theorem real_choose_square_mul_powers_ge (m k : ℕ) (hkm : k ≤ m) :
    (m : ℝ) ^ m ≤ (m.choose k : ℝ) ^ 2 * (k : ℝ) ^ k *
      ((m - k : ℕ) : ℝ) ^ (m - k) := by
  exact_mod_cast choose_square_mul_powers_ge m k hkm

end Schmeisser

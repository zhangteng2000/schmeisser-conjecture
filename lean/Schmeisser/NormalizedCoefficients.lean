import Schmeisser.CoefficientExpansion
import Schmeisser.ChooseBounds
import Mathlib.Data.Nat.Choose.Cast

open scoped BigOperators
open Polynomial

namespace Schmeisser

theorem centredGeneratingPolynomial_eq_one_of_variance_zero {ι : Type*}
    (t : Finset ι) (η : ι → ℂ) (hV : ∑ j ∈ t, ‖η j‖ ^ 2 ≤ 0) :
    centredGeneratingPolynomial t η = 1 := by
  classical
  have hz (j : ι) (hj : j ∈ t) : η j = 0 := by
    have hs : ‖η j‖ ^ 2 ≤ ∑ l ∈ t, ‖η l‖ ^ 2 :=
      Finset.single_le_sum (fun l _ => sq_nonneg ‖η l‖) hj
    have hn : ‖η j‖ = 0 := by nlinarith [norm_nonneg (η j)]
    exact norm_eq_zero.mp hn
  unfold centredGeneratingPolynomial
  apply Finset.prod_eq_one
  intro j hj
  simp [hz j hj]

theorem coeff_norm_le_choose_mul_rpow {ι : Type*}
    (t : Finset ι) (η : ι → ℂ) (V : ℝ) (hV0 : 0 ≤ V)
    (hη : ∑ j ∈ t, η j = 0)
    (hV : ∑ j ∈ t, ‖η j‖ ^ 2 ≤ (t.card : ℝ) * V)
    (k : ℕ) (hkm : k ≤ t.card) :
    ‖(centredGeneratingPolynomial t η).coeff k‖ ≤
      (t.card.choose k : ℝ) * V ^ ((k : ℝ) / 2) := by
  by_cases hk0 : k = 0
  · subst k
    simp
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
  by_cases hv : V = 0
  · subst V
    have hp : centredGeneratingPolynomial t η = 1 :=
      centredGeneratingPolynomial_eq_one_of_variance_zero t η (by simpa using hV)
    rw [hp]
    simp only [Polynomial.coeff_one, ite_eq_right hk0, norm_zero]
    positivity
  have hvpos : 0 < V := lt_of_le_of_ne hV0 (Ne.symm hv)
  by_cases hkeq : k = t.card
  · subst k
    simpa only [Nat.choose_self, Nat.cast_one, one_mul] using
      centredGeneratingPolynomial_coeff_card_bound t η V hV0 hV
  have hklt : k < t.card := lt_of_le_of_ne hkm hkeq
  have hlpos : (0 : ℝ) < ((t.card - k : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt hklt
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hden : 0 < (k : ℝ) ^ k * ((t.card - k : ℕ) : ℝ) ^ (t.card - k) := by positivity
  have hratio : (t.card : ℝ) ^ t.card /
      ((k : ℝ) ^ k * ((t.card - k : ℕ) : ℝ) ^ (t.card - k)) ≤
      (t.card.choose k : ℝ) ^ 2 := by
    apply (div_le_iff₀ hden).2
    simpa only [mul_assoc] using real_choose_square_mul_powers_ge t.card k hkm
  have hsqrt : Real.sqrt ((t.card : ℝ) ^ t.card /
      ((k : ℝ) ^ k * ((t.card - k : ℕ) : ℝ) ^ (t.card - k))) ≤
      (t.card.choose k : ℝ) := by
    simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ t.card.choose k by positivity)]
      using Real.sqrt_le_sqrt hratio
  exact (centredGeneratingPolynomial_coeff_cauchy t η V hvpos hη hV k hkpos hklt).trans
    (mul_le_mul_of_nonneg_right hsqrt (Real.rpow_nonneg hV0 _))

theorem coeff_norm_div_choose_bound {ι : Type*}
    (t : Finset ι) (η : ι → ℂ) (V : ℝ) (hV0 : 0 ≤ V)
    (hη : ∑ j ∈ t, η j = 0)
    (hV : ∑ j ∈ t, ‖η j‖ ^ 2 ≤ (t.card : ℝ) * V)
    (k : ℕ) (hkm : k ≤ t.card) :
    ‖(centredGeneratingPolynomial t η).coeff k‖ / (t.card.choose k : ℝ) ≤
      V ^ ((k : ℝ) / 2) := by
  have hc : (0 : ℝ) < t.card.choose k := by exact_mod_cast Nat.choose_pos hkm
  apply (div_le_iff₀ hc).2
  simpa only [mul_comm] using coeff_norm_le_choose_mul_rpow t η V hV0 hη hV k hkm

theorem coeff_two_norm_div_choose_bound {ι : Type*}
    (t : Finset ι) (η : ι → ℂ) (V : ℝ) (hm : 2 ≤ t.card)
    (hη : ∑ j ∈ t, η j = 0)
    (hV : ∑ j ∈ t, ‖η j‖ ^ 2 ≤ (t.card : ℝ) * V) :
    ‖(centredGeneratingPolynomial t η).coeff 2‖ / (t.card.choose 2 : ℝ) ≤
      V / ((t.card : ℝ) - 1) := by
  have hmR : (2 : ℝ) ≤ t.card := by exact_mod_cast hm
  have hc : (0 : ℝ) < t.card.choose 2 := by exact_mod_cast Nat.choose_pos hm
  have h := div_le_div_of_nonneg_right
    (centredGeneratingPolynomial_coeff_two_bound t η V hη hV) hc.le
  have heq : ((t.card : ℝ) * V / 2) / (t.card.choose 2 : ℝ) = V / ((t.card : ℝ) - 1) := by
    rw [Nat.cast_choose_two]
    have hm0 : (t.card : ℝ) ≠ 0 := by linarith
    field_simp
  exact h.trans_eq heq

end Schmeisser

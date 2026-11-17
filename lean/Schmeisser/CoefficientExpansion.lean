import Schmeisser.CauchyCoefficients

open scoped BigOperators
open Polynomial

namespace Schmeisser

@[simp] theorem centredGeneratingPolynomial_coeff_zero {ι : Type*}
    (t : Finset ι) (η : ι → ℂ) : (centredGeneratingPolynomial t η).coeff 0 = 1 := by
  simp [centredGeneratingPolynomial, Polynomial.coeff_zero_prod]

theorem centredGeneratingPolynomial_insert {ι : Type*} [DecidableEq ι]
    (t : Finset ι) (η : ι → ℂ) {a : ι} (ha : a ∉ t) :
    centredGeneratingPolynomial (insert a t) η =
      centredGeneratingPolynomial t η + C (η a) * (X * centredGeneratingPolynomial t η) := by
  simp only [centredGeneratingPolynomial, Finset.prod_insert ha]
  ring

theorem centredGeneratingPolynomial_coeff_insert_succ {ι : Type*} [DecidableEq ι]
    (t : Finset ι) (η : ι → ℂ) {a : ι} (ha : a ∉ t) (k : ℕ) :
    (centredGeneratingPolynomial (insert a t) η).coeff (k + 1) =
      (centredGeneratingPolynomial t η).coeff (k + 1) +
      η a * (centredGeneratingPolynomial t η).coeff k := by
  rw [centredGeneratingPolynomial_insert t η ha]
  simp

@[simp] theorem centredGeneratingPolynomial_coeff_one {ι : Type*}
    (t : Finset ι) (η : ι → ℂ) :
    (centredGeneratingPolynomial t η).coeff 1 = ∑ j ∈ t, η j := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [centredGeneratingPolynomial, Polynomial.coeff_one]
  | @insert a t ha ih =>
    rw [show (1 : ℕ) = 0 + 1 by rfl, centredGeneratingPolynomial_coeff_insert_succ t η ha]
    simp [ih, ha, add_comm]

theorem centredGeneratingPolynomial_coeff_two_identity {ι : Type*}
    (t : Finset ι) (η : ι → ℂ) :
    (∑ j ∈ t, η j) ^ 2 =
      2 * (centredGeneratingPolynomial t η).coeff 2 + ∑ j ∈ t, (η j) ^ 2 := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [centredGeneratingPolynomial, Polynomial.coeff_one]
  | @insert a t ha ih =>
    rw [show (2 : ℕ) = 1 + 1 by rfl, centredGeneratingPolynomial_coeff_insert_succ t η ha]
    rw [centredGeneratingPolynomial_coeff_one, Finset.sum_insert ha, Finset.sum_insert ha]
    linear_combination ih

theorem centredGeneratingPolynomial_coeff_two {ι : Type*}
    (t : Finset ι) (η : ι → ℂ) (hη : ∑ j ∈ t, η j = 0) :
    (centredGeneratingPolynomial t η).coeff 2 = -(∑ j ∈ t, (η j) ^ 2) / 2 := by
  have h := centredGeneratingPolynomial_coeff_two_identity t η
  rw [hη] at h
  linear_combination -h / 2

theorem centredGeneratingPolynomial_coeff_two_bound {ι : Type*}
    (t : Finset ι) (η : ι → ℂ) (V : ℝ)
    (hη : ∑ j ∈ t, η j = 0)
    (hV : ∑ j ∈ t, ‖η j‖ ^ 2 ≤ (t.card : ℝ) * V) :
    ‖(centredGeneratingPolynomial t η).coeff 2‖ ≤ (t.card : ℝ) * V / 2 := by
  rw [centredGeneratingPolynomial_coeff_two t η hη, norm_div, norm_neg]
  norm_num
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
  calc
    ‖∑ j ∈ t, (η j) ^ 2‖ ≤ ∑ j ∈ t, ‖(η j) ^ 2‖ := norm_sum_le _ _
    _ = ∑ j ∈ t, ‖η j‖ ^ 2 := by simp only [norm_pow]
    _ ≤ (t.card : ℝ) * V := hV

theorem centredGeneratingPolynomial_natDegree_le {ι : Type*}
    (t : Finset ι) (η : ι → ℂ) : (centredGeneratingPolynomial t η).natDegree ≤ t.card := by
  have hdeg (j : ι) (hj : j ∈ t) : (1 + C (η j) * X : Polynomial ℂ).natDegree ≤ 1 := by
    apply Polynomial.natDegree_add_le_of_degree_le
    · simp
    · exact (Polynomial.natDegree_mul_le).trans (by simp)
  unfold centredGeneratingPolynomial
  calc
    (∏ j ∈ t, (1 + C (η j) * X)).natDegree ≤
        ∑ j ∈ t, (1 + C (η j) * X : Polynomial ℂ).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _j ∈ t, 1 := Finset.sum_le_sum hdeg
    _ = t.card := by simp

theorem centredGeneratingPolynomial_homogeneous_eval {ι : Type*}
    (t : Finset ι) (η : ι → ℂ) (d z : ℂ) :
    (∏ j ∈ t, (d + z * η j)) =
      ∑ k ∈ Finset.range (t.card + 1),
        (centredGeneratingPolynomial t η).coeff k * d ^ (t.card - k) * z ^ k := by
  classical
  by_cases hd : d = 0
  · subst d
    rw [Finset.sum_eq_single t.card]
    · simp [centredGeneratingPolynomial_coeff_card, Finset.prod_mul_distrib, mul_comm]
    · intro k hk hkm
      have hklt : k < t.card := by have := Finset.mem_range.mp hk; omega
      simp [Nat.sub_ne_zero_of_lt hklt]
    · simp
  have hdeg : (centredGeneratingPolynomial t η).natDegree < t.card + 1 :=
    Nat.lt_succ_of_le (centredGeneratingPolynomial_natDegree_le t η)
  have heval := Polynomial.eval_eq_sum_range' hdeg (z / d)
  have hfactor : (∏ j ∈ t, (d + z * η j)) = d ^ t.card *
      (centredGeneratingPolynomial t η).eval (z / d) := by
    rw [centredGeneratingPolynomial_eval, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j hj
    field_simp
  rw [hfactor, heval, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkm : k ≤ t.card := by have := Finset.mem_range.mp hk; omega
  have hpow : d ^ t.card = d ^ (t.card - k) * d ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hkm]
  rw [hpow, div_pow]
  field_simp

end Schmeisser

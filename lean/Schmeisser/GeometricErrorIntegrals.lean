import Schmeisser.CoefficientErrorIntegrals
import Schmeisser.NormalizedCoefficients
import Schmeisser.FiniteGeometricTail

open scoped BigOperators
open MeasureTheory Set

namespace Schmeisser

noncomputable def normalizedCauchyCoefficient (m k : ℕ) : ℝ :=
  Real.sqrt ((m : ℝ) ^ m /
    ((k : ℝ) ^ k * ((m - k : ℕ) : ℝ) ^ (m - k))) / (m.choose k : ℝ)

theorem normalized_coefficient_term_le {a c u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (k : ℕ) (hk : 2 ≤ k)
    (ha : a ≤ c * (u * (1 - u)) ^ ((k : ℝ) / 2)) :
    a / (u ^ (k + 1) * (1 - u)) ≤
      c / u ^ 2 * (Real.sqrt ((1 - u) / u)) ^ (k - 2) := by
  let z := Real.sqrt ((1 - u) / u)
  have heps : 0 < 1 - u := by linarith
  have hz : 0 ≤ z := Real.sqrt_nonneg _
  have hzsq : z ^ 2 = (1 - u) / u := Real.sq_sqrt (by positivity)
  have hscale : (u * z) ^ 2 = u * (1 - u) := by
    rw [mul_pow, hzsq]
    field_simp
  have hsqrt : Real.sqrt (u * (1 - u)) = u * z := by
    nlinarith [Real.sq_sqrt (show 0 ≤ u * (1 - u) by positivity),
      Real.sqrt_nonneg (u * (1 - u)), mul_nonneg hu0.le hz]
  have hp : (u * (1 - u)) ^ ((k : ℝ) / 2) = (u * z) ^ k := by
    rw [Real.rpow_div_two_eq_sqrt _ (by positivity), hsqrt, Real.rpow_natCast]
  rw [hp] at ha
  have h := div_le_div_of_nonneg_right ha
    (show 0 ≤ u ^ (k + 1) * (1 - u) by positivity)
  have hzpow : z ^ k = z ^ 2 * z ^ (k - 2) := by
    rw [← pow_add, Nat.add_sub_of_le hk]
  have heq : c * (u * z) ^ k / (u ^ (k + 1) * (1 - u)) =
      c / u ^ 2 * z ^ (k - 2) := by
    rw [mul_pow, hzpow, hzsq, pow_succ]
    field_simp
  exact h.trans_eq heq

theorem normalized_centered_error_le {ι : Type*}
    (jset : Finset ι) (η : ι → ℂ) (m : ℕ) (hm : 1 ≤ m) (hcard : jset.card = m)
    (hη : ∑ j ∈ jset, η j = 0) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (c : ℕ → ℝ)
    (hc : ∀ k ∈ Finset.Ico 2 (m + 1),
      ‖(centredGeneratingPolynomial jset η).coeff k‖ / (m.choose k : ℝ) ≤
        c k * (u * (1 - u)) ^ ((k : ℝ) / 2)) :
    centeredErrorIntegral jset η m u / (1 - u) ≤
      (∑ k ∈ Finset.Ico 2 (m + 1),
        c k * (Real.sqrt ((1 - u) / u)) ^ (k - 2)) / u ^ 2 := by
  have heps : 0 < 1 - u := by linarith
  have hsum := div_le_div_of_nonneg_right
    (centeredErrorIntegral_le_coefficient_sum jset η m hm hcard hη hu0 hu1.le) heps.le
  rw [Finset.sum_div] at hsum
  refine hsum.trans ?_
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro k hk
  have h := normalized_coefficient_term_le hu0 hu1 k (Finset.mem_Ico.mp hk).1 (hc k hk)
  convert h using 1
  · simp only [div_div, mul_assoc]
  · ring

theorem centeredErrorIntegral_geometric_cauchy {ι : Type*}
    (jset : Finset ι) (η : ι → ℂ) (m : ℕ) (hm : 11 ≤ m) (hcard : jset.card = m)
    (hη : ∑ j ∈ jset, η j = 0) {u : ℝ} (hu0 : 1 / 2 < u) (hu1 : u < 1)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (m : ℝ) * (u * (1 - u))) :
    centeredErrorIntegral jset η m u / (1 - u) ≤
      (1 / ((m : ℝ) - 1) +
        (∑ k ∈ Finset.Ico 3 11, normalizedCauchyCoefficient m k *
          (Real.sqrt ((1 - u) / u)) ^ (k - 2)) +
        (Real.sqrt ((1 - u) / u)) ^ 9 / (1 - Real.sqrt ((1 - u) / u))) / u ^ 2 := by
  classical
  have hu : 0 < u := by linarith
  have heps : 0 < 1 - u := by linarith
  have hvar : 0 < u * (1 - u) := mul_pos hu heps
  let z := Real.sqrt ((1 - u) / u)
  have hz : 0 ≤ z := Real.sqrt_nonneg _
  have hz1 : z < 1 := by
    have hzsq : z ^ 2 = (1 - u) / u := Real.sq_sqrt (by positivity)
    have hr : (1 - u) / u < 1 := (div_lt_one hu).mpr (by linarith)
    nlinarith
  let c : ℕ → ℝ := fun k =>
    if k = 2 then 1 / ((m : ℝ) - 1)
    else if k < 11 then normalizedCauchyCoefficient m k else 1
  have hc : ∀ k ∈ Finset.Ico 2 (m + 1),
      ‖(centredGeneratingPolynomial jset η).coeff k‖ / (m.choose k : ℝ) ≤
        c k * (u * (1 - u)) ^ ((k : ℝ) / 2) := by
    intro k hk
    have hk0 : 2 ≤ k := (Finset.mem_Ico.mp hk).1
    have hkm : k ≤ m := by have := (Finset.mem_Ico.mp hk).2; omega
    by_cases hk2 : k = 2
    · subst k
      have h := coeff_two_norm_div_choose_bound jset η (u * (1 - u)) (by omega)
        hη (by simpa only [hcard] using hV)
      simpa [c, hcard, div_eq_mul_inv, mul_comm] using h
    by_cases hk11 : k < 11
    · have h := centredGeneratingPolynomial_coeff_cauchy jset η (u * (1 - u)) hvar hη
        (by simpa only [hcard] using hV) k (by omega) (by omega)
      rw [hcard] at h
      have hd : (0 : ℝ) ≤ m.choose k := by positivity
      have hdv := div_le_div_of_nonneg_right h hd
      simpa [c, hk2, hk11, normalizedCauchyCoefficient, div_mul_eq_mul_div] using hdv
    · have h := coeff_norm_div_choose_bound jset η (u * (1 - u)) hvar.le hη
        (by simpa only [hcard] using hV) k (by omega)
      simpa [c, hk2, hk11, hcard] using h
  have hmain := normalized_centered_error_le jset η m (by omega) hcard hη hu hu1 c hc
  have hsplit : (∑ k ∈ Finset.Ico 2 (m + 1), c k * z ^ (k - 2)) =
      1 / ((m : ℝ) - 1) +
        (∑ k ∈ Finset.Ico 3 11, normalizedCauchyCoefficient m k * z ^ (k - 2)) +
        ∑ k ∈ Finset.Ico 11 (m + 1), z ^ (k - 2) := by
    rw [← Finset.sum_Ico_consecutive _ (by omega : 2 ≤ 3) (by omega : 3 ≤ m + 1)]
    rw [← Finset.sum_Ico_consecutive _ (by omega : 3 ≤ 11) (by omega : 11 ≤ m + 1)]
    have hfirst : (∑ k ∈ Finset.Ico 2 3, c k * z ^ (k - 2)) = 1 / ((m : ℝ) - 1) := by
      norm_num [c]
    have hmiddle : (∑ k ∈ Finset.Ico 3 11, c k * z ^ (k - 2)) =
        ∑ k ∈ Finset.Ico 3 11, normalizedCauchyCoefficient m k * z ^ (k - 2) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkk := Finset.mem_Ico.mp hk
      simp [c, show k ≠ 2 by omega, hkk.2]
    have hlast : (∑ k ∈ Finset.Ico 11 (m + 1), c k * z ^ (k - 2)) =
        ∑ k ∈ Finset.Ico 11 (m + 1), z ^ (k - 2) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkk := Finset.mem_Ico.mp hk
      simp [c, show k ≠ 2 by omega, show ¬k < 11 by omega]
    rw [hfirst, hmiddle, hlast]
    ring
  change centeredErrorIntegral jset η m u / (1 - u) ≤
    (∑ k ∈ Finset.Ico 2 (m + 1), c k * z ^ (k - 2)) / u ^ 2 at hmain
  rw [hsplit] at hmain
  refine hmain.trans (div_le_div_of_nonneg_right ?_ (sq_nonneg u))
  have htail := finite_geometric_tail_bound 11 m 2 (by norm_num) hz hz1
  simpa only [z] using add_le_add
    (le_refl (1 / ((m : ℝ) - 1) +
      ∑ k ∈ Finset.Ico 3 11, normalizedCauchyCoefficient m k * z ^ (k - 2))) htail

end Schmeisser

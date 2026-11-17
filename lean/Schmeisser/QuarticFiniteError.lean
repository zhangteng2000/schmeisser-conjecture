import Schmeisser.FiniteCoefficientError
import Schmeisser.QuarticEndpoint

namespace Schmeisser

theorem quartic_finite_error_bound {ι : Type*} (jset : Finset ι) (η : ι → ℂ)
    (hcard : jset.card = 3) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (hη : ∑ j ∈ jset, η j = 0)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (3 : ℝ) * (u * (1 - u))) :
    centeredErrorIntegral jset η 3 u / (1 - u) ≤
      u / 2 * (1 + 3 * (1 - u)) + u * Real.sqrt (1 - u) := by
  classical
  have heps : 0 < 1 - u := sub_pos.mpr hu1
  let V := u * (1 - u)
  have hV0 : 0 ≤ V := by dsimp [V]; positivity
  have hv : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (jset.card : ℝ) * V := by
    simpa only [hcard, Nat.cast_ofNat, V] using hV
  have h2 := centredGeneratingPolynomial_coeff_two_bound jset η V hη hv
  have h3 := centredGeneratingPolynomial_coeff_card_bound jset η V hV0 hv
  rw [hcard] at h2 h3
  norm_num only [Nat.cast_ofNat] at h2 h3
  have hVs : Real.sqrt V ≤ Real.sqrt (1 - u) := by
    apply Real.sqrt_le_sqrt
    dsimp [V]
    nlinarith
  rw [rpow_three_halves_eq_mul_sqrt hV0] at h3
  have h3' : ‖(centredGeneratingPolynomial jset η).coeff 3‖ ≤ V * Real.sqrt (1 - u) :=
    h3.trans (mul_le_mul_of_nonneg_left hVs hV0)
  have hE := centeredErrorIntegral_le_finite_coefficient_sum jset η 3 (by norm_num)
    hcard hη hu0 hu1.le
  have hset : Finset.Ico 2 (3 + 1) = ({2, 3} : Finset ℕ) := by decide
  rw [hset] at hE
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.choose,
    finiteBetaPolynomial, Finset.sum_range_succ] at hE
  have he2 : ‖(centredGeneratingPolynomial jset η).coeff 2‖ / 3 *
      (1 + 3 * (1 - u)) ≤ (3 * V / 2) / 3 * (1 + 3 * (1 - u)) :=
    mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right h2 (by norm_num : (0 : ℝ) ≤ 3)) (by positivity)
  have hsum := hE.trans (add_le_add he2 h3')
  apply (div_le_iff₀ heps).mpr
  convert hsum using 1
  dsimp [V]
  ring

end Schmeisser

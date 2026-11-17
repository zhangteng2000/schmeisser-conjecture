import Schmeisser.FiniteCoefficientError
import Schmeisser.NewtonCoefficients
import Schmeisser.QuarticEndpoint

namespace Schmeisser

theorem quintic_newton_coefficient_three :
    newtonMajorant 4 3 = (4 / 3 : ℝ) * Real.sqrt 3 := by
  rw [newtonMajorant_recurrence 4 1]
  norm_num [Finset.sum_range_succ, newtonMajorant, ← Real.sqrt_eq_rpow]

theorem quintic_finite_error_bound {ι : Type*} (jset : Finset ι) (η : ι → ℂ)
    (hcard : jset.card = 4) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (hη : ∑ j ∈ jset, η j = 0)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (4 : ℝ) * (u * (1 - u))) :
    centeredErrorIntegral jset η 4 u / (1 - u) ≤
      10 * u / 3 - 4 * u ^ 2 + u ^ 3 +
        (Real.sqrt 3 / 3) * (5 - 4 * u) * u ^ (3 / 2 : ℝ) * Real.sqrt (1 - u) := by
  classical
  let V := u * (1 - u)
  have hV0 : 0 ≤ V := by dsimp [V]; positivity
  have hv : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (jset.card : ℝ) * V := by
    simpa only [hcard, Nat.cast_ofNat, V] using hV
  have h2 := centredGeneratingPolynomial_coeff_two_bound jset η V hη hv
  have h3 := coeff_norm_le_newtonMajorant jset η V (by omega) hV0 hη hv 3
  have h4 := centredGeneratingPolynomial_coeff_card_bound jset η V hV0 hv
  rw [hcard] at h2 h3 h4
  rw [quintic_newton_coefficient_three] at h3
  norm_num only [Nat.cast_ofNat] at h2 h3 h4
  let c : ℕ → ℝ := fun k => if k = 2 then 2 else if k = 3 then (4 / 3) * Real.sqrt 3 else 1
  have hc (k : ℕ) (hk : k ∈ Finset.Ico 2 (4 + 1)) :
      ‖(centredGeneratingPolynomial jset η).coeff k‖ ≤
        c k * (u * (1 - u)) ^ ((k : ℝ) / 2) := by
    have hk' : k = 2 ∨ k = 3 ∨ k = 4 := by
      have := Finset.mem_Ico.mp hk
      omega
    rcases hk' with rfl | rfl | rfl
    · have h2' : ‖(centredGeneratingPolynomial jset η).coeff 2‖ ≤ 2 * V := by
        linarith [h2]
      simpa [c, V] using h2'
    · simpa [c, V] using h3
    · convert h4 using 1
      norm_num [c, V, Real.rpow_two]
  have hE := centeredErrorIntegral_finite_bound jset η 4 (by norm_num)
    hcard hη hu0 hu1 c hc
  have hset : Finset.Ico 2 (4 + 1) = ({2, 3, 4} : Finset ℕ) := by decide
  rw [hset] at hE
  norm_num [c, Finset.sum_insert, Finset.sum_singleton, Nat.choose,
    finiteBetaPolynomial, Finset.sum_range_succ, ← Real.sqrt_eq_rpow] at hE
  convert hE using 1
  ring

theorem quintic_finite_error_bound_sqrt {ι : Type*} (jset : Finset ι) (η : ι → ℂ)
    (hcard : jset.card = 4) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (hη : ∑ j ∈ jset, η j = 0)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (4 : ℝ) * (u * (1 - u))) :
    centeredErrorIntegral jset η 4 u / (1 - u) ≤
      10 * u / 3 - 4 * u ^ 2 + u ^ 3 +
        (Real.sqrt 3 / 3) * (5 - 4 * u) * u * Real.sqrt u * Real.sqrt (1 - u) := by
  have h := quintic_finite_error_bound jset η hcard hu0 hu1 hη hV
  rw [rpow_three_halves_eq_mul_sqrt hu0.le] at h
  simpa only [mul_assoc] using h

end Schmeisser

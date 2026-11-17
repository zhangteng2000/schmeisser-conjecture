import Schmeisser.FiniteCoefficientError
import Schmeisser.NewtonCoefficients
import Schmeisser.QuarticEndpoint

namespace Schmeisser

theorem rpow_five_halves_eq_mul_sqrt {x : ℝ} (hx : 0 ≤ x) :
    x ^ (5 / 2 : ℝ) = x ^ 2 * Real.sqrt x := by
  rw [show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num,
    Real.rpow_add_of_nonneg hx (by norm_num) (by norm_num), Real.rpow_two,
    ← Real.sqrt_eq_rpow]

theorem sextic_newton_coefficient_three : newtonMajorant 5 3 = (10 / 3 : ℝ) := by
  rw [newtonMajorant_recurrence 5 1]
  norm_num [Finset.sum_range_succ, newtonMajorant, ← Real.sqrt_eq_rpow]

noncomputable def sexticErrorBound (u : ℝ) : ℝ :=
  let e := 1 - u
  u / 4 * (1 + 3 * e + 6 * e ^ 2 + 10 * e ^ 3) +
    (7 / 10 : ℝ) * u ^ 2 * e * (1 + 5 * e) +
    Real.sqrt e * ((1 + u) / 2) *
      (u / 3 * (1 + 4 * e + 10 * e ^ 2) + u ^ 2 * e)

theorem sextic_finite_error_bound {ι : Type*} (jset : Finset ι) (η : ι → ℂ)
    (hcard : jset.card = 5) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (hη : ∑ j ∈ jset, η j = 0)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (5 : ℝ) * (u * (1 - u))) :
    centeredErrorIntegral jset η 5 u / (1 - u) ≤ sexticErrorBound u := by
  classical
  let V := u * (1 - u)
  have heps : 0 < 1 - u := by linarith
  have hVpos : 0 < V := by dsimp [V]; positivity
  have hv : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (jset.card : ℝ) * V := by
    simpa only [hcard, Nat.cast_ofNat, V] using hV
  have h2 := centredGeneratingPolynomial_coeff_two_bound jset η V hη hv
  have h3 := coeff_norm_le_newtonMajorant jset η V (by omega) hVpos.le hη hv 3
  have h4 := centredGeneratingPolynomial_coeff_cauchy jset η V hVpos hη hv 4 (by norm_num) (by omega)
  have h5 := centredGeneratingPolynomial_coeff_card_bound jset η V hVpos.le hv
  rw [hcard] at h2 h3 h4 h5
  rw [sextic_newton_coefficient_three] at h3
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, show (4 : ℝ) / 2 = 2 by norm_num,
    Real.rpow_two] at h2 h3 h4 h5
  have hroot : Real.sqrt ((3125 : ℝ) / 256) ≤ 7 / 2 := by
    apply (Real.sqrt_le_iff).2
    norm_num
  have h4' : ‖(centredGeneratingPolynomial jset η).coeff 4‖ ≤ (7 / 2 : ℝ) * V ^ 2 :=
    h4.trans (mul_le_mul_of_nonneg_right hroot (sq_nonneg V))
  let c : ℕ → ℝ := fun k => if k = 2 then 5 / 2 else if k = 3 then 10 / 3
    else if k = 4 then 7 / 2 else 1
  have hc (k : ℕ) (hk : k ∈ Finset.Ico 2 (5 + 1)) :
      ‖(centredGeneratingPolynomial jset η).coeff k‖ ≤
        c k * (u * (1 - u)) ^ ((k : ℝ) / 2) := by
    have hk' : k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by
      have := Finset.mem_Ico.mp hk
      omega
    rcases hk' with rfl | rfl | rfl | rfl
    · have h2' : ‖(centredGeneratingPolynomial jset η).coeff 2‖ ≤ (5 / 2 : ℝ) * V := by
        linarith
      simpa [c, V] using h2'
    · simpa [c, V] using h3
    · convert h4' using 1
      norm_num [c, V, Real.rpow_two]
    · simpa [c, V] using h5
  have hE := centeredErrorIntegral_finite_bound jset η 5 (by norm_num)
    hcard hη hu0 hu1 c hc
  have hset : Finset.Ico 2 (5 + 1) = ({2, 3, 4, 5} : Finset ℕ) := by decide
  rw [hset] at hE
  norm_num [c, Finset.sum_insert, Finset.sum_singleton, Nat.choose,
    finiteBetaPolynomial, Finset.sum_range_succ, ← Real.sqrt_eq_rpow] at hE
  rw [rpow_three_halves_eq_mul_sqrt hu0.le, rpow_five_halves_eq_mul_sqrt hu0.le,
    rpow_three_halves_eq_mul_sqrt heps.le] at hE
  have hE' : centeredErrorIntegral jset η 5 u / (1 - u) ≤
      u / 4 * (1 + 3 * (1 - u) + 6 * (1 - u) ^ 2 + 10 * (1 - u) ^ 3) +
        (7 / 10 : ℝ) * u ^ 2 * (1 - u) * (1 + 5 * (1 - u)) +
        Real.sqrt (1 - u) * Real.sqrt u *
          (u / 3 * (1 + 4 * (1 - u) + 10 * (1 - u) ^ 2) + u ^ 2 * (1 - u)) := by
    convert hE using 1
    ring
  have hs : Real.sqrt u ≤ (1 + u) / 2 := by
    nlinarith [Real.sq_sqrt hu0.le, sq_nonneg (Real.sqrt u - 1)]
  have hb : 0 ≤ u / 3 * (1 + 4 * (1 - u) + 10 * (1 - u) ^ 2) + u ^ 2 * (1 - u) := by
    positivity
  unfold sexticErrorBound
  refine hE'.trans (add_le_add le_rfl ?_)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg _)) hb

end Schmeisser

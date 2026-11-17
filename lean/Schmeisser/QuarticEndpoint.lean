import Schmeisser.PolarCertification
import Schmeisser.ComparisonParameters
import Schmeisser.CoefficientErrorIntegrals
import Schmeisser.QuadraticTrapezoid

noncomputable section

namespace Schmeisser

open Set MeasureTheory

theorem quartic_drop_parameters {u : ℝ} (hu : 99 / 100 ≤ u) (hu1 : u < 1) :
    0 < comparisonDrop u 3 ∧ comparisonDrop u 3 ≤ 1 / 33 ∧ (3 : ℝ) / u < 4 := by
  have hu0 : 0 < u := by linarith
  unfold comparisonDrop
  refine ⟨by positivity, ?_, ?_⟩
  · apply (div_le_iff₀ hu0).mpr
    linarith
  · apply (div_lt_iff₀ hu0).mpr
    linarith

theorem quartic_polar_test {u : ℝ} (hu : 99 / 100 ≤ u) (hu1 : u < 1) :
    (∫ t in (0 : ℝ)..1,
      (1 - comparisonDrop u 3 + comparisonDrop u 3 * (1 + u) * t) ^ (3 / 2 : ℝ)) < 1 := by
  have hu0 : 0 < u := by linarith
  let H := comparisonDrop u 3
  have hpar := quartic_drop_parameters hu hu1
  have hH0 : 0 < H := hpar.1
  have hH1 : H ≤ 1 := hpar.2.1.trans (by norm_num)
  have hbound := polar_cubic_quadratic_bound hu0.le hH0.le hH1
  have hrel : H * u = 3 * (1 - u) := by dsimp [H, comparisonDrop]; field_simp
  have hsmall : H < (9 / 2 : ℝ) * (1 - u) := by
    have hh : 0 < ((9 / 2 : ℝ) * u - 3) * (1 - u) :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  have hpoly : u ^ 2 - u + 1 ≤ 1 := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hpoly (sq_nonneg H)
  have hstrict := mul_lt_mul_of_pos_left hsmall hH0
  linarith

theorem quartic_theta_lower {u : ℝ} (hu : 99 / 100 ≤ u) (hu1 : u < 1) :
    (37 / 25 : ℝ) < comparisonTheta u 3 / (1 - u) := by
  have hu0 : 0 < u := by linarith
  have heps : 0 < 1 - u := by linarith
  have hden : 0 < 2 * (u ^ 2 + 3 * (1 - u)) := by positivity
  have he : comparisonTheta u 3 / (1 - u) = 3 / (2 * (u ^ 2 + 3 * (1 - u))) := by
    unfold comparisonTheta comparisonD comparisonDrop
    field_simp
  rw [he]
  apply (lt_div_iff₀ hden).mpr
  have hs : (1 - u) ^ 2 ≤ (1 / 100 : ℝ) ^ 2 := by nlinarith
  nlinarith

theorem rpow_three_halves_eq_mul_sqrt {x : ℝ} (hx : 0 ≤ x) :
    x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
    Real.rpow_add_of_nonneg hx (by norm_num) (by norm_num), Real.rpow_one,
    ← Real.sqrt_eq_rpow]

theorem quartic_comparison_bound_of_one {u : ℝ} (hu : 99 / 100 ≤ u) (hu1 : u < 1)
    (hR1 : comparisonIntegral 1 u 3 ≤ 1 + Real.sqrt (1 - u)) :
    comparisonIntegral 3 u 3 < 1 + (7 / 40 : ℝ) * (1 - u) := by
  have hu0 : 0 < u := by linarith
  have heps : 0 < 1 - u := by linarith
  have hκ := (quartic_drop_parameters hu hu1).2.2
  have hmin := comparisonMinimum_bounds hu0 hu1.le (by norm_num : (0 : ℝ) ≤ 3) hκ.le
  have hs0 := Real.sqrt_nonneg (1 - u)
  have hs2 := Real.sq_sqrt heps.le
  have hs : Real.sqrt (1 - u) ≤ 1 / 10 := by nlinarith
  have hp : (1 - u) ^ (3 / 2 : ℝ) ≤ 1 / 1000 := by
    rw [rpow_three_halves_eq_mul_sqrt heps.le]
    have hh := mul_le_mul_of_nonneg_left hs heps.le
    nlinarith
  have htheta := quartic_theta_lower hu hu1
  have hthetamul : (37 / 25 : ℝ) * (1 - u) < comparisonTheta u 3 :=
    (lt_div_iff₀ heps).mp htheta
  have hθ0 : 0 ≤ comparisonTheta u 3 := by
    unfold comparisonTheta comparisonD comparisonDrop
    positivity
  have hcorrection : (3 / 2 : ℝ) * comparisonMinimum u 3 * comparisonIntegral 1 u 3 ≤
      (3 / 2 : ℝ) * (1 - u) * (1 + 1 / 10) := by
    have h1 := mul_le_mul_of_nonneg_left hR1
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2) hmin.1)
    have h2 := mul_le_mul_of_nonneg_left hs
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2) hmin.1)
    have h3 := mul_le_mul_of_nonneg_right hmin.2 (by norm_num : (0 : ℝ) ≤ (3 / 2) * (1 + 1 / 10))
    nlinarith
  have hnegative : comparisonTheta u 3 * (1 - (1 - u) ^ (3 / 2 : ℝ)) >
      (37 / 25 : ℝ) * (1 - u) * (1 - 1 / 1000) := by
    have h1 := mul_le_mul_of_nonneg_left (show 1 - 1 / 1000 ≤ 1 - (1 - u) ^ (3 / 2 : ℝ) by linarith) hθ0
    have h2 := mul_lt_mul_of_pos_right hthetamul (by norm_num : (0 : ℝ) < 1 - 1 / 1000)
    nlinarith
  have hrec := comparisonIntegral_recurrence 3 (by norm_num) hu0 hu1.le
    (by norm_num : (0 : ℝ) ≤ 3) hκ.le
  norm_num at hrec
  nlinarith

theorem quartic_error_bound {ι : Type*} (jset : Finset ι) (η : ι → ℂ)
    (hcard : jset.card = 3) {u : ℝ} (hu : 99 / 100 ≤ u) (hu1 : u < 1)
    (hη : ∑ j ∈ jset, η j = 0)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (3 : ℝ) * (u * (1 - u))) :
    centeredErrorIntegral jset η 3 u / (1 - u) ≤ 123 / 200 := by
  classical
  have hu0 : 0 < u := by linarith
  have heps : 0 < 1 - u := by linarith
  let V := u * (1 - u)
  have hV0 : 0 ≤ V := by dsimp [V]; positivity
  have hv : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (jset.card : ℝ) * V := by simpa [hcard, V] using hV
  have h2 := centredGeneratingPolynomial_coeff_two_bound jset η V hη hv
  have h3 := centredGeneratingPolynomial_coeff_card_bound jset η V hV0 hv
  rw [hcard] at h2 h3
  norm_num only [Nat.cast_ofNat] at h2 h3
  have hs : Real.sqrt (1 - u) ≤ 1 / 10 := by
    nlinarith [Real.sq_sqrt heps.le, Real.sqrt_nonneg (1 - u)]
  have hVs : Real.sqrt V ≤ Real.sqrt (1 - u) := by
    apply Real.sqrt_le_sqrt
    dsimp [V]
    nlinarith
  rw [rpow_three_halves_eq_mul_sqrt hV0] at h3
  have h3' : ‖(centredGeneratingPolynomial jset η).coeff 3‖ ≤ V * Real.sqrt (1 - u) :=
    h3.trans (mul_le_mul_of_nonneg_left hVs hV0)
  have hE := centeredErrorIntegral_le_coefficient_sum jset η 3 (by norm_num) hcard hη hu0 hu1.le
  have hset : Finset.Ico 2 (3 + 1) = ({2, 3} : Finset ℕ) := by decide
  rw [hset] at hE
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.choose] at hE
  have he2 := div_le_div_of_nonneg_right h2 (show 0 ≤ (3 : ℝ) * u ^ 3 by positivity)
  have he3 := div_le_div_of_nonneg_right h3' (show 0 ≤ u ^ 4 by positivity)
  have heq : (3 * V / 2) / (3 * u ^ 3) + (V * Real.sqrt (1 - u)) / u ^ 4 =
      (1 - u) * (1 / (2 * u ^ 2) + Real.sqrt (1 - u) / u ^ 3) := by
    dsimp [V]
    field_simp
    <;> ring
  have hnorm : centeredErrorIntegral jset η 3 u / (1 - u) ≤
      1 / (2 * u ^ 2) + Real.sqrt (1 - u) / u ^ 3 := by
    apply (div_le_iff₀ heps).mpr
    rw [mul_comm, ← heq]
    exact hE.trans (add_le_add he2 he3)
  have hu2 : (99 / 100 : ℝ) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ (by norm_num) hu 2
  have hu3 : (99 / 100 : ℝ) ^ 3 ≤ u ^ 3 := pow_le_pow_left₀ (by norm_num) hu 3
  have hterm2 : 1 / (2 * u ^ 2) ≤ 1 / (2 * (99 / 100 : ℝ) ^ 2) :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hterm3 : Real.sqrt (1 - u) / u ^ 3 ≤ (1 / 10 : ℝ) / (99 / 100 : ℝ) ^ 3 :=
    div_le_div₀ (by norm_num) hs (by norm_num) hu3
  refine hnorm.trans ((add_le_add hterm2 hterm3).trans ?_)
  norm_num

theorem quartic_endpoint_scalar_exclusion {ι : Type*} (jset : Finset ι) (η : ι → ℂ)
    (hcard : jset.card = 3) {u h : ℝ} (hu : 99 / 100 ≤ u) (hu1 : u < 1)
    (hh0 : 0 < h)
    (hη : ∑ j ∈ jset, η j = 0)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (3 : ℝ) * (u * (1 - u)))
    (hpolar : 1 ≤ ∫ t in (0 : ℝ)..1, (1 - h + h * (1 + u) * t) ^ (3 / 2 : ℝ)) :
    (4 : ℝ) * (∫ t in (0 : ℝ)..1,
      (max (1 - 2 * u * t + u * t ^ 2 - h * t * (1 - t)) 0) ^ (3 / 2 : ℝ)) <
      ((4 : ℝ) * ∫ t in (0 : ℝ)..1, (1 - u * t) ^ 3) -
        centeredErrorIntegral jset η 3 u := by
  have hu0 : 0 < u := by linarith
  have heps : 0 < 1 - u := by linarith
  obtain ⟨hH0, hH1, hκ⟩ := quartic_drop_parameters hu hu1
  have hdrop := polar_certification hu0.le hh0 hH0 (hH1.trans (by norm_num))
    (by norm_num : (1 : ℝ) ≤ 3 / 2) hpolar (quartic_polar_test hu hu1)
  have hR1 := comparisonIntegral_one_le_endpoints hu0 hu1.le (by norm_num : (0 : ℝ) ≤ 3) hκ.le
  have hR3 := quartic_comparison_bound_of_one hu hu1 hR1
  have hE := quartic_error_bound jset η hcard hu hu1 hη hV
  have hEn := (div_le_iff₀ heps).mp hE
  have hbase : (4 : ℝ) * (∫ t in (0 : ℝ)..1, (1 - u * t) ^ 3) ≥ 1 + (1 - u) := by
    have he := baseline_integral_eq 3 hu0.ne'
    norm_num only [Nat.cast_ofNat, Nat.reduceAdd] at he
    have hgeom : (1 - (1 - u) ^ 4) / u = 1 + (1 - u) + (1 - u) ^ 2 + (1 - u) ^ 3 := by
      field_simp
      ring
    rw [he, hgeom]
    nlinarith [sq_nonneg (1 - u), pow_nonneg heps.le 3]
  have hstrict : comparisonIntegral 3 u 3 <
      ((4 : ℝ) * ∫ t in (0 : ℝ)..1, (1 - u * t) ^ 3) - centeredErrorIntegral jset η 3 u := by
    linarith
  have hQ := second_integral_le_comparison 3 hu0 hu1.le (by norm_num : (0 : ℝ) ≤ 3) hκ.le hdrop.le
  norm_num only [Nat.cast_ofNat, Nat.reduceAdd] at hQ
  exact hQ.trans_lt hstrict

end Schmeisser

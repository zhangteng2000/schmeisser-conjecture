import Schmeisser.SepticFiniteError
import Schmeisser.SexticAnalytic
import Schmeisser.Certificates.Count6PolynomialBounds

/-! An analytic exclusion for critical-point count six. -/

noncomputable section

namespace Schmeisser

open Set MeasureTheory

theorem septic_parameter_gt_seventeen_twenty_ninths {u h : ℝ}
    (hu : 0 ≤ u) (hh0 : 0 < h) (hh1 : h ≤ 1)
    (hpolar : 1 ≤ ∫ t in (0 : ℝ)..1, (1 - h + h * (1 + u) * t) ^ (3 : ℝ)) :
    17 / 29 < u := by
  have hp := polar_integral_power_threshold hu hh0 hh1 (by norm_num : (1 : ℝ) ≤ 3) hpolar
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hp
  norm_num only [Nat.cast_ofNat] at hp
  by_contra hn
  have hupp : u ≤ 17 / 29 := le_of_not_gt hn
  have hc := pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 + u by linarith)
    (show 1 + u ≤ 46 / 29 by linarith) 3
  norm_num at hc
  linarith

theorem septic_drop_parameters {u : ℝ} (hu : 17 / 29 ≤ u) (hu1 : u < 1) :
    0 < comparisonDrop u (17 / 12) ∧ comparisonDrop u (17 / 12) ≤ 1 ∧
      (17 / 12 : ℝ) / u ≤ 4 := by
  have hu0 : 0 < u := by linarith
  unfold comparisonDrop
  refine ⟨by positivity, ?_, ?_⟩
  · apply (div_le_one hu0).2
    linarith
  · apply (div_le_iff₀ hu0).2
    linarith

theorem septic_polar_integral_eq (u h : ℝ) :
    (∫ t in (0 : ℝ)..1, (1 - h + h * (1 + u) * t) ^ (3 : ℝ)) =
      1 - (3 / 2 : ℝ) * h * (1 - u) + h ^ 2 * (u ^ 2 - u + 1) -
        h ^ 3 * (1 - u) * (u ^ 2 + 1) / 4 := by
  simp_rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  calc
    _ = ∫ t in (0 : ℝ)..1, h ^ 3 * (1 + u) ^ 3 * t ^ 3 +
        (3 * h ^ 2 * (1 + u) ^ 2 * (1 - h) * t ^ 2 +
          3 * h * (1 + u) * (1 - h) ^ 2 * t + (1 - h) ^ 3) := by
      apply intervalIntegral.integral_congr
      intro t _
      ring
    _ = _ := by rw [integral_cubic]; ring

theorem septic_polar_test {u : ℝ} (hu : 17 / 29 ≤ u) (hu1 : u < 1) :
    (∫ t in (0 : ℝ)..1,
      (1 - comparisonDrop u (17 / 12) + comparisonDrop u (17 / 12) * (1 + u) * t) ^ (3 : ℝ)) < 1 := by
  have hu0 : 0 < u := by linarith
  have heps : 0 < 1 - u := by linarith
  rw [septic_polar_integral_eq]
  have he : 1 - (3 / 2 : ℝ) * comparisonDrop u (17 / 12) * (1 - u) +
      comparisonDrop u (17 / 12) ^ 2 * (u ^ 2 - u + 1) -
        comparisonDrop u (17 / 12) ^ 3 * (1 - u) * (u ^ 2 + 1) / 4 - 1 =
      -((1 - u) ^ 2 / u ^ 3) *
        (17 * (17 * u ^ 2 - 42 * u + 17) * (17 * u ^ 2 - 40 * u + 17) / 6912) := by
    unfold comparisonDrop
    field_simp
    ring
  have hq1 : 17 * u ^ 2 - 42 * u + 17 < 0 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hu1.le)]
  have hq2 : 17 * u ^ 2 - 40 * u + 17 < 0 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hu1.le)]
  have hfactor : 0 < 17 * (17 * u ^ 2 - 42 * u + 17) *
      (17 * u ^ 2 - 40 * u + 17) / 6912 := by
    apply div_pos _ (by norm_num)
    exact mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg (by norm_num) hq1) hq2
  have hneg := mul_neg_of_neg_of_pos
    (neg_neg_of_pos (show 0 < (1 - u) ^ 2 / u ^ 3 by positivity)) hfactor
  linarith

theorem septic_normalized_comparison_eq {u : ℝ} (hu : 17 / 29 ≤ u) (hu1 : u < 1) :
    normalizedComparisonIntegral 6 u (17 / 12) =
      -(110592 * u ^ 5 - 369504 * u ^ 4 + 481944 * u ^ 3 -
        294065 * u ^ 2 + 58378 * u - 4913) / (34560 * u ^ 3) := by
  have hu0 : 0 < u := by linarith
  have hκ := (septic_drop_parameters hu hu1).2.2
  have hd := comparisonD_pos hu0 hu1.le (by norm_num : (0 : ℝ) ≤ 17 / 12)
  have hq : 0 < 12 * u ^ 2 + 17 * (1 - u) := by positivity
  have hdval : comparisonD u (17 / 12) = (12 * u ^ 2 + 17 * (1 - u)) / (12 * u) := by
    unfold comparisonD comparisonDrop
    field_simp
  rw [normalizedComparisonIntegral_recurrence 6 (by norm_num) hu0 hu1
    (by norm_num : (0 : ℝ) ≤ 17 / 12) hκ]
  norm_num only [Nat.reduceSub, Nat.cast_ofNat, show (6 : ℝ) / 2 = 3 by norm_num,
    show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [show (1 - u) ^ (3 : ℝ) = (1 - u) ^ (3 : ℕ) from Real.rpow_natCast _ _]
  rw [normalizedComparisonIntegral_recurrence 4 (by norm_num) hu0 hu1
    (by norm_num : (0 : ℝ) ≤ 17 / 12) hκ]
  norm_num only [Nat.reduceSub, Nat.cast_ofNat, show (4 : ℝ) / 2 = 2 by norm_num, Real.rpow_two]
  rw [normalizedComparisonIntegral_two hu0 hu1 (by norm_num : (0 : ℝ) ≤ 17 / 12),
    comparisonMinimum_normalized u (17 / 12) hu0.ne' hd.ne', hdval]
  field_simp (disch := first | positivity | nlinarith [hq])
  ring

theorem septic_gap_identity {u t : ℝ} (hu0 : 0 < u) (ht0 : 0 ≤ t) (ht2 : t ^ 2 = 1 - u)
    (hu : 17 / 29 ≤ u) (hu1 : u < 1) :
    172800 * u ^ 3 * (normalizedComparisonIntegral 6 u (17 / 12) -
      septicErrorBound u - (1 - u) ^ 6 / u) = septicGapPolynomial t := by
  have hs : Real.sqrt (1 - u) = t := by rw [← ht2, Real.sqrt_sq_eq_abs, abs_of_nonneg ht0]
  have hut : u = 1 - t ^ 2 := by linarith
  rw [septic_normalized_comparison_eq hu hu1]
  dsimp only [septicErrorBound]
  rw [hs]
  field_simp [hu0.ne']
  rw [hut]
  unfold septicGapPolynomial
  ring

theorem septic_normalized_comparison_gap {u : ℝ} (hu : 17 / 29 ≤ u) (hu1 : u < 1) :
    septicErrorBound u + (1 - u) ^ 6 / u < normalizedComparisonIntegral 6 u (17 / 12) := by
  have hu0 : 0 < u := by linarith
  have heps : 0 < 1 - u := by linarith
  let t := Real.sqrt (1 - u)
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have ht2 : t ^ 2 = 1 - u := Real.sq_sqrt heps.le
  have ht1 : t < 13 / 20 := by nlinarith
  have hpoly := septicGapPolynomial_pos ht0 ht1
  have hscale : 0 < 172800 * u ^ 3 := by positivity
  have hprod : 0 < 172800 * u ^ 3 * (normalizedComparisonIntegral 6 u (17 / 12) -
      septicErrorBound u - (1 - u) ^ 6 / u) := by
    rw [septic_gap_identity hu0 ht0 ht2 hu hu1]
    exact hpoly
  have hdiff := pos_of_mul_pos_right hprod hscale.le
  linarith

theorem septic_scalar_exclusion {ι : Type*} (jset : Finset ι) (η : ι → ℂ)
    (hcard : jset.card = 6) {u h : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (hh0 : 0 < h) (hh1 : h < 1)
    (hη : ∑ j ∈ jset, η j = 0)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (6 : ℝ) * (u * (1 - u)))
    (hpolar : 1 ≤ ∫ t in (0 : ℝ)..1, (1 - h + h * (1 + u) * t) ^ (3 : ℝ)) :
    (7 : ℝ) * (∫ t in (0 : ℝ)..1,
      (max (1 - 2 * u * t + u * t ^ 2 - h * t * (1 - t)) 0) ^ (3 : ℝ)) <
      ((7 : ℝ) * ∫ t in (0 : ℝ)..1, (1 - u * t) ^ 6) -
        centeredErrorIntegral jset η 6 u := by
  have hu := septic_parameter_gt_seventeen_twenty_ninths hu0.le hh0 hh1.le hpolar
  have hpar := septic_drop_parameters hu.le hu1
  have hdrop := polar_certification hu0.le hh0 hpar.1 hpar.2.1
    (by norm_num : (1 : ℝ) ≤ 3) hpolar (septic_polar_test hu.le hu1)
  have herror := septic_finite_error_bound jset η hcard hu0 hu1 hη hV
  have hgap := septic_normalized_comparison_gap hu.le hu1
  simpa only [Nat.cast_ofNat, show (6 : ℝ) + 1 = 7 by norm_num,
    show (6 : ℝ) / 2 = 3 by norm_num] using
    scalar_exclusion_of_normalized_comparison jset η 6 hu0 hu1
      (by norm_num : (0 : ℝ) ≤ 17 / 12) hpar.2.2 hdrop.le herror hgap

end Schmeisser

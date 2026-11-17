import Schmeisser.QuarticEndpoint
import Schmeisser.FiniteReduction
import Schmeisser.Certificates.Count4PolynomialBounds
import Schmeisser.QuinticFiniteError

/-! A purely analytic exclusion for critical-point count four. The required
polynomial signs follow from exact positive Bernstein expansions. -/

noncomputable section

namespace Schmeisser

open Set MeasureTheory

theorem quintic_parameter_gt_eight_elevenths {u h : ℝ}
    (hu : 0 ≤ u) (hh0 : 0 < h) (hh1 : h ≤ 1)
    (hpolar : 1 ≤ ∫ t in (0 : ℝ)..1, (1 - h + h * (1 + u) * t) ^ (2 : ℝ)) :
    8 / 11 < u := by
  have hp := polar_integral_power_threshold hu hh0 hh1 (by norm_num : (1 : ℝ) ≤ 2) hpolar
  rw [Real.rpow_two] at hp
  by_contra hn
  have hupp : u ≤ 8 / 11 := le_of_not_gt hn
  have hc := pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 + u by linarith)
    (show 1 + u ≤ 19 / 11 by linarith) 2
  norm_num at hc
  linarith

theorem quintic_drop_parameters {u : ℝ} (hu : 8 / 11 ≤ u) (hu1 : u < 1) :
    0 < comparisonDrop u (8 / 3) ∧ comparisonDrop u (8 / 3) ≤ 1 ∧
      (8 / 3 : ℝ) / u ≤ 4 := by
  have hu0 : 0 < u := by linarith
  unfold comparisonDrop
  refine ⟨by positivity, ?_, ?_⟩
  · apply (div_le_one hu0).2
    linarith
  · apply (div_le_iff₀ hu0).2
    linarith

theorem quintic_polar_integral_eq (u h : ℝ) :
    (∫ t in (0 : ℝ)..1, (1 - h + h * (1 + u) * t) ^ (2 : ℝ)) =
      1 - h * (1 - u) + h ^ 2 * (u ^ 2 - u + 1) / 3 := by
  simp_rw [Real.rpow_two]
  calc
    _ = ∫ t in (0 : ℝ)..1, h ^ 2 * (1 + u) ^ 2 * t ^ 2 +
        2 * h * (1 + u) * (1 - h) * t + (1 - h) ^ 2 := by
      apply intervalIntegral.integral_congr
      intro t _
      ring
    _ = _ := by rw [integral_quadratic]; ring

theorem quintic_polar_test {u : ℝ} (hu : 8 / 11 ≤ u) (hu1 : u < 1) :
    (∫ t in (0 : ℝ)..1,
      (1 - comparisonDrop u (8 / 3) + comparisonDrop u (8 / 3) * (1 + u) * t) ^ (2 : ℝ)) < 1 := by
  have hu0 : 0 < u := by linarith
  have heps : 0 < 1 - u := by linarith
  rw [quintic_polar_integral_eq]
  have he : 1 - comparisonDrop u (8 / 3) * (1 - u) +
      comparisonDrop u (8 / 3) ^ 2 * (u ^ 2 - u + 1) / 3 - 1 =
      (8 * (1 - u) ^ 2 / (27 * u ^ 2)) * (8 * u ^ 2 - 17 * u + 8) := by
    unfold comparisonDrop
    field_simp
    ring
  have hq : 8 * u ^ 2 - 17 * u + 8 < 0 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hu1.le)]
  have hneg := mul_neg_of_pos_of_neg
    (show 0 < 8 * (1 - u) ^ 2 / (27 * u ^ 2) by positivity) hq
  linarith

theorem quintic_normalized_comparison_eq {u : ℝ} (hu : 8 / 11 ≤ u) (hu1 : u < 1) :
    normalizedComparisonIntegral 4 u (8 / 3) =
      (72 * u ^ 3 - 192 * u ^ 2 + 179 * u - 32) / (27 * u ^ 2) := by
  have hu0 : 0 < u := by linarith
  have hκ := (quintic_drop_parameters hu hu1).2.2
  have hd := comparisonD_pos hu0 hu1.le (by norm_num : (0 : ℝ) ≤ 8 / 3)
  have hq : 0 < 3 * u ^ 2 + 8 * (1 - u) := by positivity
  have hdval : comparisonD u (8 / 3) = (3 * u ^ 2 + 8 * (1 - u)) / (3 * u) := by
    unfold comparisonD comparisonDrop
    field_simp
  rw [normalizedComparisonIntegral_recurrence 4 (by norm_num) hu0 hu1
    (by norm_num : (0 : ℝ) ≤ 8 / 3) hκ]
  norm_num only [Nat.reduceSub, Nat.cast_ofNat, show (4 : ℝ) / 2 = 2 by norm_num, Real.rpow_two]
  rw [normalizedComparisonIntegral_two hu0 hu1 (by norm_num : (0 : ℝ) ≤ 8 / 3),
    comparisonMinimum_normalized u (8 / 3) hu0.ne' hd.ne', hdval]
  field_simp
  ring_nf
  have hqn : 8 - u * 8 + u ^ 2 * 3 ≠ 0 := by nlinarith [hq]
  have hinv := inv_mul_cancel₀ hqn
  linear_combination -(15552 - 50544 * u + 17496 * u ^ 2) * hinv

theorem quintic_normalized_comparison_gap {u : ℝ} (hu : 8 / 11 ≤ u) (hu1 : u < 1) :
    (10 * u / 3 - 4 * u ^ 2 + u ^ 3) +
      (Real.sqrt 3 / 3) * (5 - 4 * u) * u ^ (3 / 2 : ℝ) * Real.sqrt (1 - u) +
      (1 - u) ^ 4 / u < normalizedComparisonIntegral 4 u (8 / 3) := by
  have hu0 : 0 < u := by linarith
  have heps : 0 < 1 - u := by linarith
  have hlin : 0 ≤ 5 - 4 * u := by linarith
  let r := (Real.sqrt 3 / 3) * (5 - 4 * u) * u ^ (3 / 2 : ℝ) * Real.sqrt (1 - u)
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hr2 : r ^ 2 = (1 / 3 : ℝ) * (5 - 4 * u) ^ 2 * u ^ 3 * (1 - u) := by
    dsimp [r]
    rw [rpow_three_halves_eq_mul_sqrt hu0.le]
    simp only [mul_pow, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
      Real.sq_sqrt hu0.le, Real.sq_sqrt heps.le]
    ring
  have hrs : (27 * u ^ 2 * r) ^ 2 = 243 * u ^ 7 * (1 - u) * (5 - 4 * u) ^ 2 := by
    rw [mul_pow, hr2]
    ring
  have hG := quinticGapPolynomial_pos hu hu1
  have hP := quinticSquaredGapPolynomial_pos hu hu1
  have hs : (27 * u ^ 2 * r) ^ 2 < quinticGapPolynomial u ^ 2 := by
    rw [hrs]
    unfold quinticSquaredGapPolynomial at hP
    linarith
  have hscaled := (sq_lt_sq₀ (show 0 ≤ 27 * u ^ 2 * r by positivity) hG.le).1 hs
  have hden : 0 < 27 * u ^ 2 := by positivity
  have hrad : r < quinticGapPolynomial u / (27 * u ^ 2) :=
    (lt_div_iff₀ hden).2 (by simpa only [mul_comm] using hscaled)
  have hGval : quinticGapPolynomial u / (27 * u ^ 2) =
      normalizedComparisonIntegral 4 u (8 / 3) -
        (10 * u / 3 - 4 * u ^ 2 + u ^ 3) - (1 - u) ^ 4 / u := by
    rw [quintic_normalized_comparison_eq hu hu1]
    unfold quinticGapPolynomial
    field_simp
    ring
  rw [hGval] at hrad
  change (10 * u / 3 - 4 * u ^ 2 + u ^ 3) + r + (1 - u) ^ 4 / u < _
  linarith

theorem quintic_scalar_exclusion {ι : Type*} (jset : Finset ι) (η : ι → ℂ)
    (hcard : jset.card = 4) {u h : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (hh0 : 0 < h) (hh1 : h < 1)
    (hη : ∑ j ∈ jset, η j = 0)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (4 : ℝ) * (u * (1 - u)))
    (hpolar : 1 ≤ ∫ t in (0 : ℝ)..1, (1 - h + h * (1 + u) * t) ^ (2 : ℝ)) :
    (5 : ℝ) * (∫ t in (0 : ℝ)..1,
      (max (1 - 2 * u * t + u * t ^ 2 - h * t * (1 - t)) 0) ^ (2 : ℝ)) <
      ((5 : ℝ) * ∫ t in (0 : ℝ)..1, (1 - u * t) ^ 4) -
        centeredErrorIntegral jset η 4 u := by
  have hu := quintic_parameter_gt_eight_elevenths hu0.le hh0 hh1.le hpolar
  have hpar := quintic_drop_parameters hu.le hu1
  have hdrop := polar_certification hu0.le hh0 hpar.1 hpar.2.1
    (by norm_num : (1 : ℝ) ≤ 2) hpolar (quintic_polar_test hu.le hu1)
  have herror := quintic_finite_error_bound jset η hcard hu0 hu1 hη hV
  have hgap := quintic_normalized_comparison_gap hu.le hu1
  simpa only [Nat.cast_ofNat, show (4 : ℝ) + 1 = 5 by norm_num,
    show (4 : ℝ) / 2 = 2 by norm_num] using
    scalar_exclusion_of_normalized_comparison jset η 4 hu0 hu1
      (by norm_num : (0 : ℝ) ≤ 8 / 3) hpar.2.2 hdrop.le herror hgap

end Schmeisser

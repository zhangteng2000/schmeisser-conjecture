import Schmeisser.QuarticEndpoint
import Schmeisser.PolarThresholds
import Schmeisser.FiniteReduction
import Schmeisser.QuarticFiniteError

/-! A purely analytic exclusion for critical-point count three. -/

noncomputable section

namespace Schmeisser

open Set MeasureTheory

theorem quartic_parameter_gt_three_quarters {u h : ℝ}
    (hu : 0 ≤ u) (hh0 : 0 < h) (hh1 : h ≤ 1)
    (hpolar : 1 ≤ ∫ t in (0 : ℝ)..1, (1 - h + h * (1 + u) * t) ^ (3 / 2 : ℝ)) :
    3 / 4 < u := by
  have hp := polar_threshold_squared 3 (by norm_num) hu hh0 hh1 hpolar
  norm_num only [Nat.cast_ofNat] at hp
  by_contra hn
  have hupp : u ≤ 3 / 4 := le_of_not_gt hn
  have hc := pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 + u by linarith)
    (show 1 + u ≤ 7 / 4 by linarith) 3
  norm_num at hc
  linarith

theorem quartic_three_drop_parameters {u : ℝ} (hu : 3 / 4 ≤ u) (hu1 : u < 1) :
    0 < comparisonDrop u 3 ∧ comparisonDrop u 3 ≤ 1 ∧ (3 : ℝ) / u ≤ 4 := by
  have hu0 : 0 < u := by linarith
  unfold comparisonDrop
  refine ⟨by positivity, ?_, ?_⟩
  · apply (div_le_one hu0).2
    linarith
  · apply (div_le_iff₀ hu0).2
    linarith

theorem quartic_three_polar_test {u : ℝ} (hu : 3 / 4 ≤ u) (hu1 : u < 1) :
    (∫ t in (0 : ℝ)..1,
      (1 - comparisonDrop u 3 + comparisonDrop u 3 * (1 + u) * t) ^ (3 / 2 : ℝ)) < 1 := by
  have hu0 : 0 < u := by linarith
  have heps : 0 < 1 - u := by linarith
  have hpar := quartic_three_drop_parameters hu hu1
  have hp := polar_cubic_quadratic_bound hu0.le hpar.1.le hpar.2.1
  have he : 1 - (3 / 4 : ℝ) * comparisonDrop u 3 * (1 - u) +
      comparisonDrop u 3 ^ 2 * (u ^ 2 - u + 1) / 6 - 1 =
      (3 * (1 - u) ^ 2 / (4 * u ^ 2)) * (2 * u - 1) * (u - 2) := by
    unfold comparisonDrop
    field_simp
    ring
  have hneg : (3 * (1 - u) ^ 2 / (4 * u ^ 2)) * (2 * u - 1) * (u - 2) < 0 := by
    apply mul_neg_of_pos_of_neg
    · apply mul_pos
      · positivity
      · linarith
    · linarith
  linarith

theorem quartic_gap_polynomial_sos (t : ℝ) :
    4 - 20 * t + 15 * t ^ 2 + 23 * t ^ 3 + 20 * t ^ 4 + 12 * t ^ 5 +
      8 * t ^ 6 + 20 * t ^ 7 - 8 * t ^ 9 - 20 * t ^ 10 =
      15 * (t - 253 / 810) ^ 2 + 4031 / 43740 +
        (t - 1 / 3) ^ 2 * (20 * t ^ 2 + (109 / 3) * t + 22) +
        12 * t ^ 5 + 8 * t ^ 6 * (1 - t ^ 3) + 20 * t ^ 7 * (1 - t ^ 3) := by
  ring

theorem quartic_gap_polynomial_pos {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < 4 - 20 * t + 15 * t ^ 2 + 23 * t ^ 3 + 20 * t ^ 4 + 12 * t ^ 5 +
      8 * t ^ 6 + 20 * t ^ 7 - 8 * t ^ 9 - 20 * t ^ 10 := by
  have hcube : 0 ≤ 1 - t ^ 3 := sub_nonneg.mpr (pow_le_one₀ ht0 ht1)
  rw [quartic_gap_polynomial_sos]
  positivity

theorem quartic_rational_gap {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    let u := 1 - t ^ 2
    let a := 1 + t ^ 2 + t ^ 4
    u / 2 * (1 + 3 * t ^ 2) + u * t + t ^ 6 / u <
      1 / u + 3 / (2 * a) * (1 - t ^ 3) -
        (3 / 2 : ℝ) * (1 - 9 * t ^ 2 / (4 * u * a)) * (1 + t) := by
  let u := 1 - t ^ 2
  let a := 1 + t ^ 2 + t ^ 4
  change u / 2 * (1 + 3 * t ^ 2) + u * t + t ^ 6 / u <
    1 / u + 3 / (2 * a) * (1 - t ^ 3) -
      (3 / 2 : ℝ) * (1 - 9 * t ^ 2 / (4 * u * a)) * (1 + t)
  have hu : 0 < u := by dsimp [u]; nlinarith
  have ha : 0 < a := by dsimp [a]; positivity
  have he : 8 * u * a *
      ((1 / u + 3 / (2 * a) * (1 - t ^ 3) -
          (3 / 2 : ℝ) * (1 - 9 * t ^ 2 / (4 * u * a)) * (1 + t)) -
        u / 2 * (1 + 3 * t ^ 2) - u * t - t ^ 6 / u) =
      4 - 20 * t + 15 * t ^ 2 + 23 * t ^ 3 + 20 * t ^ 4 + 12 * t ^ 5 +
        8 * t ^ 6 + 20 * t ^ 7 - 8 * t ^ 9 - 20 * t ^ 10 := by
    field_simp
    dsimp [u, a]
    ring
  have hprod : 0 < 8 * u * a *
      ((1 / u + 3 / (2 * a) * (1 - t ^ 3) -
          (3 / 2 : ℝ) * (1 - 9 * t ^ 2 / (4 * u * a)) * (1 + t)) -
        u / 2 * (1 + 3 * t ^ 2) - u * t - t ^ 6 / u) := by
    rw [he]
    exact quartic_gap_polynomial_pos ht0 ht1.le
  have hdiff := pos_of_mul_pos_right hprod (show 0 ≤ 8 * u * a by positivity)
  linarith

theorem quartic_normalized_comparison_gap {u : ℝ} (hu : 3 / 4 ≤ u) (hu1 : u < 1) :
    u / 2 * (1 + 3 * (1 - u)) + u * Real.sqrt (1 - u) + (1 - u) ^ 3 / u <
      normalizedComparisonIntegral 3 u 3 := by
  have hu0 : 0 < u := by linarith
  have heps : 0 < 1 - u := by linarith
  have hκ := (quartic_three_drop_parameters hu hu1).2.2
  let t := Real.sqrt (1 - u)
  let a := 1 + t ^ 2 + t ^ 4
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have ht2 : t ^ 2 = 1 - u := Real.sq_sqrt heps.le
  have hut : u = 1 - t ^ 2 := by linarith
  have ht1 : t < 1 := by nlinarith
  have ha : 0 < a := by dsimp [a]; positivity
  have hd := comparisonD_pos hu0 hu1.le (by norm_num : (0 : ℝ) ≤ 3)
  have hdval : comparisonD u 3 = a / u := by
    unfold comparisonD comparisonDrop
    have hu' : 1 - t ^ 2 ≠ 0 := by rw [← hut]; exact hu0.ne'
    rw [hut]
    dsimp [a]
    field_simp
    ring
  have hmin : comparisonMinimum u 3 / (1 - u) = 1 - 9 * t ^ 2 / (4 * u * a) := by
    rw [comparisonMinimum_normalized u 3 hu0.ne' hd.ne', hdval, ht2]
    field_simp
    norm_num
  have hp : (1 - u) ^ (3 / 2 : ℝ) = t ^ 3 := by
    rw [rpow_three_halves_eq_mul_sqrt heps.le]
    change (1 - u) * t = t ^ 3
    rw [← ht2]
    ring
  have hR1 := comparisonIntegral_one_le_endpoints hu0 hu1.le (by norm_num : (0 : ℝ) ≤ 3) hκ
  have hL := normalizedComparisonIntegral_three_lower hu0 hu1 (by norm_num : (0 : ℝ) ≤ 3) hκ hR1
  rw [hdval, hmin, hp] at hL
  have hfrac : 3 / (2 * u * (a / u)) = 3 / (2 * a) := by field_simp
  rw [hfrac] at hL
  have hgap := quartic_rational_gap ht0 ht1
  change (1 - t ^ 2) / 2 * (1 + 3 * t ^ 2) + (1 - t ^ 2) * t + t ^ 6 / (1 - t ^ 2) <
    1 / (1 - t ^ 2) + 3 / (2 * a) * (1 - t ^ 3) -
      (3 / 2 : ℝ) * (1 - 9 * t ^ 2 / (4 * (1 - t ^ 2) * a)) * (1 + t) at hgap
  rw [← hut] at hgap
  have ht6 : t ^ 6 = (1 - u) ^ 3 := by
    rw [show 6 = 2 * 3 by norm_num, pow_mul, ht2]
  simp only [ht2, ht6] at hgap hL
  exact hgap.trans_le hL

theorem quartic_scalar_exclusion {ι : Type*} (jset : Finset ι) (η : ι → ℂ)
    (hcard : jset.card = 3) {u h : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (hh0 : 0 < h) (hh1 : h < 1)
    (hη : ∑ j ∈ jset, η j = 0)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (3 : ℝ) * (u * (1 - u)))
    (hpolar : 1 ≤ ∫ t in (0 : ℝ)..1, (1 - h + h * (1 + u) * t) ^ (3 / 2 : ℝ)) :
    (4 : ℝ) * (∫ t in (0 : ℝ)..1,
      (max (1 - 2 * u * t + u * t ^ 2 - h * t * (1 - t)) 0) ^ (3 / 2 : ℝ)) <
      ((4 : ℝ) * ∫ t in (0 : ℝ)..1, (1 - u * t) ^ 3) -
        centeredErrorIntegral jset η 3 u := by
  have hu := quartic_parameter_gt_three_quarters hu0.le hh0 hh1.le hpolar
  have hpar := quartic_three_drop_parameters hu.le hu1
  have hdrop := polar_certification hu0.le hh0 hpar.1 hpar.2.1
    (by norm_num : (1 : ℝ) ≤ 3 / 2) hpolar (quartic_three_polar_test hu.le hu1)
  have herror := quartic_finite_error_bound jset η hcard hu0 hu1 hη hV
  have hgap := quartic_normalized_comparison_gap hu.le hu1
  simpa only [Nat.cast_ofNat, show (3 : ℝ) + 1 = 4 by norm_num] using
    scalar_exclusion_of_normalized_comparison jset η 3 hu0 hu1
      (by norm_num : (0 : ℝ) ≤ 3) hpar.2.2 hdrop.le herror hgap

end Schmeisser

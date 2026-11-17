import Schmeisser.SexticFiniteError
import Schmeisser.PolarThresholds
import Schmeisser.FiniteReduction
import Schmeisser.Certificates.Count5PolynomialBounds

/-! A purely analytic exclusion for critical-point count five. -/

noncomputable section

namespace Schmeisser

open Set MeasureTheory

theorem sextic_parameter_gt_thirteen_twentieths {u h : ℝ}
    (hu : 0 ≤ u) (hh0 : 0 < h) (hh1 : h ≤ 1)
    (hpolar : 1 ≤ ∫ t in (0 : ℝ)..1, (1 - h + h * (1 + u) * t) ^ (5 / 2 : ℝ)) :
    13 / 20 < u := by
  have hp := polar_threshold_squared 5 (by norm_num) hu hh0 hh1 hpolar
  norm_num only [Nat.cast_ofNat] at hp
  by_contra hn
  have hupp : u ≤ 13 / 20 := le_of_not_gt hn
  have hc := pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 + u by linarith)
    (show 1 + u ≤ 33 / 20 by linarith) 5
  norm_num at hc
  linarith

theorem sextic_drop_parameters {u : ℝ} (hu : 13 / 20 ≤ u) (hu1 : u < 1) :
    0 < comparisonDrop u (7 / 4) ∧ comparisonDrop u (7 / 4) ≤ 1 ∧
      (7 / 4 : ℝ) / u ≤ 4 := by
  have hu0 : 0 < u := by linarith
  unfold comparisonDrop
  refine ⟨by positivity, ?_, ?_⟩
  · apply (div_le_one hu0).2
    linarith
  · apply (div_le_iff₀ hu0).2
    linarith

theorem rpow_five_halves_le_cubic {x : ℝ} (hx : 0 ≤ x) :
    x ^ (5 / 2 : ℝ) ≤ (x ^ 3 + x ^ 2) / 2 := by
  have hs : Real.sqrt x ≤ (x + 1) / 2 := by
    nlinarith [Real.sq_sqrt hx, sq_nonneg (Real.sqrt x - 1)]
  rw [rpow_five_halves_eq_mul_sqrt hx]
  nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg x)]

theorem integral_cubic (a b c d : ℝ) :
    (∫ t in (0 : ℝ)..1, a * t ^ 3 + (b * t ^ 2 + c * t + d)) =
      a / 4 + b / 3 + c / 2 + d := by
  have ha : Continuous (fun t : ℝ => a * t ^ 3) := by fun_prop
  have hb : Continuous (fun t : ℝ => b * t ^ 2 + c * t + d) := by fun_prop
  rw [intervalIntegral.integral_add (ha.intervalIntegrable 0 1) (hb.intervalIntegrable 0 1),
    intervalIntegral.integral_const_mul, integral_pow, integral_quadratic]
  norm_num
  ring

theorem polar_five_cubic_bound {u h : ℝ} (hu : 0 ≤ u) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) :
    (∫ t in (0 : ℝ)..1, (1 - h + h * (1 + u) * t) ^ (5 / 2 : ℝ)) ≤
      1 - (5 / 4 : ℝ) * h * (1 - u) + (2 / 3 : ℝ) * h ^ 2 * (u ^ 2 - u + 1) -
        h ^ 3 * (1 - u) * (u ^ 2 + 1) / 8 := by
  let f : ℝ → ℝ := fun t => 1 - h + h * (1 + u) * t
  have hc : Continuous f := by dsimp [f]; fun_prop
  have hg : Continuous (fun t : ℝ => (f t ^ 3 + f t ^ 2) / 2) := by fun_prop
  have hi : (∫ t in (0 : ℝ)..1, (f t) ^ (5 / 2 : ℝ)) ≤
      ∫ t in (0 : ℝ)..1, (f t ^ 3 + f t ^ 2) / 2 := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      (((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 5 / 2)).comp hc).intervalIntegrable 0 1)
      (hg.intervalIntegrable 0 1)
    intro t ht
    apply rpow_five_halves_le_cubic
    dsimp [f]
    have hs : 0 ≤ h * (1 + u) * t := mul_nonneg (by positivity) ht.1
    linarith
  refine hi.trans_eq ?_
  calc
    _ = ∫ t in (0 : ℝ)..1, (h ^ 3 * (1 + u) ^ 3 / 2) * t ^ 3 +
        ((h ^ 2 * (1 + u) ^ 2 * (4 - 3 * h) / 2) * t ^ 2 +
          (h * (1 + u) * (1 - h) * (5 - 3 * h) / 2) * t +
          ((1 - h) ^ 3 + (1 - h) ^ 2) / 2) := by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp [f]
      ring
    _ = _ := by rw [integral_cubic]; ring

theorem sextic_polar_test {u : ℝ} (hu : 13 / 20 ≤ u) (hu1 : u < 1) :
    (∫ t in (0 : ℝ)..1,
      (1 - comparisonDrop u (7 / 4) + comparisonDrop u (7 / 4) * (1 + u) * t) ^ (5 / 2 : ℝ)) < 1 := by
  have hu0 : 0 < u := by linarith
  have heps : 0 < 1 - u := by linarith
  have hpar := sextic_drop_parameters hu hu1
  have hp := polar_five_cubic_bound hu0.le hpar.1.le hpar.2.1
  have he : 1 - (5 / 4 : ℝ) * comparisonDrop u (7 / 4) * (1 - u) +
      (2 / 3 : ℝ) * comparisonDrop u (7 / 4) ^ 2 * (u ^ 2 - u + 1) -
        comparisonDrop u (7 / 4) ^ 3 * (1 - u) * (u ^ 2 + 1) / 8 - 1 =
      -((1 - u) ^ 2 / u ^ 3) *
        (7 * (3 * u - 7) * (7 * u - 3) * (7 * u ^ 2 - 16 * u + 7) / 1536) := by
    unfold comparisonDrop
    field_simp
    ring
  have hq : 7 * u ^ 2 - 16 * u + 7 < 0 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hu1.le)]
  have hfactor : 0 < 7 * (3 * u - 7) * (7 * u - 3) * (7 * u ^ 2 - 16 * u + 7) / 1536 := by
    apply div_pos _ (by norm_num)
    apply mul_pos_of_neg_of_neg _ hq
    apply mul_neg_of_neg_of_pos
    · nlinarith
    · linarith
  have hneg := mul_neg_of_neg_of_pos
    (neg_neg_of_pos (show 0 < (1 - u) ^ 2 / u ^ 3 by positivity)) hfactor
  linarith

def sexticComparisonLower (u : ℝ) : ℝ :=
  let e := 1 - u
  let t := Real.sqrt e
  let a := 4 * u ^ 2 + 7 * e
  let mt := 1 - 49 * e / (16 * u * a)
  let theta := 7 * e / (2 * a)
  1 / u + 7 / (2 * a) * (1 - t ^ 5) - (5 / 4 : ℝ) * mt *
    (1 - theta + theta * t ^ 3 + (3 / 2 : ℝ) * e * mt * (1 + t))

theorem sextic_comparison_lower {u : ℝ} (hu : 13 / 20 ≤ u) (hu1 : u < 1) :
    sexticComparisonLower u ≤ normalizedComparisonIntegral 5 u (7 / 4) := by
  have hu0 : 0 < u := by linarith
  have heps : 0 < 1 - u := by linarith
  have hκ := (sextic_drop_parameters hu hu1).2.2
  let e := 1 - u
  let t := Real.sqrt e
  let a := 4 * u ^ 2 + 7 * e
  let mt := 1 - 49 * e / (16 * u * a)
  let theta := 7 * e / (2 * a)
  let b := 1 - theta + theta * t ^ 3 + (3 / 2 : ℝ) * e * mt * (1 + t)
  have he : 0 < e := heps
  have ha : 0 < a := by dsimp [a]; positivity
  have hd := comparisonD_pos hu0 hu1.le (by norm_num : (0 : ℝ) ≤ 7 / 4)
  have hdval : comparisonD u (7 / 4) = a / (4 * u) := by
    unfold comparisonD comparisonDrop
    dsimp [a, e]
    field_simp
  have hmin : comparisonMinimum u (7 / 4) = e * mt := by
    rw [comparisonMinimum_normalized u (7 / 4) hu0.ne' hd.ne', hdval]
    dsimp [mt, e]
    field_simp
    ring
  have htheta : comparisonTheta u (7 / 4) = theta := by
    unfold comparisonTheta comparisonDrop
    rw [hdval]
    dsimp [theta, e]
    field_simp
  have hmt : 0 ≤ mt := by
    have hm := (comparisonMinimum_bounds hu0 hu1.le (by norm_num : (0 : ℝ) ≤ 7 / 4) hκ).1
    rw [hmin] at hm
    nlinarith
  have ht2 : t ^ 2 = e := Real.sq_sqrt he.le
  have hp3 : (1 - u) ^ (3 / 2 : ℝ) = t ^ 3 := by
    rw [rpow_three_halves_eq_mul_sqrt heps.le]
    change e * t = t ^ 3
    rw [← ht2]
    ring
  have hp5 : (1 - u) ^ (5 / 2 : ℝ) = t ^ 5 := by
    rw [rpow_five_halves_eq_mul_sqrt heps.le]
    change e ^ 2 * t = t ^ 5
    rw [← ht2]
    ring
  have hR1 := comparisonIntegral_one_le_endpoints hu0 hu1.le (by norm_num : (0 : ℝ) ≤ 7 / 4) hκ
  have hR3 := comparisonIntegral_recurrence 3 (by norm_num) hu0 hu1.le (by norm_num : (0 : ℝ) ≤ 7 / 4) hκ
  have hR5 := comparisonIntegral_recurrence 5 (by norm_num) hu0 hu1.le (by norm_num : (0 : ℝ) ≤ 7 / 4) hκ
  norm_num only [Nat.cast_ofNat, Nat.reduceSub] at hR3 hR5
  rw [hmin, htheta, hp3] at hR3
  rw [hmin, htheta, hp5] at hR5
  have hR3b : comparisonIntegral 3 u (7 / 4) ≤ b := by
    rw [hR3]
    have h := mul_le_mul_of_nonneg_left hR1 (show 0 ≤ (3 / 2 : ℝ) * e * mt by positivity)
    dsimp [b]
    simpa only [mul_assoc] using add_le_add le_rfl h
  have hR5b : comparisonIntegral 5 u (7 / 4) ≤
      1 - theta + theta * t ^ 5 + (5 / 4 : ℝ) * e * mt * b := by
    rw [hR5]
    have h := mul_le_mul_of_nonneg_left hR3b (show 0 ≤ (5 / 4 : ℝ) * e * mt by positivity)
    simpa only [mul_assoc] using add_le_add le_rfl h
  have hbound := div_le_div_of_nonneg_right (sub_le_sub_left hR5b (1 / u)) he.le
  have halgebra : (1 / u - (1 - theta + theta * t ^ 5 + (5 / 4 : ℝ) * e * mt * b)) / e =
      1 / u + 7 / (2 * a) * (1 - t ^ 5) - (5 / 4 : ℝ) * mt * b := by
    dsimp [theta, e]
    field_simp
    ring
  rw [halgebra] at hbound
  exact hbound

theorem sextic_gap_identity {u t : ℝ} (hu0 : 0 < u) (ht0 : 0 ≤ t) (ht2 : t ^ 2 = 1 - u) :
    30720 * u ^ 2 * (4 * u ^ 2 + 7 * (1 - u)) ^ 2 *
      (sexticComparisonLower u - sexticErrorBound u - (1 - u) ^ 5 / u) =
      (1 + t) * sexticGapPolynomial t := by
  have he : 0 ≤ 1 - u := by rw [← ht2]; positivity
  have ha : 0 < 4 * u ^ 2 + 7 * (1 - u) := by positivity
  have hs : Real.sqrt (1 - u) = t := by rw [← ht2, Real.sqrt_sq_eq_abs, abs_of_nonneg ht0]
  have hut : u = 1 - t ^ 2 := by linarith
  dsimp only [sexticComparisonLower, sexticErrorBound]
  rw [hs]
  field_simp [hu0.ne', ha.ne']
  rw [hut]
  unfold sexticGapPolynomial
  ring

theorem sextic_normalized_comparison_gap {u : ℝ} (hu : 13 / 20 ≤ u) (hu1 : u < 1) :
    sexticErrorBound u + (1 - u) ^ 5 / u < normalizedComparisonIntegral 5 u (7 / 4) := by
  have hu0 : 0 < u := by linarith
  have heps : 0 < 1 - u := by linarith
  let t := Real.sqrt (1 - u)
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have ht2 : t ^ 2 = 1 - u := Real.sq_sqrt heps.le
  have ht1 : t < 3 / 5 := by nlinarith
  have hpoly := sexticGapPolynomial_pos ht0 ht1
  have hscale : 0 < 30720 * u ^ 2 * (4 * u ^ 2 + 7 * (1 - u)) ^ 2 := by positivity
  have hprod : 0 < 30720 * u ^ 2 * (4 * u ^ 2 + 7 * (1 - u)) ^ 2 *
      (sexticComparisonLower u - sexticErrorBound u - (1 - u) ^ 5 / u) := by
    rw [sextic_gap_identity hu0 ht0 ht2]
    exact mul_pos (by linarith) hpoly
  have hdiff := pos_of_mul_pos_right hprod hscale.le
  have hlower := sextic_comparison_lower hu hu1
  linarith

theorem sextic_scalar_exclusion {ι : Type*} (jset : Finset ι) (η : ι → ℂ)
    (hcard : jset.card = 5) {u h : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (hh0 : 0 < h) (hh1 : h < 1)
    (hη : ∑ j ∈ jset, η j = 0)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (5 : ℝ) * (u * (1 - u)))
    (hpolar : 1 ≤ ∫ t in (0 : ℝ)..1, (1 - h + h * (1 + u) * t) ^ (5 / 2 : ℝ)) :
    (6 : ℝ) * (∫ t in (0 : ℝ)..1,
      (max (1 - 2 * u * t + u * t ^ 2 - h * t * (1 - t)) 0) ^ (5 / 2 : ℝ)) <
      ((6 : ℝ) * ∫ t in (0 : ℝ)..1, (1 - u * t) ^ 5) -
        centeredErrorIntegral jset η 5 u := by
  have hu := sextic_parameter_gt_thirteen_twentieths hu0.le hh0 hh1.le hpolar
  have hpar := sextic_drop_parameters hu.le hu1
  have hdrop := polar_certification hu0.le hh0 hpar.1 hpar.2.1
    (by norm_num : (1 : ℝ) ≤ 5 / 2) hpolar (sextic_polar_test hu.le hu1)
  have herror := sextic_finite_error_bound jset η hcard hu0 hu1 hη hV
  have hgap := sextic_normalized_comparison_gap hu.le hu1
  simpa only [Nat.cast_ofNat, show (5 : ℝ) + 1 = 6 by norm_num] using
    scalar_exclusion_of_normalized_comparison jset η 5 hu0 hu1
      (by norm_num : (0 : ℝ) ≤ 7 / 4) hpar.2.2 hdrop.le herror hgap

end Schmeisser

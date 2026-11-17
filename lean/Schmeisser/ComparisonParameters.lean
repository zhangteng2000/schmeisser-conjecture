import Schmeisser.NumericalBounds
import Schmeisser.QuadraticIntegrals

noncomputable section

namespace Schmeisser

open Set MeasureTheory

theorem polar_comparison_drop {m u h : ℝ} (hm : 3 ≤ m)
    (hu0 : 0 < u) (hu1 : u ≤ 1) (hh0 : 0 < h) (hh1 : h < 1)
    (hpolar : 1 ≤ ∫ t in (0 : ℝ)..1, (1 - h + h * (1 + u) * t) ^ (m / 2)) :
    (6 / m) / u < 4 ∧ comparisonDrop u (6 / m) < h := by
  have hm0 : 0 < m := by linarith
  have ht := polar_integral_power_threshold hu0.le hh0 hh1.le
    (show 1 ≤ m / 2 by linarith) hpolar
  have hmu := degree_parameter_gt_three_halves hm hu0 ht
  have hproduct := polar_integral_product_lower_bound hu0.le hu1 hh0 hh1
    (show 0 < m / 2 by positivity) hpolar
  constructor
  · rw [div_div, div_lt_iff₀ (mul_pos hm0 hu0)]
    linarith
  · unfold comparisonDrop
    rw [div_mul_eq_mul_div, div_div, div_lt_iff₀ (mul_pos hm0 hu0)]
    nlinarith

theorem second_integral_le_comparison (m : ℕ) {u h κ : ℝ}
    (hu0 : 0 < u) (hu1 : u ≤ 1) (hκ0 : 0 ≤ κ) (hκ4 : κ / u ≤ 4)
    (hdrop : comparisonDrop u κ ≤ h) :
    ((m : ℝ) + 1) * (∫ t in (0 : ℝ)..1,
      (max (1 - 2 * u * t + u * t ^ 2 - h * t * (1 - t)) 0) ^ ((m : ℝ) / 2)) ≤
      comparisonIntegral m u κ := by
  have hD := comparisonD_pos hu0 hu1 hκ0
  have hmin := (comparisonMinimum_bounds hu0 hu1 hκ0 hκ4).1
  have hQ (t : ℝ) : 0 ≤ comparisonQuadratic u κ t := by
    rw [comparisonQuadratic_eq_shifted u κ t hD.ne']
    exact shiftedQuadratic_nonneg _ _ _ _ hD.le hmin
  have hleft : Continuous (fun t : ℝ ↦
      (max (1 - 2 * u * t + u * t ^ 2 - h * t * (1 - t)) 0) ^ ((m : ℝ) / 2)) :=
    (Real.continuous_rpow_const (by positivity : 0 ≤ (m : ℝ) / 2)).comp (by fun_prop)
  have hright : Continuous (fun t : ℝ ↦ comparisonQuadratic u κ t ^ ((m : ℝ) / 2)) := by
    apply (Real.continuous_rpow_const (by positivity : 0 ≤ (m : ℝ) / 2)).comp
    unfold comparisonQuadratic
    fun_prop
  unfold comparisonIntegral
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply intervalIntegral.integral_mono_on (by norm_num)
    (hleft.intervalIntegrable 0 1) (hright.intervalIntegrable 0 1)
  intro t ht
  apply Real.rpow_le_rpow (le_max_right _ _) _ (by positivity)
  apply max_le _ (hQ t)
  have hdiff := mul_le_mul_of_nonneg_right hdrop
    (mul_nonneg ht.1 (sub_nonneg.mpr ht.2))
  unfold comparisonQuadratic
  nlinarith

theorem comparisonB_at_large_scale (m u : ℝ) :
    comparisonB u (6 / m) = u + 3 * (1 - u) / (m * u) := by
  unfold comparisonB comparisonDrop
  ring

theorem comparisonB_le_endpoint {m u v : ℝ}
    (hm : 0 < m) (hu : 0 < u) (huv : u ≤ v) (hmuv : 3 ≤ m * u * v) :
    comparisonB u (6 / m) ≤ comparisonB v (6 / m) := by
  have hv : 0 < v := hu.trans_le huv
  have hprod : 0 < m * u * v := by positivity
  have he : (comparisonB u (6 / m) - comparisonB v (6 / m)) * (m * u * v) =
      (u - v) * (m * u * v - 3) := by
    rw [comparisonB_at_large_scale, comparisonB_at_large_scale]
    field_simp
    <;> ring
  have hs : (comparisonB u (6 / m) - comparisonB v (6 / m)) * (m * u * v) ≤ 0 := by
    rw [he]
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr huv) (by linarith)
  nlinarith

theorem large_comparisonB_small {m u : ℝ} (hm : 6000 ≤ m)
    (hu : 0 < u) (htu : 16 < m * u) (hu1 : u ≤ 1 / 2) :
    comparisonB u (6 / m) < 501 / 1000 := by
  have hb := comparisonB_le_endpoint (by linarith : 0 < m) hu hu1 (by nlinarith : 3 ≤ m * u * (1 / 2))
  rw [comparisonB_at_large_scale m (1 / 2)] at hb
  have he : (1 / 2 : ℝ) + 3 * (1 - 1 / 2) / (m * (1 / 2)) = 1 / 2 + 3 / m := by ring
  rw [he] at hb
  have hfrac : 3 / m ≤ (3 / 6000 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hm
  linarith

theorem large_comparisonB_middle {m u : ℝ} (hm : 6000 ≤ m)
    (hu : 0 < u) (htu : 16 < m * u) (hu1 : u ≤ 4 / 5) :
    comparisonB u (6 / m) < 801 / 1000 := by
  have hb := comparisonB_le_endpoint (by linarith : 0 < m) hu hu1 (by nlinarith : 3 ≤ m * u * (4 / 5))
  rw [comparisonB_at_large_scale m (4 / 5)] at hb
  have he : (4 / 5 : ℝ) + 3 * (1 - 4 / 5) / (m * (4 / 5)) = 4 / 5 + (3 / 4) / m := by ring
  rw [he] at hb
  have hfrac : (3 / 4) / m ≤ ((3 / 4) / 6000 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hm
  linarith

theorem large_comparisonB_le_one {m u : ℝ} (hm : 0 < m)
    (hu : 0 < u) (htu : 16 < m * u) (hu1 : u ≤ 1) :
    comparisonB u (6 / m) ≤ 1 := by
  have hb := comparisonB_le_endpoint hm hu hu1 (by nlinarith : 3 ≤ m * u * 1)
  simpa [comparisonB, comparisonDrop] using hb

theorem large_comparison_alpha {m u : ℝ} (hm : 6000 ≤ m)
    (hu0 : 0 < u) (hu1 : u < 1) :
    90 < m * ((comparisonB u (6 / m)) ^ 2 / comparisonD u (6 / m)) := by
  have hm0 : 0 < m := by linarith
  let b := comparisonB u (6 / m)
  let d := comparisonD u (6 / m)
  let α := b ^ 2 / d
  have hd : 0 < d := comparisonD_pos hu0 hu1.le (by positivity)
  have hdrop : 0 < comparisonDrop u (6 / m) := by
    unfold comparisonDrop
    positivity
  have hb : 0 < b := by dsimp [b, comparisonB]; positivity
  have hbu : u ≤ b := by dsimp [b, comparisonB]; linarith
  have hdrel : d = 2 * b - u := by dsimp [d, b, comparisonD, comparisonB]; ring
  have hαb : b / 2 ≤ α := by
    apply (le_div_iff₀ hd).mpr
    rw [hdrel]
    nlinarith [mul_pos hb hu0]
  have hαu : u ≤ α := by
    apply (le_div_iff₀ hd).mpr
    rw [hdrel]
    nlinarith [sq_nonneg (b - u)]
  have hbeq : b = u + 3 * (1 - u) / (m * u) := comparisonB_at_large_scale m u
  have hscaled : 2 * m * u * α ≥ m * u ^ 2 + 3 * (1 - u) := by
    have hmul := mul_le_mul_of_nonneg_left hαb (show 0 ≤ 2 * m * u by positivity)
    have he : (2 * m * u) * (b / 2) = m * u ^ 2 + 3 * (1 - u) := by
      rw [hbeq]
      field_simp
      <;> ring
    rw [he] at hmul
    nlinarith
  by_contra hn
  have hsmall : m * α ≤ 90 := le_of_not_gt hn
  have hmu : m * u ≤ 90 := (mul_le_mul_of_nonneg_left hαu hm0.le).trans hsmall
  have huhalf : u ≤ 1 / 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hm) hu0.le]
  have hupper := mul_le_mul_of_nonneg_left hsmall hu0.le
  have hquad := mul_nonneg (sub_nonneg.mpr hm) (sq_nonneg u)
  nlinarith [sq_nonneg (u - 3 / 200)]

end Schmeisser

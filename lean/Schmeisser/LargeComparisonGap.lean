import Schmeisser.LargeErrorBounds
import Schmeisser.ComparisonParameters

noncomputable section

namespace Schmeisser

open Set MeasureTheory

theorem large_baseline_remainder (m : ℕ) (hm : 6000 ≤ m) {u : ℝ}
    (hu0 : 0 < u) (hu1 : u < 1) (htu : 16 ≤ (m : ℝ) * u) :
    (1 / u - ((m : ℝ) + 1) * (∫ t in (0 : ℝ)..1, (1 - u * t) ^ m)) /
      errorScale m u < 1 / 1000 := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have heps : 1 - u ≠ 0 := by linarith
  have he : (1 / u - ((m : ℝ) + 1) * (∫ t in (0 : ℝ)..1, (1 - u * t) ^ m)) /
      errorScale m u = ((m : ℝ) * u) * (1 - u) ^ m := by
    rw [baseline_integral_eq m hu0.ne']
    unfold errorScale
    rw [pow_succ]
    field_simp
    <;> ring
  have hpow := one_sub_rpow_le_exp (r := (m : ℝ)) hu1 (by positivity)
  rw [Real.rpow_natCast] at hpow
  rw [he]
  refine (mul_le_mul_of_nonneg_left hpow (show 0 ≤ (m : ℝ) * u by positivity)).trans_lt ?_
  convert large_baseline_decay htu using 1 <;> congr 1 <;> ring

theorem large_comparison_endpoint (m : ℕ) (hm : 6000 ≤ m) {u : ℝ}
    (hu0 : 0 < u) (hu1 : u < 1) (htu : 16 ≤ (m : ℝ) * u) :
    (((m : ℝ) + 1) * comparisonTheta u (6 / (m : ℝ)) *
      (1 - u) ^ ((m : ℝ) / 2)) / errorScale m u < 1 / 20 := by
  have hmR : (6000 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
  have heps : 0 < 1 - u := by linarith
  have hs := errorScale_pos (by omega : 0 < m) hu0 hu1
  have hD := comparisonD_pos hu0 hu1.le (show 0 ≤ 6 / (m : ℝ) by positivity)
  have hθ : comparisonTheta u (6 / (m : ℝ)) ≤ 1 / 2 := by
    unfold comparisonTheta
    apply (div_le_iff₀ (show 0 < 2 * comparisonD u (6 / (m : ℝ)) by positivity)).mpr
    unfold comparisonD
    linarith
  have hp : (1 - u) ^ ((m : ℝ) / 2) =
      (1 - u) ^ ((m : ℝ) / 2 - 1) * (1 - u) := by
    calc
      _ = (1 - u) ^ (((m : ℝ) / 2 - 1) + 1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add heps, Real.rpow_one]
  have hpow := one_sub_rpow_le_exp (r := (m : ℝ) / 2 - 1) hu1 (by linarith)
  have he : (((m : ℝ) + 1) * (1 / 2) * (1 - u) ^ ((m : ℝ) / 2)) /
      errorScale m u = ((1 + 1 / (m : ℝ)) / 2) * ((m : ℝ) * u) ^ 2 *
        (1 - u) ^ ((m : ℝ) / 2 - 1) := by
    rw [hp]
    unfold errorScale
    field_simp
    <;> ring
  calc
    _ ≤ (((m : ℝ) + 1) * (1 / 2) * (1 - u) ^ ((m : ℝ) / 2)) / errorScale m u := by
      apply div_le_div_of_nonneg_right _ hs.le
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hθ (by positivity)) (Real.rpow_nonneg heps.le _)
    _ = _ := he
    _ ≤ ((1 + 1 / (m : ℝ)) / 2) * ((m : ℝ) * u) ^ 2 *
        Real.exp (-((m : ℝ) / 2 - 1) * u) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ < 1 / 20 := by
      convert large_endpoint_decay hmR htu using 1 <;> congr 1 <;> field_simp <;> ring

theorem comparison_moment_correction (m : ℕ) (hm : 0 < m) {u κ : ℝ}
    (hu0 : 0 < u) (hu1 : u < 1) (hκ : 0 ≤ κ) (hκ4 : κ / u ≤ 4) :
    (comparisonMinimum u κ * comparisonD u κ /
      ((m : ℝ) * (comparisonB u κ) ^ 3)) / errorScale m u ≤ 1 := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have heps : 0 < 1 - u := by linarith
  have hd := comparisonD_pos hu0 hu1.le hκ
  have hmin := comparisonMinimum_bounds hu0 hu1.le hκ hκ4
  have hdrop : 0 ≤ comparisonDrop u κ := by unfold comparisonDrop; positivity
  have hb : 0 < comparisonB u κ := by unfold comparisonB; positivity
  have hbu : u ≤ comparisonB u κ := by unfold comparisonB; linarith
  have hdrel : comparisonD u κ = 2 * comparisonB u κ - u := by
    unfold comparisonD comparisonB
    ring
  have hrat : u ^ 2 * comparisonD u κ / (comparisonB u κ) ^ 3 ≤ 1 := by
    apply (div_le_one (pow_pos hb 3)).mpr
    rw [hdrel]
    have hpoly : 0 ≤ (comparisonB u κ - u) *
        ((comparisonB u κ) ^ 2 + comparisonB u κ * u - u ^ 2) := by
      apply mul_nonneg (sub_nonneg.mpr hbu)
      nlinarith [mul_nonneg (sub_nonneg.mpr hbu) (add_nonneg hb.le hu0.le),
        mul_nonneg hb.le hu0.le]
    nlinarith
  have hrat0 : 0 ≤ u ^ 2 * comparisonD u κ / (comparisonB u κ) ^ 3 := by positivity
  have hminrat : comparisonMinimum u κ / (1 - u) ≤ 1 := (div_le_one heps).mpr hmin.2
  have hmin0 : 0 ≤ comparisonMinimum u κ / (1 - u) := div_nonneg hmin.1 heps.le
  have he : (comparisonMinimum u κ * comparisonD u κ /
      ((m : ℝ) * (comparisonB u κ) ^ 3)) / errorScale m u =
      (comparisonMinimum u κ / (1 - u)) *
        (u ^ 2 * comparisonD u κ / (comparisonB u κ) ^ 3) := by
    unfold errorScale
    field_simp
  rw [he]
  simpa only [one_mul] using mul_le_mul hminrat hrat hrat0 (by norm_num : (0 : ℝ) ≤ 1)

theorem large_comparison_b_gap (m : ℕ) (hm : 0 < m) {u : ℝ}
    (hu0 : 0 < u) (hu1 : u < 1) :
    (1 / u - 1 / comparisonB u (6 / (m : ℝ))) / errorScale m u =
      3 / comparisonB u (6 / (m : ℝ)) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have heps : 1 - u ≠ 0 := by linarith
  have hb : 0 < comparisonB u (6 / (m : ℝ)) := by
    unfold comparisonB comparisonDrop
    positivity
  have hbeq := comparisonB_at_large_scale (m : ℝ) u
  have he : (comparisonB u (6 / (m : ℝ)) - u) * ((m : ℝ) * u) = 3 * (1 - u) := by
    rw [hbeq]
    field_simp
    ring
  unfold errorScale
  field_simp
  nlinarith [he]

theorem large_comparison_gap (m : ℕ) (hm : 6000 ≤ m) {u : ℝ}
    (hu0 : 0 < u) (hu1 : u < 1) (htu : 16 ≤ (m : ℝ) * u)
    (hκ4 : (6 / (m : ℝ)) / u ≤ 4)
    (hR : comparisonIntegral m u (6 / (m : ℝ)) ≤
      1 / comparisonB u (6 / (m : ℝ)) +
      (11 / 10 : ℝ) * (comparisonMinimum u (6 / (m : ℝ)) * comparisonD u (6 / (m : ℝ)) /
        ((m : ℝ) * (comparisonB u (6 / (m : ℝ))) ^ 3)) +
      ((m : ℝ) + 1) * comparisonTheta u (6 / (m : ℝ)) * (1 - u) ^ ((m : ℝ) / 2)) :
    ((((m : ℝ) + 1) * (∫ t in (0 : ℝ)..1, (1 - u * t) ^ m)) -
      comparisonIntegral m u (6 / (m : ℝ))) / errorScale m u >
      3 / comparisonB u (6 / (m : ℝ)) - 11 / 10 - 1 / 20 - 1 / 1000 := by
  have hs := errorScale_pos (by omega : 0 < m) hu0 hu1
  have hb := large_comparison_b_gap m (by omega) hu0 hu1
  have hc := comparison_moment_correction m (by omega) hu0 hu1
    (show 0 ≤ 6 / (m : ℝ) by positivity) hκ4
  have he := large_comparison_endpoint m hm hu0 hu1 htu
  have hbase := large_baseline_remainder m hm hu0 hu1 htu
  have hRs := div_le_div_of_nonneg_right hR hs.le
  simp only [add_div, sub_div, mul_div_assoc] at hb hc he hbase hRs ⊢
  linarith

end Schmeisser

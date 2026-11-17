import Schmeisser.LargeComparisonGap

noncomputable section

namespace Schmeisser

open Set MeasureTheory

/-- The scalar exclusion in every critical-point count at least 6000. -/
theorem large_degree_scalar_exclusion {ι : Type*} [DecidableEq ι]
    (jset : Finset ι) (η : ι → ℂ) (m : ℕ) (hm : 6000 ≤ m) (hcard : jset.card = m)
    {u h : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (hh0 : 0 < h) (hh1 : h < 1)
    (hη : ∑ j ∈ jset, η j = 0)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (m : ℝ) * (u * (1 - u)))
    (hpolar : 1 ≤ ∫ t in (0 : ℝ)..1, (1 - h + h * (1 + u) * t) ^ ((m : ℝ) / 2)) :
    ((m : ℝ) + 1) * (∫ t in (0 : ℝ)..1,
      (max (1 - 2 * u * t + u * t ^ 2 - h * t * (1 - t)) 0) ^ ((m : ℝ) / 2)) <
      (((m : ℝ) + 1) * ∫ t in (0 : ℝ)..1, (1 - u * t) ^ m) -
        centeredErrorIntegral jset η m u := by
  have hmR : (6000 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm3 : (3 : ℝ) ≤ (m : ℝ) := by linarith
  have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
  have hthreshold := polar_integral_power_threshold hu0.le hh0 hh1.le
    (show 1 ≤ (m : ℝ) / 2 by linarith) hpolar
  have htu := degree_parameter_gt_sixteen hmR hu0 hthreshold
  have hdrop := polar_comparison_drop hm3 hu0 hu1.le hh0 hh1 hpolar
  have hα := large_comparison_alpha hmR hu0 hu1
  have hR := comparisonIntegral_sharp_bound m hu0 hu1.le
    (show 0 ≤ 6 / (m : ℝ) by positivity) hdrop.1.le hα.le
  have hgap := large_comparison_gap m hm hu0 hu1 htu.le hdrop.1.le
    (by simpa only [mul_div_assoc] using hR)
  have hs := errorScale_pos (by omega : 0 < m) hu0 hu1
  have hb0 : 0 < comparisonB u (6 / (m : ℝ)) := by
    unfold comparisonB comparisonDrop
    positivity
  have hstrict : comparisonIntegral m u (6 / (m : ℝ)) <
      (((m : ℝ) + 1) * ∫ t in (0 : ℝ)..1, (1 - u * t) ^ m) -
        centeredErrorIntegral jset η m u := by
    apply (div_lt_div_iff_of_pos_right hs).mp
    by_cases huhalf : u ≤ 1 / 2
    · have he := large_error_small jset η m hm hcard hu0 huhalf htu.le hη hV
      have hb := large_comparisonB_small hmR hu0 htu huhalf
      have hbi : (3 : ℝ) / (501 / 1000) ≤ 3 / comparisonB u (6 / (m : ℝ)) :=
        div_le_div_of_nonneg_left (by norm_num) hb0 hb.le
      simp only [sub_div] at hgap ⊢
      norm_num at hbi
      linarith
    · by_cases hu45 : u ≤ 4 / 5
      · have he := large_error_middle jset η m hm hcard (by linarith : 1 / 2 ≤ u) hu1 hη hV
        have hb := large_comparisonB_middle hmR hu0 htu hu45
        have hbi : (3 : ℝ) / (801 / 1000) ≤ 3 / comparisonB u (6 / (m : ℝ)) :=
          div_le_div_of_nonneg_left (by norm_num) hb0 hb.le
        simp only [sub_div] at hgap ⊢
        norm_num at hbi
        linarith
      · have he := large_error_top jset η m hm hcard (by linarith : 4 / 5 ≤ u) hu1 hη hV
        have hb := large_comparisonB_le_one hm0 hu0 htu hu1.le
        have hbi : (3 : ℝ) ≤ 3 / comparisonB u (6 / (m : ℝ)) := by
          simpa using div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 3) hb0 hb
        simp only [sub_div] at hgap ⊢
        linarith
  exact (second_integral_le_comparison m hu0 hu1.le
    (show 0 ≤ 6 / (m : ℝ) by positivity) hdrop.1.le hdrop.2.le).trans_lt hstrict

end Schmeisser

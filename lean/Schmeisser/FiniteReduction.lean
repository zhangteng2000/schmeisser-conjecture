import Schmeisser.ComparisonParameters
import Schmeisser.DecayBounds
import Schmeisser.NecessaryIntegrals

noncomputable section

namespace Schmeisser

open Set MeasureTheory

/-- The exact normalization used by every finite certificate. -/
theorem baseline_normalized_remainder (m : ℕ) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    (1 / u - ((m : ℝ) + 1) * (∫ t in (0 : ℝ)..1, (1 - u * t) ^ m)) / (1 - u) =
      (1 - u) ^ m / u := by
  rw [baseline_integral_eq m hu0.ne', pow_succ]
  have heps : 1 - u ≠ 0 := by linarith
  field_simp
  <;> ring

/-- A bound for the actual error, together with a strict certified lower
bound for the normalized quadratic integral, gives the scalar exclusion. -/
theorem scalar_exclusion_of_normalized_comparison {ι : Type*}
    (jset : Finset ι) (η : ι → ℂ) (m : ℕ) {u h κ e : ℝ}
    (hu0 : 0 < u) (hu1 : u < 1) (hκ0 : 0 ≤ κ) (hκ4 : κ / u ≤ 4)
    (hdrop : comparisonDrop u κ ≤ h)
    (herror : centeredErrorIntegral jset η m u / (1 - u) ≤ e)
    (hgap : e + (1 - u) ^ m / u < normalizedComparisonIntegral m u κ) :
    ((m : ℝ) + 1) * (∫ t in (0 : ℝ)..1,
      (max (1 - 2 * u * t + u * t ^ 2 - h * t * (1 - t)) 0) ^ ((m : ℝ) / 2)) <
      (((m : ℝ) + 1) * ∫ t in (0 : ℝ)..1, (1 - u * t) ^ m) -
        centeredErrorIntegral jset η m u := by
  have heps : 0 < 1 - u := by linarith
  have hbase := baseline_normalized_remainder m hu0 hu1
  have hR : comparisonIntegral m u κ <
      (((m : ℝ) + 1) * ∫ t in (0 : ℝ)..1, (1 - u * t) ^ m) -
        centeredErrorIntegral jset η m u := by
    apply (div_lt_div_iff_of_pos_right heps).mp
    unfold normalizedComparisonIntegral at hgap
    simp only [sub_div] at hbase hgap ⊢
    linarith
  exact (second_integral_le_comparison m hu0 hu1.le hκ0 hκ4 hdrop).trans_lt hR

theorem normalizedComparisonIntegral_three_lower {u κ b : ℝ}
    (hu0 : 0 < u) (hu1 : u < 1) (hκ0 : 0 ≤ κ) (hκ4 : κ / u ≤ 4)
    (hb : comparisonIntegral 1 u κ ≤ b) :
    1 / u + (κ / (2 * u * comparisonD u κ)) * (1 - (1 - u) ^ (3 / 2 : ℝ)) -
        (3 / 2 : ℝ) * (comparisonMinimum u κ / (1 - u)) * b ≤
      normalizedComparisonIntegral 3 u κ := by
  have heps : 0 < 1 - u := by linarith
  have hd := comparisonD_pos hu0 hu1.le hκ0
  have hmin := (comparisonMinimum_bounds hu0 hu1.le hκ0 hκ4).1
  have hrec := comparisonIntegral_recurrence 3 (by norm_num) hu0 hu1.le hκ0 hκ4
  norm_num at hrec
  have he : normalizedComparisonIntegral 3 u κ =
      1 / u + (κ / (2 * u * comparisonD u κ)) * (1 - (1 - u) ^ (3 / 2 : ℝ)) -
        (3 / 2 : ℝ) * (comparisonMinimum u κ / (1 - u)) * comparisonIntegral 1 u κ := by
    unfold normalizedComparisonIntegral
    rw [hrec, comparisonTheta_normalized]
    field_simp
    <;> ring
  rw [he]
  have hscale := mul_le_mul_of_nonneg_left hb
    (show 0 ≤ (3 / 2 : ℝ) * (comparisonMinimum u κ / (1 - u)) by positivity)
  linarith

end Schmeisser

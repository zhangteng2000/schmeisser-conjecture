import Schmeisser.QuadraticIntegrals

namespace Schmeisser

theorem normalizedComparisonIntegral_sharp_lower (m : ℕ)
    {u κ : ℝ} (hu : 0 < u) (hu1 : u < 1) (hκ : 0 ≤ κ) (hκ4 : κ / u ≤ 4)
    (hlarge : 90 ≤ (m : ℝ) * (comparisonB u κ ^ 2 / comparisonD u κ)) :
    κ / (2 * u ^ 2 * comparisonB u κ) -
      (11 / 10 : ℝ) * (comparisonMinimum u κ / (1 - u)) * comparisonD u κ /
        ((m : ℝ) * comparisonB u κ ^ 3) -
      ((m : ℝ) + 1) * (κ / (2 * u * comparisonD u κ)) * (1 - u) ^ ((m : ℝ) / 2) ≤
      normalizedComparisonIntegral m u κ := by
  have he : 0 < 1 - u := sub_pos.mpr hu1
  have hd := comparisonD_pos hu hu1.le hκ
  have hdrop : 0 ≤ comparisonDrop u κ := by
    unfold comparisonDrop
    positivity
  have hb : 0 < comparisonB u κ := by
    unfold comparisonB
    linarith
  have hR := comparisonIntegral_sharp_bound m hu hu1.le hκ hκ4 hlarge
  have hfirst : κ / (2 * u ^ 2 * comparisonB u κ) * (1 - u) =
      1 / u - 1 / comparisonB u κ := by
    field_simp
    unfold comparisonB comparisonDrop
    field_simp
    <;> ring
  apply (le_div_iff₀ he).mpr
  have halg :
      (κ / (2 * u ^ 2 * comparisonB u κ) -
        (11 / 10 : ℝ) * (comparisonMinimum u κ / (1 - u)) * comparisonD u κ /
          ((m : ℝ) * comparisonB u κ ^ 3) -
        ((m : ℝ) + 1) * (κ / (2 * u * comparisonD u κ)) * (1 - u) ^ ((m : ℝ) / 2)) *
        (1 - u) =
      1 / u - (1 / comparisonB u κ +
        (11 / 10 : ℝ) * (comparisonMinimum u κ * comparisonD u κ) /
          ((m : ℝ) * comparisonB u κ ^ 3) +
        ((m : ℝ) + 1) * comparisonTheta u κ * (1 - u) ^ ((m : ℝ) / 2)) := by
    rw [sub_mul, sub_mul, hfirst, comparisonTheta_normalized]
    field_simp
    <;> ring
  rw [halg]
  exact sub_le_sub_left hR (1 / u)

theorem normalizedComparisonIntegral_block_moment_lower (lo m hi : ℕ)
    (hlo : 0 < lo) (hlm : lo ≤ m) (hmh : m ≤ hi)
    {u κ : ℝ} (hu : 0 < u) (hu1 : u < 1) (hκ : 0 ≤ κ) (hκ4 : κ / u ≤ 4)
    (hlarge : 90 ≤ (lo : ℝ) * (comparisonB u κ ^ 2 / comparisonD u κ)) :
    κ / (2 * u ^ 2 * comparisonB u κ) -
      (11 / 10 : ℝ) * (comparisonMinimum u κ / (1 - u)) * comparisonD u κ /
        ((lo : ℝ) * comparisonB u κ ^ 3) -
      ((hi : ℝ) + 1) * (κ / (2 * u * comparisonD u κ)) * (1 - u) ^ ((lo : ℝ) / 2) ≤
      normalizedComparisonIntegral m u κ := by
  have hl0 : (0 : ℝ) < (lo : ℝ) := by exact_mod_cast hlo
  have hlmR : (lo : ℝ) ≤ (m : ℝ) := by exact_mod_cast hlm
  have hmhR : (m : ℝ) ≤ (hi : ℝ) := by exact_mod_cast hmh
  have hm0 : (0 : ℝ) < (m : ℝ) := hl0.trans_le hlmR
  have he : 0 < 1 - u := sub_pos.mpr hu1
  have hd := comparisonD_pos hu hu1.le hκ
  have hdrop : 0 ≤ comparisonDrop u κ := by
    unfold comparisonDrop
    positivity
  have hb : 0 < comparisonB u κ := by
    unfold comparisonB
    linarith
  have hmin := (comparisonMinimum_bounds hu hu1.le hκ hκ4).1
  have halpha : 0 ≤ comparisonB u κ ^ 2 / comparisonD u κ := by positivity
  have hlargeM : 90 ≤ (m : ℝ) * (comparisonB u κ ^ 2 / comparisonD u κ) :=
    hlarge.trans (mul_le_mul_of_nonneg_right hlmR halpha)
  have hbound := normalizedComparisonIntegral_sharp_lower m hu hu1 hκ hκ4 hlargeM
  have hden : (lo : ℝ) * comparisonB u κ ^ 3 ≤ (m : ℝ) * comparisonB u κ ^ 3 :=
    mul_le_mul_of_nonneg_right hlmR (by positivity)
  have hterm := div_le_div_of_nonneg_left
    (show 0 ≤ (11 / 10 : ℝ) * (comparisonMinimum u κ / (1 - u)) * comparisonD u κ by positivity)
    (show 0 < (lo : ℝ) * comparisonB u κ ^ 3 by positivity) hden
  have hpow : (1 - u) ^ ((m : ℝ) / 2) ≤ (1 - u) ^ ((lo : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_ge he (by linarith) (by linarith)
  have hcoeff : ((m : ℝ) + 1) * (κ / (2 * u * comparisonD u κ)) ≤
      ((hi : ℝ) + 1) * (κ / (2 * u * comparisonD u κ)) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have htail := mul_le_mul hcoeff hpow (Real.rpow_nonneg he.le _)
    (show 0 ≤ ((hi : ℝ) + 1) * (κ / (2 * u * comparisonD u κ)) by positivity)
  exact (sub_le_sub (sub_le_sub_left hterm _) htail).trans hbound

end Schmeisser

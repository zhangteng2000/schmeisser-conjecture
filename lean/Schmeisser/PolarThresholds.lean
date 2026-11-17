import Schmeisser.PolarCertification
import Schmeisser.ComparisonParameters
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

namespace Schmeisser

open Set MeasureTheory

theorem polar_threshold_squared (m : ℕ) (hm : 2 ≤ m) {u h : ℝ}
    (hu : 0 ≤ u) (hh0 : 0 < h) (hh1 : h ≤ 1)
    (hpolar : 1 ≤ ∫ t in (0 : ℝ)..1, (1 - h + h * (1 + u) * t) ^ ((m : ℝ) / 2)) :
    ((m : ℝ) + 2) ^ 2 ≤ 4 * (1 + u) ^ m := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hp := polar_integral_power_threshold hu hh0 hh1 (show 1 ≤ (m : ℝ) / 2 by linarith) hpolar
  have hnonneg : 0 ≤ (m : ℝ) / 2 + 1 := by positivity
  have hs := pow_le_pow_left₀ hnonneg hp 2
  have he : ((1 + u) ^ ((m : ℝ) / 2)) ^ 2 = (1 + u) ^ m := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity : 0 ≤ 1 + u)]
    simp only [Nat.cast_ofNat]
    rw [show (m : ℝ) / 2 * (2 : ℝ) = (m : ℝ) by ring, Real.rpow_natCast]
  rw [he] at hs
  nlinarith

theorem polar_threshold_for_block (lo m hi : ℕ) (hm : 2 ≤ m)
    (hlm : lo ≤ m) (hmh : m ≤ hi) {u h : ℝ}
    (hu : 0 ≤ u) (hh0 : 0 < h) (hh1 : h ≤ 1)
    (hpolar : 1 ≤ ∫ t in (0 : ℝ)..1, (1 - h + h * (1 + u) * t) ^ ((m : ℝ) / 2)) :
    ((lo : ℝ) + 2) ^ 2 ≤ 4 * (1 + u) ^ hi := by
  have hp := polar_threshold_squared m hm hu hh0 hh1 hpolar
  have hlmR : (lo : ℝ) ≤ (m : ℝ) := by exact_mod_cast hlm
  have hleft := pow_le_pow_left₀ (by positivity : 0 ≤ (lo : ℝ) + 2)
    (show (lo : ℝ) + 2 ≤ (m : ℝ) + 2 by linarith) 2
  have hright := pow_le_pow_right₀ (show (1 : ℝ) ≤ 1 + u by linarith) hmh
  nlinarith

theorem polar_default_drop_for_block (m hi : ℕ) (hm : 3 ≤ m) (hmh : m ≤ hi)
    {u h : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) (hh0 : 0 < h) (hh1 : h < 1)
    (hpolar : 1 ≤ ∫ t in (0 : ℝ)..1, (1 - h + h * (1 + u) * t) ^ ((m : ℝ) / 2)) :
    (6 / (hi : ℝ)) / u < 4 ∧ comparisonDrop u (6 / (hi : ℝ)) < h := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hmR : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmhR : (m : ℝ) ≤ (hi : ℝ) := by exact_mod_cast hmh
  have hκ : 6 / (hi : ℝ) ≤ 6 / (m : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) hm0 hmhR
  have hp := polar_comparison_drop hmR hu0 hu1 hh0 hh1 hpolar
  constructor
  · exact (div_le_div_of_nonneg_right hκ hu0.le).trans_lt hp.1
  · have hd : comparisonDrop u (6 / (hi : ℝ)) ≤ comparisonDrop u (6 / (m : ℝ)) := by
      unfold comparisonDrop
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hκ (by linarith : 0 ≤ 1 - u)) hu0.le
    exact hd.trans_lt hp.2

theorem polar_threshold_block_upper (m hi : ℕ) (hm : 2 ≤ m) (hmh : m ≤ hi)
    {u h : ℝ} (hu : 0 ≤ u) (hh0 : 0 < h) (hh1 : h ≤ 1)
    (hpolar : 1 ≤ ∫ t in (0 : ℝ)..1, (1 - h + h * (1 + u) * t) ^ ((m : ℝ) / 2)) :
    ((hi : ℝ) + 2) ^ 2 ≤ 4 * (1 + u) ^ hi := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
  have hmhR : (m : ℝ) ≤ (hi : ℝ) := by exact_mod_cast hmh
  have hratio : 1 ≤ (hi : ℝ) / (m : ℝ) := (one_le_div hm0).mpr hmhR
  have hbern := one_add_mul_self_le_rpow_one_add
    (by linarith : (-1 : ℝ) ≤ (m : ℝ) / 2) hratio
  have hthreshold := polar_integral_power_threshold hu hh0 hh1
    (show 1 ≤ (m : ℝ) / 2 by linarith) hpolar
  have hpow := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (m : ℝ) / 2 + 1)
    hthreshold (show 0 ≤ (hi : ℝ) / (m : ℝ) by positivity)
  have he : ((1 + u) ^ ((m : ℝ) / 2)) ^ ((hi : ℝ) / (m : ℝ)) =
      (1 + u) ^ ((hi : ℝ) / 2) := by
    rw [← Real.rpow_mul (by positivity : 0 ≤ 1 + u)]
    congr 1
    field_simp
  rw [he] at hpow
  have hleft : 1 + ((hi : ℝ) / (m : ℝ)) * ((m : ℝ) / 2) = (hi : ℝ) / 2 + 1 := by
    field_simp
    <;> ring
  rw [hleft, add_comm (1 : ℝ) ((m : ℝ) / 2)] at hbern
  have hhi := hbern.trans hpow
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ (hi : ℝ) / 2 + 1) hhi 2
  have hexp : ((1 + u) ^ ((hi : ℝ) / 2)) ^ 2 = (1 + u) ^ hi := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity : 0 ≤ 1 + u)]
    simp only [Nat.cast_ofNat]
    rw [show (hi : ℝ) / 2 * (2 : ℝ) = (hi : ℝ) by ring, Real.rpow_natCast]
  rw [hexp] at hs
  nlinarith

theorem polar_parameter_gt_of_block_threshold (m hi : ℕ) (hm : 2 ≤ m) (hmh : m ≤ hi)
    {u h τ : ℝ} (hu : 0 ≤ u) (hh0 : 0 < h) (hh1 : h ≤ 1)
    (hpolar : 1 ≤ ∫ t in (0 : ℝ)..1, (1 - h + h * (1 + u) * t) ^ ((m : ℝ) / 2))
    (htest : 4 * (1 + τ) ^ hi < ((hi : ℝ) + 2) ^ 2) :
    τ < u := by
  have hp := polar_threshold_block_upper m hi hm hmh hu hh0 hh1 hpolar
  by_contra hn
  have huτ : u ≤ τ := le_of_not_gt hn
  have hpow := pow_le_pow_left₀ (by linarith : 0 ≤ 1 + u)
    (by linarith : 1 + u ≤ 1 + τ) hi
  linarith

end Schmeisser

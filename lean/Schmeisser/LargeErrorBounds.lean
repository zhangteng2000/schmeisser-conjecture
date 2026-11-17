import Schmeisser.ErrorIntegrals
import Schmeisser.DecayBounds

noncomputable section

namespace Schmeisser

open Set MeasureTheory

def errorScale (m : ℕ) (u : ℝ) : ℝ := (1 - u) / ((m : ℝ) * u ^ 2)

theorem errorScale_pos {m : ℕ} {u : ℝ} (hm : 0 < m) (hu0 : 0 < u) (hu1 : u < 1) :
    0 < errorScale m u := by unfold errorScale; positivity

theorem large_error_front {ι : Type*} [DecidableEq ι]
    (jset : Finset ι) (η : ι → ℂ) (m : ℕ) (hm : 3 ≤ m) (hcard : jset.card = m)
    {u d : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (hd0 : 0 ≤ d) (hd1 : d < 1)
    (hη : ∑ j ∈ jset, η j = 0)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (m : ℝ) * (u * (1 - u))) :
    (((m : ℝ) + 1) * ∫ t in (0 : ℝ)..d, centeredErrorIntegrand jset η m u t) /
      errorScale m u < 40 / (3 * (2 - d) ^ 3) := by
  have hmR : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < (m : ℝ) := by positivity
  have hs := errorScale_pos (by omega : 0 < m) hu0 hu1
  have hf := centered_error_front_bound jset η m hm hcard hu0 hu1 hd0 hd1 hη hV
  have hratio : (m : ℝ) ^ 2 / (((m : ℝ) - 1) * ((m : ℝ) + 3)) < 1 := by
    apply (div_lt_one (mul_pos (by linarith : 0 < (m : ℝ) - 1) (by positivity))).mpr
    nlinarith
  have he :
      (40 * (m : ℝ) * (1 - u) /
        (3 * ((m : ℝ) - 1) * ((m : ℝ) + 3) * (2 - d) ^ 3 * u ^ 2)) / errorScale m u =
      (40 / (3 * (2 - d) ^ 3)) * ((m : ℝ) ^ 2 / (((m : ℝ) - 1) * ((m : ℝ) + 3))) := by
    unfold errorScale
    have heps : 1 - u ≠ 0 := by linarith
    field_simp
  have hc : 0 < 40 / (3 * (2 - d) ^ 3) := by
    have hd : 0 < 2 - d := by linarith
    positivity
  calc
    _ ≤ _ := div_le_div_of_nonneg_right hf hs.le
    _ = _ := he
    _ < _ := by simpa only [mul_one] using mul_lt_mul_of_pos_left hratio hc

theorem large_error_tail_small {ι : Type*}
    (jset : Finset ι) (η : ι → ℂ) (m : ℕ) (hm : 6000 ≤ m) (hcard : jset.card = m)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1 / 2) (htu : 16 ≤ (m : ℝ) * u)
    (hη : ∑ j ∈ jset, η j = 0)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (m : ℝ) * (u * (1 - u))) :
    (((m : ℝ) + 1) * ∫ t in (1 / 2 : ℝ)..1, centeredErrorIntegrand jset η m u t) /
      errorScale m u < 73 / 100 := by
  have hmR : (6000 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < (m : ℝ) := by positivity
  have hu : u < 1 := by linarith
  have hs := errorScale_pos (by omega : 0 < m) hu0 hu
  have ht := centered_error_tail_triangle jset η m (by omega) hcard hu0 hu
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1) hη hV
  let B := baseQuadratic u (1 / 2) ^ ((m : ℝ) / 2) + (1 - u * (1 / 2)) ^ m
  let E := Real.exp (-(3 * ((m : ℝ) * u) / 8)) + Real.exp (-(((m : ℝ) * u) / 2))
  have hb : B ≤ E := by
    have h1 := one_sub_rpow_le_exp (r := (m : ℝ) / 2)
      (by linarith : 3 * u / 4 < 1) (by positivity)
    have h2 := one_sub_rpow_le_exp (r := (m : ℝ))
      (by linarith : u / 2 < 1) (by positivity)
    rw [Real.rpow_natCast] at h2
    dsimp [B, E]
    have hq : baseQuadratic u (1 / 2) = 1 - 3 * u / 4 := by unfold baseQuadratic; ring
    rw [hq]
    convert add_le_add h1 h2 using 1 <;> congr 1 <;> ring
  have hB : 0 ≤ B := by
    dsimp [B]
    exact add_nonneg (Real.rpow_nonneg (baseQuadratic_pos hu0.le hu).le _)
      (pow_nonneg (by linarith) _)
  have hcoef : ((m : ℝ) + 1) * (m : ℝ) * u ^ 2 / (2 * (1 - u)) ≤
      (1 + 1 / (m : ℝ)) * ((m : ℝ) * u) ^ 2 := by
    have he : (1 + 1 / (m : ℝ)) * ((m : ℝ) * u) ^ 2 =
        ((m : ℝ) + 1) * (m : ℝ) * u ^ 2 := by field_simp
    rw [he]
    apply div_le_self (by positivity)
    linarith
  have he : (((m : ℝ) + 1) * (1 - (1 / 2 : ℝ)) * B) / errorScale m u =
      (((m : ℝ) + 1) * (m : ℝ) * u ^ 2 / (2 * (1 - u))) * B := by
    unfold errorScale
    have heps : 1 - u ≠ 0 := by linarith
    field_simp
    <;> ring
  calc
    _ ≤ (((m : ℝ) + 1) * (1 - (1 / 2 : ℝ)) * B) / errorScale m u :=
      div_le_div_of_nonneg_right ht hs.le
    _ = _ := he
    _ ≤ ((1 + 1 / (m : ℝ)) * ((m : ℝ) * u) ^ 2) * B :=
      mul_le_mul_of_nonneg_right hcoef hB
    _ ≤ ((1 + 1 / (m : ℝ)) * ((m : ℝ) * u) ^ 2) * E :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ < 73 / 100 := large_small_u_tail_decay hmR htu

theorem large_error_tail_large {ι : Type*} [DecidableEq ι]
    (jset : Finset ι) (η : ι → ℂ) (m : ℕ) (hm : 6000 ≤ m) (hcard : jset.card = m)
    {u d : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hdecay : 31 / 640 ≤ u * d * (2 - d) / 2)
    (hη : ∑ j ∈ jset, η j = 0)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (m : ℝ) * (u * (1 - u))) :
    (((m : ℝ) + 1) * ∫ t in d..1, centeredErrorIntegrand jset η m u t) /
      errorScale m u < 1 / 1000 := by
  have hmR : (6000 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < (m : ℝ) := by positivity
  have hs := errorScale_pos (by omega : 0 < m) hu0 hu1
  have ht := centered_error_tail_interpolation jset η m (by omega) hcard hu0 hu1 hd0 hd1 hη hV
  let B := baseQuadratic u d ^ (((m : ℝ) - 3) / 2)
  let E := Real.exp (-(31 * ((m : ℝ) - 3) / 640))
  have hB : 0 ≤ B := Real.rpow_nonneg (baseQuadratic_pos hu0.le hu1).le _
  have hb : B ≤ E := by
    have hdd : 0 ≤ d * (2 - d) := mul_nonneg hd0 (by linarith)
    have hdd1 : d * (2 - d) ≤ 1 := by nlinarith [sq_nonneg (1 - d)]
    have harg : u * d * (2 - d) < 1 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hu1.le) (sub_nonneg.mpr hdd1)]
    have hp := one_sub_rpow_le_exp harg (show 0 ≤ ((m : ℝ) - 3) / 2 by linarith)
    have hq : baseQuadratic u d = 1 - u * d * (2 - d) := by unfold baseQuadratic; ring
    dsimp [B, E]
    rw [hq]
    refine hp.trans (Real.exp_le_exp.mpr ?_)
    have hh := mul_le_mul_of_nonneg_right hdecay (show 0 ≤ (m : ℝ) - 3 by linarith)
    nlinarith
  have hufactor : (5 / 6 : ℝ) * u ^ 3 * (1 - d) ≤ 1 := by
    have hu3 : u ^ 3 ≤ (1 : ℝ) ^ 3 := pow_le_pow_left₀ hu0.le hu1.le 3
    have hu3pos : 0 ≤ u ^ 3 := by positivity
    have hd : 0 ≤ 1 - d := by linarith
    have hsmall := mul_le_mul_of_nonneg_left (show 1 - d ≤ 1 by linarith) hu3pos
    nlinarith
  have he : ((5 / 6 : ℝ) * ((m : ℝ) + 1) * (m : ℝ) * u * (1 - u) * (1 - d) * B) /
      errorScale m u = (((m : ℝ) + 1) * (m : ℝ) ^ 2) *
        ((5 / 6 : ℝ) * u ^ 3 * (1 - d)) * B := by
    unfold errorScale
    have heps : 1 - u ≠ 0 := by linarith
    field_simp
  calc
    _ ≤ ((5 / 6 : ℝ) * ((m : ℝ) + 1) * (m : ℝ) * u * (1 - u) * (1 - d) * B) /
        errorScale m u := div_le_div_of_nonneg_right ht hs.le
    _ = _ := he
    _ ≤ (((m : ℝ) + 1) * (m : ℝ) ^ 2) * B := by
      have hh := mul_le_mul_of_nonneg_left hufactor (show 0 ≤ ((m : ℝ) + 1) * (m : ℝ) ^ 2 by positivity)
      simpa only [mul_one] using mul_le_mul_of_nonneg_right hh hB
    _ ≤ (((m : ℝ) + 1) * (m : ℝ) ^ 2) * E := mul_le_mul_of_nonneg_left hb (by positivity)
    _ < 1 / 1000 := large_tiny_tail_decay hmR

theorem large_error_small {ι : Type*} [DecidableEq ι]
    (jset : Finset ι) (η : ι → ℂ) (m : ℕ) (hm : 6000 ≤ m) (hcard : jset.card = m)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1 / 2) (htu : 16 ≤ (m : ℝ) * u)
    (hη : ∑ j ∈ jset, η j = 0)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (m : ℝ) * (u * (1 - u))) :
    centeredErrorIntegral jset η m u / errorScale m u < 320 / 81 + 73 / 100 := by
  have hf := large_error_front jset η m (by omega) hcard hu0 (by linarith : u < 1)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1) hη hV
  have ht := large_error_tail_small jset η m hm hcard hu0 hu1 htu hη hV
  rw [centered_error_split jset η m u (1 / 2), add_div]
  norm_num at hf
  linarith

theorem large_error_middle {ι : Type*} [DecidableEq ι]
    (jset : Finset ι) (η : ι → ℂ) (m : ℕ) (hm : 6000 ≤ m) (hcard : jset.card = m)
    {u : ℝ} (hu0 : 1 / 2 ≤ u) (hu1 : u < 1)
    (hη : ∑ j ∈ jset, η j = 0)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (m : ℝ) * (u * (1 - u))) :
    centeredErrorIntegral jset η m u / errorScale m u < 2560 / 1029 + 1 / 1000 := by
  have hu : 0 < u := by linarith
  have hf := large_error_front jset η m (by omega) hcard hu hu1
    (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1) hη hV
  have ht := large_error_tail_large jset η m hm hcard hu hu1
    (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) ≤ 1)
    (by nlinarith : (31 / 640 : ℝ) ≤ u * (1 / 4) * (2 - 1 / 4) / 2) hη hV
  rw [centered_error_split jset η m u (1 / 4), add_div]
  norm_num at hf
  linarith

theorem large_error_top {ι : Type*} [DecidableEq ι]
    (jset : Finset ι) (η : ι → ℂ) (m : ℕ) (hm : 6000 ≤ m) (hcard : jset.card = m)
    {u : ℝ} (hu0 : 4 / 5 ≤ u) (hu1 : u < 1)
    (hη : ∑ j ∈ jset, η j = 0)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (m : ℝ) * (u * (1 - u))) :
    centeredErrorIntegral jset η m u / errorScale m u < 163840 / 89373 + 1 / 1000 := by
  have hu : 0 < u := by linarith
  have hf := large_error_front jset η m (by omega) hcard hu hu1
    (by norm_num : (0 : ℝ) ≤ 1 / 16) (by norm_num : (1 / 16 : ℝ) < 1) hη hV
  have ht := large_error_tail_large jset η m hm hcard hu hu1
    (by norm_num : (0 : ℝ) ≤ 1 / 16) (by norm_num : (1 / 16 : ℝ) ≤ 1)
    (by nlinarith : (31 / 640 : ℝ) ≤ u * (1 / 16) * (2 - 1 / 16) / 2) hη hV
  rw [centered_error_split jset η m u (1 / 16), add_div]
  norm_num at hf
  linarith

end Schmeisser

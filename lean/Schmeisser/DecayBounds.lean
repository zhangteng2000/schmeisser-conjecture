import Schmeisser.NumericalBounds

namespace Schmeisser

open Set MeasureTheory

theorem baseline_integral_eq (m : ℕ) {u : ℝ} (hu : u ≠ 0) :
    ((m : ℝ) + 1) * (∫ t in (0 : ℝ)..1, (1 - u * t) ^ m) =
      (1 - (1 - u) ^ (m + 1)) / u := by
  rw [intervalIntegral.integral_comp_sub_mul (fun t : ℝ ↦ t ^ m) hu 1]
  simp only [mul_one, mul_zero, sub_zero, smul_eq_mul, integral_pow, one_pow]
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  field_simp

theorem exp_neg_six_lt : Real.exp (-6 : ℝ) < 1 / 403 := by
  rw [Real.exp_neg, ← one_div]
  exact one_div_lt_one_div_of_lt (by norm_num) exp_six_gt_403

theorem exp_neg_eight_lt : Real.exp (-8 : ℝ) < 1 / 2980 := by
  rw [Real.exp_neg, ← one_div]
  exact one_div_lt_one_div_of_lt (by norm_num) exp_eight_gt_2980

theorem exp_neg_79_div_ten_lt : Real.exp (-(79 / 10) : ℝ) < 1 / 2600 := by
  rw [Real.exp_neg, ← one_div]
  exact one_div_lt_one_div_of_lt (by norm_num) exp_79_div_ten_gt_2600

theorem large_endpoint_decay {m t : ℝ} (hm : 6000 ≤ m) (ht : 16 ≤ t) :
    ((1 + 1 / m) / 2) * t ^ 2 * Real.exp (-((1 / 2) - 1 / m) * t) < 1 / 20 := by
  have hm0 : 0 < m := by linarith
  have hinv := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 6000) hm
  let c := (1 / 2 : ℝ) - 1 / m
  have hc : 0 < c := by dsimp [c]; linarith
  have hca : 2 ≤ c * 16 := by dsimp [c]; linarith
  have hmono := square_mul_exp_antitone (by norm_num : (0 : ℝ) ≤ 16) hc hca
  have hb := hmono (show (16 : ℝ) ∈ Ici 16 by simp) ht ht
  have hce : -c * 16 ≤ -(79 / 10 : ℝ) := by dsimp [c]; linarith
  have he : Real.exp (-c * 16) < 1 / 2600 :=
    (Real.exp_le_exp.mpr hce).trans_lt exp_neg_79_div_ten_lt
  have hp : 0 < (1 + 1 / m) / 2 := by positivity
  have hpup : (1 + 1 / m) / 2 ≤ (1 + 1 / 6000 : ℝ) / 2 := by linarith
  calc
    _ = ((1 + 1 / m) / 2) * (t ^ 2 * Real.exp (-c * t)) := by ring
    _ ≤ ((1 + 1 / m) / 2) * (16 ^ 2 * Real.exp (-c * 16)) :=
      mul_le_mul_of_nonneg_left hb hp.le
    _ < ((1 + 1 / m) / 2) * (16 ^ 2 * (1 / 2600)) := by
      apply mul_lt_mul_of_pos_left _ hp
      exact mul_lt_mul_of_pos_left he (by norm_num)
    _ ≤ ((1 + 1 / 6000 : ℝ) / 2) * (16 ^ 2 * (1 / 2600)) :=
      mul_le_mul_of_nonneg_right hpup (by norm_num)
    _ < 1 / 20 := by norm_num

theorem large_baseline_decay {t : ℝ} (ht : 16 ≤ t) :
    t * Real.exp (-t) < 1 / 1000 := by
  have hm := linear_mul_exp_antitone (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (1 : ℝ) ≤ 1 * 16)
  have hb := hm (show (16 : ℝ) ∈ Ici 16 by simp) ht ht
  simp only [neg_mul, one_mul] at hb
  exact hb.trans_lt sixteen_exp_neg_sixteen_lt

theorem large_small_u_tail_decay {m t : ℝ} (hm : 6000 ≤ m) (ht : 16 ≤ t) :
    (1 + 1 / m) * t ^ 2 * (Real.exp (-(3 * t / 8)) + Real.exp (-(t / 2))) <
      73 / 100 := by
  have hm0 : 0 < m := by linarith
  have hinv := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 6000) hm
  have h3 := square_mul_exp_antitone (by norm_num : (0 : ℝ) ≤ 16)
    (by norm_num : (0 : ℝ) < 3 / 8) (by norm_num : (2 : ℝ) ≤ (3 / 8) * 16)
  have h4 := square_mul_exp_antitone (by norm_num : (0 : ℝ) ≤ 16)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (2 : ℝ) ≤ (1 / 2) * 16)
  have hb3 := h3 (show (16 : ℝ) ∈ Ici 16 by simp) ht ht
  have hb4 := h4 (show (16 : ℝ) ∈ Ici 16 by simp) ht ht
  have hb : t ^ 2 * (Real.exp (-(3 * t / 8)) + Real.exp (-(t / 2))) <
      256 * ((1 / 403 : ℝ) + 1 / 2980) := by
    have he3 := mul_lt_mul_of_pos_left exp_neg_six_lt (by norm_num : (0 : ℝ) < 256)
    have he4 := mul_lt_mul_of_pos_left exp_neg_eight_lt (by norm_num : (0 : ℝ) < 256)
    norm_num at hb3 hb4
    have heq3 : -((3 / 8 : ℝ) * t) = -(3 * t / 8) := by ring
    have heq4 : -((1 / 2 : ℝ) * t) = -(t / 2) := by ring
    rw [heq3] at hb3
    rw [heq4] at hb4
    nlinarith
  calc
    _ = (1 + 1 / m) * (t ^ 2 * (Real.exp (-(3 * t / 8)) + Real.exp (-(t / 2)))) := by ring
    _ < (1 + 1 / m) * (256 * ((1 / 403 : ℝ) + 1 / 2980)) :=
      mul_lt_mul_of_pos_left hb (by positivity)
    _ ≤ (1 + 1 / 6000 : ℝ) * (256 * ((1 / 403 : ℝ) + 1 / 2980)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by norm_num)
    _ < 73 / 100 := by norm_num

theorem cube_mul_exp_shift_antitone {a c d : ℝ} (hc : 0 < c) (hca : 3 ≤ c * a) :
    AntitoneOn (fun t : ℝ ↦ t ^ 3 * Real.exp (-c * (t - d))) (Ici a) := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ ↦ t ^ 3 * Real.exp (-c * (t - d)))
      (t ^ 2 * (3 - c * t) * Real.exp (-c * (t - d))) t := by
    convert ((hasDerivAt_id t).pow 3).mul
      ((((hasDerivAt_id t).sub_const d).const_mul (-c)).exp) using 1
    · rfl
    · norm_num
      ring
  have hcont : Continuous (fun t : ℝ ↦ t ^ 3 * Real.exp (-c * (t - d))) := by fun_prop
  apply antitoneOn_of_deriv_nonpos (convex_Ici _) hcont.continuousOn
  · intro t _
    exact (hd t).differentiableAt.differentiableWithinAt
  · intro t ht
    have hat : a < t := by simpa using ht
    have hct : 3 ≤ c * t := hca.trans (mul_le_mul_of_nonneg_left hat.le hc.le)
    rw [(hd t).deriv]
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg t) (by linarith)) (Real.exp_pos _).le

theorem large_tiny_tail_decay {m : ℝ} (hm : 6000 ≤ m) :
    (m + 1) * m ^ 2 * Real.exp (-(31 * (m - 3) / 640)) < 1 / 1000 := by
  have hm0 : 0 ≤ m := by linarith
  have hmono := cube_mul_exp_shift_antitone (d := (4 : ℝ))
    (by norm_num : (0 : ℝ) < 31 / 640)
    (by norm_num : (3 : ℝ) ≤ (31 / 640) * 6001)
  have hb := hmono (show (6001 : ℝ) ∈ Ici 6001 by simp)
    (show m + 1 ∈ Ici 6001 by change 6001 ≤ m + 1; linarith)
    (by linarith : 6001 ≤ m + 1)
  have heq : -(31 / 640 : ℝ) * (m + 1 - 4) = -(31 * (m - 3) / 640) := by ring
  dsimp only at hb
  rw [heq] at hb
  have he : Real.exp (-(31 / 640 : ℝ) * (6001 - 4)) < 1 / (2 : ℝ) ^ 280 := by
    have htwo : (2 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9.trans' (by norm_num)
    have hp := pow_lt_pow_left₀ htwo (by norm_num : (0 : ℝ) ≤ 2) (by decide : (280 : ℕ) ≠ 0)
    rw [Real.exp_one_pow] at hp
    have hpinv := one_div_lt_one_div_of_lt (by positivity : (0 : ℝ) < 2 ^ 280) hp
    have hx : -(31 / 640 : ℝ) * (6001 - 4) ≤ -280 := by norm_num
    refine (Real.exp_le_exp.mpr hx).trans_lt ?_
    simpa only [Real.exp_neg, one_div, Nat.cast_ofNat] using hpinv
  have hpoly : (m + 1) * m ^ 2 ≤ (m + 1) ^ 3 := by nlinarith [sq_nonneg m]
  calc
    _ ≤ (m + 1) ^ 3 * Real.exp (-(31 * (m - 3) / 640)) :=
      mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
    _ ≤ (6001 : ℝ) ^ 3 * Real.exp (-(31 / 640 : ℝ) * (6001 - 4)) := hb
    _ < (6001 : ℝ) ^ 3 * (1 / (2 : ℝ) ^ 280) :=
      mul_lt_mul_of_pos_left he (by norm_num)
    _ < 1 / 1000 := by
      rw [one_div, mul_inv_lt_iff₀ (by positivity : (0 : ℝ) < 2 ^ 280)]
      have hp : (2 : ℝ) ^ 48 ≤ (2 : ℝ) ^ 280 :=
        pow_le_pow_right₀ (by norm_num) (by decide : (48 : ℕ) ≤ 280)
      exact (show (6001 : ℝ) ^ 3 < (1 / 1000 : ℝ) * (2 : ℝ) ^ 48 by norm_num).trans_le
        (mul_le_mul_of_nonneg_left hp (by norm_num))

theorem moment_tail_decay {t : ℝ} (ht : 90 ≤ t) :
    6 * t ^ 2 * Real.exp (-(t / 4)) < 1 / 1000 := by
  have hmono := square_mul_exp_antitone (by norm_num : (0 : ℝ) ≤ 90)
    (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (2 : ℝ) ≤ (1 / 4) * 90)
  have hb := hmono (show (90 : ℝ) ∈ Ici 90 by simp) ht ht
  have heq : -(1 / 4 : ℝ) * t = -(t / 4) := by ring
  dsimp only at hb
  rw [heq] at hb
  have he : Real.exp (-(1 / 4 : ℝ) * 90) < 1 / (5 / 2 : ℝ) ^ 22 := by
    have hbase : (5 / 2 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9.trans' (by norm_num)
    have hp := pow_lt_pow_left₀ hbase (by norm_num : (0 : ℝ) ≤ 5 / 2)
      (by decide : (22 : ℕ) ≠ 0)
    rw [Real.exp_one_pow] at hp
    have hinv := one_div_lt_one_div_of_lt (by positivity : (0 : ℝ) < (5 / 2) ^ 22) hp
    refine (Real.exp_le_exp.mpr (by norm_num : -(1 / 4 : ℝ) * 90 ≤ -22)).trans_lt ?_
    simpa only [Real.exp_neg, one_div, Nat.cast_ofNat] using hinv
  have h1 := mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 6)
  have h2 := mul_lt_mul_of_pos_left he (by norm_num : (0 : ℝ) < 6 * 90 ^ 2)
  have hn : (6 : ℝ) * 90 ^ 2 * (1 / (5 / 2 : ℝ) ^ 22) < 1 / 1000 := by norm_num
  nlinarith

end Schmeisser

import Schmeisser.PolarLowerBound
import Mathlib.Analysis.Complex.ExponentialBounds

namespace Schmeisser

open Set

theorem exp_three_quarters_lt : Real.exp (3 / 4 : ℝ) < 5 / 2 := by
  have hq : Real.exp (1 / 4 : ℝ) ≤ 4 / 3 := by
    have h := Real.exp_bound_div_one_sub_of_interval
      (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1)
    norm_num at h ⊢
    exact h
  have hp := pow_le_pow_left₀ (Real.exp_pos (1 / 4 : ℝ)).le hq 3
  have he : Real.exp (3 / 4 : ℝ) = Real.exp (1 / 4 : ℝ) ^ 3 := by
    convert Real.exp_nat_mul (1 / 4 : ℝ) 3 using 1 <;> norm_num
  rw [he]
  exact hp.trans_lt (by norm_num)

theorem exp_eight_lt_3001 : Real.exp (8 : ℝ) < 3001 := by
  have he : Real.exp (1 : ℝ) < 87 / 32 := Real.exp_one_lt_d9.trans (by norm_num)
  have hp := pow_lt_pow_left₀ he (Real.exp_pos 1).le (by decide : (8 : ℕ) ≠ 0)
  rw [Real.exp_one_pow] at hp
  exact hp.trans (by norm_num)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem exp_six_gt_403 : (403 : ℝ) < Real.exp 6 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 6) 33
  have hn : (403 : ℝ) < ∑ i ∈ Finset.range 33, (6 : ℝ) ^ i / i.factorial := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  exact hn.trans_le h

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem exp_eight_gt_2980 : (2980 : ℝ) < Real.exp 8 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 8) 33
  have hn : (2980 : ℝ) < ∑ i ∈ Finset.range 33, (8 : ℝ) ^ i / i.factorial := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  exact hn.trans_le h

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem exp_79_div_ten_gt_2600 : (2600 : ℝ) < Real.exp (79 / 10) := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 79 / 10) 33
  have hn : (2600 : ℝ) < ∑ i ∈ Finset.range 33, (79 / 10 : ℝ) ^ i / i.factorial := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  exact hn.trans_le h

theorem sixteen_exp_neg_sixteen_lt : (16 : ℝ) * Real.exp (-16) < 1 / 1000 := by
  have hh : Real.exp (16 : ℝ) = Real.exp 8 ^ 2 := by
    convert Real.exp_nat_mul (8 : ℝ) 2 using 1 <;> norm_num
  have he := exp_eight_gt_2980
  rw [Real.exp_neg, hh]
  apply (mul_inv_lt_iff₀ (pow_pos (Real.exp_pos 8) 2)).mpr
  nlinarith

theorem degree_parameter_log_bound {m u : ℝ} (hm : 0 < m) (hu : 0 < u)
    (hthreshold : m / 2 + 1 ≤ (1 + u) ^ (m / 2)) :
    2 * Real.log (m / 2 + 1) < m * u := by
  have hlog := Real.log_le_log (by positivity : 0 < m / 2 + 1) hthreshold
  rw [Real.log_rpow (by positivity : 0 < 1 + u)] at hlog
  have hstrict := Real.log_lt_sub_one_of_pos (by positivity : 0 < 1 + u)
    (by linarith : 1 + u ≠ 1)
  nlinarith

theorem degree_parameter_gt_three_halves {m u : ℝ} (hm : 3 ≤ m) (hu : 0 < u)
    (hthreshold : m / 2 + 1 ≤ (1 + u) ^ (m / 2)) :
    3 / 2 < m * u := by
  have hlow : (3 / 4 : ℝ) < Real.log (5 / 2) :=
    (Real.lt_log_iff_exp_lt (by norm_num)).mpr exp_three_quarters_lt
  have hmono := Real.log_le_log (by norm_num : (0 : ℝ) < 5 / 2)
    (by linarith : (5 / 2 : ℝ) ≤ m / 2 + 1)
  have hlog := degree_parameter_log_bound (by linarith : 0 < m) hu hthreshold
  linarith

theorem degree_parameter_gt_sixteen {m u : ℝ} (hm : 6000 ≤ m) (hu : 0 < u)
    (hthreshold : m / 2 + 1 ≤ (1 + u) ^ (m / 2)) :
    16 < m * u := by
  have hlow : (8 : ℝ) < Real.log 3001 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).mpr exp_eight_lt_3001
  have hmono := Real.log_le_log (by norm_num : (0 : ℝ) < 3001)
    (by linarith : (3001 : ℝ) ≤ m / 2 + 1)
  have hlog := degree_parameter_log_bound (by linarith : 0 < m) hu hthreshold
  linarith

theorem one_sub_rpow_le_exp {x r : ℝ} (hx : x < 1) (hr : 0 ≤ r) :
    (1 - x) ^ r ≤ Real.exp (-r * x) := by
  have hb : 0 < 1 - x := by linarith
  rw [Real.rpow_def_of_pos hb]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_right (Real.log_le_sub_one_of_pos hb) hr
  nlinarith

theorem square_mul_exp_antitone {a c : ℝ} (ha : 0 ≤ a) (hc : 0 < c)
    (hca : 2 ≤ c * a) :
    AntitoneOn (fun t : ℝ ↦ t ^ 2 * Real.exp (-c * t)) (Ici a) := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ ↦ t ^ 2 * Real.exp (-c * t))
      (t * (2 - c * t) * Real.exp (-c * t)) t := by
    convert ((hasDerivAt_id t).pow 2).mul (((hasDerivAt_id t).const_mul (-c)).exp) using 1
    · rfl
    · norm_num
      ring
  have hcont : Continuous (fun t : ℝ ↦ t ^ 2 * Real.exp (-c * t)) := by fun_prop
  apply antitoneOn_of_deriv_nonpos (convex_Ici _) hcont.continuousOn
  · intro t _
    exact (hd t).differentiableAt.differentiableWithinAt
  · intro t ht
    have hat : a < t := by simpa using ht
    have ht0 := ha.trans hat.le
    have hct : 2 ≤ c * t := hca.trans (mul_le_mul_of_nonneg_left hat.le hc.le)
    rw [(hd t).deriv]
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos ht0 (by linarith)) (Real.exp_pos _).le

theorem linear_mul_exp_antitone {a c : ℝ} (hc : 0 < c) (hca : 1 ≤ c * a) :
    AntitoneOn (fun t : ℝ ↦ t * Real.exp (-c * t)) (Ici a) := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ ↦ t * Real.exp (-c * t))
      ((1 - c * t) * Real.exp (-c * t)) t := by
    convert (hasDerivAt_id t).mul (((hasDerivAt_id t).const_mul (-c)).exp) using 1
    · rfl
    · norm_num
      ring
  have hcont : Continuous (fun t : ℝ ↦ t * Real.exp (-c * t)) := by fun_prop
  apply antitoneOn_of_deriv_nonpos (convex_Ici _) hcont.continuousOn
  · intro t _
    exact (hd t).differentiableAt.differentiableWithinAt
  · intro t ht
    have hat : a < t := by simpa using ht
    have hct : 1 ≤ c * t := hca.trans (mul_le_mul_of_nonneg_left hat.le hc.le)
    rw [(hd t).deriv]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.exp_pos _).le

end Schmeisser

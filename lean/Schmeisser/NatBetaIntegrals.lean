import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Tactic

open MeasureTheory Set

namespace Schmeisser

theorem beta_nat_integral_recurrence (k l : ℕ) :
    ((l : ℝ) + 1) * (∫ t : ℝ in 0..1, t ^ (k + 1) * (1 - t) ^ l) =
      ((k : ℝ) + 1) * (∫ t : ℝ in 0..1, t ^ k * (1 - t) ^ (l + 1)) := by
  let F : ℝ → ℝ := fun t => t ^ (k + 1) * (1 - t) ^ (l + 1)
  let f : ℝ → ℝ := fun t =>
    ((k : ℝ) + 1) * (t ^ k * (1 - t) ^ (l + 1)) -
      ((l : ℝ) + 1) * (t ^ (k + 1) * (1 - t) ^ l)
  have hf (t : ℝ) : HasDerivAt F (f t) t := by
    have h1 := (hasDerivAt_id t).pow (k + 1)
    have h2 := ((hasDerivAt_id t).const_sub 1).pow (l + 1)
    convert h1.mul h2 using 1
    · rfl
    · simp [f]
      ring
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := (1 : ℝ))
    (fun t ht => hf t) ((show Continuous f by dsimp [f]; fun_prop).intervalIntegrable 0 1)
  have hzero : F 1 - F 0 = 0 := by simp [F]
  rw [hzero] at hint
  dsimp [f] at hint
  rw [intervalIntegral.integral_sub,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hint
  · linarith
  · exact (show Continuous (fun t : ℝ =>
      ((k : ℝ) + 1) * (t ^ k * (1 - t) ^ (l + 1))) by fun_prop).intervalIntegrable 0 1
  · exact (show Continuous (fun t : ℝ =>
      ((l : ℝ) + 1) * (t ^ (k + 1) * (1 - t) ^ l)) by fun_prop).intervalIntegrable 0 1

theorem beta_nat_integral (k l : ℕ) :
    (∫ t : ℝ in 0..1, t ^ k * (1 - t) ^ l) =
      (k.factorial : ℝ) * (l.factorial : ℝ) / ((k + l + 1).factorial : ℝ) := by
  induction k generalizing l with
  | zero =>
      have h : (∫ t : ℝ in 0..1, (1 - t) ^ l) = 1 / ((l : ℝ) + 1) := by
        calc
          _ = ∫ t : ℝ in 0..1, t ^ l := by
            simpa using intervalIntegral.integral_comp_sub_left (fun t : ℝ => t ^ l)
              (a := (0 : ℝ)) (b := (1 : ℝ)) 1
          _ = _ := by rw [integral_pow]; simp
      simp only [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, Nat.zero_add]
      rw [h, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      field_simp
  | succ k ih =>
      have h := beta_nat_integral_recurrence k l
      rw [ih] at h
      have hl : (l : ℝ) + 1 ≠ 0 := by positivity
      have hf : ((k + (l + 1) + 1).factorial : ℝ) ≠ 0 := by positivity
      apply (mul_left_cancel₀ hl)
      rw [h]
      rw [Nat.factorial_succ l, Nat.factorial_succ k]
      push_cast
      have heq : k + 1 + l + 1 = k + (l + 1) + 1 := by omega
      rw [heq]
      field_simp

theorem beta_nat_integral_choose (m k : ℕ) (hkm : k ≤ m) :
    ((m : ℝ) + 1) * (m.choose k : ℝ) *
      (∫ t : ℝ in 0..1, t ^ k * (1 - t) ^ (m - k)) = 1 := by
  rw [beta_nat_integral, Nat.add_sub_of_le hkm]
  have hfac : (m.choose k : ℝ) * (k.factorial : ℝ) * ((m - k).factorial : ℝ) =
      (m.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkm
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  have hf : (m.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  exact hfac

theorem scaled_beta_nat_integral_le (k l : ℕ) {u : ℝ}
    (hu0 : 0 < u) (hu1 : u ≤ 1) :
    u ^ (k + 1) * (∫ t : ℝ in 0..1, t ^ k * (1 - u * t) ^ l) ≤
      (∫ t : ℝ in 0..1, t ^ k * (1 - t) ^ l) := by
  let f : ℝ → ℝ := fun t => t ^ k * (1 - t) ^ l
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hchange := intervalIntegral.smul_integral_comp_mul_left f
    (a := (0 : ℝ)) (b := (1 : ℝ)) u
  simp only [smul_eq_mul, mul_zero, mul_one] at hchange
  have hfun : (fun t : ℝ => f (u * t)) =
      fun t => u ^ k * (t ^ k * (1 - u * t) ^ l) := by
    funext t
    dsimp [f]
    ring
  rw [hfun, intervalIntegral.integral_const_mul] at hchange
  have hleft : u ^ (k + 1) * (∫ t : ℝ in 0..1, t ^ k * (1 - u * t) ^ l) =
      ∫ t : ℝ in 0..u, f t := by
    rw [← hchange, pow_succ]
    ring
  rw [hleft]
  apply intervalIntegral.integral_mono_interval (show (0 : ℝ) ≤ 0 by rfl) hu0.le hu1
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact mul_nonneg (pow_nonneg ht.1.le _) (pow_nonneg (sub_nonneg.mpr ht.2) _)
  · exact hf.intervalIntegrable 0 1

theorem scaled_beta_nat_integral_choose_le (m k : ℕ) (hkm : k ≤ m) {u : ℝ}
    (hu0 : 0 < u) (hu1 : u ≤ 1) :
    ((m : ℝ) + 1) * (∫ t : ℝ in 0..1, t ^ k * (1 - u * t) ^ (m - k)) ≤
      1 / ((m.choose k : ℝ) * u ^ (k + 1)) := by
  have hc : (0 : ℝ) < m.choose k := by exact_mod_cast Nat.choose_pos hkm
  have h := mul_le_mul_of_nonneg_left
    (scaled_beta_nat_integral_le k (m - k) hu0 hu1)
    (show 0 ≤ ((m : ℝ) + 1) * (m.choose k : ℝ) by positivity)
  rw [← mul_assoc, beta_nat_integral_choose m k hkm] at h
  apply (le_div_iff₀ (show 0 < (m.choose k : ℝ) * u ^ (k + 1) by positivity)).mpr
  nlinarith only [h]

end Schmeisser

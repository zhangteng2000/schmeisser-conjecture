import Schmeisser.ScalarIntegrals

namespace Schmeisser

open Set MeasureTheory

/-- The elementary beta integral needed for the front part of the error. -/
theorem integral_sq_one_sub_rpow {r : ℝ} (hr : 0 ≤ r) :
    (∫ t in (0 : ℝ)..1, t ^ 2 * (1 - t) ^ r) =
      2 / ((r + 1) * (r + 2) * (r + 3)) := by
  have hc (s : ℝ) (hs : 0 ≤ s) : Continuous (fun t : ℝ ↦ t ^ s) :=
    Real.continuous_rpow_const hs
  calc
    (∫ t in (0 : ℝ)..1, t ^ 2 * (1 - t) ^ r) =
        ∫ t in (0 : ℝ)..1, (1 - t) ^ 2 * t ^ r := by
      have h := intervalIntegral.integral_comp_sub_left
        (fun t : ℝ ↦ (1 - t) ^ 2 * t ^ r) (a := 0) (b := 1) 1
      simpa using h
    _ = ∫ t in (0 : ℝ)..1, (t ^ r - 2 * t ^ (r + 1) + t ^ (r + 2)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht0 : 0 ≤ t := by simpa using ht.1
      dsimp only
      rw [Real.rpow_add_of_nonneg ht0 hr (by norm_num : (0 : ℝ) ≤ 1),
        Real.rpow_add_of_nonneg ht0 hr (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_one, Real.rpow_two]
      ring
    _ = 1 / (r + 1) - 2 * (1 / (r + 2)) + 1 / (r + 3) := by
      rw [intervalIntegral.integral_add
        (((hc r hr).intervalIntegrable 0 1).sub
          (((hc (r + 1) (by linarith)).intervalIntegrable 0 1).const_mul 2))
        ((hc (r + 2) (by linarith)).intervalIntegrable 0 1)]
      rw [intervalIntegral.integral_sub ((hc r hr).intervalIntegrable 0 1)
        (((hc (r + 1) (by linarith)).intervalIntegrable 0 1).const_mul 2)]
      rw [intervalIntegral.integral_const_mul,
        integral_rpow_zero_one (by linarith : -1 < r),
        integral_rpow_zero_one (by linarith : -1 < r + 1),
        integral_rpow_zero_one (by linarith : -1 < r + 2)]
      congr 2 <;> ring
    _ = _ := by
      have h1 : r + 1 ≠ 0 := by linarith
      have h2 : r + 2 ≠ 0 := by linarith
      have h3 : r + 3 ≠ 0 := by linarith
      field_simp
      ring

theorem integral_sq_one_sub_mul_rpow {r c : ℝ} (hr : 0 ≤ r) (hc : 0 < c) :
    (∫ t in (0 : ℝ)..(1 / c), t ^ 2 * (1 - c * t) ^ r) =
      2 / (c ^ 3 * (r + 1) * (r + 2) * (r + 3)) := by
  calc
    (∫ t in (0 : ℝ)..(1 / c), t ^ 2 * (1 - c * t) ^ r) =
        c⁻¹ ^ 2 * ∫ t in (0 : ℝ)..(1 / c),
          (c * t) ^ 2 * (1 - c * t) ^ r := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      field_simp
    _ = c⁻¹ ^ 2 * (c⁻¹ * (2 / ((r + 1) * (r + 2) * (r + 3)))) := by
      rw [intervalIntegral.integral_comp_mul_left
        (fun t : ℝ ↦ t ^ 2 * (1 - t) ^ r) hc.ne']
      simp only [mul_zero, mul_one_div_cancel hc.ne', smul_eq_mul,
        integral_sq_one_sub_rpow hr]
    _ = _ := by
      simp only [mul_inv_rev, inv_pow, div_eq_mul_inv]
      ring

theorem integral_sq_one_sub_mul_rpow_le {r c d : ℝ} (hr : 0 ≤ r) (hc : 0 < c)
    (hd0 : 0 ≤ d) (hdc : d ≤ 1 / c) :
    (∫ t in (0 : ℝ)..d, t ^ 2 * (1 - c * t) ^ r) ≤
      2 / (c ^ 3 * (r + 1) * (r + 2) * (r + 3)) := by
  rw [← integral_sq_one_sub_mul_rpow hr hc]
  have hcont : Continuous (fun t : ℝ ↦ t ^ 2 * (1 - c * t) ^ r) :=
    (continuous_id.pow 2).mul ((Real.continuous_rpow_const hr).comp (by fun_prop))
  apply intervalIntegral.integral_mono_interval le_rfl hd0 hdc _
    (hcont.intervalIntegrable 0 (1 / c))
  apply (ae_restrict_iff' measurableSet_Ioc).mpr
  apply Filter.Eventually.of_forall
  intro t ht
  have ht1 : c * t ≤ 1 := by
    have hh := (le_div_iff₀ hc).mp ht.2
    nlinarith
  exact mul_nonneg (sq_nonneg t) (Real.rpow_nonneg (by linarith) _)

end Schmeisser

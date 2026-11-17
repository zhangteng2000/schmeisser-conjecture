import Schmeisser.Hyperbolic
import Schmeisser.ScalarIntegrals

namespace Schmeisser

open Real Set MeasureTheory

theorem integral_centered_exp {z : ℝ} (hz : z ≠ 0) :
    (∫ t in (0 : ℝ)..1, Real.exp (z * (2 * t - 1))) = Real.sinh z / z := by
  calc
    (∫ t in (0 : ℝ)..1, Real.exp (z * (2 * t - 1))) =
        ∫ t in (0 : ℝ)..1, Real.exp ((2 * z) * t - z) := by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      congr 1
      ring
    _ = (2 * z)⁻¹ * (Real.exp z - Real.exp (-z)) := by
      rw [intervalIntegral.integral_comp_mul_sub Real.exp (mul_ne_zero (by norm_num) hz)]
      simp only [mul_zero, zero_sub, mul_one, smul_eq_mul]
      have hh : 2 * z - z = z := by ring
      rw [hh, integral_exp]
    _ = Real.sinh z / z := by
      rw [Real.sinh_eq]
      field_simp

theorem integral_polar_exp {l u : ℝ} (hl : 0 < l) (hu : 0 ≤ u) :
    (∫ t in (0 : ℝ)..1, Real.exp (l * ((1 + u) * t - 1))) =
      Real.exp (-(l * (1 - u) / 2)) *
        (Real.sinh (l * (1 + u) / 2) / (l * (1 + u) / 2)) := by
  have hz : l * (1 + u) / 2 ≠ 0 := ne_of_gt (by positivity)
  calc
    (∫ t in (0 : ℝ)..1, Real.exp (l * ((1 + u) * t - 1))) =
        ∫ t in (0 : ℝ)..1, Real.exp (-(l * (1 - u) / 2)) *
          Real.exp ((l * (1 + u) / 2) * (2 * t - 1)) := by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      rw [← Real.exp_add]
      congr 1
      ring
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, integral_centered_exp hz]

theorem polar_integral_lt_exponential {u h r : ℝ}
    (hu : 0 ≤ u) (hh0 : 0 < h) (hh1 : h < 1) (hr : 0 < r) :
    (∫ t in (0 : ℝ)..1, (1 - h + h * (1 + u) * t) ^ r) <
      ∫ t in (0 : ℝ)..1, Real.exp ((r * h) * ((1 + u) * t - 1)) := by
  let f : ℝ → ℝ := fun t ↦ (1 - h + h * (1 + u) * t) ^ r
  let g : ℝ → ℝ := fun t ↦ Real.exp ((r * h) * ((1 + u) * t - 1))
  have hf : Continuous f := (Real.continuous_rpow_const hr.le).comp (by fun_prop)
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hpos (t : ℝ) (ht : 0 ≤ t) : 0 < 1 - h + h * (1 + u) * t := by
    have hp : 0 ≤ h * (1 + u) * t := by positivity
    linarith
  have hle : ∀ t ∈ Ioc (0 : ℝ) 1, f t ≤ g t := by
    intro t ht
    have hl := Real.log_le_sub_one_of_pos (hpos t ht.1.le)
    dsimp [f, g]
    rw [Real.rpow_def_of_pos (hpos t ht.1.le)]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hstrict : f 0 < g 0 := by
    have hl := Real.log_lt_sub_one_of_pos (by linarith : 0 < 1 - h)
      (by linarith : 1 - h ≠ 1)
    dsimp [f, g]
    simp only [mul_zero, add_zero, zero_sub]
    rw [Real.rpow_def_of_pos (by linarith : 0 < 1 - h)]
    apply Real.exp_lt_exp.mpr
    nlinarith
  exact intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (by norm_num) hf.continuousOn hg.continuousOn hle ⟨0, by norm_num, hstrict⟩

/-- The strict product bound implied by the first necessary integral
inequality. With `r = (n-1)/2`, this is `(n-1)*h*u > 6*(1-u)`. -/
theorem polar_integral_product_lower_bound {u h r : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hh0 : 0 < h) (hh1 : h < 1) (hr : 0 < r)
    (hpolar : 1 ≤ ∫ t in (0 : ℝ)..1, (1 - h + h * (1 + u) * t) ^ r) :
    3 * (1 - u) < r * h * u := by
  let l := r * h
  let z := l * (1 + u) / 2
  have hl : 0 < l := mul_pos hr hh0
  have hz : 0 < z := by dsimp [z]; positivity
  have hstrict : 1 < Real.exp (-(l * (1 - u) / 2)) * (Real.sinh z / z) := by
    have hi := hpolar.trans_lt (polar_integral_lt_exponential hu0 hh0 hh1 hr)
    rw [integral_polar_exp hl hu0] at hi
    exact hi
  have hq : 0 < Real.sinh z / z := div_pos (Real.sinh_pos_iff.mpr hz) hz
  have hlog := Real.log_lt_log (by norm_num : (0 : ℝ) < 1) hstrict
  rw [Real.log_one, Real.log_mul (Real.exp_pos _).ne' hq.ne', Real.log_exp] at hlog
  have hmajor := log_sinh_div_le_sqrt hz
  have hsqrt : l * (1 - u) / 2 + 3 < Real.sqrt (z ^ 2 + 9) := by linarith
  have hleft : 0 ≤ l * (1 - u) / 2 + 3 := by positivity
  have hsquare : (l * (1 - u) / 2 + 3) ^ 2 < z ^ 2 + 9 := by
    have hs := (sq_lt_sq₀ hleft (Real.sqrt_nonneg _)).mpr hsqrt
    rwa [Real.sq_sqrt (by positivity : 0 ≤ z ^ 2 + 9)] at hs
  dsimp [z] at hsquare
  change 3 * (1 - u) < l * u
  nlinarith

end Schmeisser

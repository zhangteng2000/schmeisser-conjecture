import Schmeisser.IntegralComparison
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace Schmeisser

open Set MeasureTheory

theorem integral_rpow_zero_one {r : ℝ} (hr : -1 < r) :
    (∫ t in (0 : ℝ)..1, t ^ r) = 1 / (r + 1) := by
  have h := integral_rpow (a := (0 : ℝ)) (b := (1 : ℝ)) (Or.inl hr)
  simpa [Real.zero_rpow (by linarith : r + 1 ≠ 0)] using h

theorem polar_integral_upper_bound {u h r : ℝ}
    (hu : 0 ≤ u) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hr : 1 ≤ r) :
    (∫ t in (0 : ℝ)..1, (1 - h + h * (1 + u) * t) ^ r) ≤
      (1 - h) + h * ((1 + u) ^ r / (r + 1)) := by
  have hr0 : 0 ≤ r := by linarith
  have hc : Continuous (fun t : ℝ ↦ (1 - h + h * (1 + u) * t) ^ r) :=
    (Real.continuous_rpow_const hr0).comp (by fun_prop)
  have hb : Continuous (fun t : ℝ ↦ (1 - h) + h * ((1 + u) ^ r * t ^ r)) := by
    exact continuous_const.add (continuous_const.mul
      (continuous_const.mul (Real.continuous_rpow_const hr0)))
  have hpoint : ∀ t ∈ Icc (0 : ℝ) 1,
      (1 - h + h * (1 + u) * t) ^ r ≤
        (1 - h) + h * ((1 + u) ^ r * t ^ r) := by
    intro t ht
    have hbase : 0 ≤ (1 + u) * t := mul_nonneg (by linarith) ht.1
    have hconv := (convexOn_rpow hr).2 (show (1 : ℝ) ∈ Ici 0 by norm_num)
      (show (1 + u) * t ∈ Ici 0 from hbase)
      (show 0 ≤ 1 - h by linarith) hh0 (show 1 - h + h = 1 by ring)
    simpa only [smul_eq_mul, mul_one, Real.one_rpow,
      Real.mul_rpow (by linarith : 0 ≤ 1 + u) ht.1, mul_assoc] using hconv
  calc
    (∫ t in (0 : ℝ)..1, (1 - h + h * (1 + u) * t) ^ r) ≤
        ∫ t in (0 : ℝ)..1, ((1 - h) + h * ((1 + u) ^ r * t ^ r)) :=
      intervalIntegral.integral_mono_on (by norm_num)
        (hc.intervalIntegrable 0 1) (hb.intervalIntegrable 0 1) hpoint
    _ = (1 - h) + h * ((1 + u) ^ r / (r + 1)) := by
      rw [intervalIntegral.integral_add intervalIntegrable_const
        (((Real.continuous_rpow_const hr0).intervalIntegrable 0 1).const_mul _ |>.const_mul _)]
      simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_mul,
        intervalIntegral.integral_const_mul, integral_rpow_zero_one (by linarith : -1 < r)]
      ring

/-- The first necessary integral inequality forces a lower bound for
the scalar parameter, before taking any fractional root. -/
theorem polar_integral_power_threshold {u h r : ℝ}
    (hu : 0 ≤ u) (hh0 : 0 < h) (hh1 : h ≤ 1) (hr : 1 ≤ r)
    (hpolar : 1 ≤ ∫ t in (0 : ℝ)..1, (1 - h + h * (1 + u) * t) ^ r) :
    r + 1 ≤ (1 + u) ^ r := by
  have hb := polar_integral_upper_bound hu hh0.le hh1 hr
  have hfrac : 1 ≤ (1 + u) ^ r / (r + 1) := by nlinarith
  simpa only [one_mul] using (le_div_iff₀ (by linarith : 0 < r + 1)).mp hfrac

theorem polar_integral_cubic_parameter {u h : ℝ}
    (hu : 0 ≤ u) (hh0 : 0 < h) (hh1 : h ≤ 1)
    (hpolar : 1 ≤ ∫ t in (0 : ℝ)..1, 1 - h + h * (1 + u) * t) :
    1 ≤ u := by
  have h := polar_integral_power_threshold (r := (1 : ℝ)) hu hh0 hh1 (by norm_num)
    (by simpa using hpolar)
  simpa using h

theorem unit_parameter_second_integral_lt {h r : ℝ} (hh : 0 < h) (hr : 0 < r) :
    (2 * r + 1) * (∫ t in (0 : ℝ)..1,
      (max ((1 - t) ^ 2 - h * t * (1 - t)) 0) ^ r) < 1 := by
  let f : ℝ → ℝ := fun t ↦ (max ((1 - t) ^ 2 - h * t * (1 - t)) 0) ^ r
  let g : ℝ → ℝ := fun t ↦ (1 - t) ^ (2 * r)
  have hf : Continuous f := by
    apply (Real.continuous_rpow_const hr.le).comp
    fun_prop
  have hg : Continuous g := by
    apply (Real.continuous_rpow_const (by positivity : 0 ≤ 2 * r)).comp
    fun_prop
  have hsq (t : ℝ) (ht : t ≤ 1) : ((1 - t) ^ 2) ^ r = g t := by
    dsimp [g]
    rw [Real.rpow_mul (sub_nonneg.mpr ht), Real.rpow_two]
  have hle : ∀ t ∈ Ioc (0 : ℝ) 1, f t ≤ g t := by
    intro t ht
    rw [← hsq t ht.2]
    exact Real.rpow_le_rpow (le_max_right _ _)
      (max_le (sub_le_self _ (mul_nonneg (mul_nonneg hh.le ht.1.le)
        (sub_nonneg.mpr ht.2))) (sq_nonneg _)) hr.le
  have hstrict : f (1 / 2) < g (1 / 2) := by
    rw [← hsq (1 / 2) (by norm_num)]
    apply Real.rpow_lt_rpow (le_max_right _ _) _ hr
    apply max_lt_iff.mpr
    constructor
    · nlinarith
    · norm_num
  have hi : (∫ t in (0 : ℝ)..1, f t) < ∫ t in (0 : ℝ)..1, g t :=
    intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      (by norm_num) hf.continuousOn hg.continuousOn hle
      ⟨1 / 2, by norm_num, hstrict⟩
  have hgint : (∫ t in (0 : ℝ)..1, g t) = 1 / (2 * r + 1) := by
    calc
      (∫ t in (0 : ℝ)..1, g t) = ∫ t in (0 : ℝ)..1, t ^ (2 * r) := by
        simpa [g] using intervalIntegral.integral_comp_sub_left
          (fun t : ℝ ↦ t ^ (2 * r)) (a := (0 : ℝ)) (b := (1 : ℝ)) 1
      _ = _ := integral_rpow_zero_one (by linarith)
  rw [hgint] at hi
  have hden : 0 < 2 * r + 1 := by linarith
  simpa only [mul_comm] using (lt_div_iff₀ hden).mp hi

end Schmeisser

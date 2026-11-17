import Schmeisser.QuadraticIntegrals
import Mathlib.Analysis.Complex.Norm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule

open scoped BigOperators
open Set MeasureTheory

namespace Schmeisser

theorem sqrt_shiftedQuadratic_eq_norm (c d v t : ℝ) (hd : 0 ≤ d) (hv : 0 ≤ v) :
    Real.sqrt (shiftedQuadratic c d v t) =
      ‖(Real.sqrt v : ℂ) + Complex.I * (Real.sqrt d * (t - c) : ℝ)‖ := by
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  congr 1
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero,
    Complex.add_im, Complex.mul_im, one_mul, zero_add]
  rw [mul_pow, Real.sq_sqrt hv, Real.sq_sqrt hd]
  rfl

theorem convexOn_sqrt_shiftedQuadratic (c d v : ℝ) (hd : 0 ≤ d) (hv : 0 ≤ v) :
    ConvexOn ℝ univ (fun t : ℝ => Real.sqrt (shiftedQuadratic c d v t)) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  rw [sqrt_shiftedQuadratic_eq_norm c d v _ hd hv,
    sqrt_shiftedQuadratic_eq_norm c d v x hd hv,
    sqrt_shiftedQuadratic_eq_norm c d v y hd hv]
  have haff : (Real.sqrt v : ℂ) + Complex.I * (Real.sqrt d * (a * x + b * y - c) : ℝ) =
      a • ((Real.sqrt v : ℂ) + Complex.I * (Real.sqrt d * (x - c) : ℝ)) +
      b • ((Real.sqrt v : ℂ) + Complex.I * (Real.sqrt d * (y - c) : ℝ)) := by
    have hb' : b = 1 - a := by linarith
    rw [hb']
    apply Complex.ext <;> simp <;> ring
  rw [haff]
  have h := norm_add_le
    (a • ((Real.sqrt v : ℂ) + Complex.I * (Real.sqrt d * (x - c) : ℝ)))
    (b • ((Real.sqrt v : ℂ) + Complex.I * (Real.sqrt d * (y - c) : ℝ)))
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb] using h

theorem convexOn_integral_le_trapezoid {f : ℝ → ℝ} (hcont : Continuous f)
    (hconv : ConvexOn ℝ univ f) {a b : ℝ} (hab : a ≤ b) :
    (∫ t : ℝ in a..b, f t) ≤ (b - a) / 2 * (f a + f b) := by
  by_cases he : a = b
  · subst b
    simp
  have hba : 0 < b - a := sub_pos.mpr (lt_of_le_of_ne hab he)
  have hi : (∫ s : ℝ in 0..1, f ((b - a) * s + a)) ≤
      ∫ s : ℝ in 0..1, (f a + (f b - f a) * s) := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      ((hcont.comp (by fun_prop)).intervalIntegrable 0 1)
      ((by fun_prop : Continuous (fun s : ℝ => f a + (f b - f a) * s)).intervalIntegrable 0 1)
    intro s hs
    have h := hconv.2 (mem_univ a) (mem_univ b)
      (show 0 ≤ 1 - s by linarith [hs.2]) hs.1 (by ring : 1 - s + s = 1)
    simp only [smul_eq_mul] at h
    have heq : (b - a) * s + a = (1 - s) * a + s * b := by ring
    change f ((b - a) * s + a) ≤ f a + (f b - f a) * s
    rw [heq]
    calc
      f ((1 - s) * a + s * b) ≤ (1 - s) * f a + s * f b := h
      _ = f a + (f b - f a) * s := by ring
  have hline : (∫ s : ℝ in 0..1, (f a + (f b - f a) * s)) = (f a + f b) / 2 := by
    rw [intervalIntegral.integral_add intervalIntegrable_const
      (Continuous.intervalIntegrable (by fun_prop) 0 1),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
    simp only [sub_zero, smul_eq_mul, one_mul, one_pow, zero_pow (by decide : 2 ≠ 0)]
    ring
  rw [hline] at hi
  have hchange := intervalIntegral.smul_integral_comp_mul_add f
    (a := (0 : ℝ)) (b := (1 : ℝ)) (b - a) a
  have he1 : (b - a) * 1 + a = b := by ring
  simp only [smul_eq_mul, mul_zero, zero_add, he1] at hchange
  rw [← hchange]
  convert mul_le_mul_of_nonneg_left hi hba.le using 1
  ring

theorem integral_sqrt_shiftedQuadratic_le_trapezoid (c d v : ℝ)
    (hd : 0 ≤ d) (hv : 0 ≤ v) {a b : ℝ} (hab : a ≤ b) :
    (∫ t : ℝ in a..b, Real.sqrt (shiftedQuadratic c d v t)) ≤
      (b - a) / 2 * (Real.sqrt (shiftedQuadratic c d v a) +
        Real.sqrt (shiftedQuadratic c d v b)) := by
  apply convexOn_integral_le_trapezoid _ (convexOn_sqrt_shiftedQuadratic c d v hd hv) hab
  exact Real.continuous_sqrt.comp (by unfold shiftedQuadratic; fun_prop)

theorem convexOn_integral_le_composite_trapezoid {f : ℝ → ℝ} (hcont : Continuous f)
    (hconv : ConvexOn ℝ univ f) (k : ℕ) (hk : 0 < k) {a b : ℝ} (hab : a ≤ b) :
    (∫ t : ℝ in a..b, f t) ≤ trapezoidal_integral f k a b := by
  let h : ℝ := (b - a) / k
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hh : 0 ≤ h := div_nonneg (sub_nonneg.mpr hab) hkR.le
  have hend : a + (k : ℝ) * h = b := by dsimp [h]; field_simp; ring
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (f := f) (μ := volume) (a := fun j : ℕ => a + (j : ℝ) * h) (n := k)
    (fun j _ => hcont.intervalIntegrable _ _)
  simp only [Nat.cast_zero, zero_mul, add_zero, hend] at hsum
  have htrap := sum_trapezoidal_integral_adjacent_intervals (f := f) (a := a) (h := h) hk
  rw [hend] at htrap
  calc
    (∫ t : ℝ in a..b, f t) =
        ∑ j ∈ Finset.range k, ∫ t : ℝ in (a + (j : ℝ) * h)..(a + ((j + 1 : ℕ) : ℝ) * h), f t := hsum.symm
    _ ≤ ∑ j ∈ Finset.range k, trapezoidal_integral f 1
        (a + (j : ℝ) * h) (a + ((j : ℝ) + 1) * h) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [Nat.cast_add, Nat.cast_one, trapezoidal_integral_one]
      exact convexOn_integral_le_trapezoid hcont hconv (by nlinarith)
    _ = trapezoidal_integral f k a b := htrap

theorem integral_sqrt_shiftedQuadratic_le_composite_trapezoid (c d v : ℝ)
    (hd : 0 ≤ d) (hv : 0 ≤ v) (k : ℕ) (hk : 0 < k) {a b : ℝ} (hab : a ≤ b) :
    (∫ t : ℝ in a..b, Real.sqrt (shiftedQuadratic c d v t)) ≤
      trapezoidal_integral (fun t => Real.sqrt (shiftedQuadratic c d v t)) k a b := by
  apply convexOn_integral_le_composite_trapezoid _
    (convexOn_sqrt_shiftedQuadratic c d v hd hv) k hk hab
  exact Real.continuous_sqrt.comp (by unfold shiftedQuadratic; fun_prop)

theorem convexOn_sqrt_comparisonQuadratic {u κ : ℝ}
    (hu : 0 < u) (hu1 : u ≤ 1) (hκ : 0 ≤ κ) (hκ4 : κ / u ≤ 4) :
    ConvexOn ℝ univ (fun t : ℝ => Real.sqrt (comparisonQuadratic u κ t)) := by
  have hD := comparisonD_pos hu hu1 hκ
  have hv := (comparisonMinimum_bounds hu hu1 hκ hκ4).1
  have he : (fun t : ℝ => Real.sqrt (comparisonQuadratic u κ t)) =
      (fun t : ℝ => Real.sqrt (shiftedQuadratic (comparisonB u κ / comparisonD u κ)
        (comparisonD u κ) (comparisonMinimum u κ) t)) := by
    funext t
    rw [comparisonQuadratic_eq_shifted u κ t (ne_of_gt hD)]
  rw [he]
  exact convexOn_sqrt_shiftedQuadratic _ _ _ hD.le hv

theorem comparisonIntegral_one_eq_sqrt (u κ : ℝ) :
    comparisonIntegral 1 u κ =
      2 * ∫ t : ℝ in 0..1, Real.sqrt (comparisonQuadratic u κ t) := by
  simp only [comparisonIntegral, Nat.cast_one, Real.sqrt_eq_rpow]
  norm_num

theorem comparisonIntegral_one_le_composite_trapezoid {u κ : ℝ}
    (hu : 0 < u) (hu1 : u ≤ 1) (hκ : 0 ≤ κ) (hκ4 : κ / u ≤ 4)
    (k : ℕ) (hk : 0 < k) :
    comparisonIntegral 1 u κ ≤
      (1 + Real.sqrt (1 - u) + 2 * ∑ j ∈ Finset.range (k - 1),
        Real.sqrt (comparisonQuadratic u κ (((j : ℝ) + 1) / k))) / k := by
  have hcont : Continuous (fun t : ℝ => Real.sqrt (comparisonQuadratic u κ t)) :=
    Real.continuous_sqrt.comp (by unfold comparisonQuadratic; fun_prop)
  have h := convexOn_integral_le_composite_trapezoid hcont
    (convexOn_sqrt_comparisonQuadratic hu hu1 hκ hκ4) k hk
    (by norm_num : (0 : ℝ) ≤ 1)
  have hs := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)
  rw [← comparisonIntegral_one_eq_sqrt] at hs
  unfold trapezoidal_integral at hs
  simp only [comparisonQuadratic_zero, comparisonQuadratic_one, Real.sqrt_one,
    sub_zero, zero_add, mul_one] at hs
  refine hs.trans_eq ?_
  ring

theorem comparisonIntegral_one_le_endpoints {u κ : ℝ}
    (hu : 0 < u) (hu1 : u ≤ 1) (hκ : 0 ≤ κ) (hκ4 : κ / u ≤ 4) :
    comparisonIntegral 1 u κ ≤ 1 + Real.sqrt (1 - u) := by
  simpa using comparisonIntegral_one_le_composite_trapezoid hu hu1 hκ hκ4 1 (by decide)

end Schmeisser

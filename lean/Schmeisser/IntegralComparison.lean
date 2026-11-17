import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
Convexity and reflection of the integration variable in the last step of
the necessary-integral-inequalities lemma. All integrals are ordinary real
interval integrals; their integrability is supplied by continuity.
-/

namespace Schmeisser

open Set MeasureTheory

theorem convexOn_positivePart_rpow {r : ℝ} (hr : 1 ≤ r) :
    ConvexOn ℝ Set.univ (fun x : ℝ ↦ (max x 0) ^ r) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  have hmax : max (a * x + b * y) 0 ≤ a * max x 0 + b * max y 0 := by
    apply max_le
    · exact add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
        (mul_le_mul_of_nonneg_left (le_max_left _ _) hb)
    · positivity
  calc
    (max (a * x + b * y) 0) ^ r ≤ (a * max x 0 + b * max y 0) ^ r :=
      Real.rpow_le_rpow (le_max_right _ _) hmax (by linarith)
    _ ≤ a * (max x 0) ^ r + b * (max y 0) ^ r := by
      simpa only [smul_eq_mul] using
        (convexOn_rpow hr).2 (le_max_right x 0) (le_max_right y 0) ha hb hab

theorem continuous_positivePart_rpow {r : ℝ} (hr : 0 ≤ r) :
    Continuous (fun x : ℝ ↦ (max x 0) ^ r) :=
  (Real.continuous_rpow_const hr).comp (continuous_id.max continuous_const)

theorem monotone_positivePart_rpow {r : ℝ} (hr : 0 ≤ r) :
    Monotone (fun x : ℝ ↦ (max x 0) ^ r) := by
  intro x y hxy
  exact Real.rpow_le_rpow (le_max_right _ _) (max_le_max_right 0 hxy) hr

theorem integral_convex_combination_le {F f g : ℝ → ℝ} {l : ℝ}
    (hF : Continuous F) (hf : Continuous f) (hg : Continuous g)
    (hconv : ConvexOn ℝ Set.univ F) (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (hend : (∫ t in (0 : ℝ)..1, F (g t)) ≤ ∫ t in (0 : ℝ)..1, F (f t)) :
    (∫ t in (0 : ℝ)..1, F ((1 - l) * f t + l * g t)) ≤
      ∫ t in (0 : ℝ)..1, F (f t) := by
  have hi0 : IntervalIntegrable (fun t ↦ F (f t)) volume 0 1 :=
    (hF.comp hf).intervalIntegrable 0 1
  have hi1 : IntervalIntegrable (fun t ↦ F (g t)) volume 0 1 :=
    (hF.comp hg).intervalIntegrable 0 1
  have hic : IntervalIntegrable (fun t ↦ F ((1 - l) * f t + l * g t)) volume 0 1 :=
    (hF.comp ((hf.const_mul (1 - l)).add (hg.const_mul l))).intervalIntegrable 0 1
  calc
    (∫ t in (0 : ℝ)..1, F ((1 - l) * f t + l * g t)) ≤
        ∫ t in (0 : ℝ)..1, ((1 - l) * F (f t) + l * F (g t)) := by
      apply intervalIntegral.integral_mono_on (by norm_num) hic
        ((hi0.const_mul (1 - l)).add (hi1.const_mul l))
      intro t _
      simpa only [smul_eq_mul] using
        hconv.2 (mem_univ (f t)) (mem_univ (g t)) (by linarith : 0 ≤ 1 - l)
          hl0 (by ring : (1 - l) + l = 1)
    _ = (1 - l) * (∫ t in (0 : ℝ)..1, F (f t)) +
        l * (∫ t in (0 : ℝ)..1, F (g t)) := by
      rw [intervalIntegral.integral_add (hi0.const_mul _) (hi1.const_mul _)]
      simp only [intervalIntegral.integral_const_mul]
    _ ≤ ∫ t in (0 : ℝ)..1, F (f t) := by
      nlinarith [mul_le_mul_of_nonneg_left hend hl0]

theorem integral_le_of_reflected_pointwise_le {F f g : ℝ → ℝ}
    (hF : Continuous F) (hf : Continuous f) (hg : Continuous g)
    (hmono : Monotone F)
    (hle : ∀ t ∈ Set.Icc (0 : ℝ) 1, g (1 - t) ≤ f t) :
    (∫ t in (0 : ℝ)..1, F (g t)) ≤ ∫ t in (0 : ℝ)..1, F (f t) := by
  calc
    (∫ t in (0 : ℝ)..1, F (g t)) = ∫ t in (0 : ℝ)..1, F (g (1 - t)) := by
      simpa using (intervalIntegral.integral_comp_sub_left
        (fun t ↦ F (g t)) (a := (0 : ℝ)) (b := (1 : ℝ)) 1).symm
    _ ≤ ∫ t in (0 : ℝ)..1, F (f t) := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        ((hF.comp (hg.comp (continuous_const.sub continuous_id))).intervalIntegrable 0 1)
        ((hF.comp hf).intervalIntegrable 0 1)
      intro t ht
      exact hmono (hle t ht)

/-- The endpoint comparison removes the comparison point from the
quadratic integral. The exponent can be any real number at least one. -/
theorem quadratic_integral_endpoint_bound {u δ h l r : ℝ}
    (hu : u ≤ 1) (hd : δ ≤ u) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hr : 1 ≤ r) :
    (∫ t in (0 : ℝ)..1,
      (max ((1 - t) * (1 - l) + t * (1 - u + δ * l) -
        (u + h) * t * (1 - t)) 0) ^ r) ≤
    ∫ t in (0 : ℝ)..1, (max (1 - 2 * u * t + u * t ^ 2 - h * t * (1 - t)) 0) ^ r := by
  let f : ℝ → ℝ := fun t ↦ 1 - 2 * u * t + u * t ^ 2 - h * t * (1 - t)
  let g : ℝ → ℝ := fun t ↦ t * (1 - u + δ) - (u + h) * t * (1 - t)
  let F : ℝ → ℝ := fun x ↦ (max x 0) ^ r
  have hF : Continuous F := continuous_positivePart_rpow (by linarith)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hend : (∫ t in (0 : ℝ)..1, F (g t)) ≤ ∫ t in (0 : ℝ)..1, F (f t) := by
    apply integral_le_of_reflected_pointwise_le hF hf hg
      (monotone_positivePart_rpow (by linarith))
    intro t ht
    have heq : f t - g (1 - t) = (1 - u) * t + (u - δ) * (1 - t) := by
      dsimp [f, g]
      ring
    have hp := mul_nonneg (sub_nonneg.mpr hu) ht.1
    have hq := mul_nonneg (sub_nonneg.mpr hd) (sub_nonneg.mpr ht.2)
    linarith
  have hb := integral_convex_combination_le hF hf hg (convexOn_positivePart_rpow hr)
    hl0 hl1 hend
  convert hb using 1
  apply intervalIntegral.integral_congr
  intro t _
  dsimp [F]
  congr 2
  dsimp [f, g]
  ring

end Schmeisser

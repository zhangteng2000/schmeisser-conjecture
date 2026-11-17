import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-!
A differential proof of the hyperbolic estimate used in the scalar
parameter bound. The integrating factor avoids a power-series comparison.
-/

namespace Schmeisser

open Real Set Filter
open scoped Topology

noncomputable def hyperbolicRadius (x : ℝ) : ℝ := Real.sqrt (x ^ 2 + 9)

noncomputable def hyperbolicAux (x : ℝ) : ℝ :=
  (1 + x ^ 2 / hyperbolicRadius x) * Real.sinh x - x * Real.cosh x

theorem hyperbolicRadius_pos (x : ℝ) : 0 < hyperbolicRadius x := by
  unfold hyperbolicRadius
  positivity

theorem hyperbolicRadius_sq (x : ℝ) : hyperbolicRadius x ^ 2 = x ^ 2 + 9 :=
  Real.sq_sqrt (by positivity)

theorem hyperbolicRadius_ge_three (x : ℝ) : 3 ≤ hyperbolicRadius x := by
  have hs := hyperbolicRadius_sq x
  have hp := hyperbolicRadius_pos x
  nlinarith [sq_nonneg x]

theorem hasDerivAt_hyperbolicRadius (x : ℝ) :
    HasDerivAt hyperbolicRadius (x / hyperbolicRadius x) x := by
  have hd := (((hasDerivAt_id x).pow 2).add_const 9).sqrt (by positivity : x ^ 2 + 9 ≠ 0)
  unfold hyperbolicRadius
  convert hd using 1 <;> simp <;> field_simp

theorem hasDerivAt_weighted_hyperbolicAux (x : ℝ) :
    HasDerivAt (fun z ↦ Real.exp (hyperbolicRadius z) * hyperbolicAux z)
      (Real.exp (hyperbolicRadius x) *
        (x * (2 * hyperbolicRadius x - 3) * (hyperbolicRadius x - 3) /
          hyperbolicRadius x ^ 3) * Real.sinh x) x := by
  have hs := hasDerivAt_hyperbolicRadius x
  have hsne := (hyperbolicRadius_pos x).ne'
  have hq := ((hasDerivAt_id x).pow 2).div hs hsne
  have hw := ((hq.const_add 1).mul (Real.hasDerivAt_sinh x)).sub
    ((hasDerivAt_id x).mul (Real.hasDerivAt_cosh x))
  have hg := hs.exp.mul hw
  convert hg using 1
  · rfl
  · have heq := hyperbolicRadius_sq x
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.div_apply, Pi.pow_apply, id_eq]
    field_simp
    linear_combination x * Real.sinh x * (hyperbolicRadius x - 1) * heq

theorem hyperbolicAux_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ hyperbolicAux x := by
  let G : ℝ → ℝ := fun z ↦ Real.exp (hyperbolicRadius z) * hyperbolicAux z
  have hc : Continuous G := continuous_iff_continuousAt.mpr
    (fun z ↦ (hasDerivAt_weighted_hyperbolicAux z).continuousAt)
  have hm : MonotoneOn G (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _) hc.continuousOn
      (fun z _ ↦ (hasDerivAt_weighted_hyperbolicAux z).differentiableAt.differentiableWithinAt)
    intro z hz
    have hz0 : 0 ≤ z := (show 0 < z by simpa using hz).le
    rw [(hasDerivAt_weighted_hyperbolicAux z).deriv]
    have hs3 : 0 ≤ hyperbolicRadius z - 3 := sub_nonneg.mpr (hyperbolicRadius_ge_three z)
    have hs2 : 0 ≤ 2 * hyperbolicRadius z - 3 := by linarith [hyperbolicRadius_ge_three z]
    have hsh : 0 ≤ Real.sinh z := Real.sinh_nonneg_iff.mpr hz0
    have hsr := hyperbolicRadius_pos z
    positivity
  have hg0 : G 0 = 0 := by simp [G, hyperbolicAux]
  have hbound := hm (show (0 : ℝ) ∈ Ici 0 by simp) hx hx
  rw [hg0] at hbound
  exact nonneg_of_mul_nonneg_right hbound (Real.exp_pos _)

theorem continuous_dslope_sinh : Continuous (dslope Real.sinh 0) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    exact continuousAt_dslope_same.mpr (Real.differentiable_sinh 0)
  · exact (continuousAt_dslope_of_ne hx).mpr Real.continuous_sinh.continuousAt

theorem dslope_sinh_eq {x : ℝ} (hx : x ≠ 0) :
    dslope Real.sinh 0 x = Real.sinh x / x := by
  rw [dslope_of_ne _ hx]
  simp [slope_def_field]

theorem hasDerivAt_weighted_dslope_sinh {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun z ↦ Real.exp (3 - hyperbolicRadius z) * dslope Real.sinh 0 z)
      (-Real.exp (3 - hyperbolicRadius x) * hyperbolicAux x / x ^ 2) x := by
  have hs := hasDerivAt_hyperbolicRadius x
  have hsne := (hyperbolicRadius_pos x).ne'
  have hq := (Real.hasDerivAt_sinh x).div (hasDerivAt_id x) hx
  have hd := (hs.const_sub 3).exp.mul hq
  have hraw : HasDerivAt (fun z ↦ Real.exp (3 - hyperbolicRadius z) * (Real.sinh z / z))
      (-Real.exp (3 - hyperbolicRadius x) * hyperbolicAux x / x ^ 2) x := by
    convert hd using 1
    · rfl
    · simp only [hyperbolicAux, Pi.div_apply, id_eq, mul_one]
      field_simp
      ring
  apply hraw.congr_of_eventuallyEq
  filter_upwards [isOpen_ne.mem_nhds hx] with z hz
  rw [dslope_sinh_eq hz]

theorem sinh_div_le_exp_radius {x : ℝ} (hx : 0 < x) :
    Real.sinh x / x ≤ Real.exp (hyperbolicRadius x - 3) := by
  let R : ℝ → ℝ := fun z ↦ Real.exp (3 - hyperbolicRadius z) * dslope Real.sinh 0 z
  have hcr : Continuous hyperbolicRadius := continuous_iff_continuousAt.mpr
    (fun z ↦ (hasDerivAt_hyperbolicRadius z).continuousAt)
  have hc : Continuous R :=
    (Real.continuous_exp.comp (continuous_const.sub hcr)).mul continuous_dslope_sinh
  have hm : AntitoneOn R (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _) hc.continuousOn
    · intro z hz
      have hz0 : 0 < z := by simpa using hz
      exact (hasDerivAt_weighted_dslope_sinh hz0.ne').differentiableAt.differentiableWithinAt
    · intro z hz
      have hz0 : 0 < z := by simpa using hz
      rw [(hasDerivAt_weighted_dslope_sinh hz0.ne').deriv]
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Real.exp_pos _).le)
          (hyperbolicAux_nonneg hz0.le)) (sq_nonneg z)
  have hr0 : R 0 = 1 := by norm_num [R, hyperbolicRadius]
  have hbound := hm (show (0 : ℝ) ∈ Ici 0 by simp) hx.le hx.le
  rw [hr0] at hbound
  change Real.exp (3 - hyperbolicRadius x) * dslope Real.sinh 0 x ≤ 1 at hbound
  rw [dslope_sinh_eq hx.ne'] at hbound
  have hmul := mul_le_mul_of_nonneg_left hbound (Real.exp_pos (hyperbolicRadius x - 3)).le
  have he : Real.exp (hyperbolicRadius x - 3) * Real.exp (3 - hyperbolicRadius x) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  simpa only [← mul_assoc, he, one_mul, mul_one] using hmul

theorem log_sinh_div_le_sqrt {x : ℝ} (hx : 0 < x) :
    Real.log (Real.sinh x / x) ≤ Real.sqrt (x ^ 2 + 9) - 3 := by
  have hp : 0 < Real.sinh x / x := div_pos (Real.sinh_pos_iff.mpr hx) hx
  have h := Real.log_le_log hp (sinh_div_le_exp_radius hx)
  simpa [hyperbolicRadius] using h

end Schmeisser

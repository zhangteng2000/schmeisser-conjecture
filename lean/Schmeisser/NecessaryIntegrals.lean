import Schmeisser.ReflectedIntegral
import Schmeisser.RootMoments
import Schmeisser.ScalarReduction
import Schmeisser.IntegralComparison
import Schmeisser.AffineMoments
import Schmeisser.CentredProduct

/-!
# Necessary integral inequalities

This module connects the actual polynomial and its reciprocal critical-point
moments with the scalar integral comparison. The error term will be attached
to the actual centred family; no auxiliary maximum is needed.
-/

noncomputable section

namespace Schmeisser

open Polynomial MeasureTheory Set
open scoped BigOperators ComplexConjugate

def centeredErrorIntegral {ι : Type*} (jset : Finset ι) (η : ι → ℂ) (m : ℕ) (u : ℝ) : ℝ :=
  ((m : ℝ) + 1) * ∫ t : ℝ in 0..1,
    ‖(∏ j ∈ jset, (((1 - u * t : ℝ) : ℂ) + (t : ℂ) * η j)) -
      ((1 - u * t : ℝ) : ℂ) ^ m‖

def criticalCenteredIncrement (p : Polynomial ℂ) (a σ : ℝ) (j : ℂ × ℕ) : ℂ :=
  (-conj (criticalReciprocalMean p (a : ℂ)) / (σ : ℂ)) *
    (1 / ((a : ℂ) - j.1) - criticalReciprocalMean p (a : ℂ))

theorem critical_centered_sum_zero (p : Polynomial ℂ) (a σ : ℝ) (hn : 2 ≤ p.natDegree) :
    ∑ j ∈ rootIndices p.derivative, criticalCenteredIncrement p a σ j = 0 := by
  exact scaled_centered_sum_eq_zero (rootIndices p.derivative)
    (fun j => 1 / ((a : ℂ) - j.1)) (criticalReciprocalMean p (a : ℂ))
    (-conj (criticalReciprocalMean p (a : ℂ)) / (σ : ℂ))
    ((p.natDegree - 1 : ℕ) : ℝ)
    (by exact_mod_cast critical_rootIndices_card p)
    (critical_reciprocal_first_moment p (a : ℂ) hn)

theorem critical_centered_sq_sum_bound (p : Polynomial ℂ) (a σ : ℝ)
    (hn : 2 ≤ p.natDegree) (hσ : σ ≠ 0)
    (hsσ : criticalReciprocalSecondMoment p (a : ℂ) ≤ σ) :
    ∑ j ∈ rootIndices p.derivative, ‖criticalCenteredIncrement p a σ j‖ ^ 2 ≤
      ((p.natDegree - 1 : ℕ) : ℝ) * (‖criticalReciprocalMean p (a : ℂ)‖ ^ 2 / σ) *
        (1 - ‖criticalReciprocalMean p (a : ℂ)‖ ^ 2 / σ) := by
  exact reciprocal_centering_second_moment_bound (rootIndices p.derivative)
    (fun j => 1 / ((a : ℂ) - j.1)) (criticalReciprocalMean p (a : ℂ))
    ((p.natDegree - 1 : ℕ) : ℝ) (criticalReciprocalSecondMoment p (a : ℂ)) σ
    (by positivity) hσ hsσ (by exact_mod_cast critical_rootIndices_card p)
    (critical_reciprocal_first_moment p (a : ℂ) hn)
    (critical_reciprocal_second_moment p (a : ℂ) hn)

theorem critical_centering_factor_identity (p : Polynomial ℂ) (a σ t : ℝ) (j : ℂ × ℕ) :
    let μ := criticalReciprocalMean p (a : ℂ)
    let γ := (a : ℂ) - conj μ / (σ : ℂ)
    let u := ‖μ‖ ^ 2 / σ
    1 + (t : ℂ) * (γ - (a : ℂ)) / ((a : ℂ) - j.1) =
      ((1 - u * t : ℝ) : ℂ) + (t : ℂ) * criticalCenteredIncrement p a σ j := by
  dsimp only
  calc
    _ = 1 + (((a : ℂ) - conj (criticalReciprocalMean p (a : ℂ)) / (σ : ℂ)) -
        (a : ℂ)) * (t : ℂ) * (1 / ((a : ℂ) - j.1)) := by ring
    _ = _ := reciprocal_centering_factor_identity a σ t
      (criticalReciprocalMean p (a : ℂ)) (1 / ((a : ℂ) - j.1))

theorem integral_baseline_sub_error_le_norm {F : ℝ → ℂ} {b : ℝ → ℝ}
    (hF : Continuous F) (hb : Continuous b) (hb0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ b t) :
    (∫ t : ℝ in 0..1, b t) - (∫ t : ℝ in 0..1, ‖F t - (b t : ℂ)‖) ≤
      ‖∫ t : ℝ in 0..1, F t‖ := by
  have hbc : Continuous (fun t => (b t : ℂ)) := Complex.continuous_ofReal.comp hb
  have hnonneg : 0 ≤ ∫ t : ℝ in 0..1, b t :=
    intervalIntegral.integral_nonneg (by norm_num) hb0
  have hbase : ‖∫ t : ℝ in 0..1, (b t : ℂ)‖ = ∫ t : ℝ in 0..1, b t := by
    rw [intervalIntegral.integral_ofReal, Complex.norm_real, Real.norm_of_nonneg hnonneg]
  have hdiff : ‖(∫ t : ℝ in 0..1, (b t : ℂ)) - (∫ t : ℝ in 0..1, F t)‖ ≤
      ∫ t : ℝ in 0..1, ‖F t - (b t : ℂ)‖ := by
    calc
      _ = ‖∫ t : ℝ in 0..1, ((b t : ℂ) - F t)‖ := by
        rw [intervalIntegral.integral_sub (hbc.intervalIntegrable 0 1) (hF.intervalIntegrable 0 1)]
      _ ≤ ∫ t : ℝ in 0..1, ‖(b t : ℂ) - F t‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by norm_num)
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro t _
        exact norm_sub_rev _ _
  have htri := norm_add_le (∫ t : ℝ in 0..1, F t)
    ((∫ t : ℝ in 0..1, (b t : ℂ)) - (∫ t : ℝ in 0..1, F t))
  rw [← add_sub_assoc, add_sub_cancel_left, hbase] at htri
  linarith

theorem centered_integral_lower_bound {ι : Type*} (jset : Finset ι)
    (η : ι → ℂ) (m : ℕ) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (((m : ℝ) + 1) * ∫ t : ℝ in 0..1, (1 - u * t) ^ m) -
      centeredErrorIntegral jset η m u ≤
      ((m : ℝ) + 1) * ‖∫ t : ℝ in 0..1,
        ∏ j ∈ jset, (((1 - u * t : ℝ) : ℂ) + (t : ℂ) * η j)‖ := by
  have hF : Continuous (fun t : ℝ =>
      ∏ j ∈ jset, (((1 - u * t : ℝ) : ℂ) + (t : ℂ) * η j)) := by fun_prop
  have hb : Continuous (fun t : ℝ => (1 - u * t) ^ m) := by fun_prop
  have hb0 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : 0 ≤ (1 - u * t) ^ m :=
    pow_nonneg (by nlinarith [ht.1, ht.2]) _
  have h := integral_baseline_sub_error_le_norm hF hb hb0
  have hm : 0 ≤ (m : ℝ) + 1 := by positivity
  have hmul := mul_le_mul_of_nonneg_left h hm
  simpa only [mul_sub, centeredErrorIntegral, Complex.ofReal_pow] using hmul

theorem norm_integral_affine_product_le {ι : Type*} (jset : Finset ι)
    (q : ι → ℂ) (μ : ℂ) (m s σ : ℝ) (hm : 0 < m)
    (hcard : (jset.card : ℝ) = m)
    (hmean : ∑ j ∈ jset, q j = (m : ℂ) * μ)
    (hnorm : ∑ j ∈ jset, ‖q j‖ ^ 2 = m * s)
    (hvar : ‖μ‖ ^ 2 ≤ s) (hsσ : s ≤ σ)
    (A B : ℝ → ℂ) (hA : Continuous A) (hB : Continuous B) :
    ‖∫ t : ℝ in 0..1, ∏ j ∈ jset, (A t + B t * q j)‖ ≤
      ∫ t : ℝ in 0..1,
        (‖A t + B t * μ‖ ^ 2 + ‖B t‖ ^ 2 * (σ - ‖μ‖ ^ 2)) ^ (m / 2) := by
  have hleft : Continuous (fun t : ℝ => ‖∏ j ∈ jset, (A t + B t * q j)‖) := by
    fun_prop
  have hright : Continuous (fun t : ℝ =>
      (‖A t + B t * μ‖ ^ 2 + ‖B t‖ ^ 2 * (σ - ‖μ‖ ^ 2)) ^ (m / 2)) := by
    apply (Real.continuous_rpow_const (by positivity : 0 ≤ m / 2)).comp
    fun_prop
  calc
    ‖∫ t : ℝ in 0..1, ∏ j ∈ jset, (A t + B t * q j)‖ ≤
        ∫ t : ℝ in 0..1, ‖∏ j ∈ jset, (A t + B t * q j)‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ ≤ _ := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (hleft.intervalIntegrable 0 1) (hright.intervalIntegrable 0 1)
      intro t _
      apply (norm_affine_product_le jset q μ (A t) (B t) m s hm hcard hmean hnorm).trans
      apply Real.rpow_le_rpow
      · exact add_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hvar))
      · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
          (sub_le_sub_right hsσ _) (sq_nonneg _))
      · positivity

theorem actual_reflection_integral_rms_bound (p : Polynomial ℂ) (hn : 2 ≤ p.natDegree)
    {a : ℂ} (ha : p.eval a = 0) (hpa : p.derivative.eval a ≠ 0)
    (hroots : ∀ z : ℂ, p.eval z = 0 → ‖z‖ ≤ 1) {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1)
    (σ : ℝ) (hsσ : criticalReciprocalSecondMoment p a ≤ σ) :
    ‖∫ t : ℝ in 0..1, ∏ j ∈ rootIndices p.derivative,
      (1 + (t : ℂ) * (ξ - a) / (a - j.1))‖ ≤
      ∫ t : ℝ in 0..1,
        (‖conj ξ + ((1 - a * conj ξ) * (t : ℂ)) * criticalReciprocalMean p a‖ ^ 2 +
          ‖(1 - a * conj ξ) * (t : ℂ)‖ ^ 2 *
            (σ - ‖criticalReciprocalMean p a‖ ^ 2)) ^
        (((p.natDegree - 1 : ℕ) : ℝ) / 2) := by
  let q : ℂ × ℕ → ℂ := fun j => 1 / (a - j.1)
  let μ := criticalReciprocalMean p a
  let s := criticalReciprocalSecondMoment p a
  let m : ℝ := ((p.natDegree - 1 : ℕ) : ℝ)
  have hm : 0 < m := by dsimp [m]; exact_mod_cast (show 0 < p.natDegree - 1 by omega)
  have href := reflection_integral_comparison p ha hpa hroots hξ
  have href' :
      ‖∫ t : ℝ in 0..1, ∏ j ∈ rootIndices p.derivative,
        (1 + (t : ℂ) * (ξ - a) / (a - j.1))‖ ≤
      ‖∫ t : ℝ in 0..1, ∏ j ∈ rootIndices p.derivative,
        (conj ξ + ((1 - a * conj ξ) * (t : ℂ)) * q j)‖ := by
    have hl (t : ℝ) : (∏ j ∈ rootIndices p.derivative,
        (1 + (t : ℂ) * (ξ - a) / (a - j.1))) =
        (p.derivative.roots.map (fun ζ => 1 + (t : ℂ) * (ξ - a) / (a - ζ))).prod :=
      prod_rootIndices p.derivative (fun ζ => 1 + (t : ℂ) * (ξ - a) / (a - ζ))
    have hr (t : ℝ) : (∏ j ∈ rootIndices p.derivative,
        (conj ξ + ((1 - a * conj ξ) * (t : ℂ)) * q j)) =
        (p.derivative.roots.map
          (fun ζ => conj ξ + (1 - a * conj ξ) * (t : ℂ) / (a - ζ))).prod := by
      simpa only [q, div_eq_mul_inv, one_mul] using
        prod_rootIndices p.derivative
          (fun ζ => conj ξ + (1 - a * conj ξ) * (t : ℂ) / (a - ζ))
    simpa only [hl, hr] using href
  have hb := norm_integral_affine_product_le (rootIndices p.derivative) q μ m s σ hm
    (by dsimp [m]; exact_mod_cast critical_rootIndices_card p)
    (critical_reciprocal_first_moment p a hn)
    (critical_reciprocal_second_moment p a hn)
    (critical_reciprocal_mean_bound p a hn) hsσ
    (fun _ : ℝ => conj ξ) (fun t : ℝ => (1 - a * conj ξ) * (t : ℂ))
    continuous_const (by fun_prop)
  exact href'.trans hb

theorem reflected_quadratic_identity (a σ t : ℝ) (μ : ℂ) (hσ : σ ≠ 0) :
    let γ := (a : ℂ) - conj μ / (σ : ℂ)
    let δ := (1 - a ^ 2) * σ + 2 * a * μ.re - 1
    let u := ‖μ‖ ^ 2 / σ
    let h := (1 - a ^ 2) * (1 - u + δ)
    let l := 1 - ‖γ‖ ^ 2
    ‖conj γ + ((1 - (a : ℂ) * conj γ) * (t : ℂ)) * μ‖ ^ 2 +
        ‖(1 - (a : ℂ) * conj γ) * (t : ℂ)‖ ^ 2 * (σ - ‖μ‖ ^ 2) =
      (1 - t) * (1 - l) + t * (1 - u + δ * l) - (u + h) * t * (1 - t) := by
  dsimp
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.div_re, Complex.div_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im]
  field_simp [hσ]
  ring

theorem polar_quadratic_identity (a σ t : ℝ) (μ : ℂ) :
    let δ := (1 - a ^ 2) * σ + 2 * a * μ.re - 1
    ‖(a : ℂ) + (((1 - a ^ 2) * t : ℝ) : ℂ) * μ‖ ^ 2 +
        ‖(((1 - a ^ 2) * t : ℝ) : ℂ)‖ ^ 2 * (σ - ‖μ‖ ^ 2) =
      a ^ 2 + (1 - a ^ 2) * (1 + δ) * t - (1 - a ^ 2) ^ 2 * σ * t * (1 - t) := by
  dsimp
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem polar_quadratic_majorant {a σ δ u h t : ℝ}
    (ha : a ^ 2 ≤ 1) (hσ : 0 ≤ σ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hδ : δ ≤ u) (hh : h = (1 - a ^ 2) * (1 - u + δ))
    (ht : t ∈ Icc (0 : ℝ) 1) :
    a ^ 2 + (1 - a ^ 2) * (1 + δ) * t - (1 - a ^ 2) ^ 2 * σ * t * (1 - t) ≤
      1 - h + h * (1 + u) * t := by
  have hut : 0 ≤ 1 - u * t := by nlinarith [ht.1, ht.2]
  have hp : 0 ≤ (1 - a ^ 2) * (u - δ) * (1 - u * t) :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hδ)) hut
  have hq : 0 ≤ (1 - a ^ 2) ^ 2 * σ * t * (1 - t) :=
    mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hσ) ht.1) (sub_nonneg.mpr ht.2)
  have hid : (1 - h + h * (1 + u) * t) -
      (a ^ 2 + (1 - a ^ 2) * (1 + δ) * t - (1 - a ^ 2) ^ 2 * σ * t * (1 - t)) =
      (1 - a ^ 2) * (u - δ) * (1 - u * t) + (1 - a ^ 2) ^ 2 * σ * t * (1 - t) := by
    rw [hh]
    ring
  linarith

theorem necessary_polar_integral (p : Polynomial ℂ) (hn : 2 ≤ p.natDegree)
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (ha : p.eval (a : ℂ) = 0) (hpa : p.derivative.eval (a : ℂ) ≠ 0)
    (hroots : ∀ z : ℂ, p.eval z = 0 → ‖z‖ ≤ 1)
    (σ : ℝ) (hσ : 1 ≤ σ) (hsσ : criticalReciprocalSecondMoment p (a : ℂ) ≤ σ)
    (hδu : (1 - a ^ 2) * σ + 2 * a * (criticalReciprocalMean p (a : ℂ)).re - 1 ≤
      ‖criticalReciprocalMean p (a : ℂ)‖ ^ 2 / σ) :
    let μ := criticalReciprocalMean p (a : ℂ)
    let δ := (1 - a ^ 2) * σ + 2 * a * μ.re - 1
    let u := ‖μ‖ ^ 2 / σ
    let h := (1 - a ^ 2) * (1 - u + δ)
    1 ≤ ∫ t : ℝ in 0..1,
      (1 - h + h * (1 + u) * t) ^ (((p.natDegree - 1 : ℕ) : ℝ) / 2) := by
  let μ := criticalReciprocalMean p (a : ℂ)
  let δ := (1 - a ^ 2) * σ + 2 * a * μ.re - 1
  let u := ‖μ‖ ^ 2 / σ
  let h := (1 - a ^ 2) * (1 - u + δ)
  let r : ℝ := ((p.natDegree - 1 : ℕ) : ℝ) / 2
  let D : ℝ → ℝ := fun t =>
    ‖(a : ℂ) + (((1 - a ^ 2) * t : ℝ) : ℂ) * μ‖ ^ 2 +
      ‖(((1 - a ^ 2) * t : ℝ) : ℂ)‖ ^ 2 * (σ - ‖μ‖ ^ 2)
  change 1 ≤ ∫ t : ℝ in 0..1, (1 - h + h * (1 + u) * t) ^ r
  have hσ0 : 0 < σ := by linarith
  have hvar : ‖μ‖ ^ 2 ≤ σ := (critical_reciprocal_mean_bound p (a : ℂ) hn).trans hsσ
  have hu0 : 0 ≤ u := div_nonneg (sq_nonneg _) hσ0.le
  have hu1 : u ≤ 1 := (div_le_one hσ0).mpr hvar
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hna : ‖(a : ℂ)‖ ≤ 1 := by
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha0] using ha1.le
  have hB (t : ℝ) : (1 - (a : ℂ) * conj (a : ℂ)) * (t : ℂ) =
      (((1 - a ^ 2) * t : ℝ) : ℂ) := by
    push_cast
    simp only [Complex.conj_ofReal]
    ring
  have hb : 1 ≤ ∫ t : ℝ in 0..1, (D t) ^ r := by
    have hbound := actual_reflection_integral_rms_bound p hn ha hpa hroots hna σ hsσ
    simpa [D, μ, r, hB, pow_two] using hbound
  have hD0 (t : ℝ) : 0 ≤ D t :=
    add_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hvar))
  have hD (t : ℝ) : D t = a ^ 2 + (1 - a ^ 2) * (1 + δ) * t -
      (1 - a ^ 2) ^ 2 * σ * t * (1 - t) := polar_quadratic_identity a σ t μ
  have hDr : Continuous (fun t => (D t) ^ r) := by
    apply (Real.continuous_rpow_const hr0).comp
    dsimp [D]
    fun_prop
  have hPr : Continuous (fun t : ℝ => (1 - h + h * (1 + u) * t) ^ r) := by
    apply (Real.continuous_rpow_const hr0).comp
    fun_prop
  apply hb.trans
  apply intervalIntegral.integral_mono_on (by norm_num)
    (hDr.intervalIntegrable 0 1) (hPr.intervalIntegrable 0 1)
  intro t ht
  apply Real.rpow_le_rpow (hD0 t) _ hr0
  rw [hD]
  exact polar_quadratic_majorant (by nlinarith) hσ0.le hu0 hu1 hδu rfl ht

theorem necessary_second_integral_norm_bound (p : Polynomial ℂ) (hn : 3 ≤ p.natDegree)
    (a : ℝ) (ha : p.eval (a : ℂ) = 0) (hpa : p.derivative.eval (a : ℂ) ≠ 0)
    (hroots : ∀ z : ℂ, p.eval z = 0 → ‖z‖ ≤ 1)
    (σ : ℝ) (hσ : 1 ≤ σ) (hsσ : criticalReciprocalSecondMoment p (a : ℂ) ≤ σ)
    (hδu : (1 - a ^ 2) * σ + 2 * a * (criticalReciprocalMean p (a : ℂ)).re - 1 ≤
      ‖criticalReciprocalMean p (a : ℂ)‖ ^ 2 / σ)
    (hγ : ‖(a : ℂ) - conj (criticalReciprocalMean p (a : ℂ)) / (σ : ℂ)‖ ≤ 1) :
    let μ := criticalReciprocalMean p (a : ℂ)
    let δ := (1 - a ^ 2) * σ + 2 * a * μ.re - 1
    let u := ‖μ‖ ^ 2 / σ
    let h := (1 - a ^ 2) * (1 - u + δ)
    let γ := (a : ℂ) - conj μ / (σ : ℂ)
    ‖∫ t : ℝ in 0..1, ∏ j ∈ rootIndices p.derivative,
      (1 + (t : ℂ) * (γ - (a : ℂ)) / ((a : ℂ) - j.1))‖ ≤
      ∫ t : ℝ in 0..1,
        (max (1 - 2 * u * t + u * t ^ 2 - h * t * (1 - t)) 0) ^
        (((p.natDegree - 1 : ℕ) : ℝ) / 2) := by
  let μ := criticalReciprocalMean p (a : ℂ)
  let δ := (1 - a ^ 2) * σ + 2 * a * μ.re - 1
  let u := ‖μ‖ ^ 2 / σ
  let h := (1 - a ^ 2) * (1 - u + δ)
  let γ := (a : ℂ) - conj μ / (σ : ℂ)
  let l := 1 - ‖γ‖ ^ 2
  let r : ℝ := ((p.natDegree - 1 : ℕ) : ℝ) / 2
  let E : ℝ → ℝ := fun t =>
    ‖conj γ + ((1 - (a : ℂ) * conj γ) * (t : ℂ)) * μ‖ ^ 2 +
      ‖(1 - (a : ℂ) * conj γ) * (t : ℂ)‖ ^ 2 * (σ - ‖μ‖ ^ 2)
  change ‖∫ t : ℝ in 0..1, ∏ j ∈ rootIndices p.derivative,
      (1 + (t : ℂ) * (γ - (a : ℂ)) / ((a : ℂ) - j.1))‖ ≤
    ∫ t : ℝ in 0..1, (max (1 - 2 * u * t + u * t ^ 2 - h * t * (1 - t)) 0) ^ r
  have hn2 : 2 ≤ p.natDegree := by omega
  have hσ0 : 0 < σ := by linarith
  have hvar : ‖μ‖ ^ 2 ≤ σ := (critical_reciprocal_mean_bound p (a : ℂ) hn2).trans hsσ
  have hu1 : u ≤ 1 := (div_le_one hσ0).mpr hvar
  have hr1 : 1 ≤ r := by
    have hm2 : (2 : ℝ) ≤ ((p.natDegree - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 2 ≤ p.natDegree - 1 by omega)
    dsimp [r]
    linarith
  have hl0 : 0 ≤ l := by dsimp [l]; nlinarith [norm_nonneg γ]
  have hl1 : l ≤ 1 := by dsimp [l]; nlinarith [sq_nonneg ‖γ‖]
  have hE0 (t : ℝ) : 0 ≤ E t :=
    add_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hvar))
  have hE (t : ℝ) : E t =
      (1 - t) * (1 - l) + t * (1 - u + δ * l) - (u + h) * t * (1 - t) :=
    reflected_quadratic_identity a σ t μ hσ0.ne'
  calc
    ‖∫ t : ℝ in 0..1, ∏ j ∈ rootIndices p.derivative,
        (1 + (t : ℂ) * (γ - (a : ℂ)) / ((a : ℂ) - j.1))‖ ≤
        ∫ t : ℝ in 0..1, (E t) ^ r :=
      actual_reflection_integral_rms_bound p hn2 ha hpa hroots hγ σ hsσ
    _ = ∫ t : ℝ in 0..1,
        (max ((1 - t) * (1 - l) + t * (1 - u + δ * l) -
          (u + h) * t * (1 - t)) 0) ^ r := by
      apply intervalIntegral.integral_congr
      intro t _
      change (E t) ^ r = (max ((1 - t) * (1 - l) + t * (1 - u + δ * l) -
        (u + h) * t * (1 - t)) 0) ^ r
      rw [← hE, max_eq_left (hE0 t)]
    _ ≤ _ := quadratic_integral_endpoint_bound hu1 hδu hl0 hl1 hr1

/-- Failure of the covering criterion produces the two necessary scalar
integral inequalities, with the error of the actual centred critical-point
family. All polynomial and moment hypotheses are discharged here. -/
theorem necessary_integrals_of_failure (p : Polynomial ℂ) (hn : 3 ≤ p.natDegree)
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (ha : p.eval (a : ℂ) = 0) (hpa : p.derivative.eval (a : ℂ) ≠ 0)
    (hroots : ∀ z : ℂ, p.eval z = 0 → ‖z‖ ≤ 1)
    (hfail : ¬ (1 ≤ criticalReciprocalSecondMoment p (a : ℂ) ∧
      (a * (criticalReciprocalMean p (a : ℂ)).im) ^ 2 ≤
        (criticalReciprocalSecondMoment p (a : ℂ) - 1) *
          ((1 - a ^ 2) * criticalReciprocalSecondMoment p (a : ℂ) +
            2 * a * (criticalReciprocalMean p (a : ℂ)).re - 1))) :
    ∃ σ : ℝ,
      let μ := criticalReciprocalMean p (a : ℂ)
      let δ := (1 - a ^ 2) * σ + 2 * a * μ.re - 1
      let u := ‖μ‖ ^ 2 / σ
      let h := (1 - a ^ 2) * (1 - u + δ)
      let m := p.natDegree - 1
      let η := criticalCenteredIncrement p a σ
      1 ≤ σ ∧ criticalReciprocalSecondMoment p (a : ℂ) < σ ∧
      0 < u ∧ u ≤ 1 ∧ 0 < h ∧ h < 1 ∧
      (∑ j ∈ rootIndices p.derivative, η j) = 0 ∧
      (∑ j ∈ rootIndices p.derivative, ‖η j‖ ^ 2) ≤ (m : ℝ) * u * (1 - u) ∧
      (1 ≤ ∫ t : ℝ in 0..1, (1 - h + h * (1 + u) * t) ^ ((m : ℝ) / 2)) ∧
      ((((m : ℝ) + 1) * ∫ t : ℝ in 0..1, (1 - u * t) ^ m) -
        centeredErrorIntegral (rootIndices p.derivative) η m u ≤
        ((m : ℝ) + 1) * ∫ t : ℝ in 0..1,
          (max (1 - 2 * u * t + u * t ^ 2 - h * t * (1 - t)) 0) ^ ((m : ℝ) / 2)) := by
  have hn2 : 2 ≤ p.natDegree := by omega
  have hvar := critical_reciprocal_mean_bound p (a : ℂ) hn2
  have hdelta := critical_reciprocal_delta_nonneg p a hn2 hroots hpa
  obtain ⟨σ, hσ, hsσ, hd, hboundary, hu0, hu1, hδu, hh0, hh1, hγ⟩ :=
    comparison_parameters_of_failure ha0 ha1 hvar hdelta hfail
  let μ := criticalReciprocalMean p (a : ℂ)
  let δ := (1 - a ^ 2) * σ + 2 * a * μ.re - 1
  let u := ‖μ‖ ^ 2 / σ
  let h := (1 - a ^ 2) * (1 - u + δ)
  let γ := (a : ℂ) - conj μ / (σ : ℂ)
  let m := p.natDegree - 1
  let η := criticalCenteredIncrement p a σ
  have hσne : σ ≠ 0 := by linarith
  refine ⟨σ, hσ, hsσ, hu0, hu1, hh0, hh1,
    critical_centered_sum_zero p a σ hn2,
    critical_centered_sq_sum_bound p a σ hn2 hσne hsσ.le,
    necessary_polar_integral p hn2 a ha0 ha1 ha hpa hroots σ hσ hsσ.le hδu, ?_⟩
  have hlower := centered_integral_lower_bound (rootIndices p.derivative) η m u hu0.le hu1
  have hupper := necessary_second_integral_norm_bound p hn a ha hpa hroots σ hσ hsσ.le hδu hγ.le
  have hprod (t : ℝ) : (∏ j ∈ rootIndices p.derivative,
      (1 + (t : ℂ) * (γ - (a : ℂ)) / ((a : ℂ) - j.1))) =
      ∏ j ∈ rootIndices p.derivative, (((1 - u * t : ℝ) : ℂ) + (t : ℂ) * η j) := by
    apply Finset.prod_congr rfl
    intro j _
    exact critical_centering_factor_identity p a σ t j
  change ‖∫ t : ℝ in 0..1, ∏ j ∈ rootIndices p.derivative,
      (1 + (t : ℂ) * (γ - (a : ℂ)) / ((a : ℂ) - j.1))‖ ≤
    ∫ t : ℝ in 0..1,
      (max (1 - 2 * u * t + u * t ^ 2 - h * t * (1 - t)) 0) ^ ((m : ℝ) / 2) at hupper
  simp_rw [hprod] at hupper
  exact hlower.trans (mul_le_mul_of_nonneg_left hupper (by positivity))

end Schmeisser

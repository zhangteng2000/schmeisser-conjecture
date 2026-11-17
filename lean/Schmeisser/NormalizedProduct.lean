import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Normalized root products and integration along a segment

The factors retain root multiplicities. The final identity expresses a
polynomial value relative to a simple zero as the integral of a normalized
product over the critical points.
-/

noncomputable section

namespace Schmeisser

open Polynomial MeasureTheory

theorem sub_root_ne_zero_of_eval_ne_zero {q : Polynomial ℂ} {a : ℂ}
    (hqa : q.eval a ≠ 0) {ζ : ℂ} (hζ : ζ ∈ q.roots) : a - ζ ≠ 0 := by
  intro h
  apply hqa
  rw [sub_eq_zero.mp h]
  exact ((Polynomial.mem_roots').mp hζ).2

theorem normalized_eval_eq_root_product (q : Polynomial ℂ) {a : ℂ}
    (hqa : q.eval a ≠ 0) (z : ℂ) :
    q.eval z / q.eval a = (q.roots.map (fun ζ => 1 + (z - a) / (a - ζ))).prod := by
  have hq : q ≠ 0 := by
    intro h
    simp [h] at hqa
  have hc : q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq
  have hs : q.Splits := IsAlgClosed.splits q
  calc
    q.eval z / q.eval a =
        (q.roots.map (z - ·)).prod / (q.roots.map (a - ·)).prod := by
      rw [hs.eval_eq_prod_roots, hs.eval_eq_prod_roots, mul_div_mul_left _ _ hc]
    _ = (q.roots.map (fun ζ => (z - ζ) / (a - ζ))).prod :=
      Multiset.prod_map_div.symm
    _ = (q.roots.map (fun ζ => 1 + (z - a) / (a - ζ))).prod := by
      refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
      intro ζ hζ
      have haζ := sub_root_ne_zero_of_eval_ne_zero hqa hζ
      field_simp [haζ]
      ring

theorem polynomial_segment_integral (p : Polynomial ℂ) (a δ : ℂ) :
    (∫ t : ℝ in 0..1, p.derivative.eval (a + (t : ℂ) * δ) * δ) =
      p.eval (a + δ) - p.eval a := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => p.eval (a + (t : ℂ) * δ))
      (p.derivative.eval (a + (t : ℂ) * δ) * δ) t := by
    have ht : HasDerivAt (fun t : ℝ => a + (t : ℂ) * δ) δ t := by
      simpa using (Complex.ofRealCLM.hasDerivAt.mul_const δ).const_add a
    simpa only [Function.comp_apply] using!
      (p.hasDerivAt (a + (t : ℂ) * δ)).comp t ht
  have hc : Continuous (fun t : ℝ => p.derivative.eval (a + (t : ℂ) * δ) * δ) := by
    fun_prop
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hd t) (hc.intervalIntegrable 0 1)

theorem normalized_derivative_product_integral (p : Polynomial ℂ) {a : ℂ}
    (hpa : p.derivative.eval a ≠ 0) (δ : ℂ) :
    p.eval (a + δ) - p.eval a = (δ * p.derivative.eval a) *
      (∫ t : ℝ in 0..1,
        (p.derivative.roots.map (fun ζ => 1 + (t : ℂ) * δ / (a - ζ))).prod) := by
  let f : ℝ → ℂ := fun t =>
    (p.derivative.roots.map (fun ζ => 1 + (t : ℂ) * δ / (a - ζ))).prod
  have heval (t : ℝ) : p.derivative.eval (a + (t : ℂ) * δ) =
      p.derivative.eval a * f t := by
    have h := normalized_eval_eq_root_product p.derivative hpa (a + (t : ℂ) * δ)
    simp only [add_sub_cancel_left] at h
    calc
      p.derivative.eval (a + (t : ℂ) * δ) =
          p.derivative.eval a *
            (p.derivative.eval (a + (t : ℂ) * δ) / p.derivative.eval a) := by
        field_simp [hpa]
      _ = p.derivative.eval a * f t := by rw [h]
  calc
    p.eval (a + δ) - p.eval a =
        ∫ t : ℝ in 0..1, p.derivative.eval (a + (t : ℂ) * δ) * δ :=
      (polynomial_segment_integral p a δ).symm
    _ = ∫ t : ℝ in 0..1, (δ * p.derivative.eval a) * f t := by
      apply intervalIntegral.integral_congr
      intro t _
      change p.derivative.eval (a + (t : ℂ) * δ) * δ =
        (δ * p.derivative.eval a) * f t
      rw [heval]
      ring
    _ = (δ * p.derivative.eval a) * (∫ t : ℝ in 0..1, f t) :=
      intervalIntegral.integral_const_mul _ _

theorem value_at_root_eq_critical_product_integral (p : Polynomial ℂ) {a : ℂ}
    (ha : p.eval a = 0) (hpa : p.derivative.eval a ≠ 0) (γ : ℂ) :
    p.eval γ = ((γ - a) * p.derivative.eval a) *
      (∫ t : ℝ in 0..1,
        (p.derivative.roots.map (fun ζ => 1 + (t : ℂ) * (γ - a) / (a - ζ))).prod) := by
  have haγ : a + (γ - a) = γ := by ring
  simpa [haγ, ha] using normalized_derivative_product_integral p hpa (γ - a)

end Schmeisser

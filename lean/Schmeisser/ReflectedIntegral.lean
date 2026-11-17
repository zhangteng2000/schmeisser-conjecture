import Schmeisser.NormalizedProduct
import Schmeisser.Reflection
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Integral comparison from polynomial reflection

Removing a simple zero gives an integral of the normalized derivative.
Reflecting this identity gives the second integral. Their comparison holds
throughout the closed unit disk, including zero.
-/

noncomputable section

namespace Schmeisser

open Polynomial MeasureTheory
open scoped ComplexConjugate

theorem derivative_eval_of_linear_factor {p g : Polynomial ℂ} {a : ℂ}
    (hp : p = (X - C a) * g) : p.derivative.eval a = g.eval a := by
  rw [hp]
  simp [Polynomial.derivative_mul]

theorem reduced_polynomial_integral {p g : Polynomial ℂ} {a : ℂ}
    (hp : p = (X - C a) * g) (hpa : p.derivative.eval a ≠ 0) (ξ : ℂ) :
    g.eval ξ = p.derivative.eval a *
      (∫ t : ℝ in 0..1,
        (p.derivative.roots.map (fun ζ => 1 + (t : ℂ) * (ξ - a) / (a - ζ))).prod) := by
  by_cases hξ : ξ = a
  · subst ξ
    rw [derivative_eval_of_linear_factor hp]
    simp
  · have ha : p.eval a = 0 := by rw [hp]; simp
    have h := value_at_root_eq_critical_product_integral p ha hpa ξ
    have heval : p.eval ξ = (ξ - a) * g.eval ξ := by rw [hp]; simp
    rw [heval] at h
    apply mul_left_cancel₀ (sub_ne_zero.mpr hξ)
    simpa only [mul_assoc] using h

theorem critical_roots_card_of_linear_factor {p g : Polynomial ℂ} {a : ℂ}
    (hp : p = (X - C a) * g) (hpa : p.derivative.eval a ≠ 0) :
    p.derivative.roots.card = g.natDegree := by
  have hg : g ≠ 0 := by
    intro h
    have hd := derivative_eval_of_linear_factor hp
    simp [h] at hd
    exact hpa hd
  have hdeg : p.natDegree = g.natDegree + 1 := by
    rw [hp, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero a) hg,
      Polynomial.natDegree_X_sub_C]
    omega
  rw [← (IsAlgClosed.splits p.derivative).natDegree_eq_card_roots,
    Polynomial.natDegree_derivative, hdeg]
  omega

theorem mul_pow_multiset_product {ι : Type*} (s : Multiset ι) (k : ℂ) (f : ι → ℂ) :
    k ^ s.card * (s.map f).prod = (s.map (fun x => k * f x)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
      simp only [Multiset.card_cons, Multiset.map_cons, Multiset.prod_cons, pow_succ]
      rw [← ih]
      ring

theorem reflected_reduced_integral_of_ne_zero {p g : Polynomial ℂ} {a ξ : ℂ}
    (hp : p = (X - C a) * g) (hpa : p.derivative.eval a ≠ 0) (hξ : ξ ≠ 0) :
    conj ((reflectedPolynomial g).eval ξ) = p.derivative.eval a *
      (∫ t : ℝ in 0..1,
        (p.derivative.roots.map
          (fun ζ => conj ξ + (1 - a * conj ξ) * (t : ℂ) / (a - ζ))).prod) := by
  have hk : conj ξ ≠ 0 := by simpa using hξ
  have hcard := critical_roots_card_of_linear_factor hp hpa
  have hfactor (t : ℝ) : (conj ξ) ^ g.natDegree *
      (p.derivative.roots.map
        (fun ζ => 1 + (t : ℂ) * ((conj ξ)⁻¹ - a) / (a - ζ))).prod =
      (p.derivative.roots.map
        (fun ζ => conj ξ + (1 - a * conj ξ) * (t : ℂ) / (a - ζ))).prod := by
    rw [← hcard, mul_pow_multiset_product]
    refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
    intro ζ hζ
    have haζ := sub_root_ne_zero_of_eval_ne_zero hpa hζ
    field_simp [hk, haζ]
  rw [reflectedPolynomial_eval g hξ]
  simp only [map_mul, map_pow, starRingEnd_self_apply]
  rw [reduced_polynomial_integral hp hpa ((conj ξ)⁻¹)]
  rw [mul_left_comm, ← intervalIntegral.integral_const_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  exact hfactor t

theorem reflected_reduced_integral {p g : Polynomial ℂ} {a : ℂ}
    (hp : p = (X - C a) * g) (hpa : p.derivative.eval a ≠ 0) (ξ : ℂ) :
    conj ((reflectedPolynomial g).eval ξ) = p.derivative.eval a *
      (∫ t : ℝ in 0..1,
        (p.derivative.roots.map
          (fun ζ => conj ξ + (1 - a * conj ξ) * (t : ℂ) / (a - ζ))).prod) := by
  have hleft : Continuous (fun ξ : ℂ => conj ((reflectedPolynomial g).eval ξ)) := by
    fun_prop
  have hright : Continuous (fun ξ : ℂ =>
      ∫ t : ℝ in 0..1, (p.derivative.roots.map
        (fun ζ => conj ξ + (1 - a * conj ξ) * (t : ℂ) / (a - ζ))).prod) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    change Continuous (fun w : ℂ × ℝ => (p.derivative.roots.map
      (fun ζ => conj w.1 + (1 - a * conj w.1) * (w.2 : ℂ) / (a - ζ))).prod)
    apply continuous_multiset_prod
    intro ζ _
    fun_prop
  have heq := Continuous.ext_on (dense_compl_singleton (0 : ℂ)) hleft
    (continuous_const.mul hright) (by
      intro z hz
      exact reflected_reduced_integral_of_ne_zero hp hpa (by simpa using hz))
  exact congrFun heq ξ

theorem reflection_integral_comparison_of_linear_factor {p g : Polynomial ℂ} {a : ℂ}
    (hp : p = (X - C a) * g) (hpa : p.derivative.eval a ≠ 0)
    (hroots : ∀ z : ℂ, p.eval z = 0 → ‖z‖ ≤ 1) {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1) :
    ‖∫ t : ℝ in 0..1,
      (p.derivative.roots.map (fun ζ => 1 + (t : ℂ) * (ξ - a) / (a - ζ))).prod‖ ≤
    ‖∫ t : ℝ in 0..1,
      (p.derivative.roots.map
        (fun ζ => conj ξ + (1 - a * conj ξ) * (t : ℂ) / (a - ζ))).prod‖ := by
  have hgroots : ∀ z : ℂ, g.eval z = 0 → ‖z‖ ≤ 1 := by
    intro z hz
    apply hroots z
    rw [hp]
    simp [hz]
  have hbound := norm_eval_le_reflected hgroots hξ
  rw [reduced_polynomial_integral hp hpa ξ, norm_mul] at hbound
  have hnorm := congrArg norm (reflected_reduced_integral hp hpa ξ)
  rw [Complex.norm_conj, norm_mul] at hnorm
  rw [hnorm] at hbound
  nlinarith [norm_pos_iff.mpr hpa]

/-- The two normalized critical-point integrals satisfy the reflection
comparison at every point of the closed unit disk. -/
theorem reflection_integral_comparison (p : Polynomial ℂ) {a : ℂ}
    (ha : p.eval a = 0) (hpa : p.derivative.eval a ≠ 0)
    (hroots : ∀ z : ℂ, p.eval z = 0 → ‖z‖ ≤ 1) {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1) :
    ‖∫ t : ℝ in 0..1,
      (p.derivative.roots.map (fun ζ => 1 + (t : ℂ) * (ξ - a) / (a - ζ))).prod‖ ≤
    ‖∫ t : ℝ in 0..1,
      (p.derivative.roots.map
        (fun ζ => conj ξ + (1 - a * conj ξ) * (t : ℂ) / (a - ζ))).prod‖ := by
  obtain ⟨g, hg⟩ := Polynomial.dvd_iff_isRoot.mpr ha
  exact reflection_integral_comparison_of_linear_factor hg hpa hroots hξ

end Schmeisser

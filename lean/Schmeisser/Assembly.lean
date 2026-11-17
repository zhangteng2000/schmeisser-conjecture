import Schmeisser.ScalarExclusion
import Schmeisser.Rotation
import Schmeisser.Quadratic

/-!
# Geometric assembly

The all-degree conclusion below is conditional on the explicitly stated
scalar exclusion assertion. Rotation removes the restriction to real zeros,
and diameter disks cover the real convex hull. The quadratic case is proved
separately and does not use the scalar assertion.
-/

noncomputable section

namespace Schmeisser

open Polynomial
open scoped BigOperators

theorem simple_real_root_diameter_covered_of_criterion (p : Polynomial ℂ)
    (hn : 2 ≤ p.natDegree) (a : ℝ) (ha0 : 0 ≤ a)
    (hpa : p.derivative.eval (a : ℂ) ≠ 0)
    (hroots : ∀ z : ℂ, p.eval z = 0 → ‖z‖ ≤ 1)
    (hcrit : 1 ≤ criticalReciprocalSecondMoment p (a : ℂ) ∧
      (a * (criticalReciprocalMean p (a : ℂ)).im) ^ 2 ≤
        (criticalReciprocalSecondMoment p (a : ℂ) - 1) *
          ((1 - a ^ 2) * criticalReciprocalSecondMoment p (a : ℂ) +
            2 * a * (criticalReciprocalMean p (a : ℂ)).re - 1))
    (ξ : ℂ) (hξ : ‖ξ - ((a / 2 : ℝ) : ℂ)‖ ≤ a / 2) :
    ∃ ζ : ℂ, p.derivative.eval ζ = 0 ∧ ‖ξ - ζ‖ ≤ 1 := by
  let μ := criticalReciprocalMean p (a : ℂ)
  let s := criticalReciprocalSecondMoment p (a : ℂ)
  let m : ℝ := ((p.natDegree - 1 : ℕ) : ℝ)
  have hm : 0 < m := by dsimp [m]; exact_mod_cast (show 0 < p.natDegree - 1 by omega)
  have hdelta := critical_reciprocal_delta_nonneg p a hn hroots hpa
  have hdet : a ^ 2 * μ.im ^ 2 ≤
      (s - 1) * ((1 - a ^ 2) * s + 2 * a * μ.re - 1) := by
    simpa only [mul_pow] using hcrit.2
  obtain ⟨j, hj, hdist⟩ := reciprocal_moment_covering (rootIndices p.derivative)
    a m s μ ξ (fun j => 1 / ((a : ℂ) - j.1)) Prod.fst ha0 hm hcrit.1
    (by dsimp [m]; exact_mod_cast critical_rootIndices_card p)
    (fun j hj => critical_reciprocal_relation hpa hj)
    (critical_reciprocal_second_moment p (a : ℂ) hn)
    (critical_reciprocal_first_moment p (a : ℂ) hn) hdelta hdet hξ
  exact ⟨j.1, eval_eq_zero_of_mem_rootIndices hj, hdist⟩

theorem positive_real_root_diameter_covered (hcriterion : InteriorMomentCriterion)
    (p : Polynomial ℂ) (hn : 3 ≤ p.natDegree) (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1)
    (ha : p.eval (a : ℂ) = 0)
    (hroots : ∀ z : ℂ, p.eval z = 0 → ‖z‖ ≤ 1)
    (ξ : ℂ) (hξ : ‖ξ - ((a / 2 : ℝ) : ℂ)‖ ≤ a / 2) :
    ∃ ζ : ℂ, p.derivative.eval ζ = 0 ∧ ‖ξ - ζ‖ ≤ 1 := by
  by_cases hpa : p.derivative.eval (a : ℂ) = 0
  · refine ⟨(a : ℂ), hpa, ?_⟩
    have hball : ξ ∈ diameterBall (a : ℂ) := by
      simpa [diameterBall, Complex.real_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ha0, div_eq_mul_inv, mul_comm] using hξ
    have hdist := norm_sub_le_of_mem_diameterBall hball
    have hnorm : ‖(a : ℂ)‖ ≤ 1 := by
      simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha0] using ha1
    exact hdist.trans hnorm
  · by_cases haeq : a = 1
    · subst a
      apply unit_root_diameter_covered p (by omega) hroots ha ξ
      simpa using hξ
    · have halt : a < 1 := lt_of_le_of_ne ha1 haeq
      exact simple_real_root_diameter_covered_of_criterion p (by omega) a ha0.le hpa hroots
        (hcriterion p hn a ha0 halt ha hpa hroots) ξ hξ

theorem main_of_interior_moment_criterion (hcriterion : InteriorMomentCriterion)
    (p : Polynomial ℂ) (hn : 2 ≤ p.natDegree)
    (hroots : ∀ z : ℂ, p.eval z = 0 → ‖z‖ ≤ 1)
    (ξ : ℂ) (hξ : ξ ∈ convexHull ℝ {z : ℂ | p.eval z = 0}) :
    ∃ ζ : ℂ, p.derivative.eval ζ = 0 ∧ ‖ξ - ζ‖ ≤ 1 := by
  by_cases htwo : p.natDegree = 2
  · exact quadratic p htwo hroots ξ hξ
  · have hn3 : 3 ≤ p.natDegree := by omega
    obtain ⟨a, ha, hξa⟩ := convexHull_covered_by_diameter_disks hξ
    by_cases ha0 : a = 0
    · subst a
      have hξ0 : ξ = 0 := by simpa using hξa
      subst ξ
      exact origin_within_one_of_critical_point hn hroots
    · let ρ := a / (‖a‖ : ℂ)
      let q := rotatedPolynomial p ρ
      have hρ : ‖ρ‖ = 1 := unit_direction_norm ha0
      have hρ0 : ρ ≠ 0 := by intro h; simp [h] at hρ
      have hρa : ρ * (‖a‖ : ℂ) = a := unit_direction_mul_norm ha0
      have hqdeg : q.natDegree = p.natDegree := rotatedPolynomial_natDegree p hρ0
      have hqroot : q.eval (‖a‖ : ℂ) = 0 := by
        change (rotatedPolynomial p ρ).eval (‖a‖ : ℂ) = 0
        rw [rotatedPolynomial_eval, hρa]
        exact ha
      have hqroots : ∀ z : ℂ, q.eval z = 0 → ‖z‖ ≤ 1 :=
        rotatedPolynomial_roots_in_unit_disk p hρ hroots
      have hξrot : ‖ξ / ρ - ((‖a‖ / 2 : ℝ) : ℂ)‖ ≤ ‖a‖ / 2 :=
        unit_rotation_disk hρ hρa hξa
      obtain ⟨ζ, hζ, hdist⟩ := positive_real_root_diameter_covered hcriterion q
        (by omega) ‖a‖ (norm_pos_iff.mpr ha0) (hroots a ha) hqroot hqroots (ξ / ρ) hξrot
      refine ⟨ρ * ζ, ?_, ?_⟩
      · change (rotatedPolynomial p ρ).derivative.eval ζ = 0 at hζ
        rw [rotatedPolynomial_derivative_eval] at hζ
        exact (mul_eq_zero.mp hζ).resolve_left hρ0
      · rw [unit_rotation_distance hρ]
        exact hdist

/-- Conditional assembly of the full all-degree theorem. The remaining
scalar estimate is an explicit hypothesis, not an axiom or an admitted lemma. -/
theorem main_of_scalar_exclusion (hexclude : ScalarExclusion)
    (p : Polynomial ℂ) (hn : 2 ≤ p.natDegree)
    (hroots : ∀ z : ℂ, p.eval z = 0 → ‖z‖ ≤ 1)
    (ξ : ℂ) (hξ : ξ ∈ convexHull ℝ {z : ℂ | p.eval z = 0}) :
    ∃ ζ : ℂ, p.derivative.eval ζ = 0 ∧ ‖ξ - ζ‖ ≤ 1 :=
  main_of_interior_moment_criterion
    (interior_moment_criterion_of_scalar_exclusion hexclude) p hn hroots ξ hξ

end Schmeisser

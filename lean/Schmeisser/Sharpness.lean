import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Tactic

/-!
# Optimality of the constant in Schmeisser's conjecture

For every degree `n ≥ 2`, the polynomial `X ^ n - 1` has all its zeros on the
unit circle and has exactly one distinct critical point, namely zero. Its zero
`1` therefore rules out every bound strictly smaller than one.

This module is independent of the proof of Schmeisser's conjecture.
-/

noncomputable section

namespace Schmeisser

open Polynomial

/-- The polynomial witnessing sharpness in degree `n`. -/
def sharpnessPolynomial (n : ℕ) : Polynomial ℂ := X ^ n - 1

theorem sharpnessPolynomial_natDegree (n : ℕ) :
    (sharpnessPolynomial n).natDegree = n := by
  simpa [sharpnessPolynomial] using
    (Polynomial.natDegree_X_pow_sub_C (R := ℂ) (n := n) (r := 1))

theorem sharpnessPolynomial_eval_one (n : ℕ) :
    (sharpnessPolynomial n).eval 1 = 0 := by
  simp [sharpnessPolynomial]

theorem sharpnessPolynomial_root_norm {n : ℕ} (hn : 0 < n)
    {z : ℂ} (hz : (sharpnessPolynomial n).eval z = 0) : ‖z‖ = 1 := by
  have hpow : z ^ n = 1 := by
    simpa [sharpnessPolynomial, sub_eq_zero] using hz
  exact Complex.norm_eq_one_of_pow_eq_one hpow (Nat.ne_of_gt hn)

theorem sharpnessPolynomial_derivative_eval_eq_zero_iff {n : ℕ} (hn : 2 ≤ n)
    (z : ℂ) : (sharpnessPolynomial n).derivative.eval z = 0 ↔ z = 0 := by
  have hn0 : n ≠ 0 := by omega
  have hnm1 : n - 1 ≠ 0 := by omega
  have hcast : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  simp [sharpnessPolynomial, Polynomial.derivative_X_pow, hcast,
    pow_eq_zero_iff hnm1]

theorem one_mem_convexHull_sharpnessPolynomial (n : ℕ) :
    (1 : ℂ) ∈ convexHull ℝ {z : ℂ | (sharpnessPolynomial n).eval z = 0} := by
  exact subset_convexHull ℝ _ (sharpnessPolynomial_eval_one n)

theorem sharpnessPolynomial_critical_distance {n : ℕ} (hn : 2 ≤ n)
    {z : ℂ} (hz : (sharpnessPolynomial n).derivative.eval z = 0) :
    ‖(1 : ℂ) - z‖ = 1 := by
  rw [(sharpnessPolynomial_derivative_eval_eq_zero_iff hn z).mp hz]
  simp

/-- In every degree at least two, one is the smallest possible universal
distance bound in the convex-hull conclusion. -/
theorem sharpness (n : ℕ) (hn : 2 ≤ n) (r : ℝ) (hr : r < 1) :
    ∃ p : Polynomial ℂ, p.natDegree = n ∧
      (∀ z : ℂ, p.eval z = 0 → ‖z‖ ≤ 1) ∧
      ∃ ξ : ℂ, ξ ∈ convexHull ℝ {z : ℂ | p.eval z = 0} ∧
        ¬ ∃ ζ : ℂ, p.derivative.eval ζ = 0 ∧ ‖ξ - ζ‖ ≤ r := by
  refine ⟨sharpnessPolynomial n, sharpnessPolynomial_natDegree n, ?_,
    1, one_mem_convexHull_sharpnessPolynomial n, ?_⟩
  · intro z hz
    exact (sharpnessPolynomial_root_norm (by omega) hz).le
  · rintro ⟨ζ, hζ, hdist⟩
    rw [sharpnessPolynomial_critical_distance hn hζ] at hdist
    exact (not_le_of_gt hr) hdist

end Schmeisser

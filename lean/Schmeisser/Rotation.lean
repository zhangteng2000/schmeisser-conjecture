import Schmeisser.Basic
import Schmeisser.Geometry

/-!
# Rotation of a polynomial and its diameter disks

The change of variable `z ↦ ρ z`, for `‖ρ‖ = 1`, preserves the degree,
root bounds, critical points and distances. No leading-coefficient
normalization is needed.
-/

noncomputable section

namespace Schmeisser

open Polynomial

def rotatedPolynomial (p : Polynomial ℂ) (ρ : ℂ) : Polynomial ℂ :=
  p.comp (C ρ * X)

@[simp]
theorem rotatedPolynomial_eval (p : Polynomial ℂ) (ρ z : ℂ) :
    (rotatedPolynomial p ρ).eval z = p.eval (ρ * z) := by
  simp [rotatedPolynomial]

theorem rotatedPolynomial_derivative_eval (p : Polynomial ℂ) (ρ z : ℂ) :
    (rotatedPolynomial p ρ).derivative.eval z = ρ * p.derivative.eval (ρ * z) := by
  simp [rotatedPolynomial, Polynomial.derivative_comp, Polynomial.derivative_mul]

theorem rotatedPolynomial_natDegree (p : Polynomial ℂ) {ρ : ℂ} (hρ : ρ ≠ 0) :
    (rotatedPolynomial p ρ).natDegree = p.natDegree := by
  simp [rotatedPolynomial, Polynomial.natDegree_comp, Polynomial.natDegree_C_mul hρ]

theorem rotatedPolynomial_roots_in_unit_disk (p : Polynomial ℂ) {ρ : ℂ} (hρ : ‖ρ‖ = 1)
    (hroots : ∀ z : ℂ, p.eval z = 0 → ‖z‖ ≤ 1) :
    ∀ z : ℂ, (rotatedPolynomial p ρ).eval z = 0 → ‖z‖ ≤ 1 := by
  intro z hz
  have h := hroots (ρ * z) (by simpa using hz)
  simpa [norm_mul, hρ] using h

theorem unit_direction_norm {a : ℂ} (ha : a ≠ 0) : ‖a / (‖a‖ : ℂ)‖ = 1 := by
  simp [Complex.norm_real, norm_ne_zero_iff.mpr ha]

theorem unit_direction_mul_norm {a : ℂ} (ha : a ≠ 0) :
    (a / (‖a‖ : ℂ)) * (‖a‖ : ℂ) = a := by
  apply div_mul_cancel₀
  exact_mod_cast norm_ne_zero_iff.mpr ha

theorem unit_rotation_disk {a ρ ξ : ℂ} {r : ℝ} (hρ : ‖ρ‖ = 1)
    (har : ρ * (r : ℂ) = a) (hξ : ‖ξ - a / 2‖ ≤ r / 2) :
    ‖ξ / ρ - ((r / 2 : ℝ) : ℂ)‖ ≤ r / 2 := by
  have hρ0 : ρ ≠ 0 := by intro h; simp [h] at hρ
  have heq : ξ / ρ - (r : ℂ) / 2 = (ξ - a / 2) / ρ := by
    calc
      _ = (ξ - (ρ * (r : ℂ)) / 2) / ρ := by field_simp
      _ = _ := by rw [har]
  rw [Complex.ofReal_div]
  norm_num only [Complex.ofReal_ofNat]
  rw [heq, norm_div, hρ, div_one]
  exact hξ

theorem unit_rotation_distance {ρ ξ ζ : ℂ} (hρ : ‖ρ‖ = 1) :
    ‖ξ - ρ * ζ‖ = ‖ξ / ρ - ζ‖ := by
  have hρ0 : ρ ≠ 0 := by intro h; simp [h] at hρ
  calc
    ‖ξ - ρ * ζ‖ = ‖ρ * (ξ / ρ - ζ)‖ := by congr 1; field_simp
    _ = ‖ξ / ρ - ζ‖ := by rw [norm_mul, hρ, one_mul]

end Schmeisser

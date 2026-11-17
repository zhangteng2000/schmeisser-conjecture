import Schmeisser.FiniteDegreeExclusion
import Schmeisser.LargeDegreeExclusion
import Schmeisser.Assembly
import Schmeisser.Sharpness

namespace Schmeisser

theorem scalar_exclusion : ScalarExclusion := by
  classical
  intro m hm jset η hcard u h hu0 hu1 hh0 hh1 hη hV hpolar
  have hV' : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (m : ℝ) * (u * (1 - u)) := by
    simpa only [mul_assoc] using hV
  by_cases hlarge : 6000 ≤ m
  · exact large_degree_scalar_exclusion jset η m hlarge hcard hu0 hu1 hh0 hh1 hη hV' hpolar
  · exact finite_degree_scalar_exclusion jset η m hm (by omega) hcard
      hu0 hu1 hh0 hh1 hη hV' hpolar

theorem main (p : Polynomial ℂ) (hn : 2 ≤ p.natDegree)
    (hroots : ∀ z : ℂ, p.eval z = 0 → ‖z‖ ≤ 1)
    (ξ : ℂ) (hξ : ξ ∈ convexHull ℝ {z : ℂ | p.eval z = 0}) :
    ∃ ζ : ℂ, p.derivative.eval ζ = 0 ∧ ‖ξ - ζ‖ ≤ 1 :=
  main_of_scalar_exclusion scalar_exclusion p hn hroots ξ hξ

/-- In each degree at least two, the universal distance bounds are exactly
the real constants greater than or equal to one. -/
theorem universal_bound_iff (n : ℕ) (hn : 2 ≤ n) (r : ℝ) :
    (∀ p : Polynomial ℂ, p.natDegree = n →
      (∀ z : ℂ, p.eval z = 0 → ‖z‖ ≤ 1) →
      ∀ ξ : ℂ, ξ ∈ convexHull ℝ {z : ℂ | p.eval z = 0} →
        ∃ ζ : ℂ, p.derivative.eval ζ = 0 ∧ ‖ξ - ζ‖ ≤ r) ↔ 1 ≤ r := by
  constructor
  · intro hbound
    by_contra hr
    obtain ⟨p, hp, hroots, ξ, hξ, hfail⟩ := sharpness n hn r (lt_of_not_ge hr)
    exact hfail (hbound p hp hroots ξ hξ)
  · intro hr p hp hroots ξ hξ
    obtain ⟨ζ, hζ, hdist⟩ := main p (by omega) hroots ξ hξ
    exact ⟨ζ, hζ, hdist.trans hr⟩

end Schmeisser

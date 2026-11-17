import Mathlib.Analysis.Complex.Polynomial.GaussLucas
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Tactic

/-!
Basic polynomial facts used in the geometric reduction.  The zero set is
written using evaluation, so that the final statement has no convention about
`Polynomial.rootSet` at the zero polynomial.
-/

namespace Schmeisser

open Polynomial

theorem polynomial_ne_zero_of_two_le_natDegree {p : Polynomial ℂ}
    (hn : 2 ≤ p.natDegree) : p ≠ 0 := by
  intro hp
  subst p
  simp at hn

theorem rootSet_eq_zeroSet {p : Polynomial ℂ} (hp : p ≠ 0) :
    p.rootSet ℂ = {z : ℂ | p.eval z = 0} := by
  ext z
  simp [Polynomial.mem_rootSet_of_ne hp]

theorem norm_le_one_of_mem_convexHull_zeros {p : Polynomial ℂ}
    (hroots : ∀ z : ℂ, p.eval z = 0 → ‖z‖ ≤ 1)
    {ξ : ℂ} (hξ : ξ ∈ convexHull ℝ {z : ℂ | p.eval z = 0}) :
    ‖ξ‖ ≤ 1 := by
  have hsub : ({z : ℂ | p.eval z = 0} : Set ℂ) ⊆ Metric.closedBall 0 1 := by
    intro z hz
    simpa [Metric.mem_closedBall, dist_zero_right] using hroots z hz
  have hx := convexHull_min hsub (convex_closedBall (0 : ℂ) (1 : ℝ)) hξ
  simpa [Metric.mem_closedBall, dist_zero_right] using hx

theorem critical_point_norm_le_one {p : Polynomial ℂ}
    (hn : 2 ≤ p.natDegree)
    (hroots : ∀ z : ℂ, p.eval z = 0 → ‖z‖ ≤ 1)
    {ζ : ℂ} (hζ : p.derivative.eval ζ = 0) : ‖ζ‖ ≤ 1 := by
  have hp : p ≠ 0 := polynomial_ne_zero_of_two_le_natDegree hn
  have hdp : 0 < p.derivative.natDegree := by
    rw [Polynomial.natDegree_derivative]
    omega
  have hpd : p.derivative ≠ 0 := by
    intro h
    simp [h] at hdp
  have hdeg : 0 < p.degree := Polynomial.natDegree_pos_iff_degree_pos.mp (by omega)
  have hmem : ζ ∈ p.derivative.rootSet ℂ := by
    rw [rootSet_eq_zeroSet hpd]
    exact hζ
  have hHull := Polynomial.rootSet_derivative_subset_convexHull_rootSet hdeg hmem
  rw [rootSet_eq_zeroSet hp] at hHull
  exact norm_le_one_of_mem_convexHull_zeros hroots hHull

theorem exists_critical_point {p : Polynomial ℂ} (hn : 2 ≤ p.natDegree) :
    ∃ ζ : ℂ, p.derivative.eval ζ = 0 := by
  have hdp : 0 < p.derivative.natDegree := by
    rw [Polynomial.natDegree_derivative]
    omega
  exact Complex.exists_root (Polynomial.natDegree_pos_iff_degree_pos.mp hdp)

theorem origin_within_one_of_critical_point {p : Polynomial ℂ}
    (hn : 2 ≤ p.natDegree)
    (hroots : ∀ z : ℂ, p.eval z = 0 → ‖z‖ ≤ 1) :
    ∃ ζ : ℂ, p.derivative.eval ζ = 0 ∧ ‖(0 : ℂ) - ζ‖ ≤ 1 := by
  obtain ⟨ζ, hζ⟩ := exists_critical_point hn
  exact ⟨ζ, hζ, by simpa using critical_point_norm_le_one hn hroots hζ⟩

end Schmeisser

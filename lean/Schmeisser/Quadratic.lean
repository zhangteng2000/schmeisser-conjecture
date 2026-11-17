import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Convex.Hull
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic

/-!
# The quadratic case

The critical point of a quadratic is the midpoint of its two zeros, counted
with multiplicity. Both zeros lie in the closed unit ball about this midpoint,
so their real convex hull lies in the same ball.
-/

noncomputable section

namespace Schmeisser

open Polynomial

theorem norm_sub_half_add_le_one {a b : ℂ} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖a - (a + b) / 2‖ ≤ 1 := by
  have hab : ‖a - b‖ ≤ 2 := (norm_sub_le a b).trans (by linarith)
  calc
    ‖a - (a + b) / 2‖ = ‖(a - b) / 2‖ := by congr 1; ring
    _ = ‖a - b‖ / 2 := by rw [norm_div]; norm_num
    _ ≤ 1 := by linarith

/-- The full convex-hull conclusion in degree two, including repeated zeros. -/
theorem quadratic (p : Polynomial ℂ) (hn : p.natDegree = 2)
    (hroots : ∀ z : ℂ, p.eval z = 0 → ‖z‖ ≤ 1)
    (ξ : ℂ) (hξ : ξ ∈ convexHull ℝ {z : ℂ | p.eval z = 0}) :
    ∃ ζ : ℂ, p.derivative.eval ζ = 0 ∧ ‖ξ - ζ‖ ≤ 1 := by
  have hp : p ≠ 0 := by
    intro h
    simp [h] at hn
  have hs : p.Splits := IsAlgClosed.splits p
  have hc : p.roots.card = 2 := by rw [← hs.natDegree_eq_card_roots, hn]
  obtain ⟨a, b, hab⟩ := Multiset.card_eq_two.mp hc
  have hfac : p = C p.leadingCoeff * ((X - C a) * (X - C b)) := by
    calc
      p = C p.leadingCoeff * (p.roots.map (X - C ·)).prod := hs.eq_prod_roots
      _ = C p.leadingCoeff * ((X - C a) * (X - C b)) := by simp [hab]
  have ha : p.eval a = 0 := (Polynomial.mem_roots hp).mp (by simp [hab])
  have hb : p.eval b = 0 := (Polynomial.mem_roots hp).mp (by simp [hab])
  have hcritical : p.derivative.eval ((a + b) / 2) = 0 := by
    rw [hfac]
    simp only [derivative_mul, derivative_C, derivative_sub, derivative_X,
      zero_mul, sub_zero, one_mul, mul_one, zero_add, eval_mul, eval_C,
      eval_add, eval_sub, eval_X]
    ring
  have hsub : ({z : ℂ | p.eval z = 0} : Set ℂ) ⊆
      Metric.closedBall ((a + b) / 2) 1 := by
    intro z hz
    have hzab : z = a ∨ z = b := by
      have hmem := (Polynomial.mem_roots hp).mpr hz
      simpa [hab] using hmem
    rcases hzab with hza | hzb
    · rw [hza]
      simpa [Metric.mem_closedBall, dist_eq_norm] using
        norm_sub_half_add_le_one (hroots a ha) (hroots b hb)
    · rw [hzb]
      simpa [Metric.mem_closedBall, dist_eq_norm, add_comm a b] using
        norm_sub_half_add_le_one (hroots b hb) (hroots a ha)
  refine ⟨(a + b) / 2, hcritical, ?_⟩
  have hball := convexHull_min hsub (convex_closedBall ((a + b) / 2) 1) hξ
  simpa [Metric.mem_closedBall, dist_eq_norm] using hball

end Schmeisser

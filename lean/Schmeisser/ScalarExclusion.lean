import Schmeisser.Cubic

/-!
# The remaining scalar assertion

`ScalarExclusion` states the strict inequality needed for critical-point
counts at least three. The theorem below proves how this assertion implies
the interior moment criterion. It retains the scalar assertion as an
explicit argument.
-/

noncomputable section

namespace Schmeisser

open Polynomial MeasureTheory
open scoped BigOperators

def ScalarExclusion : Prop :=
  ∀ (m : ℕ), 3 ≤ m → ∀ (jset : Finset (ℂ × ℕ)) (η : ℂ × ℕ → ℂ),
    jset.card = m → ∀ (u h : ℝ), 0 < u → u < 1 → 0 < h → h < 1 →
    (∑ j ∈ jset, η j) = 0 →
    (∑ j ∈ jset, ‖η j‖ ^ 2) ≤ (m : ℝ) * u * (1 - u) →
    (1 ≤ ∫ t : ℝ in 0..1, (1 - h + h * (1 + u) * t) ^ ((m : ℝ) / 2)) →
    ((m : ℝ) + 1) * (∫ t : ℝ in 0..1,
      (max (1 - 2 * u * t + u * t ^ 2 - h * t * (1 - t)) 0) ^ ((m : ℝ) / 2)) <
    (((m : ℝ) + 1) * ∫ t : ℝ in 0..1, (1 - u * t) ^ m) -
      centeredErrorIntegral jset η m u

def InteriorMomentCriterion : Prop :=
  ∀ (p : Polynomial ℂ), 3 ≤ p.natDegree → ∀ (a : ℝ), 0 < a → a < 1 →
    p.eval (a : ℂ) = 0 → p.derivative.eval (a : ℂ) ≠ 0 →
    (∀ z : ℂ, p.eval z = 0 → ‖z‖ ≤ 1) →
    1 ≤ criticalReciprocalSecondMoment p (a : ℂ) ∧
      (a * (criticalReciprocalMean p (a : ℂ)).im) ^ 2 ≤
        (criticalReciprocalSecondMoment p (a : ℂ) - 1) *
          ((1 - a ^ 2) * criticalReciprocalSecondMoment p (a : ℂ) +
            2 * a * (criticalReciprocalMean p (a : ℂ)).re - 1)

theorem interior_moment_criterion_of_scalar_exclusion (hexclude : ScalarExclusion) :
    InteriorMomentCriterion := by
  intro p hn a ha0 ha1 ha hpa hroots
  by_cases h3 : p.natDegree = 3
  · exact cubic_moment_criterion p h3 a ha0 ha1 ha hpa hroots
  · by_contra hfail
    obtain ⟨σ, hσ, hsσ, hu0, hu1, hh0, hh1, hsum, hsq, hpolar, hsecond⟩ :=
      necessary_integrals_of_failure p hn a ha0 ha1 ha hpa hroots hfail
    let m := p.natDegree - 1
    let u := ‖criticalReciprocalMean p (a : ℂ)‖ ^ 2 / σ
    let h := (1 - a ^ 2) *
      (1 - u + ((1 - a ^ 2) * σ + 2 * a * (criticalReciprocalMean p (a : ℂ)).re - 1))
    let η := criticalCenteredIncrement p a σ
    have hm : 3 ≤ m := by dsimp [m]; omega
    have hcard : (rootIndices p.derivative).card = m := critical_rootIndices_card p
    have hult : u < 1 := necessary_scalar_parameter_lt_one (rootIndices p.derivative) η m
      (by omega) hcard u h hu1 hh0 hsq hsecond
    have hstrict := hexclude m hm (rootIndices p.derivative) η hcard u h
      hu0 hult hh0 hh1 hsum hsq hpolar
    exact (not_le_of_gt hstrict) hsecond

end Schmeisser

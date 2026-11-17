import Schmeisser.NecessaryIntegrals
import Schmeisser.ScalarIntegrals

/-!
# The endpoint parameter and the cubic case

At `u = 1` the second-moment bound forces every centred increment to vanish.
The second necessary integral inequality then contradicts its strict scalar
bound. In degree three the first inequality forces this excluded endpoint.
-/

noncomputable section

namespace Schmeisser

open Polynomial MeasureTheory
open scoped BigOperators

theorem centeredErrorIntegral_eq_zero_of_sq_sum_nonpos {ι : Type*}
    (jset : Finset ι) (η : ι → ℂ) (m : ℕ) (u : ℝ) (hcard : jset.card = m)
    (hsq : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ 0) : centeredErrorIntegral jset η m u = 0 := by
  have hη : ∀ j ∈ jset, η j = 0 := by
    intro j hj
    have hjle := Finset.single_le_sum (fun k _ => sq_nonneg ‖η k‖) hj
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (η j)]
  have hprod (t : ℝ) :
      (∏ j ∈ jset, (((1 - u * t : ℝ) : ℂ) + (t : ℂ) * η j)) =
        ((1 - u * t : ℝ) : ℂ) ^ m := by
    calc
      _ = ∏ _j ∈ jset, ((1 - u * t : ℝ) : ℂ) := by
        apply Finset.prod_congr rfl
        intro j hj
        rw [hη j hj]
        simp
      _ = _ := by simp [hcard]
  simp only [centeredErrorIntegral, hprod, sub_self, norm_zero]
  simp

theorem polynomial_baseline_integral_one (m : ℕ) :
    ((m : ℝ) + 1) * (∫ t : ℝ in 0..1, (1 - t) ^ m) = 1 := by
  have hi : (∫ t : ℝ in 0..1, (1 - t) ^ m) = 1 / ((m : ℝ) + 1) := by
    calc
      _ = ∫ t : ℝ in 0..1, t ^ m := by
        simpa using intervalIntegral.integral_comp_sub_left (fun t : ℝ => t ^ m)
          (a := (0 : ℝ)) (b := (1 : ℝ)) 1
      _ = _ := by rw [integral_pow]; simp
  rw [hi]
  field_simp

theorem necessary_scalar_parameter_lt_one {ι : Type*}
    (jset : Finset ι) (η : ι → ℂ) (m : ℕ) (hm : 0 < m) (hcard : jset.card = m)
    (u h : ℝ) (hu1 : u ≤ 1) (hh : 0 < h)
    (hsq : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (m : ℝ) * u * (1 - u))
    (hsecond : (((m : ℝ) + 1) * ∫ t : ℝ in 0..1, (1 - u * t) ^ m) -
      centeredErrorIntegral jset η m u ≤
      ((m : ℝ) + 1) * ∫ t : ℝ in 0..1,
        (max (1 - 2 * u * t + u * t ^ 2 - h * t * (1 - t)) 0) ^ ((m : ℝ) / 2)) :
    u < 1 := by
  refine lt_of_le_of_ne hu1 ?_
  intro hu
  subst u
  have hsq0 : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ 0 := by simpa using hsq
  have herror := centeredErrorIntegral_eq_zero_of_sq_sum_nonpos jset η m 1 hcard hsq0
  have hbase : ((m : ℝ) + 1) * (∫ t : ℝ in 0..1, (1 - 1 * t) ^ m) = 1 := by
    simpa using polynomial_baseline_integral_one m
  rw [hbase, herror, sub_zero] at hsecond
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hstrict := unit_parameter_second_integral_lt (r := (m : ℝ) / 2) hh (by positivity)
  have hcoef : 2 * ((m : ℝ) / 2) + 1 = (m : ℝ) + 1 := by ring
  rw [hcoef] at hstrict
  have hpoly (t : ℝ) : 1 - 2 * 1 * t + 1 * t ^ 2 - h * t * (1 - t) =
      (1 - t) ^ 2 - h * t * (1 - t) := by ring
  simp_rw [hpoly] at hsecond
  exact (not_le_of_gt hstrict) hsecond

/-- The reciprocal-moment covering criterion holds at every nonzero
simple interior zero of a cubic. -/
theorem cubic_moment_criterion (p : Polynomial ℂ) (hn : p.natDegree = 3)
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (ha : p.eval (a : ℂ) = 0) (hpa : p.derivative.eval (a : ℂ) ≠ 0)
    (hroots : ∀ z : ℂ, p.eval z = 0 → ‖z‖ ≤ 1) :
    1 ≤ criticalReciprocalSecondMoment p (a : ℂ) ∧
      (a * (criticalReciprocalMean p (a : ℂ)).im) ^ 2 ≤
        (criticalReciprocalSecondMoment p (a : ℂ) - 1) *
          ((1 - a ^ 2) * criticalReciprocalSecondMoment p (a : ℂ) +
            2 * a * (criticalReciprocalMean p (a : ℂ)).re - 1) := by
  by_contra hfail
  obtain ⟨σ, hσ, hsσ, hu0, hu1, hh0, hh1, hsum, hsq, hpolar, hsecond⟩ :=
    necessary_integrals_of_failure p (by omega) a ha0 ha1 ha hpa hroots hfail
  let u := ‖criticalReciprocalMean p (a : ℂ)‖ ^ 2 / σ
  let h := (1 - a ^ 2) *
    (1 - u + ((1 - a ^ 2) * σ + 2 * a * (criticalReciprocalMean p (a : ℂ)).re - 1))
  let η := criticalCenteredIncrement p a σ
  have hm : p.natDegree - 1 = 2 := by omega
  rw [hm] at hsq hpolar hsecond
  have hcard : (rootIndices p.derivative).card = 2 := by rw [critical_rootIndices_card, hm]
  have hult : u < 1 := necessary_scalar_parameter_lt_one (rootIndices p.derivative) η 2
    (by decide) hcard u h hu1 hh0 hsq hsecond
  have hp' : 1 ≤ ∫ t : ℝ in 0..1, 1 - h + h * (1 + u) * t := by
    simpa only [Nat.cast_ofNat, div_self (by norm_num : (2 : ℝ) ≠ 0), Real.rpow_one] using hpolar
  have huge : 1 ≤ u := polar_integral_cubic_parameter hu0.le hh0 hh1.le hp'
  exact (not_le_of_gt hult) huge

end Schmeisser

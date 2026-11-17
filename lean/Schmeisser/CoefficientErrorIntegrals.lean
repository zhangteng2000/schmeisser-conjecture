import Schmeisser.CoefficientExpansion
import Schmeisser.NatBetaIntegrals
import Schmeisser.NecessaryIntegrals

open scoped BigOperators
open MeasureTheory Set

namespace Schmeisser

theorem centred_homogeneous_error_eq_sum {ι : Type*}
    (jset : Finset ι) (η : ι → ℂ) (hm : 1 ≤ jset.card)
    (hη : ∑ j ∈ jset, η j = 0) (d t : ℂ) :
    (∏ j ∈ jset, (d + t * η j)) - d ^ jset.card =
      ∑ k ∈ Finset.Ico 2 (jset.card + 1),
        (centredGeneratingPolynomial jset η).coeff k * d ^ (jset.card - k) * t ^ k := by
  classical
  rw [Finset.sum_Ico_eq_sub _ (by omega : 2 ≤ jset.card + 1)]
  rw [← centredGeneratingPolynomial_homogeneous_eval]
  simp [Finset.sum_range_succ, hη]

theorem centred_homogeneous_error_norm_le {ι : Type*}
    (jset : Finset ι) (η : ι → ℂ) (hm : 1 ≤ jset.card)
    (hη : ∑ j ∈ jset, η j = 0) (d t : ℝ) (hd : 0 ≤ d) (ht : 0 ≤ t) :
    ‖(∏ j ∈ jset, ((d : ℂ) + (t : ℂ) * η j)) - (d : ℂ) ^ jset.card‖ ≤
      ∑ k ∈ Finset.Ico 2 (jset.card + 1),
        ‖(centredGeneratingPolynomial jset η).coeff k‖ * t ^ k * d ^ (jset.card - k) := by
  rw [centred_homogeneous_error_eq_sum jset η hm hη]
  calc
    _ ≤ ∑ k ∈ Finset.Ico 2 (jset.card + 1),
        ‖(centredGeneratingPolynomial jset η).coeff k *
          (d : ℂ) ^ (jset.card - k) * (t : ℂ) ^ k‖ := norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hd, abs_of_nonneg ht]
      ring

/-- Integrating each homogeneous coefficient gives the beta weights.
The upper limit is enlarged after the change of variable `v = u t`. -/
theorem centeredErrorIntegral_le_coefficient_sum {ι : Type*}
    (jset : Finset ι) (η : ι → ℂ) (m : ℕ) (hm : 1 ≤ m) (hcard : jset.card = m)
    (hη : ∑ j ∈ jset, η j = 0) {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) :
    centeredErrorIntegral jset η m u ≤
      ∑ k ∈ Finset.Ico 2 (m + 1),
        ‖(centredGeneratingPolynomial jset η).coeff k‖ /
          ((m.choose k : ℝ) * u ^ (k + 1)) := by
  classical
  let e : ℕ → ℝ := fun k => ‖(centredGeneratingPolynomial jset η).coeff k‖
  let f : ℕ → ℝ → ℝ := fun k t => t ^ k * (1 - u * t) ^ (m - k)
  have hf (k : ℕ) : Continuous (f k) := by dsimp [f]; fun_prop
  have hi (k : ℕ) : IntervalIntegrable (fun t => e k * f k t) volume 0 1 :=
    (continuous_const.mul (hf k)).intervalIntegrable 0 1
  have hmono : (∫ t : ℝ in 0..1,
      ‖(∏ j ∈ jset, (((1 - u * t : ℝ) : ℂ) + (t : ℂ) * η j)) -
        ((1 - u * t : ℝ) : ℂ) ^ m‖) ≤
      ∫ t : ℝ in 0..1, ∑ k ∈ Finset.Ico 2 (m + 1), e k * f k t := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      ((show Continuous (fun t : ℝ =>
        ‖(∏ j ∈ jset, (((1 - u * t : ℝ) : ℂ) + (t : ℂ) * η j)) -
          ((1 - u * t : ℝ) : ℂ) ^ m‖) by fun_prop).intervalIntegrable 0 1)
      ((show Continuous (fun t : ℝ => ∑ k ∈ Finset.Ico 2 (m + 1), e k * f k t) by
        fun_prop).intervalIntegrable 0 1)
    intro t ht
    have hd : 0 ≤ 1 - u * t := by nlinarith [ht.1, ht.2]
    simpa only [hcard, e, f, mul_assoc] using
      centred_homogeneous_error_norm_le jset η (by omega) hη (1 - u * t) t hd ht.1
  unfold centeredErrorIntegral
  calc
    _ ≤ ((m : ℝ) + 1) *
        (∫ t : ℝ in 0..1, ∑ k ∈ Finset.Ico 2 (m + 1), e k * f k t) :=
      mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = ∑ k ∈ Finset.Ico 2 (m + 1),
        e k * (((m : ℝ) + 1) * (∫ t : ℝ in 0..1, f k t)) := by
      rw [intervalIntegral.integral_finsetSum (fun k hk => hi k), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [intervalIntegral.integral_const_mul]
      ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro k hk
      have hkm : k ≤ m := by have := (Finset.mem_Ico.mp hk).2; omega
      have h := mul_le_mul_of_nonneg_left
        (scaled_beta_nat_integral_choose_le m k hkm hu0 hu1) (norm_nonneg
          ((centredGeneratingPolynomial jset η).coeff k))
      simpa only [e, f, mul_one_div] using h

end Schmeisser

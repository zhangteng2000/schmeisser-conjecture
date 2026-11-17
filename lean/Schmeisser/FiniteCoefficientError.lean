import Schmeisser.CoefficientErrorIntegrals
import Schmeisser.FiniteBetaIntegrals

open scoped BigOperators
open MeasureTheory Set

namespace Schmeisser

theorem centeredErrorIntegral_le_finite_coefficient_sum {ι : Type*}
    (jset : Finset ι) (η : ι → ℂ) (m : ℕ) (hm : 1 ≤ m) (hcard : jset.card = m)
    (hη : ∑ j ∈ jset, η j = 0) {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) :
    centeredErrorIntegral jset η m u ≤
      ∑ k ∈ Finset.Ico 2 (m + 1),
        ‖(centredGeneratingPolynomial jset η).coeff k‖ / (m.choose k : ℝ) *
          finiteBetaPolynomial m k (1 - u) := by
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
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkm : k ≤ m := by have := (Finset.mem_Ico.mp hk).2; omega
      dsimp [f, e]
      rw [beta_nat_integral_finite_div_choose m k hkm u]
      ring

theorem normalized_variance_power {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (k : ℕ) (hk : 2 ≤ k) :
    (u * (1 - u)) ^ ((k : ℝ) / 2) / (1 - u) =
      u ^ ((k : ℝ) / 2) * (1 - u) ^ (((k - 2 : ℕ) : ℝ) / 2) := by
  have heps : 0 < 1 - u := by linarith
  have hexp : (k : ℝ) / 2 = (((k - 2 : ℕ) : ℝ) / 2) + 1 := by
    rw [Nat.cast_sub hk]
    push_cast
    ring
  have hpow : (1 - u) ^ ((k : ℝ) / 2) =
      (1 - u) ^ (((k - 2 : ℕ) : ℝ) / 2) * (1 - u) := by
    rw [hexp, Real.rpow_add heps, Real.rpow_one]
  rw [Real.mul_rpow hu0.le heps.le, hpow]
  field_simp

/-- A finite coefficient estimate retaining the incomplete beta integral.
The coefficients `c` may be any bounds supplied by Newton's identities,
Cauchy's inequality, or the minimum of the two. -/
theorem centeredErrorIntegral_finite_bound {ι : Type*}
    (jset : Finset ι) (η : ι → ℂ) (m : ℕ) (hm : 1 ≤ m) (hcard : jset.card = m)
    (hη : ∑ j ∈ jset, η j = 0) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (c : ℕ → ℝ)
    (hc : ∀ k ∈ Finset.Ico 2 (m + 1),
      ‖(centredGeneratingPolynomial jset η).coeff k‖ ≤
        c k * (u * (1 - u)) ^ ((k : ℝ) / 2)) :
    centeredErrorIntegral jset η m u / (1 - u) ≤
      ∑ k ∈ Finset.Ico 2 (m + 1), c k / (m.choose k : ℝ) *
        u ^ ((k : ℝ) / 2) * (1 - u) ^ (((k - 2 : ℕ) : ℝ) / 2) *
          finiteBetaPolynomial m k (1 - u) := by
  have heps : 0 < 1 - u := by linarith
  have hsum := div_le_div_of_nonneg_right
    (centeredErrorIntegral_le_finite_coefficient_sum jset η m hm hcard hη hu0 hu1.le) heps.le
  rw [Finset.sum_div] at hsum
  refine hsum.trans (Finset.sum_le_sum ?_)
  intro k hk
  have hkm : k ≤ m := by have := (Finset.mem_Ico.mp hk).2; omega
  have hchoose : (0 : ℝ) ≤ m.choose k := by positivity
  have hF := finiteBetaPolynomial_nonneg m k heps.le
  have h := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hc k hk) hchoose) hF) heps.le
  refine h.trans_eq ?_
  calc
    _ = (c k / (m.choose k : ℝ)) *
        ((u * (1 - u)) ^ ((k : ℝ) / 2) / (1 - u)) *
          finiteBetaPolynomial m k (1 - u) := by ring
    _ = _ := by rw [normalized_variance_power hu0 hu1 k (Finset.mem_Ico.mp hk).1]; ring

end Schmeisser

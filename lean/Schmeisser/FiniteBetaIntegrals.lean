import Schmeisser.NatBetaIntegrals

open scoped BigOperators
open MeasureTheory Set

namespace Schmeisser

noncomputable def finiteBetaPolynomial (m k : ℕ) (e : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (m - k + 1), ((k + j).choose k : ℝ) * e ^ j

theorem beta_integrand_finite_expansion (m k : ℕ) (u t : ℝ) :
    t ^ k * (1 - u * t) ^ (m - k) =
      ∑ j ∈ Finset.range (m - k + 1),
        ((m - k).choose j : ℝ) * (1 - u) ^ j *
          (t ^ (k + j) * (1 - t) ^ (m - (k + j))) := by
  have heq : 1 - u * t = (1 - u) * t + (1 - t) := by ring
  rw [heq, add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_pow, pow_add]
  simp only [Nat.sub_sub]
  ring

/-- The incomplete beta integral is a finite polynomial in `1-u`. -/
theorem beta_nat_integral_finite (m k : ℕ) (hkm : k ≤ m) (u : ℝ) :
    ((m : ℝ) + 1) * (m.choose k : ℝ) *
      (∫ t : ℝ in 0..1, t ^ k * (1 - u * t) ^ (m - k)) =
      finiteBetaPolynomial m k (1 - u) := by
  let f : ℕ → ℝ → ℝ := fun j t =>
    ((m - k).choose j : ℝ) * (1 - u) ^ j * (t ^ (k + j) * (1 - t) ^ (m - (k + j)))
  have hf (j : ℕ) : IntervalIntegrable (f j) volume 0 1 :=
    (show Continuous (f j) by dsimp [f]; fun_prop).intervalIntegrable 0 1
  have hfun : (fun t : ℝ => t ^ k * (1 - u * t) ^ (m - k)) =
      fun t => ∑ j ∈ Finset.range (m - k + 1), f j t := by
    funext t
    exact beta_integrand_finite_expansion m k u t
  rw [hfun, intervalIntegral.integral_finsetSum (fun j hj => hf j), Finset.mul_sum]
  unfold finiteBetaPolynomial
  apply Finset.sum_congr rfl
  intro j hj
  have hjm : k + j ≤ m := by have := Finset.mem_range.mp hj; omega
  have hchoose : (m.choose (k + j) : ℝ) * ((k + j).choose k : ℝ) =
      (m.choose k : ℝ) * ((m - k).choose j : ℝ) := by
    exact_mod_cast (by simpa using (Nat.choose_mul (n := m) (k := k + j) (s := k) (by omega)))
  have hbeta := beta_nat_integral_choose m (k + j) hjm
  dsimp [f]
  rw [intervalIntegral.integral_const_mul]
  calc
    _ = ((m : ℝ) + 1) * ((m.choose k : ℝ) * ((m - k).choose j : ℝ)) * (1 - u) ^ j *
        (∫ t : ℝ in 0..1, t ^ (k + j) * (1 - t) ^ (m - (k + j))) := by ring
    _ = ((m : ℝ) + 1) * ((m.choose (k + j) : ℝ) * ((k + j).choose k : ℝ)) * (1 - u) ^ j *
        (∫ t : ℝ in 0..1, t ^ (k + j) * (1 - t) ^ (m - (k + j))) := by rw [hchoose]
    _ = ((k + j).choose k : ℝ) * (1 - u) ^ j *
        (((m : ℝ) + 1) * (m.choose (k + j) : ℝ) *
          (∫ t : ℝ in 0..1, t ^ (k + j) * (1 - t) ^ (m - (k + j)))) := by ring
    _ = _ := by rw [hbeta, mul_one]

theorem beta_nat_integral_finite_div_choose (m k : ℕ) (hkm : k ≤ m) (u : ℝ) :
    ((m : ℝ) + 1) * (∫ t : ℝ in 0..1, t ^ k * (1 - u * t) ^ (m - k)) =
      finiteBetaPolynomial m k (1 - u) / (m.choose k : ℝ) := by
  have hc : (0 : ℝ) < m.choose k := by exact_mod_cast Nat.choose_pos hkm
  apply (eq_div_iff hc.ne').mpr
  convert beta_nat_integral_finite m k hkm u using 1
  ring

theorem finiteBetaPolynomial_nonneg (m k : ℕ) {e : ℝ} (he : 0 ≤ e) :
    0 ≤ finiteBetaPolynomial m k e := by
  unfold finiteBetaPolynomial
  exact Finset.sum_nonneg (fun j hj => by positivity)

end Schmeisser

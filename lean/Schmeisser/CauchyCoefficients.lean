import Schmeisser.CentredProduct
import Mathlib.Analysis.Polynomial.Fourier
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Coefficient bounds for centred finite products

Parseval's identity supplies the coefficient estimate on a circle.
The arithmetic--geometric mean inequality then bounds the product on
that circle using only its first and second moments.
-/

open scoped BigOperators
open Polynomial

namespace Schmeisser

theorem norm_coeff_sq_le_circle_bound (p : Polynomial ℂ) (k : ℕ) (b : ℝ)
    (hb : ∀ z : ℂ, ‖z‖ = 1 → ‖p.eval z‖ ^ 2 ≤ b) :
    ‖p.coeff k‖ ^ 2 ≤ b := by
  classical
  have hsum : ‖p.coeff k‖ ^ 2 ≤ ∑ i ∈ p.support, ‖p.coeff i‖ ^ 2 := by
    by_cases hk : k ∈ p.support
    · exact Finset.single_le_sum (fun i hi => sq_nonneg ‖p.coeff i‖) hk
    · simp only [Polynomial.notMem_support_iff.mp hk, norm_zero, zero_pow (by decide : 2 ≠ 0)]
      exact Finset.sum_nonneg (fun i hi => sq_nonneg ‖p.coeff i‖)
  rw [p.sum_sq_norm_coeff_eq_circleAverage] at hsum
  refine hsum.trans (Real.circleAverage_mono_on_of_le_circle ?_ ?_)
  · exact ((p.continuous.norm).pow 2).continuousOn.circleIntegrable'
  · intro z hz
    apply hb
    simpa [Metric.mem_sphere, dist_zero_right] using hz

theorem norm_coeff_sq_mul_radius_pow_le (p : Polynomial ℂ) (k : ℕ)
    (r b : ℝ) (hr : 0 ≤ r)
    (hb : ∀ z : ℂ, ‖z‖ = r → ‖p.eval z‖ ^ 2 ≤ b) :
    ‖p.coeff k‖ ^ 2 * (r ^ 2) ^ k ≤ b := by
  have h := norm_coeff_sq_le_circle_bound (p.comp (C (r : ℂ) * X)) k b ?_
  · simpa only [Polynomial.comp_C_mul_X_coeff, norm_mul, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr, mul_pow, ← pow_mul,
      Nat.mul_comm k 2] using h
  · intro z hz
    rw [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    apply hb
    simp [hz, abs_of_nonneg hr]

noncomputable def centredGeneratingPolynomial {ι : Type*} (t : Finset ι) (η : ι → ℂ) :
    Polynomial ℂ := ∏ j ∈ t, (1 + C (η j) * X)

@[simp] theorem centredGeneratingPolynomial_eval {ι : Type*}
    (t : Finset ι) (η : ι → ℂ) (z : ℂ) :
    (centredGeneratingPolynomial t η).eval z = ∏ j ∈ t, (1 + η j * z) := by
  simp [centredGeneratingPolynomial, Polynomial.eval_prod]

theorem centredGeneratingPolynomial_eval_sq_le {ι : Type*}
    (t : Finset ι) (η : ι → ℂ) (V : ℝ) (hV0 : 0 ≤ V)
    (hη : ∑ j ∈ t, η j = 0)
    (hV : ∑ j ∈ t, ‖η j‖ ^ 2 ≤ (t.card : ℝ) * V) (z : ℂ) :
    ‖(centredGeneratingPolynomial t η).eval z‖ ^ 2 ≤
      (1 + V * ‖z‖ ^ 2) ^ t.card := by
  classical
  by_cases ht : t = ∅
  · simp [ht]
  have hc : (0 : ℝ) < t.card := by
    exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr ht)
  have hsum : ∑ j ∈ t, η j * z = 0 := by rw [← Finset.sum_mul, hη, zero_mul]
  have hsq := sum_norm_sq_centered t (1 : ℂ) (fun j => η j * z) 1 hsum
  simp only [one_smul, one_pow, one_mul, norm_one] at hsq
  have hm : (∑ j ∈ t, ‖1 + η j * z‖ ^ 2) / (t.card : ℝ) ≤
      1 + V * ‖z‖ ^ 2 := by
    rw [hsq]
    simp only [norm_mul, mul_pow, ← Finset.sum_mul]
    apply (div_le_iff₀ hc).mpr
    nlinarith [mul_le_mul_of_nonneg_right hV (sq_nonneg ‖z‖)]
  have hnorm := (norm_prod_le_rpow_mean_sq t (fun j => 1 + η j * z)).trans
    (Real.rpow_le_rpow (by positivity) hm (by positivity))
  have hp : 0 ≤ 1 + V * ‖z‖ ^ 2 := by positivity
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have heq : ((1 + V * ‖z‖ ^ 2) ^ ((t.card : ℝ) / 2)) ^ 2 =
      (1 + V * ‖z‖ ^ 2) ^ t.card := by
    calc
      _ = (1 + V * ‖z‖ ^ 2) ^ (((t.card : ℝ) / 2) * (2 : ℝ)) := by
        rw [Real.rpow_mul hp, Real.rpow_two]
      _ = (1 + V * ‖z‖ ^ 2) ^ (t.card : ℝ) := by congr 1; ring
      _ = _ := Real.rpow_natCast _ _
  rw [heq] at hsquare
  simpa only [centredGeneratingPolynomial_eval] using hsquare

theorem centredGeneratingPolynomial_coeff_circle_bound {ι : Type*}
    (t : Finset ι) (η : ι → ℂ) (V b : ℝ) (hV0 : 0 ≤ V) (hb : 0 ≤ b)
    (hη : ∑ j ∈ t, η j = 0)
    (hV : ∑ j ∈ t, ‖η j‖ ^ 2 ≤ (t.card : ℝ) * V) (k : ℕ) :
    ‖(centredGeneratingPolynomial t η).coeff k‖ ^ 2 * b ^ k ≤
      (1 + V * b) ^ t.card := by
  have h := norm_coeff_sq_mul_radius_pow_le (centredGeneratingPolynomial t η) k
    (Real.sqrt b) ((1 + V * b) ^ t.card) (Real.sqrt_nonneg _) ?_
  · simpa only [Real.sq_sqrt hb] using h
  · intro z hz
    have h := centredGeneratingPolynomial_eval_sq_le t η V hV0 hη hV z
    simpa only [hz, Real.sq_sqrt hb] using h

/-- The radius that minimizes the circle estimate gives the usual
Cauchy bound, here written without square roots. -/
theorem centredGeneratingPolynomial_coeff_sq_cauchy {ι : Type*}
    (t : Finset ι) (η : ι → ℂ) (V : ℝ) (hV0 : 0 < V)
    (hη : ∑ j ∈ t, η j = 0)
    (hV : ∑ j ∈ t, ‖η j‖ ^ 2 ≤ (t.card : ℝ) * V)
    (k : ℕ) (hk0 : 0 < k) (hkm : k < t.card) :
    ‖(centredGeneratingPolynomial t η).coeff k‖ ^ 2 ≤
      (t.card : ℝ) ^ t.card /
        ((k : ℝ) ^ k * ((t.card - k : ℕ) : ℝ) ^ (t.card - k)) * V ^ k := by
  let l := t.card - k
  have hl : (0 : ℝ) < (l : ℝ) := by
    exact_mod_cast (show 0 < l by dsimp [l]; omega)
  have hk : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
  have hmk : t.card = k + l := by dsimp [l]; omega
  have hmkR : (t.card : ℝ) = (k : ℝ) + (l : ℝ) := by exact_mod_cast hmk
  have hbase : 1 + V * ((k : ℝ) / (V * (l : ℝ))) = (t.card : ℝ) / (l : ℝ) := by
    field_simp
    nlinarith [hmkR]
  have h := centredGeneratingPolynomial_coeff_circle_bound t η V
    ((k : ℝ) / (V * (l : ℝ))) hV0.le (by positivity) hη hV k
  rw [hbase, div_pow, div_pow, mul_pow, ← mul_div_assoc] at h
  have h' := (div_le_div_iff₀
    (show 0 < V ^ k * (l : ℝ) ^ k by positivity)
    (show 0 < (l : ℝ) ^ t.card by positivity)).mp h
  have hlpow : (l : ℝ) ^ t.card = (l : ℝ) ^ k * (l : ℝ) ^ l := by
    rw [hmk, pow_add]
  rw [hlpow] at h'
  have hcancel : ‖(centredGeneratingPolynomial t η).coeff k‖ ^ 2 *
      ((k : ℝ) ^ k * (l : ℝ) ^ l) ≤ (t.card : ℝ) ^ t.card * V ^ k := by
    apply (mul_le_mul_iff_right₀ (show 0 < (l : ℝ) ^ k by positivity)).mp
    nlinarith only [h']
  change ‖(centredGeneratingPolynomial t η).coeff k‖ ^ 2 ≤
    (t.card : ℝ) ^ t.card / ((k : ℝ) ^ k * (l : ℝ) ^ l) * V ^ k
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ (show 0 < (k : ℝ) ^ k * (l : ℝ) ^ l by positivity)).mpr hcancel

theorem centredGeneratingPolynomial_coeff_cauchy {ι : Type*}
    (t : Finset ι) (η : ι → ℂ) (V : ℝ) (hV0 : 0 < V)
    (hη : ∑ j ∈ t, η j = 0)
    (hV : ∑ j ∈ t, ‖η j‖ ^ 2 ≤ (t.card : ℝ) * V)
    (k : ℕ) (hk0 : 0 < k) (hkm : k < t.card) :
    ‖(centredGeneratingPolynomial t η).coeff k‖ ≤
      Real.sqrt ((t.card : ℝ) ^ t.card /
        ((k : ℝ) ^ k * ((t.card - k : ℕ) : ℝ) ^ (t.card - k))) *
      V ^ ((k : ℝ) / 2) := by
  have h := Real.sqrt_le_sqrt
    (centredGeneratingPolynomial_coeff_sq_cauchy t η V hV0 hη hV k hk0 hkm)
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
    Real.sqrt_mul (by positivity)] at h
  have hp : Real.sqrt (V ^ k) = V ^ ((k : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hV0.le]
    congr 1
    ring
  rwa [hp] at h

@[simp] theorem centredGeneratingPolynomial_coeff_card {ι : Type*}
    (t : Finset ι) (η : ι → ℂ) :
    (centredGeneratingPolynomial t η).coeff t.card = ∏ j ∈ t, η j := by
  classical
  have hdeg (j : ι) (hj : j ∈ t) : (1 + C (η j) * X : Polynomial ℂ).natDegree ≤ 1 := by
    apply Polynomial.natDegree_add_le_of_degree_le
    · simp
    · exact (Polynomial.natDegree_mul_le).trans (by simp)
  have h := Polynomial.coeff_prod_of_natDegree_le (s := t)
    (fun j => (1 + C (η j) * X : Polynomial ℂ)) 1 hdeg
  simpa [centredGeneratingPolynomial, Polynomial.coeff_one] using h

theorem centredGeneratingPolynomial_coeff_card_bound {ι : Type*}
    (t : Finset ι) (η : ι → ℂ) (V : ℝ) (hV0 : 0 ≤ V)
    (hV : ∑ j ∈ t, ‖η j‖ ^ 2 ≤ (t.card : ℝ) * V) :
    ‖(centredGeneratingPolynomial t η).coeff t.card‖ ≤ V ^ ((t.card : ℝ) / 2) := by
  classical
  by_cases ht : t = ∅
  · simp [ht, centredGeneratingPolynomial, Polynomial.coeff_one]
  have hc : (0 : ℝ) < t.card := by
    exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr ht)
  rw [centredGeneratingPolynomial_coeff_card]
  refine (norm_prod_le_rpow_mean_sq t η).trans ?_
  exact Real.rpow_le_rpow (by positivity)
    ((div_le_iff₀ hc).mpr (by simpa only [mul_comm] using hV)) (by positivity)

end Schmeisser

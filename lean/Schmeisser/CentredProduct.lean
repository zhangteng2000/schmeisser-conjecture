import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Basic.Complex.BigOperators
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Estimates for products with centred increments

The products and sums use an arbitrary finite index set. Repeated values
are allowed, as required for polynomial roots counted with multiplicity.
-/

open scoped BigOperators
open MeasureTheory Set

namespace Schmeisser

/-- The root-mean-square bound for a finite product of complex numbers. -/
theorem norm_prod_le_rpow_mean_sq {ι : Type*} (t : Finset ι) (z : ι → ℂ) :
    ‖∏ i ∈ t, z i‖ ≤
      ((∑ i ∈ t, ‖z i‖ ^ 2) / (t.card : ℝ)) ^ ((t.card : ℝ) / 2) := by
  classical
  by_cases ht : t = ∅
  · simp [ht]
  have hc : (0 : ℝ) < (t.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr ht)
  have hamgm : ((∏ i ∈ t, ‖z i‖ ^ 2) ^ (t.card : ℝ)⁻¹) ≤
      (∑ i ∈ t, ‖z i‖ ^ 2) / (t.card : ℝ) := by
    simpa using Real.geom_mean_le_arith_mean t (fun _ => (1 : ℝ)) (fun i => ‖z i‖ ^ 2)
      (by intros; positivity) (by simpa using hc) (by intros; positivity)
  have hprod : 0 ≤ ∏ i ∈ t, ‖z i‖ ^ 2 := Finset.prod_nonneg (by intros; positivity)
  have hraised := Real.rpow_le_rpow (Real.rpow_nonneg hprod _) hamgm
    (show 0 ≤ (t.card : ℝ) / 2 by positivity)
  have hexp : (t.card : ℝ)⁻¹ * ((t.card : ℝ) / 2) = (2 : ℝ)⁻¹ := by
    field_simp
  have hp : (∏ i ∈ t, ‖z i‖ ^ 2) = ‖∏ i ∈ t, z i‖ ^ 2 := by
    rw [norm_prod, Finset.prod_pow]
  have hleft : ((∏ i ∈ t, ‖z i‖ ^ 2) ^ (t.card : ℝ)⁻¹) ^ ((t.card : ℝ) / 2) =
      ‖∏ i ∈ t, z i‖ := by
    rw [← Real.rpow_mul hprod, hexp, hp]
    exact Real.pow_rpow_inv_natCast (norm_nonneg _) (by decide : (2 : ℕ) ≠ 0)
  rwa [hleft] at hraised

theorem sum_norm_sq_centered {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (t : Finset ι) (d : E) (η : ι → E) (r : ℝ) (hη : ∑ i ∈ t, η i = 0) :
    (∑ i ∈ t, ‖d + r • η i‖ ^ 2) =
      (t.card : ℝ) * ‖d‖ ^ 2 + r ^ 2 * (∑ i ∈ t, ‖η i‖ ^ 2) := by
  have hi : ∑ i ∈ t, inner ℝ d (η i) = 0 := by
    rw [← inner_sum, hη, inner_zero_right]
  calc
    (∑ i ∈ t, ‖d + r • η i‖ ^ 2) =
        ∑ i ∈ t, (‖d‖ ^ 2 + (2 * r) * inner ℝ d (η i) + r ^ 2 * ‖η i‖ ^ 2) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
        mul_pow, sq_abs]
      ring
    _ = (t.card : ℝ) * ‖d‖ ^ 2 + (2 * r) * (∑ i ∈ t, inner ℝ d (η i)) +
        r ^ 2 * (∑ i ∈ t, ‖η i‖ ^ 2) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    _ = _ := by rw [hi]; ring

theorem centred_total_sq_bound {ι : Type*} (t : Finset ι) (d : ℂ) (η : ι → ℂ)
    (V r : ℝ) (hη : ∑ i ∈ t, η i = 0)
    (hV : ∑ i ∈ t, ‖η i‖ ^ 2 ≤ (t.card : ℝ) * V)
    (hr : r ∈ Icc (0 : ℝ) 1) :
    (∑ i ∈ t, ‖d + (r : ℂ) * η i‖ ^ 2) ≤ (t.card : ℝ) * (‖d‖ ^ 2 + V) := by
  have hs := sum_norm_sq_centered t d η r hη
  simp only [Complex.real_smul] at hs
  have hr2 : r ^ 2 ≤ 1 := by nlinarith [hr.1, hr.2]
  have hp := mul_le_mul_of_nonneg_right hr2
    (Finset.sum_nonneg (s := t) (fun i hi => sq_nonneg ‖η i‖))
  nlinarith

theorem centred_omitted_product_bound {ι : Type*} [DecidableEq ι]
    (t : Finset ι) (m : ℕ) (hm : 2 ≤ m) (hcard : t.card = m)
    (d : ℂ) (η : ι → ℂ) (V r : ℝ) (hη : ∑ i ∈ t, η i = 0)
    (hV : ∑ i ∈ t, ‖η i‖ ^ 2 ≤ (m : ℝ) * V)
    (hr : r ∈ Icc (0 : ℝ) 1) {j : ι} (hj : j ∈ t) :
    ‖∏ i ∈ t.erase j, (d + (r : ℂ) * η i)‖ ≤
      (((m : ℝ) / ((m - 1 : ℕ) : ℝ)) * (‖d‖ ^ 2 + V)) ^
        (((m - 1 : ℕ) : ℝ) / 2) := by
  have hc : (t.erase j).card = m - 1 := by rw [Finset.card_erase_of_mem hj, hcard]
  have hm1 : (0 : ℝ) < ((m - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < m - 1 by omega)
  have hs := centred_total_sq_bound t d η V r hη (by simpa [hcard] using hV) hr
  rw [hcard] at hs
  have hsub : (∑ i ∈ t.erase j, ‖d + (r : ℂ) * η i‖ ^ 2) ≤
      ∑ i ∈ t, ‖d + (r : ℂ) * η i‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset j t) (by intros; positivity)
  have hmean : (∑ i ∈ t.erase j, ‖d + (r : ℂ) * η i‖ ^ 2) / ((m - 1 : ℕ) : ℝ) ≤
      ((m : ℝ) / ((m - 1 : ℕ) : ℝ)) * (‖d‖ ^ 2 + V) := by
    convert div_le_div_of_nonneg_right (hsub.trans hs) hm1.le using 1; ring
  calc
    ‖∏ i ∈ t.erase j, (d + (r : ℂ) * η i)‖ ≤
        ((∑ i ∈ t.erase j, ‖d + (r : ℂ) * η i‖ ^ 2) /
          ((m - 1 : ℕ) : ℝ)) ^ (((m - 1 : ℕ) : ℝ) / 2) := by
      simpa only [hc] using norm_prod_le_rpow_mean_sq (t.erase j) (fun i => d + (r : ℂ) * η i)
    _ ≤ _ := Real.rpow_le_rpow (by positivity) hmean (by positivity)

theorem centred_product_hasDerivAt {ι : Type*} [DecidableEq ι]
    (t : Finset ι) (d : ℂ) (η : ι → ℂ) (r : ℝ) :
    HasDerivAt (fun r : ℝ => ∏ i ∈ t, (d + (r : ℂ) * η i))
      (∑ j ∈ t, η j * ∏ i ∈ t.erase j, (d + (r : ℂ) * η i)) r := by
  have hi (i : ι) : HasDerivAt (fun r : ℝ => d + (r : ℂ) * η i) (η i) r := by
    simpa using (Complex.ofRealCLM.hasDerivAt.mul_const (η i)).const_add d
  simpa only [smul_eq_mul, mul_comm] using
    HasDerivAt.fun_finsetProd (fun i (_ : i ∈ t) => hi i)

/-- The zero first moment removes the linear term from the derivative. -/
theorem centred_product_cancellation {ι : Type*} [DecidableEq ι]
    (t : Finset ι) (d : ℂ) (η : ι → ℂ) (r : ℝ) (hη : ∑ i ∈ t, η i = 0) :
    d * (∑ j ∈ t, η j * ∏ i ∈ t.erase j, (d + (r : ℂ) * η i)) =
      -(r : ℂ) * (∑ j ∈ t, η j ^ 2 * ∏ i ∈ t.erase j, (d + (r : ℂ) * η i)) := by
  have hz : (∑ j ∈ t, η j * (d + (r : ℂ) * η j) *
      ∏ i ∈ t.erase j, (d + (r : ℂ) * η i)) = 0 := by
    calc
      _ = (∑ j ∈ t, η j) * ∏ i ∈ t, (d + (r : ℂ) * η i) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j hj
        rw [mul_assoc, Finset.mul_prod_erase t (fun i => d + (r : ℂ) * η i) hj]
      _ = 0 := by rw [hη, zero_mul]
  have heq :
      d * (∑ j ∈ t, η j * ∏ i ∈ t.erase j, (d + (r : ℂ) * η i)) +
        (r : ℂ) * (∑ j ∈ t, η j ^ 2 * ∏ i ∈ t.erase j, (d + (r : ℂ) * η i)) =
      ∑ j ∈ t, η j * (d + (r : ℂ) * η j) *
        ∏ i ∈ t.erase j, (d + (r : ℂ) * η i) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hz] at heq
  linear_combination heq

theorem centred_product_derivative_bound {ι : Type*} [DecidableEq ι]
    (t : Finset ι) (m : ℕ) (hm : 2 ≤ m) (hcard : t.card = m)
    (d : ℂ) (hd : d ≠ 0) (η : ι → ℂ) (V r : ℝ) (hV0 : 0 ≤ V)
    (hη : ∑ i ∈ t, η i = 0) (hV : ∑ i ∈ t, ‖η i‖ ^ 2 ≤ (m : ℝ) * V)
    (hr : r ∈ Icc (0 : ℝ) 1) :
    ‖deriv (fun r : ℝ => ∏ i ∈ t, (d + (r : ℂ) * η i)) r‖ ≤
      ((m : ℝ) * V / ‖d‖ *
        (((m : ℝ) / ((m - 1 : ℕ) : ℝ)) * (‖d‖ ^ 2 + V)) ^
          (((m - 1 : ℕ) : ℝ) / 2)) * r := by
  let P : ι → ℂ := fun j => ∏ i ∈ t.erase j, (d + (r : ℂ) * η i)
  let D : ℂ := ∑ j ∈ t, η j * P j
  let S : ℂ := ∑ j ∈ t, η j ^ 2 * P j
  let K : ℝ := (((m : ℝ) / ((m - 1 : ℕ) : ℝ)) * (‖d‖ ^ 2 + V)) ^
    (((m - 1 : ℕ) : ℝ) / 2)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hP (j : ι) (hj : j ∈ t) : ‖P j‖ ≤ K :=
    centred_omitted_product_bound t m hm hcard d η V r hη hV hr hj
  have hS : ‖S‖ ≤ (m : ℝ) * V * K := by
    calc
      ‖S‖ ≤ ∑ j ∈ t, ‖η j ^ 2 * P j‖ := norm_sum_le _ _
      _ = ∑ j ∈ t, ‖η j‖ ^ 2 * ‖P j‖ := by simp only [norm_mul, norm_pow]
      _ ≤ ∑ j ∈ t, ‖η j‖ ^ 2 * K :=
        Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (hP j hj) (sq_nonneg _))
      _ = (∑ j ∈ t, ‖η j‖ ^ 2) * K := by rw [Finset.sum_mul]
      _ ≤ (m : ℝ) * V * K := mul_le_mul_of_nonneg_right hV hK
  have hcancel : d * D = -(r : ℂ) * S := centred_product_cancellation t d η r hη
  have hn : ‖d‖ * ‖D‖ = r * ‖S‖ := by
    have h := congrArg norm hcancel
    simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr.1] using h
  have hd0 : 0 < ‖d‖ := norm_pos_iff.mpr hd
  have hderiv : deriv (fun r : ℝ => ∏ i ∈ t, (d + (r : ℂ) * η i)) r = D :=
    (centred_product_hasDerivAt t d η r).deriv
  rw [hderiv]
  calc
    ‖D‖ ≤ r * ((m : ℝ) * V * K) / ‖d‖ := by
      apply (le_div_iff₀ hd0).2
      rw [mul_comm ‖D‖ ‖d‖, hn]
      exact mul_le_mul_of_nonneg_left hS hr.1
    _ = _ := by dsimp [K]; ring

/-- The centred-product interpolation estimate with its exact dimensional
constant, before replacing that constant by `5 / 3`. -/
theorem centred_product_interpolation_exact {ι : Type*} [DecidableEq ι]
    (t : Finset ι) (m : ℕ) (hm : 2 ≤ m) (hcard : t.card = m)
    (d : ℂ) (hd : d ≠ 0) (η : ι → ℂ) (V : ℝ) (hV0 : 0 ≤ V)
    (hη : ∑ i ∈ t, η i = 0) (hV : ∑ i ∈ t, ‖η i‖ ^ 2 ≤ (m : ℝ) * V) :
    ‖(∏ i ∈ t, (d + η i)) - d ^ m‖ ≤
      (m : ℝ) * V / (2 * ‖d‖) *
        (((m : ℝ) / ((m - 1 : ℕ) : ℝ)) * (‖d‖ ^ 2 + V)) ^
          (((m - 1 : ℕ) : ℝ) / 2) := by
  let G : ℝ → ℂ := fun r => ∏ i ∈ t, (d + (r : ℂ) * η i)
  let K : ℝ := (((m : ℝ) / ((m - 1 : ℕ) : ℝ)) * (‖d‖ ^ 2 + V)) ^
    (((m - 1 : ℕ) : ℝ) / 2)
  let C : ℝ := (m : ℝ) * V / ‖d‖ * K
  have hdiff : Differentiable ℝ G := fun r => (centred_product_hasDerivAt t d η r).differentiableAt
  have hcont : Continuous (fun r : ℝ => C * r) := continuous_const.mul continuous_id
  have hbound : ‖G 1 - G 0‖ ≤ ∫ r : ℝ in 0..1, C * r := by
    apply norm_sub_le_integral_of_norm_deriv_le_of_le (by norm_num)
      hdiff.continuous.continuousOn hdiff.differentiableOn
    · apply Filter.Eventually.of_forall
      intro r hr
      exact centred_product_derivative_bound t m hm hcard d hd η V r hV0 hη hV
        ⟨hr.1.le, hr.2.le⟩
    · exact hcont.intervalIntegrable 0 1
  have hbound' : ‖(∏ i ∈ t, (d + η i)) - d ^ m‖ ≤ C / 2 := by
    rw [intervalIntegral.integral_const_mul, integral_id] at hbound
    simpa [G, hcard, div_eq_mul_inv] using hbound
  calc
    ‖(∏ i ∈ t, (d + η i)) - d ^ m‖ ≤ C / 2 := hbound'
    _ = _ := by dsimp [C, K]; ring

theorem centred_dimensional_factor_le (m : ℕ) (hm : 2 ≤ m) :
    ((m : ℝ) / ((m - 1 : ℕ) : ℝ)) ^ (((m - 1 : ℕ) : ℝ) / 2) ≤ (5 / 3 : ℝ) := by
  have hk : (0 : ℝ) < ((m - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < m - 1 by omega)
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hmk : (m : ℝ) = ((m - 1 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (show m = m - 1 + 1 by omega)
  have hx : 0 < (m : ℝ) / ((m - 1 : ℕ) : ℝ) := div_pos hm0 hk
  have heq : (m : ℝ) / ((m - 1 : ℕ) : ℝ) - 1 = 1 / ((m - 1 : ℕ) : ℝ) := by
    rw [hmk]
    field_simp
    ring
  have hlog : Real.log ((m : ℝ) / ((m - 1 : ℕ) : ℝ)) ≤ 1 / ((m - 1 : ℕ) : ℝ) := by
    simpa only [heq] using Real.log_le_sub_one_of_pos hx
  have hscaled := mul_le_mul_of_nonneg_right hlog (show 0 ≤ ((m - 1 : ℕ) : ℝ) / 2 by positivity)
  have hcancel : (1 / ((m - 1 : ℕ) : ℝ)) * (((m - 1 : ℕ) : ℝ) / 2) = (1 / 2 : ℝ) := by
    field_simp
  rw [hcancel] at hscaled
  have hexp : Real.exp (1 / 2 : ℝ) ≤ (5 / 3 : ℝ) := by
    have he : (Real.exp (1 / 2 : ℝ)) ^ 2 = Real.exp 1 := by
      rw [pow_two, ← Real.exp_add]
      norm_num
    have heupper := Real.exp_one_lt_d9
    nlinarith [Real.exp_pos (1 / 2 : ℝ)]
  calc
    ((m : ℝ) / ((m - 1 : ℕ) : ℝ)) ^ (((m - 1 : ℕ) : ℝ) / 2) ≤ Real.exp (1 / 2 : ℝ) := by
      rw [Real.rpow_def_of_pos hx]
      exact Real.exp_le_exp.mpr hscaled
    _ ≤ 5 / 3 := hexp

/-- The centred-product estimate with the numerical constant from the paper. -/
theorem centred_product_interpolation {ι : Type*} [DecidableEq ι]
    (t : Finset ι) (m : ℕ) (hm : 2 ≤ m) (hcard : t.card = m)
    (d : ℂ) (hd : d ≠ 0) (η : ι → ℂ) (V : ℝ) (hV0 : 0 ≤ V)
    (hη : ∑ i ∈ t, η i = 0) (hV : ∑ i ∈ t, ‖η i‖ ^ 2 ≤ (m : ℝ) * V) :
    ‖(∏ i ∈ t, (d + η i)) - d ^ m‖ ≤
      (5 * (m : ℝ) / 6) * (V / ‖d‖) *
        (‖d‖ ^ 2 + V) ^ (((m - 1 : ℕ) : ℝ) / 2) := by
  have he := centred_product_interpolation_exact t m hm hcard d hd η V hV0 hη hV
  have hx : 0 ≤ (m : ℝ) / ((m - 1 : ℕ) : ℝ) := by positivity
  have hy : 0 ≤ ‖d‖ ^ 2 + V := by positivity
  rw [Real.mul_rpow hx hy] at he
  have hdim := centred_dimensional_factor_le m hm
  have hcoef : 0 ≤ (m : ℝ) * V / (2 * ‖d‖) := by positivity
  calc
    ‖(∏ i ∈ t, (d + η i)) - d ^ m‖ ≤
        (m : ℝ) * V / (2 * ‖d‖) *
          (((m : ℝ) / ((m - 1 : ℕ) : ℝ)) ^ (((m - 1 : ℕ) : ℝ) / 2) *
            (‖d‖ ^ 2 + V) ^ (((m - 1 : ℕ) : ℝ) / 2)) := he
    _ ≤ (m : ℝ) * V / (2 * ‖d‖) *
        ((5 / 3 : ℝ) * (‖d‖ ^ 2 + V) ^ (((m - 1 : ℕ) : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hdim (Real.rpow_nonneg hy _)) hcoef
    _ = _ := by ring

end Schmeisser

import Schmeisser.CoefficientExpansion
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.Algebra.Order.Chebyshev

open scoped BigOperators
open Polynomial

namespace Schmeisser

theorem centredGeneratingPolynomial_coeff_eq_powersetCard {ι : Type*}
    (t : Finset ι) (η : ι → ℂ) (k : ℕ) :
    (centredGeneratingPolynomial t η).coeff k =
      ∑ s ∈ t.powersetCard k, ∏ j ∈ s, η j := by
  classical
  have hp (s : Finset ι) : (∏ j ∈ s, (C (η j) * X : Polynomial ℂ)) =
      C (∏ j ∈ s, η j) * X ^ s.card := by
    rw [Finset.prod_mul_distrib, ← map_prod, Finset.prod_const]
  unfold centredGeneratingPolynomial
  rw [Finset.prod_one_add, Polynomial.finsetSum_coeff, Finset.powersetCard_eq_filter,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro s hs
  rw [hp, Polynomial.coeff_C_mul_X_pow]
  simp only [eq_comm]

theorem centredGeneratingPolynomial_coeff_eq_aeval_esymm {ι : Type*} [Fintype ι]
    (η : ι → ℂ) (k : ℕ) :
    (centredGeneratingPolynomial Finset.univ η).coeff k =
      MvPolynomial.aeval η (MvPolynomial.esymm ι ℂ k) := by
  rw [centredGeneratingPolynomial_coeff_eq_powersetCard]
  simp [MvPolynomial.esymm]

theorem centredGeneratingPolynomial_newton_univ {ι : Type*} [Fintype ι]
    (η : ι → ℂ) (k : ℕ) :
    (k : ℂ) * (centredGeneratingPolynomial Finset.univ η).coeff k =
      (-1 : ℂ) ^ (k + 1) *
        ∑ a ∈ (Finset.antidiagonal k).filter (fun a => a.1 < k),
          (-1 : ℂ) ^ a.1 * (centredGeneratingPolynomial Finset.univ η).coeff a.1 *
            ∑ j, (η j) ^ a.2 := by
  classical
  have h := congrArg (MvPolynomial.aeval η) (MvPolynomial.mul_esymm_eq_sum ι ℂ k)
  simpa only [map_mul, map_natCast, map_pow, map_neg, map_one, map_sum,
    MvPolynomial.psum, MvPolynomial.aeval_X,
    ← centredGeneratingPolynomial_coeff_eq_aeval_esymm] using h

theorem centredGeneratingPolynomial_newton {ι : Type*}
    (t : Finset ι) (η : ι → ℂ) (k : ℕ) :
    (k : ℂ) * (centredGeneratingPolynomial t η).coeff k =
      (-1 : ℂ) ^ (k + 1) *
        ∑ a ∈ (Finset.antidiagonal k).filter (fun a => a.1 < k),
          (-1 : ℂ) ^ a.1 * (centredGeneratingPolynomial t η).coeff a.1 *
            ∑ j ∈ t, (η j) ^ a.2 := by
  classical
  have h := centredGeneratingPolynomial_newton_univ (fun j : t => η j.1) k
  have hp : centredGeneratingPolynomial Finset.univ (fun j : t => η j.1) =
      centredGeneratingPolynomial t η := by
    simp only [centredGeneratingPolynomial, Finset.univ_eq_attach]
    exact Finset.prod_attach t (fun j => (1 + C (η j) * X : Polynomial ℂ))
  have hs (l : ℕ) : (∑ j : t, (η j.1) ^ l) = ∑ j ∈ t, (η j) ^ l := by
    rw [Finset.univ_eq_attach]
    exact Finset.sum_attach t (fun j => (η j) ^ l)
  simp only [hp, hs] at h
  exact h

theorem centredGeneratingPolynomial_newton_norm {ι : Type*}
    (t : Finset ι) (η : ι → ℂ) (k : ℕ) :
    (k : ℝ) * ‖(centredGeneratingPolynomial t η).coeff k‖ ≤
      ∑ j ∈ Finset.range k, ‖(centredGeneratingPolynomial t η).coeff j‖ *
        ‖∑ i ∈ t, (η i) ^ (k - j)‖ := by
  classical
  have h := congrArg norm (centredGeneratingPolynomial_newton t η k)
  simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Complex.norm_natCast] at h
  rw [h]
  have hs := norm_sum_le (Finset.filter (fun a : ℕ × ℕ => a.1 < k) (Finset.antidiagonal k))
    (fun a => (-1 : ℂ) ^ a.1 * (centredGeneratingPolynomial t η).coeff a.1 *
      ∑ j ∈ t, (η j) ^ a.2)
  simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul] at hs
  refine hs.trans_eq ?_
  rw [Finset.sum_filter, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ]
  simp only [lt_self_iff_false, ite_false, add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_range.mp hj, ite_true]

theorem centredGeneratingPolynomial_newton_norm_centered {ι : Type*}
    (t : Finset ι) (η : ι → ℂ) (hη : ∑ j ∈ t, η j = 0) (k : ℕ) (hk : 1 ≤ k) :
    (k : ℝ) * ‖(centredGeneratingPolynomial t η).coeff k‖ ≤
      ∑ j ∈ Finset.range (k - 1), ‖(centredGeneratingPolynomial t η).coeff j‖ *
        ‖∑ i ∈ t, (η i) ^ (k - j)‖ := by
  have h := centredGeneratingPolynomial_newton_norm t η k
  have hk' : k = (k - 1) + 1 := by omega
  conv at h => rhs; rw [hk', Finset.sum_range_succ]
  have he : k - (k - 1) = 1 := by omega
  simpa only [← hk', he, pow_one, hη, norm_zero, mul_zero, add_zero] using h

theorem norm_sum_sq_le_card_sum_sq {ι : Type*} (t : Finset ι) (η : ι → ℂ) :
    ‖∑ j ∈ t, η j‖ ^ 2 ≤ (t.card : ℝ) * ∑ j ∈ t, ‖η j‖ ^ 2 := by
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le t η) 2).trans
    (sq_sum_le_card_mul_sum_sq (s := t) (f := fun j => ‖η j‖))

theorem norm_sq_le_centered_variance {ι : Type*} (t : Finset ι) (η : ι → ℂ)
    (V : ℝ) (hη : ∑ j ∈ t, η j = 0)
    (hV : ∑ j ∈ t, ‖η j‖ ^ 2 ≤ (t.card : ℝ) * V) {i : ι} (hi : i ∈ t) :
    ‖η i‖ ^ 2 ≤ ((t.card : ℝ) - 1) * V := by
  classical
  have hcard : 1 ≤ t.card := Finset.card_pos.mpr ⟨i, hi⟩
  have hm : (0 : ℝ) < t.card := by exact_mod_cast hcard
  have hsum : ∑ j ∈ t.erase i, η j = -η i := by
    have h := Finset.sum_erase_add t η hi
    rw [hη] at h
    exact eq_neg_of_add_eq_zero_left h
  have hsumV : (∑ j ∈ t.erase i, ‖η j‖ ^ 2) + ‖η i‖ ^ 2 ≤ (t.card : ℝ) * V := by
    rw [Finset.sum_erase_add t (fun j => ‖η j‖ ^ 2) hi]
    exact hV
  have hsq := norm_sum_sq_le_card_sum_sq (t.erase i) η
  rw [hsum, norm_neg, Finset.card_erase_of_mem hi, Nat.cast_sub hcard, Nat.cast_one] at hsq
  have hm1 : 0 ≤ (t.card : ℝ) - 1 := sub_nonneg.mpr (by exact_mod_cast hcard)
  have hmul := mul_le_mul_of_nonneg_left hsumV hm1
  have h : (t.card : ℝ) * ‖η i‖ ^ 2 ≤ (t.card : ℝ) * (((t.card : ℝ) - 1) * V) := by
    nlinarith
  exact (mul_le_mul_iff_right₀ hm).mp h

theorem norm_powerSum_le_centered_variance {ι : Type*}
    (t : Finset ι) (η : ι → ℂ) (V : ℝ) (hm : 2 ≤ t.card) (hV0 : 0 ≤ V)
    (hη : ∑ j ∈ t, η j = 0)
    (hV : ∑ j ∈ t, ‖η j‖ ^ 2 ≤ (t.card : ℝ) * V)
    (k : ℕ) (hk : 2 ≤ k) :
    ‖∑ j ∈ t, (η j) ^ k‖ ≤ (t.card : ℝ) *
      ((t.card : ℝ) - 1) ^ (((k - 2 : ℕ) : ℝ) / 2) * V ^ ((k : ℝ) / 2) := by
  have hmR : (2 : ℝ) ≤ t.card := by exact_mod_cast hm
  have hm1 : 0 ≤ (t.card : ℝ) - 1 := by linarith
  have hbase : 0 ≤ ((t.card : ℝ) - 1) * V := mul_nonneg hm1 hV0
  have hpoint (j : ι) (hj : j ∈ t) :
      ‖η j‖ ≤ Real.sqrt (((t.card : ℝ) - 1) * V) := by
    have h := Real.sqrt_le_sqrt (norm_sq_le_centered_variance t η V hη hV hj)
    simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using h
  have hp : (Real.sqrt (((t.card : ℝ) - 1) * V)) ^ (k - 2) =
      ((t.card : ℝ) - 1) ^ (((k - 2 : ℕ) : ℝ) / 2) *
        V ^ (((k - 2 : ℕ) : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hbase]
    have he : (1 / 2 : ℝ) * ((k - 2 : ℕ) : ℝ) = ((k - 2 : ℕ) : ℝ) / 2 := by ring
    rw [he, Real.mul_rpow hm1 hV0]
  have he : (1 : ℝ) + ((k - 2 : ℕ) : ℝ) / 2 = (k : ℝ) / 2 := by
    rw [Nat.cast_sub hk]
    norm_num
    ring
  have hpow : V * V ^ (((k - 2 : ℕ) : ℝ) / 2) = V ^ ((k : ℝ) / 2) := by
    calc
      V * V ^ (((k - 2 : ℕ) : ℝ) / 2) =
          V ^ (1 : ℝ) * V ^ (((k - 2 : ℕ) : ℝ) / 2) := by rw [Real.rpow_one]
      _ = V ^ ((1 : ℝ) + ((k - 2 : ℕ) : ℝ) / 2) :=
        (Real.rpow_add_of_nonneg hV0 (by norm_num) (by positivity)).symm
      _ = V ^ ((k : ℝ) / 2) := by rw [he]
  calc
    ‖∑ j ∈ t, (η j) ^ k‖ ≤ ∑ j ∈ t, ‖η j‖ ^ k := by
      simpa only [norm_pow] using norm_sum_le t (fun j => (η j) ^ k)
    _ ≤ ∑ j ∈ t, ‖η j‖ ^ 2 * (Real.sqrt (((t.card : ℝ) - 1) * V)) ^ (k - 2) := by
      apply Finset.sum_le_sum
      intro j hj
      have hk' : k = 2 + (k - 2) := by omega
      conv_lhs => rw [hk', pow_add]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (hpoint j hj) (k - 2)) (sq_nonneg _)
    _ = (∑ j ∈ t, ‖η j‖ ^ 2) * (Real.sqrt (((t.card : ℝ) - 1) * V)) ^ (k - 2) :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ ((t.card : ℝ) * V) * (Real.sqrt (((t.card : ℝ) - 1) * V)) ^ (k - 2) :=
      mul_le_mul_of_nonneg_right hV (by positivity)
    _ = (t.card : ℝ) * ((t.card : ℝ) - 1) ^ (((k - 2 : ℕ) : ℝ) / 2) *
        V ^ ((k : ℝ) / 2) := by rw [hp, ← hpow]; ring

noncomputable def newtonMajorant (m k : ℕ) : ℝ :=
  match k with
  | 0 => 1
  | 1 => 0
  | k + 2 => (m : ℝ) / (k + 2) * ∑ j : Fin (k + 1),
      ((m : ℝ) - 1) ^ (((k - (j : ℕ) : ℕ) : ℝ) / 2) * newtonMajorant m j
termination_by k
decreasing_by omega

theorem newtonMajorant_recurrence (m k : ℕ) :
    newtonMajorant m (k + 2) = (m : ℝ) / (k + 2) *
      ∑ j ∈ Finset.range (k + 1),
        ((m : ℝ) - 1) ^ (((k - j : ℕ) : ℝ) / 2) * newtonMajorant m j := by
  rw [newtonMajorant]
  congr 1
  exact Fin.sum_univ_eq_sum_range
    (fun j : ℕ => ((m : ℝ) - 1) ^ (((k - j : ℕ) : ℝ) / 2) * newtonMajorant m j) (k + 1)

theorem newtonMajorant_nonneg (m k : ℕ) (hm : 1 ≤ m) : 0 ≤ newtonMajorant m k := by
  have hm1 : 0 ≤ (m : ℝ) - 1 := sub_nonneg.mpr (by exact_mod_cast hm)
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => simp [newtonMajorant]
    | succ k =>
      cases k with
      | zero => simp [newtonMajorant]
      | succ k =>
        rw [newtonMajorant]
        apply mul_nonneg (by positivity)
        apply Finset.sum_nonneg
        intro j hj
        exact mul_nonneg (Real.rpow_nonneg hm1 _) (ih j (by omega))

theorem newtonMajorant_recurrence_Ico (m k : ℕ) (hk : 2 ≤ k) :
    newtonMajorant m k = (m : ℝ) / k *
      ∑ j ∈ Finset.Ico 2 (k + 1),
        ((m : ℝ) - 1) ^ (((j - 2 : ℕ) : ℝ) / 2) * newtonMajorant m (k - j) := by
  obtain ⟨r, rfl⟩ : ∃ r : ℕ, k = r + 2 := ⟨k - 2, by omega⟩
  rw [newtonMajorant_recurrence]
  push_cast
  congr 1
  have hIco : (∑ j ∈ Finset.Ico 2 (r + 2 + 1),
      ((m : ℝ) - 1) ^ (((j - 2 : ℕ) : ℝ) / 2) * newtonMajorant m (r + 2 - j)) =
      ∑ j ∈ Finset.range (r + 1),
        ((m : ℝ) - 1) ^ ((j : ℝ) / 2) * newtonMajorant m (r - j) := by
    rw [Finset.sum_Ico_eq_sum_range]
    have hlen : r + 2 + 1 - 2 = r + 1 := by omega
    rw [hlen]
    apply Finset.sum_congr rfl
    intro j hj
    have h₁ : 2 + j - 2 = j := by omega
    have h₂ : r + 2 - (2 + j) = r - j := by omega
    rw [h₁, h₂]
  rw [hIco]
  have href := Finset.sum_range_reflect
    (fun j : ℕ => ((m : ℝ) - 1) ^ ((j : ℝ) / 2) * newtonMajorant m (r - j)) (r + 1)
  simp only [Nat.add_sub_cancel] at href
  rw [← href]
  apply Finset.sum_congr rfl
  intro j hj
  have hjr : j ≤ r := by have := Finset.mem_range.mp hj; omega
  rw [Nat.sub_sub_self hjr]

theorem coeff_norm_le_newtonMajorant {ι : Type*}
    (t : Finset ι) (η : ι → ℂ) (V : ℝ) (hm : 2 ≤ t.card) (hV0 : 0 ≤ V)
    (hη : ∑ j ∈ t, η j = 0)
    (hV : ∑ j ∈ t, ‖η j‖ ^ 2 ≤ (t.card : ℝ) * V) (k : ℕ) :
    ‖(centredGeneratingPolynomial t η).coeff k‖ ≤
      newtonMajorant t.card k * V ^ ((k : ℝ) / 2) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => simp [newtonMajorant]
    | succ k =>
      cases k with
      | zero => simp [newtonMajorant, hη]
      | succ k =>
        have hK : (0 : ℝ) < (k : ℝ) + 2 := by positivity
        have hnewton := centredGeneratingPolynomial_newton_norm_centered t η hη (k + 2) (by omega)
        have hterms : (∑ j ∈ Finset.range (k + 1),
            ‖(centredGeneratingPolynomial t η).coeff j‖ * ‖∑ i ∈ t, (η i) ^ (k + 2 - j)‖) ≤
            ((t.card : ℝ) * V ^ (((k + 2 : ℕ) : ℝ) / 2)) *
              ∑ j ∈ Finset.range (k + 1),
                ((t.card : ℝ) - 1) ^ (((k - j : ℕ) : ℝ) / 2) * newtonMajorant t.card j := by
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro j hj
          have hjk : j ≤ k := by have := Finset.mem_range.mp hj; omega
          have hprev := ih j (by omega)
          have hpsum := norm_powerSum_le_centered_variance t η V hm hV0 hη hV
            (k + 2 - j) (by omega)
          have he : k + 2 - j - 2 = k - j := by omega
          rw [he] at hpsum
          have hcombine : V ^ ((j : ℝ) / 2) * V ^ (((k + 2 - j : ℕ) : ℝ) / 2) =
              V ^ (((k + 2 : ℕ) : ℝ) / 2) := by
            rw [← Real.rpow_add_of_nonneg hV0 (by positivity) (by positivity)]
            congr 1
            rw [Nat.cast_sub (by omega : j ≤ k + 2)]
            push_cast
            ring
          calc
            ‖(centredGeneratingPolynomial t η).coeff j‖ * ‖∑ i ∈ t, (η i) ^ (k + 2 - j)‖ ≤
                (newtonMajorant t.card j * V ^ ((j : ℝ) / 2)) *
                  ((t.card : ℝ) * ((t.card : ℝ) - 1) ^ (((k - j : ℕ) : ℝ) / 2) *
                    V ^ (((k + 2 - j : ℕ) : ℝ) / 2)) :=
              mul_le_mul hprev hpsum (norm_nonneg _)
                (mul_nonneg (newtonMajorant_nonneg t.card j (by omega)) (Real.rpow_nonneg hV0 _))
            _ = ((t.card : ℝ) * V ^ (((k + 2 : ℕ) : ℝ) / 2)) *
                (((t.card : ℝ) - 1) ^ (((k - j : ℕ) : ℝ) / 2) * newtonMajorant t.card j) := by
              rw [← hcombine]
              ring
        have heq : (((k + 2 : ℕ) : ℝ) * newtonMajorant t.card (k + 2)) *
            V ^ (((k + 2 : ℕ) : ℝ) / 2) =
            ((t.card : ℝ) * V ^ (((k + 2 : ℕ) : ℝ) / 2)) *
              ∑ j ∈ Finset.range (k + 1),
                ((t.card : ℝ) - 1) ^ (((k - j : ℕ) : ℝ) / 2) * newtonMajorant t.card j := by
          rw [newtonMajorant_recurrence]
          push_cast
          field_simp
        have hkminus : k + 2 - 1 = k + 1 := by omega
        rw [hkminus] at hnewton
        have hbound := hnewton.trans hterms
        rw [← heq, mul_assoc] at hbound
        exact (mul_le_mul_iff_right₀ (by exact_mod_cast (show 0 < k + 2 by omega))).mp hbound

end Schmeisser

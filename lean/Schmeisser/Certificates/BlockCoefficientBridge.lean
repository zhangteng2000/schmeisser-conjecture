import Schmeisser.Certificates.BlockErrorExpressions
import Schmeisser.Certificates.GeometricErrorBridge
import Schmeisser.FiniteCoefficientError
import Schmeisser.Certificates.CoefficientCertificates
import Schmeisser.Certificates.SplitErrorBridge

open scoped BigOperators

namespace Schmeisser.Certificates.Block

theorem value_eps_general (environment : Nat → ℝ) (hu0 : 0 ≤ environment 0)
    (hu1 : environment 0 ≤ 1) : eps.value environment = 1 - environment 0 := by
  simp [eps, u, Expr.value, max_eq_right (sub_nonneg.mpr hu1),
    min_eq_right (by linarith : 1 - environment 0 ≤ 1)]

theorem value_coefficient (s : Nat) (upper : List Int) (k : Nat) (environment : Nat → ℝ) :
    (coefficient s upper k).value environment = ((upper[k]?.getD 0 : Int) : ℝ) / s := by
  simp [coefficient, Expr.value]

theorem value_polynomial (coefficients : List Nat) (a : Expr) (environment : Nat → ℝ) :
    (polynomial coefficients a).value environment =
      ∑ j ∈ Finset.range coefficients.length,
        ((coefficients[j]?.getD 0 : Nat) : ℝ) * (a.value environment) ^ j := by
  induction coefficients with
  | nil => simp [polynomial]
  | cons c coefficients ih =>
      change (c : ℝ) + a.value environment * (polynomial coefficients a).value environment = _
      rw [ih, List.length_cons, Finset.sum_range_succ']
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
        pow_zero, mul_one]
      rw [Finset.mul_sum]
      rw [add_comm (c : ℝ)]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [pow_succ]
      ring

theorem value_finiteBetaPolynomial (m k : Nat) (a : Expr) (environment : Nat → ℝ) :
    (polynomial ((List.range (m - k + 1)).map fun j => Nat.fast_choose (k + j) k) a).value environment =
      finiteBetaPolynomial m k (a.value environment) := by
  rw [value_polynomial]
  simp only [List.length_map, List.length_range, finiteBetaPolynomial]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn := Finset.mem_range.mp hj
  simp [hjn, ← Nat.choose_eq_fast_choose]

theorem value_finiteError (m s : Nat) (upper : List Int) (environment : Nat → ℝ)
    (hm : 1 ≤ m) (hu0 : 0 ≤ environment 0) (hu1 : environment 0 ≤ 1) :
    (finiteError m s upper).value environment =
      ∑ k ∈ Finset.Ico 2 (m + 1), ((coefficient s upper k).value environment) *
        (environment 0) ^ ((k : ℝ) / 2) * (1 - environment 0) ^ (((k - 2 : Nat) : ℝ) / 2) *
          finiteBetaPolynomial m k (1 - environment 0) := by
  have heps := value_eps_general environment hu0 hu1
  have hU : 0 ≤ u.value environment := hu0
  have hE : 0 ≤ eps.value environment := by rw [heps]; exact sub_nonneg.mpr hu1
  simp only [finiteError, Expr.value_sum_range, Expr.value_mul,
    Expr.value_half_rpow _ _ _ hU, Expr.value_half_rpow _ _ _ hE,
    value_finiteBetaPolynomial, heps]
  rw [Finset.sum_Ico_eq_sum_range, show m + 1 - 2 = m - 1 by omega]
  apply Finset.sum_congr rfl
  intro j hj
  simp [u, Expr.value, Nat.add_comm]

theorem finiteError_bound {ι : Type*} [DecidableEq ι]
    (table : CoefficientTable) (m : Nat) (hcheck : table.check m = true)
    (jset : Finset ι) (η : ι → ℂ) (hcard : jset.card = m)
    (hη : ∑ j ∈ jset, η j = 0) (environment : Nat → ℝ)
    (hu0 : 0 < environment 0) (hu1 : environment 0 < 1)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (m : ℝ) * (environment 0 * (1 - environment 0))) :
    centeredErrorIntegral jset η m (environment 0) / (1 - environment 0) ≤
      (finiteError m table.scale table.upper).value environment := by
  have hm : 2 ≤ m := (table.check_sound m hcheck).1
  let c : Nat → ℝ := fun k => (table.upperRat k : ℝ) * (m.choose k : ℝ)
  have hc : ∀ k ∈ Finset.Ico 2 (m + 1),
      ‖(centredGeneratingPolynomial jset η).coeff k‖ ≤
        c k * (environment 0 * (1 - environment 0)) ^ ((k : ℝ) / 2) := by
    intro k hk
    have hk' := Finset.mem_Ico.mp hk
    exact table.coeff_norm_bound m hcheck jset η (environment 0 * (1 - environment 0))
      hcard (by positivity) hη hV k hk'.1 (by omega)
  have h := centeredErrorIntegral_finite_bound jset η m (by omega) hcard hη hu0 hu1 c hc
  rw [value_finiteError m table.scale table.upper environment (by omega) hu0.le hu1.le]
  refine h.trans_eq (Finset.sum_congr rfl ?_)
  intro k hk
  have hkm : k ≤ m := by have := (Finset.mem_Ico.mp hk).2; omega
  have hchoose : (m.choose k : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hkm).ne'
  have hv : (coefficient table.scale table.upper k).value environment = (table.upperRat k : ℝ) := by
    simp [coefficient, CoefficientTable.upperRat, CoefficientTable.numerator, Expr.value]
  rw [hv]
  dsimp [c]
  rw [mul_div_cancel_right₀ _ hchoose]

theorem value_geometricError (lo hi s : Nat) (upper : List Int) (environment : Nat → ℝ)
    (hu0 : 0 < environment 0) (hu1 : environment 0 ≤ 1) :
    (geometricError lo hi s upper).value environment =
      (1 / ((lo : ℝ) - 1) +
        (∑ k ∈ Finset.Ico 3 (min 10 lo + 1), (coefficient s upper k).value environment *
          (Real.sqrt ((1 - environment 0) / environment 0)) ^ (k - 2)) +
        (if min 10 lo < hi then
          (Real.sqrt ((1 - environment 0) / environment 0)) ^ (min 10 lo - 1) /
            (1 - Real.sqrt ((1 - environment 0) / environment 0)) else 0)) / (environment 0) ^ 2 := by
  have heps := value_eps_general environment hu0.le hu1
  have hz : ((eps / u) : Expr).value environment = (1 - environment 0) / environment 0 := by
    simp [heps, u, Expr.value]
  have hhalf (n : Nat) : (((eps / u) : Expr).half n).value environment =
      (Real.sqrt ((1 - environment 0) / environment 0)) ^ n := by
    rw [Expr.value_half_sqrt _ _ _ (by rw [hz]; positivity), hz]
  have hsum : (∑ j ∈ Finset.range (min 10 lo - 2), (coefficient s upper (j + 3)).value environment *
      (Real.sqrt ((1 - environment 0) / environment 0)) ^ (j + 1)) =
      ∑ k ∈ Finset.Ico 3 (min 10 lo + 1), (coefficient s upper k).value environment *
        (Real.sqrt ((1 - environment 0) / environment 0)) ^ (k - 2) := by
    rw [Finset.sum_Ico_eq_sum_range, show min 10 lo + 1 - 3 = min 10 lo - 2 by omega]
    apply Finset.sum_congr rfl
    intro j hj
    rw [show 3 + j = j + 3 by omega, show j + 3 - 2 = j + 1 by omega]
  by_cases ht : min 10 lo < hi
  · simp only [geometricError, ht, ite_true, Expr.value_div, Expr.value_add, Expr.value_pow,
      Expr.value_sum_range, Expr.value_mul, hhalf]
    rw [hsum]
    simp [Expr.value, heps, u]
  · simp only [geometricError, ht, ite_false, Expr.value_div, Expr.value_add, Expr.value_pow,
      Expr.value_sum_range, Expr.value_mul, hhalf]
    rw [hsum]
    simp [Expr.value, u]

theorem geometricError_bound {ι : Type*}
    (jset : Finset ι) (η : ι → ℂ) (m lo hi s : Nat) (upper : List Int)
    (hlo : 3 ≤ lo) (hlom : lo ≤ m) (hmhi : m ≤ hi) (hcard : jset.card = m)
    (hη : ∑ j ∈ jset, η j = 0) (environment : Nat → ℝ)
    (hu0 : 1 / 2 < environment 0) (hu1 : environment 0 < 1)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (m : ℝ) * (environment 0 * (1 - environment 0)))
    (hcoeff : ∀ k ∈ Finset.Ico 3 (min 10 lo + 1),
      ‖(centredGeneratingPolynomial jset η).coeff k‖ / (m.choose k : ℝ) ≤
        (coefficient s upper k).value environment *
          (environment 0 * (1 - environment 0)) ^ ((k : ℝ) / 2)) :
    centeredErrorIntegral jset η m (environment 0) / (1 - environment 0) ≤
      (geometricError lo hi s upper).value environment := by
  classical
  let u := environment 0
  have hu : 0 < u := by dsimp [u]; linarith
  have heps : 0 < 1 - u := by dsimp [u]; linarith
  have hvar : 0 < u * (1 - u) := mul_pos hu heps
  let kmax := min 10 lo
  have hkmax : 3 ≤ kmax := by dsimp [kmax]; omega
  have hkm : kmax ≤ m := by dsimp [kmax]; omega
  let z := Real.sqrt ((1 - u) / u)
  have hz : 0 ≤ z := Real.sqrt_nonneg _
  have hz1 : z < 1 := by
    have hsq : z ^ 2 = (1 - u) / u := Real.sq_sqrt (by positivity)
    have hratio : (1 - u) / u < 1 := (div_lt_one hu).mpr (by dsimp [u]; linarith)
    nlinarith
  let c : Nat → ℝ := fun k => if k = 2 then 1 / ((lo : ℝ) - 1)
    else if k ≤ kmax then (coefficient s upper k).value environment else 1
  have hc : ∀ k ∈ Finset.Ico 2 (m + 1),
      ‖(centredGeneratingPolynomial jset η).coeff k‖ / (m.choose k : ℝ) ≤
        c k * (u * (1 - u)) ^ ((k : ℝ) / 2) := by
    intro k hk
    have hk2 : 2 ≤ k := (Finset.mem_Ico.mp hk).1
    have hkm' : k ≤ m := by have := (Finset.mem_Ico.mp hk).2; omega
    by_cases heq : k = 2
    · subst k
      have hsecond := coeff_two_norm_div_choose_bound jset η (u * (1 - u)) (by omega)
        hη (by simpa only [hcard] using hV)
      have hdegree : u * (1 - u) / ((m : ℝ) - 1) ≤ u * (1 - u) / ((lo : ℝ) - 1) := by
        apply div_le_div_of_nonneg_left hvar.le
        · have h : (3 : ℝ) ≤ lo := by exact_mod_cast hlo
          linarith
        · exact sub_le_sub_right (by exact_mod_cast hlom) 1
      rw [hcard] at hsecond
      simpa [c, div_eq_mul_inv, mul_comm] using hsecond.trans hdegree
    by_cases hsmall : k ≤ kmax
    · have h := hcoeff k (Finset.mem_Ico.mpr ⟨by omega, by dsimp [kmax] at hsmall; omega⟩)
      simpa [c, heq, hsmall, u] using h
    · have h := coeff_norm_div_choose_bound jset η (u * (1 - u)) hvar.le hη
        (by simpa only [hcard] using hV) k (by omega)
      simpa [c, heq, hsmall, hcard] using h
  have hmain := normalized_centered_error_le jset η m (by omega) hcard hη hu hu1 c hc
  have hsplit : (∑ k ∈ Finset.Ico 2 (m + 1), c k * z ^ (k - 2)) =
      1 / ((lo : ℝ) - 1) +
        (∑ k ∈ Finset.Ico 3 (kmax + 1), (coefficient s upper k).value environment * z ^ (k - 2)) +
        ∑ k ∈ Finset.Ico (kmax + 1) (m + 1), z ^ (k - 2) := by
    rw [← Finset.sum_Ico_consecutive _ (by omega : 2 ≤ 3) (by omega : 3 ≤ m + 1)]
    rw [← Finset.sum_Ico_consecutive _ (by omega : 3 ≤ kmax + 1) (by omega : kmax + 1 ≤ m + 1)]
    have hfirst : (∑ k ∈ Finset.Ico 2 3, c k * z ^ (k - 2)) = 1 / ((lo : ℝ) - 1) := by norm_num [c]
    have hmid : (∑ k ∈ Finset.Ico 3 (kmax + 1), c k * z ^ (k - 2)) =
        ∑ k ∈ Finset.Ico 3 (kmax + 1), (coefficient s upper k).value environment * z ^ (k - 2) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_Ico.mp hk
      simp [c, show k ≠ 2 by omega, show k ≤ kmax by omega]
    have hlast : (∑ k ∈ Finset.Ico (kmax + 1) (m + 1), c k * z ^ (k - 2)) =
        ∑ k ∈ Finset.Ico (kmax + 1) (m + 1), z ^ (k - 2) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_Ico.mp hk
      simp [c, show k ≠ 2 by omega, show ¬k ≤ kmax by omega]
    rw [hfirst, hmid, hlast]
    ring
  have htail : (∑ k ∈ Finset.Ico (kmax + 1) (m + 1), z ^ (k - 2)) ≤
      if kmax < hi then z ^ (kmax - 1) / (1 - z) else 0 := by
    by_cases ht : kmax < hi
    · rw [ite_eq_left ht]
      simpa only [show kmax + 1 - 2 = kmax - 1 by omega] using
        finite_geometric_tail_bound (kmax + 1) m 2 (by omega) hz hz1
    · have heq : m = kmax := by omega
      simp [heq, ht]
  rw [value_geometricError lo hi s upper environment hu hu1.le]
  change centeredErrorIntegral jset η m u / (1 - u) ≤
    (∑ k ∈ Finset.Ico 2 (m + 1), c k * z ^ (k - 2)) / u ^ 2 at hmain
  rw [hsplit] at hmain
  refine hmain.trans (div_le_div_of_nonneg_right ?_ (sq_nonneg u))
  exact add_le_add le_rfl htail

theorem geometricError_bound_of_table {ι : Type*} [DecidableEq ι]
    (table : CoefficientTable) (m : Nat) (hm : 3 ≤ m) (hcheck : table.check m = true)
    (jset : Finset ι) (η : ι → ℂ) (hcard : jset.card = m)
    (hη : ∑ j ∈ jset, η j = 0) (environment : Nat → ℝ)
    (hu0 : 1 / 2 < environment 0) (hu1 : environment 0 < 1)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (m : ℝ) * (environment 0 * (1 - environment 0))) :
    centeredErrorIntegral jset η m (environment 0) / (1 - environment 0) ≤
      (geometricError m m table.scale table.upper).value environment := by
  apply geometricError_bound jset η m m m table.scale table.upper hm le_rfl le_rfl hcard
    hη environment hu0 hu1 hV
  intro k hk
  have hk' := Finset.mem_Ico.mp hk
  have hkm : k ≤ m := by omega
  have hchoose : (0 : ℝ) < m.choose k := by exact_mod_cast Nat.choose_pos hkm
  have hu : 0 < environment 0 := by linarith
  have hbound := table.coeff_norm_bound m hcheck jset η (environment 0 * (1 - environment 0))
    hcard (by positivity) hη hV k (by omega) hkm
  have h := div_le_div_of_nonneg_right hbound hchoose.le
  have hv : (coefficient table.scale table.upper k).value environment = (table.upperRat k : ℝ) := by
    simp [coefficient, CoefficientTable.upperRat, CoefficientTable.numerator, Expr.value]
  rw [hv]
  convert h using 1
  field_simp

theorem geometricError_bound_of_cauchy {ι : Type*}
    (jset : Finset ι) (η : ι → ℂ) (m lo hi s : Nat) (upper : List Int)
    (hlo : 11 ≤ lo) (hlom : lo ≤ m) (hmhi : m ≤ hi) (hcard : jset.card = m)
    (hη : ∑ j ∈ jset, η j = 0) (environment : Nat → ℝ)
    (hu0 : 1 / 2 < environment 0) (hu1 : environment 0 < 1)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (m : ℝ) * (environment 0 * (1 - environment 0)))
    (hcoeff : ∀ k ∈ Finset.Ico 3 11, normalizedCauchyCoefficient m k ≤
      (coefficient s upper k).value environment) :
    centeredErrorIntegral jset η m (environment 0) / (1 - environment 0) ≤
      (geometricError lo hi s upper).value environment := by
  apply geometricError_bound jset η m lo hi s upper (by omega) hlom hmhi hcard hη environment hu0 hu1 hV
  intro k hk
  have hmin : min 10 lo = 10 := by omega
  rw [hmin] at hk
  have hk' := Finset.mem_Ico.mp hk
  have hklt : k < m := by omega
  have hchoose : (0 : ℝ) < m.choose k := by exact_mod_cast Nat.choose_pos hklt.le
  have hu : 0 < environment 0 := by linarith
  have hvar : 0 < environment 0 * (1 - environment 0) := by positivity
  have h := centredGeneratingPolynomial_coeff_cauchy jset η
    (environment 0 * (1 - environment 0)) hvar hη (by simpa only [hcard] using hV)
    k (by omega) (by omega)
  rw [hcard] at h
  have hd := div_le_div_of_nonneg_right h hchoose.le
  have hd' : ‖(centredGeneratingPolynomial jset η).coeff k‖ / (m.choose k : ℝ) ≤
      normalizedCauchyCoefficient m k * (environment 0 * (1 - environment 0)) ^ ((k : ℝ) / 2) := by
    simpa [normalizedCauchyCoefficient, div_mul_eq_mul_div] using hd
  exact hd'.trans (mul_le_mul_of_nonneg_right (hcoeff k hk) (Real.rpow_nonneg hvar.le _))

end Schmeisser.Certificates.Block

import Schmeisser.Certificates.ExpressionValues
import Schmeisser.GeometricErrorIntegrals
import Schmeisser.QuadraticIntegrals

open scoped BigOperators

namespace Schmeisser.Certificates

namespace Expr

theorem value_foldl_add (env : Nat → ℝ) (xs : List Expr) (initial : Expr) :
    (xs.foldl (· + ·) initial).value env = initial.value env + (xs.map (value env)).sum := by
  induction xs generalizing initial with
  | nil => simp
  | cons x xs ih => simp [List.foldl_cons, ih, add_assoc]

theorem value_sum (env : Nat → ℝ) (xs : List Expr) :
    (Expr.sum xs).value env = (xs.map (value env)).sum := by
  simp [Expr.sum, value_foldl_add]

theorem value_sum_range (env : Nat → ℝ) (n : Nat) (f : Nat → Expr) :
    (Expr.sum ((List.range n).map f)).value env =
      ∑ j ∈ Finset.range n, (f j).value env := by
  rw [value_sum]
  simp only [List.map_map]
  induction n with
  | zero => simp
  | succ n ih =>
      simpa [List.range_succ, Finset.sum_range_succ] using
        (congrArg (fun x : ℝ => x + (f n).value env) ih)

theorem value_half_sqrt (env : Nat → ℝ) (a : Expr) (n : Nat) (ha : 0 ≤ a.value env) :
    (a.half n).value env = (Real.sqrt (a.value env)) ^ n := by
  rw [value_half, ← rpow_half_eq_natPow_sqrt n ha,
    Real.rpow_div_two_eq_sqrt _ ha, Real.rpow_natCast]

end Expr

namespace Scalar

theorem value_cauchyCoefficient (m k : Nat) (env : Nat → ℝ) :
    (cauchyCoefficient m k).value env = normalizedCauchyCoefficient m k := by
  by_cases hkm : k ≤ m
  · simp [cauchyCoefficient, normalizedCauchyCoefficient, Expr.value,
      ← Nat.choose_eq_fast_choose, Nat.cast_sub hkm]
  · simp [cauchyCoefficient, normalizedCauchyCoefficient, Expr.value,
      ← Nat.choose_eq_fast_choose, Nat.choose_eq_zero_of_lt (by omega : m < k)]

theorem value_geometricCauchy (m : Nat) (_hm : 1 ≤ m) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x ≤ 1) :
    (geometricCauchy m).value (fun _ => x) =
      (1 / ((m : ℝ) - 1) +
        (∑ k ∈ Finset.Ico 3 11, normalizedCauchyCoefficient m k *
          (Real.sqrt ((1 - x) / x)) ^ (k - 2)) +
        (Real.sqrt ((1 - x) / x)) ^ 9 / (1 - Real.sqrt ((1 - x) / x))) / x ^ 2 := by
  have hz : ((eps / u) : Expr).value (fun _ => x) = (1 - x) / x := by
    simp [eps, u, Expr.value, max_eq_right (sub_nonneg.mpr hx1)]
  have hhalf (n : Nat) : (((eps / u) : Expr).half n).value (fun _ => x) =
      (Real.sqrt ((1 - x) / x)) ^ n := by
    rw [Expr.value_half_sqrt _ _ _ (by rw [hz]; positivity), hz]
  have hsum : (∑ j ∈ Finset.range 8,
      normalizedCauchyCoefficient m (j + 3) * (Real.sqrt ((1 - x) / x)) ^ (j + 1)) =
      ∑ k ∈ Finset.Ico 3 11, normalizedCauchyCoefficient m k *
        (Real.sqrt ((1 - x) / x)) ^ (k - 2) := by
    rw [Finset.sum_Ico_eq_sum_range]
    norm_num
    apply Finset.sum_congr rfl
    intro j hj
    rw [show 3 + j = j + 3 by omega, show j + 3 - 2 = j + 1 by omega]
  simp only [geometricCauchy, Expr.value_div, Expr.value_add, Expr.value_pow,
    Expr.value_sum_range, Expr.value_mul, value_cauchyCoefficient, hhalf]
  rw [hsum]
  simp [Expr.value, u, eps, max_eq_right (sub_nonneg.mpr hx1)]

theorem geometricCauchy_error_bound {ι : Type*}
    (jset : Finset ι) (η : ι → ℂ) (m : ℕ) (hm : 11 ≤ m) (hcard : jset.card = m)
    (hη : ∑ j ∈ jset, η j = 0) {x : ℝ} (hx0 : 1 / 2 < x) (hx1 : x < 1)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (m : ℝ) * (x * (1 - x))) :
    centeredErrorIntegral jset η m x / (1 - x) ≤
      (geometricCauchy m).value (fun _ => x) := by
  rw [value_geometricCauchy m (by omega) (by linarith) hx1.le]
  exact centeredErrorIntegral_geometric_cauchy jset η m hm hcard hη hx0 hx1 hV

end Scalar
end Schmeisser.Certificates

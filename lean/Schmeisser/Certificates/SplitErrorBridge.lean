import Schmeisser.Certificates.GeometricErrorBridge
import Schmeisser.NormalizedErrorIntegrals

open scoped BigOperators

namespace Schmeisser.Certificates

theorem Expr.value_half_rpow (env : Nat → ℝ) (a : Expr) (n : Nat) (ha : 0 ≤ a.value env) :
    (a.half n).value env = a.value env ^ ((n : ℝ) / 2) := by
  rw [Expr.value_half]
  exact (rpow_half_eq_natPow_sqrt n ha).symm

namespace Scalar

theorem value_beta (a : Expr) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    (beta a).value (fun _ => x) = baseQuadratic x (a.value (fun _ => x)) := by
  simp only [beta, Expr.value_sub, u, Expr.value]
  norm_num only
  have heq : 1 - x * a.value (fun _ => x) * (2 - a.value (fun _ => x)) =
      baseQuadratic x (a.value (fun _ => x)) := by unfold baseQuadratic; ring
  rw [heq, max_eq_right (baseQuadratic_pos hx0 hx1).le]

theorem value_da (a : Expr) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (ha1 : a.value (fun _ => x) ≤ 1) :
    (da a).value (fun _ => x) = 1 - x * a.value (fun _ => x) := by
  simp only [da, Expr.value_sub, u, Expr.value]
  norm_num only
  rw [max_eq_right (by nlinarith : 0 ≤ 1 - x * a.value (fun _ => x))]

theorem value_front (m : Nat) (a : Expr) (x : ℝ) :
    (front m a).value (fun _ => x) =
      40 * (m : ℝ) /
        (3 * ((m : ℝ) - 1) * ((m : ℝ) + 3) *
          (2 - a.value (fun _ => x)) ^ 3 * x ^ 2) := by
  simp [front, Expr.value, u]

theorem value_splitRaw (m : Nat) (a : Expr) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (ha1 : a.value (fun _ => x) ≤ 1) :
    (splitRaw m a).value (fun _ => x) =
      40 * (m : ℝ) /
        (3 * ((m : ℝ) - 1) * ((m : ℝ) + 3) * (2 - a.value (fun _ => x)) ^ 3 * x ^ 2) +
      (1 - a.value (fun _ => x)) * ((m : ℝ) + 1) *
        (baseQuadratic x (a.value (fun _ => x)) ^ ((m : ℝ) / 2) +
          (1 - x * a.value (fun _ => x)) ^ m) / (1 - x) := by
  have hb : 0 ≤ (beta a).value (fun _ => x) := by
    rw [value_beta a hx0.le hx1]
    exact (baseQuadratic_pos hx0.le hx1).le
  simp only [splitRaw, Expr.value_add, Expr.value_div, Expr.value_mul, Expr.value_sub,
    Expr.value_pow, Expr.value_ofNat, value_front, Expr.value_half_rpow _ _ _ hb,
    value_beta a hx0.le hx1, value_da a hx0.le hx1 ha1]
  simp [eps, u, Expr.value, max_eq_right (sub_nonneg.mpr hx1.le)]

theorem value_splitOld (m : Nat) (hm : 3 ≤ m) (a : Expr) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    (splitOld m a).value (fun _ => x) =
      40 * (m : ℝ) /
        (3 * ((m : ℝ) - 1) * ((m : ℝ) + 3) * (2 - a.value (fun _ => x)) ^ 3 * x ^ 2) +
      (5 / 6 : ℝ) * (1 - a.value (fun _ => x)) * x * (m : ℝ) * ((m : ℝ) + 1) *
        baseQuadratic x (a.value (fun _ => x)) ^ (((m : ℝ) - 3) / 2) := by
  have hb : 0 ≤ (beta a).value (fun _ => x) := by
    rw [value_beta a hx0.le hx1]
    exact (baseQuadratic_pos hx0.le hx1).le
  simp only [splitOld, Expr.value_add, Expr.value_div, Expr.value_mul, Expr.value_sub,
    Expr.value_ofNat, value_front, Expr.value_half_rpow _ _ _ hb, value_beta a hx0.le hx1]
  simp [Expr.value, u, Nat.cast_sub hm, mul_assoc]

theorem splitRaw_error_bound {ι : Type*} [DecidableEq ι]
    (jset : Finset ι) (η : ι → ℂ) (m : ℕ) (hm : 3 ≤ m) (hcard : jset.card = m)
    (hη : ∑ j ∈ jset, η j = 0) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (m : ℝ) * (x * (1 - x)))
    (a : Expr) (ha0 : 0 ≤ a.value (fun _ => x)) (ha1 : a.value (fun _ => x) < 1) :
    centeredErrorIntegral jset η m x / (1 - x) ≤ (splitRaw m a).value (fun _ => x) := by
  rw [value_splitRaw m a hx0 hx1 ha1.le]
  exact centered_error_split_triangle_normalized jset η m hm hcard hx0 hx1 ha0 ha1 hη hV

theorem splitOld_error_bound {ι : Type*} [DecidableEq ι]
    (jset : Finset ι) (η : ι → ℂ) (m : ℕ) (hm : 3 ≤ m) (hcard : jset.card = m)
    (hη : ∑ j ∈ jset, η j = 0) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (m : ℝ) * (x * (1 - x)))
    (a : Expr) (ha0 : 0 ≤ a.value (fun _ => x)) (ha1 : a.value (fun _ => x) < 1) :
    centeredErrorIntegral jset η m x / (1 - x) ≤ (splitOld m a).value (fun _ => x) := by
  rw [value_splitOld m hm a hx0 hx1]
  exact centered_error_split_interpolation_normalized jset η m hm hcard hx0 hx1 ha0 ha1 hη hV

end Scalar
end Schmeisser.Certificates

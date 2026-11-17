import Schmeisser.Certificates.BlockRecurrenceBridge
import Schmeisser.PolarCertification

namespace Schmeisser.Certificates.Block

open MeasureTheory

theorem value_polar (m : Nat) {x κ : ℝ}
    (hx : 0 < x) (hx1 : x < 1) (hk : 0 < κ) (hh1 : comparisonDrop x κ ≤ 1) :
    (polar m).value (env x m κ) =
      ∫ t : ℝ in 0..1,
        (1 - comparisonDrop x κ + comparisonDrop x κ * (1 + x) * t) ^ ((m : ℝ) / 2) := by
  have hh : 0 < comparisonDrop x κ := by
    unfold comparisonDrop
    exact div_pos (mul_pos hk (sub_pos.mpr hx1)) hx
  have ha : 0 ≤ 1 + comparisonDrop x κ * x := by positivity
  have hb : 0 ≤ 1 - comparisonDrop x κ := sub_nonneg.mpr hh1
  have hv1 : (1 + h * u : Expr).value (env x m κ) = 1 + comparisonDrop x κ * x := by
    simp [value_h m κ hx.le hx1.le]
  have hv2 : (1 - h : Expr).value (env x m κ) = 1 - comparisonDrop x κ := by
    simp [value_h m κ hx.le hx1.le]
  have hp1 : ((1 + h * u : Expr).half (m + 2)).value (env x m κ) =
      (1 + comparisonDrop x κ * x) ^ (((m : ℝ) + 2) / 2) := by
    rw [Expr.value_half, hv1, ← rpow_half_eq_natPow_sqrt (m + 2) ha]
    simp only [Nat.cast_add, Nat.cast_ofNat]
  have hp2 : ((1 - h : Expr).half (m + 2)).value (env x m κ) =
      (1 - comparisonDrop x κ) ^ (((m : ℝ) + 2) / 2) := by
    rw [Expr.value_half, hv2, ← rpow_half_eq_natPow_sqrt (m + 2) hb]
    simp only [Nat.cast_add, Nat.cast_ofNat]
  rw [polar_integral_degree_formula m hx.le hh]
  simp only [polar, Expr.value_div, Expr.value_mul, Expr.value_add, Expr.value_sub,
    Expr.value_ofNat, hp1, hp2, value_h m κ hx.le hx1.le, value_u,
    Expr.value, Int.cast_natCast, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one,
    Int.cast_add, Int.cast_ofNat, Int.cast_one]

theorem drop_lt_of_polar_test (m : Nat) (hm : 2 ≤ m) {x κ actualDrop : ℝ}
    (hx : 0 < x) (hx1 : x < 1) (hk : 0 < κ)
    (hh0 : 0 < actualDrop) (hh1 : comparisonDrop x κ ≤ 1)
    (hpolar : 1 ≤ ∫ t : ℝ in 0..1,
      (1 - actualDrop + actualDrop * (1 + x) * t) ^ ((m : ℝ) / 2))
    (htest : (polar m).value (env x m κ) < 1) :
    comparisonDrop x κ < actualDrop := by
  have hh : 0 < comparisonDrop x κ := by
    unfold comparisonDrop
    exact div_pos (mul_pos hk (sub_pos.mpr hx1)) hx
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  rw [value_polar m hx hx1 hk hh1] at htest
  exact polar_certification hx.le hh0 hh hh1 (by linarith) hpolar htest

end Schmeisser.Certificates.Block

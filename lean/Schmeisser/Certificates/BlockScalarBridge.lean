import Schmeisser.Certificates.BlockErrorExpressions
import Schmeisser.Certificates.BlockRecurrenceBridge
import Schmeisser.FiniteReduction

namespace Schmeisser.Certificates.Block

open MeasureTheory

theorem scalar_exclusion_of_target {ι : Type*}
    (jset : Finset ι) (η : ι → ℂ) (lo m hi s : Nat) (hlm : lo ≤ m)
    (upper : List Int) (panels : List (Rat × Rat)) (kind : ErrorKind)
    {x actualDrop κ : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (hk : 0 ≤ κ) (hk4 : κ / x ≤ 4) (hdrop : comparisonDrop x κ ≤ actualDrop)
    (herror : centeredErrorIntegral jset η m x / (1 - x) ≤
      (error lo hi s upper panels kind).value (env x m κ))
    (hgap : (target lo hi s upper panels kind).value (env x m κ) <
      normalizedComparisonIntegral m x κ) :
    ((m : ℝ) + 1) * (∫ t : ℝ in 0..1,
      (max (1 - 2 * x * t + x * t ^ 2 - actualDrop * t * (1 - t)) 0) ^ ((m : ℝ) / 2)) <
      (((m : ℝ) + 1) * ∫ t : ℝ in 0..1, (1 - x * t) ^ m) -
        centeredErrorIntegral jset η m x := by
  have hp : (1 - x) ^ m ≤ (1 - x) ^ lo :=
    pow_le_pow_of_le_one (sub_nonneg.mpr hx1.le) (by linarith) hlm
  have hrem : (1 - x) ^ m / x ≤ (1 - x) ^ lo / x :=
    div_le_div_of_nonneg_right hp hx.le
  have htarget : (target lo hi s upper panels kind).value (env x m κ) =
      (error lo hi s upper panels kind).value (env x m κ) + (1 - x) ^ lo / x := by
    simp only [target, Expr.value_add, Expr.value_div, Expr.value_pow,
      value_eps m κ hx.le hx1.le, value_u]
  rw [htarget] at hgap
  apply scalar_exclusion_of_normalized_comparison jset η m hx hx1 hk hk4 hdrop herror
  linarith

end Schmeisser.Certificates.Block

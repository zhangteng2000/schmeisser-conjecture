import Schmeisser.Certificates.BlockRecurrenceBridge
import Schmeisser.FiniteMomentBound

namespace Schmeisser.Certificates.Block

theorem moment_le_integral (lo m hi : Nat)
    (hlo : 0 < lo) (hlm : lo ≤ m) (hmh : m ≤ hi)
    {x κ : ℝ} (hx : 0 < x) (hx1 : x < 1) (hk : 0 ≤ κ) (hk4 : κ / x ≤ 4)
    (hlarge : 90 ≤ (lo : ℝ) * (comparisonB x κ ^ 2 / comparisonD x κ)) :
    (moment lo hi).value (env x m κ) ≤ normalizedComparisonIntegral m x κ := by
  have hbound := normalizedComparisonIntegral_block_moment_lower lo m hi hlo hlm hmh
    hx hx1 hk hk4 hlarge
  have he : (eps.half lo).value (env x m κ) = (1 - x) ^ ((lo : ℝ) / 2) := by
    rw [Expr.value_half, value_eps m κ hx.le hx1.le]
    exact (rpow_half_eq_natPow_sqrt lo (sub_nonneg.mpr hx1.le)).symm
  simpa only [moment, Expr.value_sub, Expr.value_mul, Expr.value_div, Expr.value_pow,
    Expr.value_ofNat, value_kap, value_u, value_b m κ hx.le hx1.le,
    value_mt_quotient m hx hx1 hk hk4, value_d m κ hx.le hx1.le,
    value_te m κ hx.le hx1.le, he, Expr.value, Int.cast_natCast,
    Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, Int.cast_add, Int.cast_one,
    Int.cast_ofNat] using hbound

end Schmeisser.Certificates.Block

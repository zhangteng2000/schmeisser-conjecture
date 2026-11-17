import Schmeisser.Certificates.BlockSoundness
import Schmeisser.Certificates.BlockMomentBridge
import Schmeisser.Certificates.BlockPolarBridge
import Schmeisser.PolarThresholds

namespace Schmeisser.Certificates.Finite

open MeasureTheory

def ErrorConditions (data : Data) (x : ℝ) : Block.ErrorKind → Prop
  | .finite => data.lo = data.hi
  | .geometric => (1 : ℝ) / 2 < x
  | .splitRaw a => (0 : ℝ) ≤ (a : ℝ) ∧ (a : ℝ) < 1
  | .riemann => True
  | .convexRiemann _ => True

structure NumericRule.RealConditions (data : Data) (rule : NumericRule)
    (m : Nat) (x actualDrop : ℝ) : Prop where
  kappa_pos : 0 < rule.kappa data
  kappa_bound : rule.kappa data / x ≤ 4
  drop_lt : comparisonDrop x (rule.kappa data) < actualDrop
  lower_le : (rule.lowerExpr data).value (Block.env x m (rule.kappa data)) ≤
    normalizedComparisonIntegral m x (rule.kappa data)
  target_lt : (rule.upperExpr data).value (Block.env x m (rule.kappa data)) <
    normalizedComparisonIntegral m x (rule.kappa data)
  error_conditions : ErrorConditions data x rule.error

theorem NumericRule.checked_real (data : Data) (rule : NumericRule)
    (m : Nat) (hlo3 : 3 ≤ data.lo) (hlm : data.lo ≤ m) (hmh : m ≤ data.hi)
    {box : Interval} {x actualDrop : ℝ}
    (hx : 0 < x) (hx1 : x < 1) (hh0 : 0 < actualDrop) (hh1 : actualDrop < 1)
    (hxbox : box.Contains scale x) (hcut : (data.cutoff : ℝ) / scale ≤ x)
    (hpolar : 1 ≤ ∫ t : ℝ in 0..1,
      (1 - actualDrop + actualDrop * (1 + x) * t) ^ ((m : ℝ) / 2))
    (hchecked : rule.Checked data box m x) :
    rule.RealConditions data m x actualDrop := by
  rcases hchecked with ⟨hdomain, hgap, hκbound, hpolarTest, hmoment⟩
  rcases hdomain with ⟨hnum, hb0, hblo, hb1, hbase, herror⟩
  have hsR : (0 : ℝ) < scale := by exact_mod_cast scale_pos
  have hcbox := data.clip_contains hxbox hcut
  have hcscaled := (Interval.contains_iff_scaled scale_pos (data.clip box) x).mp hcbox
  have hhi : (0 : ℝ) < data.hi := by exact_mod_cast (show 0 < data.hi by omega)
  have hκpos : 0 < rule.kappa data := by
    unfold NumericRule.kappa
    exact div_pos (by exact_mod_cast (show 0 < rule.num by omega)) (by positivity)
  have hκ4 : rule.kappa data / x ≤ 4 := by
    simpa only [Expr.value_div, Block.value_kap, Block.value_u] using hκbound
  have hdrop : comparisonDrop x (rule.kappa data) < actualDrop := by
    rcases hpolarTest with hdefault | ⟨hsingle, hH, htest⟩
    · have hκeq : rule.kappa data = 6 / (data.hi : ℝ) := by
        unfold NumericRule.kappa
        rw [hdefault]
        norm_num
        <;> ring
      rw [hκeq]
      exact (polar_default_drop_for_block m data.hi (by omega) hmh
        hx hx1.le hh0 hh1 hpolar).2
    · have hmeq : m = data.lo := by omega
      have hH' : comparisonDrop x (rule.kappa data) ≤ 1 := by
        simpa only [Block.value_h m (rule.kappa data) hx.le hx1.le] using hH
      apply Block.drop_lt_of_polar_test m (by omega) hx hx1 hκpos hh0 hH' hpolar
      simpa only [hmeq] using htest
  have hlower : (rule.lowerExpr data).value (Block.env x m (rule.kappa data)) ≤
      normalizedComparisonIntegral m x (rule.kappa data) := by
    cases hl : rule.lower with
    | recurrence steps kind =>
      have hd : (LowerKind.recurrence steps kind).domain data (data.clip box) := by
        simpa only [hl] using hbase
      have hind : 0 + 2 * steps + 2 ≤ m := by
        cases kind <;> simp only [LowerKind.domain] at hd <;> omega
      have hv : Block.BaseValid (m - (0 + 2 * steps)) x kind := by
        cases kind with
        | basic quarter invEps =>
          change quarter = true → (3 : ℝ) / 4 ≤ x
          intro hq
          have hqr : (3 : ℝ) * scale ≤ 4 * ((data.clip box).lo : ℝ) := by
            exact_mod_cast hd.2.1 hq
          apply (mul_le_mul_iff_of_pos_right hsR).mp
          linarith [hcscaled.1]
        | exactTwo =>
          change m - (0 + 2 * steps) = 2
          simp only [LowerKind.domain] at hd
          omega
        | trapezoidThree =>
          change m - (0 + 2 * steps) = 3
          simp only [LowerKind.domain] at hd
          omega
      simpa only [NumericRule.lowerExpr, hl, Nat.sub_zero] using
        Block.recurrence_valid_le_integral data.lo data.hi m 0 steps kind hind
          hx hx1 hκpos.le hκ4 hv
    | moment =>
      have hL : 90 ≤ (data.lo : ℝ) * (comparisonB x (rule.kappa data) ^ 2 /
          comparisonD x (rule.kappa data)) := by
        simp only [hl] at hmoment
        simpa only [Expr.value_div, Expr.value_mul, Expr.value_pow,
          Block.value_b m (rule.kappa data) hx.le hx1.le,
          Block.value_d m (rule.kappa data) hx.le hx1.le, Expr.value,
          Int.cast_natCast, mul_div_assoc] using hmoment
      simpa only [NumericRule.lowerExpr, hl] using
        Block.moment_le_integral data.lo m data.hi (by omega) hlm hmh hx hx1
          hκpos.le hκ4 hL
  have herr : ErrorConditions data x rule.error := by
    cases he : rule.error with
    | finite => simpa only [he, errorDomain, ErrorConditions] using herror
    | geometric =>
      have hgr : (scale : ℝ) < 2 * ((data.clip box).lo : ℝ) := by
        have hh : scale < 2 * (data.clip box).lo := by simpa only [he, errorDomain] using herror
        exact_mod_cast hh
      change (1 : ℝ) / 2 < x
      apply (mul_lt_mul_iff_of_pos_right hsR).mp
      linarith [hcscaled.1]
    | splitRaw a =>
      have ha : (0 : Rat) ≤ a ∧ a < 1 ∧ (data.clip box).hi < scale := by
        simpa only [he, errorDomain] using herror
      exact ⟨by exact_mod_cast ha.1, by exact_mod_cast ha.2.1⟩
    | riemann => trivial
    | convexRiemann _ => trivial
  exact ⟨hκpos, hκ4, hdrop, hlower, hgap.trans_le hlower, herr⟩

theorem NumericRule.check_real (data : Data) (rule : NumericRule)
    (m : Nat) (hdata : data.check = true) (hlm : data.lo ≤ m) (hmh : m ≤ data.hi)
    {box : Interval} {x actualDrop : ℝ}
    (hx : 0 < x) (hx1 : x < 1) (hh0 : 0 < actualDrop) (hh1 : actualDrop < 1)
    (hxbox : box.Contains scale x)
    (hpolar : 1 ≤ ∫ t : ℝ in 0..1,
      (1 - actualDrop + actualDrop * (1 + x) * t) ^ ((m : ℝ) / 2))
    (hcheck : rule.check data box = true) :
    rule.RealConditions data m x actualDrop := by
  have hd := data.check_sound hdata
  have hcut : (data.cutoff : ℝ) / scale < x :=
    polar_parameter_gt_of_block_threshold m data.hi (by omega) hmh hx.le hh0 hh1.le
      hpolar hd.2.2.2.2.2.2
  exact rule.checked_real data m hd.1 hlm hmh hx hx1 hh0 hh1 hxbox hcut.le hpolar
    (rule.check_sound data (by omega) hxbox hcut.le hlm hmh hcheck)

end Schmeisser.Certificates.Finite

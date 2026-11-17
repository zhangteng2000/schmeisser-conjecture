import Schmeisser.Certificates.VerifiedBlock
import Schmeisser.Certificates.BlockNumericBridge
import Schmeisser.Certificates.BlockScalarBridge
import Schmeisser.Certificates.BlockCoefficientBridge
import Schmeisser.Certificates.BlockErrorBridge
import Schmeisser.Certificates.ConvexPanelBridge
import Schmeisser.QuarticEndpoint

open scoped BigOperators
open MeasureTheory

namespace Schmeisser.Certificates.Finite

theorem Data.error_bound {ι : Type*} [DecidableEq ι]
    (data : Data) (hdata : data.check = true) (hcoeff : data.CoefficientsValid)
    (jset : Finset ι) (η : ι → ℂ) (m : Nat) (hlom : data.lo ≤ m) (hmhi : m ≤ data.hi)
    (hcard : jset.card = m) (hη : ∑ j ∈ jset, η j = 0)
    {x κ : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (m : ℝ) * (x * (1 - x)))
    (kind : Block.ErrorKind) (hdomain : ErrorConditions data x kind) :
    centeredErrorIntegral jset η m x / (1 - x) ≤
      (Block.error data.lo data.hi scaleNat data.upper data.panels kind).value (Block.env x m κ) := by
  have hd := data.check_sound hdata
  have hm : 3 ≤ m := hd.1.trans hlom
  cases kind with
  | finite =>
      have hsingle : data.lo = data.hi := hdomain
      have hmeq : m = data.lo := by omega
      rcases hcoeff with ⟨_, table, hs, hu, ht⟩ | ⟨hstrict, _⟩
      · have hcheck : table.check m = true := by simpa only [hmeq] using ht
        have h := Block.finiteError_bound table m hcheck jset η hcard hη (Block.env x m κ) hx hx1 hV
        simpa only [Block.error, hs, hu, hmeq, Block.env, ite_true] using h
      · exact False.elim (by omega)
  | geometric =>
      have hxhalf : (1 : ℝ) / 2 < x := hdomain
      rcases hcoeff with ⟨hsingle, table, hs, hu, ht⟩ | ⟨_, ht⟩
      · have hmeq : m = data.lo := by omega
        have hcheck : table.check m = true := by simpa only [hmeq] using ht
        have h := Block.geometricError_bound_of_table table m hm hcheck jset η hcard hη
          (Block.env x m κ) hxhalf hx1 hV
        simpa only [Block.error, hs, hu, ← hsingle, hmeq, Block.env, ite_true] using h
      · have hlo := (checkCommonCauchy_sound data.lo data.hi scaleNat data.upper ht).1
        apply Block.geometricError_bound_of_cauchy jset η m data.lo data.hi scaleNat data.upper
          hlo hlom hmhi hcard hη (Block.env x m κ) hxhalf hx1 hV
        intro k hk
        have hk' := Finset.mem_Ico.mp hk
        simpa only [Block.value_coefficient] using
          commonCauchy_coefficient_bound ht hlom hmhi hk'.1 (by omega : k ≤ 10)
  | splitRaw a =>
      obtain ⟨ha0, ha1⟩ := hdomain
      exact Block.splitRaw_error_bound jset η data.lo data.hi m hd.1 hlom hmhi hcard hη hx hx1 hV
        (Expr.ofRat a) κ (by simpa only [Expr.value_ofRat] using ha0)
        (by simpa only [Expr.value_ofRat] using ha1)
  | riemann =>
      exact Block.riemann_error_bound jset η data.lo data.hi m (by omega) hlom hmhi hcard hη hx hx1 hV
        data.panels hd.2.2.2.2.2.1 κ
  | convexRiemann mask =>
      exact Block.convexRiemannSelected_error_bound jset η data.lo data.hi m hd.1 hlom hmhi
        hcard hη hx hx1 hV data.panels hd.2.2.2.2.2.1 κ mask

theorem NumericRule.scalar_exclusion {ι : Type*} [DecidableEq ι]
    (data : Data) (rule : NumericRule) (hdata : data.check = true) (hcoeff : data.CoefficientsValid)
    (jset : Finset ι) (η : ι → ℂ) (m : Nat) (hlom : data.lo ≤ m) (hmhi : m ≤ data.hi)
    (hcard : jset.card = m) (hη : ∑ j ∈ jset, η j = 0)
    {box : Interval} {x actualDrop : ℝ}
    (hx : 0 < x) (hx1 : x < 1) (hh0 : 0 < actualDrop) (hh1 : actualDrop < 1)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (m : ℝ) * (x * (1 - x)))
    (hxbox : box.Contains scale x)
    (hpolar : 1 ≤ ∫ t : ℝ in 0..1,
      (1 - actualDrop + actualDrop * (1 + x) * t) ^ ((m : ℝ) / 2))
    (hcheck : rule.check data box = true) :
    ((m : ℝ) + 1) * (∫ t : ℝ in 0..1,
      (max (1 - 2 * x * t + x * t ^ 2 - actualDrop * t * (1 - t)) 0) ^ ((m : ℝ) / 2)) <
      (((m : ℝ) + 1) * ∫ t : ℝ in 0..1, (1 - x * t) ^ m) - centeredErrorIntegral jset η m x := by
  have hc := rule.check_real data m hdata hlom hmhi hx hx1 hh0 hh1 hxbox hpolar hcheck
  have herr := data.error_bound hdata hcoeff jset η m hlom hmhi hcard hη hx hx1 hV rule.error
    (κ := rule.kappa data) hc.error_conditions
  exact Block.scalar_exclusion_of_target jset η data.lo m data.hi scaleNat hlom data.upper data.panels
    rule.error hx hx1 hc.kappa_pos.le hc.kappa_bound hc.drop_lt.le herr hc.target_lt

theorem Rule.scalar_exclusion {ι : Type*} [DecidableEq ι]
    (data : Data) (rule : Rule) (hdata : data.check = true) (hcoeff : data.CoefficientsValid)
    (jset : Finset ι) (η : ι → ℂ) (m : Nat) (hlom : data.lo ≤ m) (hmhi : m ≤ data.hi)
    (hcard : jset.card = m) (hη : ∑ j ∈ jset, η j = 0)
    {box : Interval} {x actualDrop : ℝ}
    (hx : 0 < x) (hx1 : x < 1) (hh0 : 0 < actualDrop) (hh1 : actualDrop < 1)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (m : ℝ) * (x * (1 - x)))
    (hxbox : box.Contains scale x)
    (hpolar : 1 ≤ ∫ t : ℝ in 0..1,
      (1 - actualDrop + actualDrop * (1 + x) * t) ^ ((m : ℝ) / 2))
    (hcheck : rule.check data box = true) :
    ((m : ℝ) + 1) * (∫ t : ℝ in 0..1,
      (max (1 - 2 * x * t + x * t ^ 2 - actualDrop * t * (1 - t)) 0) ^ ((m : ℝ) / 2)) <
      (((m : ℝ) + 1) * ∫ t : ℝ in 0..1, (1 - x * t) ^ m) - centeredErrorIntegral jset η m x := by
  have hd := data.check_sound hdata
  have hs : (0 : ℝ) < scale := by exact_mod_cast scale_pos
  cases rule with
  | threshold =>
      have hcut : (data.cutoff : ℝ) / scale < x :=
        polar_parameter_gt_of_block_threshold m data.hi (by omega) hmhi hx.le hh0 hh1.le hpolar
          hd.2.2.2.2.2.2
      have hupper : box.hi ≤ data.cutoff := of_decide_eq_true hcheck
      have hxu : x ≤ (data.cutoff : ℝ) / scale := hxbox.2.trans
        (div_le_div_of_nonneg_right (by exact_mod_cast hupper) hs.le)
      exact False.elim (not_lt_of_ge hxu hcut)
  | quartic =>
      have hq : data.lo = 3 ∧ data.hi = 3 ∧ 99 * scale ≤ 100 * box.lo :=
        of_decide_eq_true hcheck
      have hm : m = 3 := by omega
      rw [hm] at hcard hV hpolar ⊢
      have hxl : (99 / 100 : ℝ) ≤ x := by
        have hscaled := (Interval.contains_iff_scaled scale_pos box x).mp hxbox
        have hnum : (99 : ℝ) * scale ≤ 100 * (box.lo : ℝ) := by exact_mod_cast hq.2.2
        nlinarith
      have h := quartic_endpoint_scalar_exclusion jset η hcard hxl hx1 hh0 hη hV hpolar
      convert h using 1 <;> norm_num
  | numeric rule =>
      exact rule.scalar_exclusion data hdata hcoeff jset η m hlom hmhi hcard hη hx hx1 hh0 hh1
        hV hxbox hpolar hcheck

theorem VerifiedBlock.scalar_exclusion {ι : Type*} [DecidableEq ι]
    (block : VerifiedBlock) (jset : Finset ι) (η : ι → ℂ) (m : Nat)
    (hlom : block.data.lo ≤ m) (hmhi : m ≤ block.data.hi)
    (hcard : jset.card = m) (hη : ∑ j ∈ jset, η j = 0)
    {x actualDrop : ℝ} (hx : 0 < x) (hx1 : x < 1) (hh0 : 0 < actualDrop) (hh1 : actualDrop < 1)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (m : ℝ) * (x * (1 - x)))
    (hpolar : 1 ≤ ∫ t : ℝ in 0..1,
      (1 - actualDrop + actualDrop * (1 + x) * t) ^ ((m : ℝ) / 2)) :
    ((m : ℝ) + 1) * (∫ t : ℝ in 0..1,
      (max (1 - 2 * x * t + x * t ^ 2 - actualDrop * t * (1 - t)) 0) ^ ((m : ℝ) / 2)) <
      (((m : ℝ) + 1) * ∫ t : ℝ in 0..1, (1 - x * t) ^ m) - centeredErrorIntegral jset η m x := by
  obtain ⟨box, rule, hxbox, hcheck⟩ := checkSegments_covers block.data block.segments 0 scale
    block.segments_checked (by simpa using hx) (by simpa [scale_pos.ne'] using hx1.le)
  exact rule.scalar_exclusion block.data block.data_checked block.coefficients_valid jset η m
    hlom hmhi hcard hη hx hx1 hh0 hh1 hV hxbox hpolar hcheck

end Schmeisser.Certificates.Finite

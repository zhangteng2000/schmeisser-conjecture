import Schmeisser.ErrorIntegrals
import Schmeisser.Certificates.PanelCoverage

open scoped BigOperators
open MeasureTheory Set

namespace Schmeisser

noncomputable def errorPanelInterpolation (m : ℕ) (u a b : ℝ) : ℝ :=
  (5 / 6 : ℝ) * u * b ^ 2 / (1 - u * b) * (m : ℝ) * ((m : ℝ) + 1) *
    baseQuadratic u a ^ (((m - 1 : ℕ) : ℝ) / 2)

noncomputable def errorPanelTriangle (m : ℕ) (u a : ℝ) : ℝ :=
  ((m : ℝ) + 1) * (baseQuadratic u a ^ ((m : ℝ) / 2) + (1 - u * a) ^ m) / (1 - u)

noncomputable def errorPanelBound (m : ℕ) (u a b : ℝ) : ℝ :=
  (b - a) * min (errorPanelInterpolation m u a b) (errorPanelTriangle m u a)

theorem centered_error_panel_interpolation_pointwise {ι : Type*} [DecidableEq ι]
    (jset : Finset ι) (η : ι → ℂ) (m : ℕ) (hm : 2 ≤ m) (hcard : jset.card = m)
    {u a b t : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (ha : 0 ≤ a) (hat : a ≤ t) (htb : t ≤ b) (hb : b ≤ 1)
    (hη : ∑ j ∈ jset, η j = 0)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (m : ℝ) * (u * (1 - u))) :
    ((m : ℝ) + 1) * centeredErrorIntegrand jset η m u t / (1 - u) ≤
      errorPanelInterpolation m u a b := by
  have ht0 := ha.trans hat
  have ht1 := htb.trans hb
  have hb0 := ht0.trans htb
  have heps : 0 < 1 - u := by linarith
  have hdt : 0 < 1 - u * t := by nlinarith [mul_nonneg hu0.le (sub_nonneg.mpr ht1)]
  have hdb : 0 < 1 - u * b := by nlinarith [mul_nonneg hu0.le (sub_nonneg.mpr hb)]
  have hd : 1 - u * b ≤ 1 - u * t := by nlinarith
  have ht2 : t ^ 2 ≤ b ^ 2 := by nlinarith
  have hfrac : t ^ 2 / (1 - u * t) ≤ b ^ 2 / (1 - u * b) := by
    exact (div_le_div_of_nonneg_right ht2 hdt.le).trans
      (div_le_div_of_nonneg_left (sq_nonneg b) hdb hd)
  have hr : 0 ≤ (((m - 1 : ℕ) : ℝ) / 2) := by positivity
  have hpow := Real.rpow_le_rpow (baseQuadratic_pos (t := t) hu0.le hu1).le
    (baseQuadratic_antitone hu0.le ha hat ht1) hr
  let C : ℝ := (5 / 6 : ℝ) * u * (m : ℝ) * ((m : ℝ) + 1)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hpoint := centered_error_pointwise_interpolation jset η m hm hcard hu0.le hu1
    ⟨ht0, ht1⟩ hη hV
  have hnorm := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpoint (show 0 ≤ (m : ℝ) + 1 by positivity)) heps.le
  have hnorm' : ((m : ℝ) + 1) * centeredErrorIntegrand jset η m u t / (1 - u) ≤
      C * (t ^ 2 / (1 - u * t)) * baseQuadratic u t ^ (((m - 1 : ℕ) : ℝ) / 2) := by
    convert hnorm using 1 <;> simp only [C, centeredErrorIntegrand]
    field_simp
  have hbpow : 0 ≤ baseQuadratic u t ^ (((m - 1 : ℕ) : ℝ) / 2) :=
    Real.rpow_nonneg (baseQuadratic_pos hu0.le hu1).le _
  refine hnorm'.trans ?_
  have hh := mul_le_mul (mul_le_mul_of_nonneg_left hfrac hC) hpow hbpow
    (mul_nonneg hC (div_nonneg (sq_nonneg b) hdb.le))
  convert hh using 1
  dsimp [errorPanelInterpolation, C]
  ring

theorem centered_error_panel_triangle_pointwise {ι : Type*}
    (jset : Finset ι) (η : ι → ℂ) (m : ℕ) (hm : 0 < m) (hcard : jset.card = m)
    {u a t : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (ha : 0 ≤ a) (hat : a ≤ t) (ht : t ≤ 1)
    (hη : ∑ j ∈ jset, η j = 0)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (m : ℝ) * (u * (1 - u))) :
    ((m : ℝ) + 1) * centeredErrorIntegrand jset η m u t / (1 - u) ≤
      errorPanelTriangle m u a := by
  have heps : 0 < 1 - u := by linarith
  have hlin0 : 0 ≤ 1 - u * t := by nlinarith [mul_nonneg hu0.le (sub_nonneg.mpr ht)]
  have hlin : 1 - u * t ≤ 1 - u * a := by nlinarith
  have hpow := Real.rpow_le_rpow (baseQuadratic_pos (t := t) hu0.le hu1).le
    (baseQuadratic_antitone hu0.le ha hat ht) (by positivity : 0 ≤ (m : ℝ) / 2)
  have hp := (centered_error_pointwise_triangle jset η m hm hcard hu0.le hu1
    ⟨ha.trans hat, ht⟩ hη hV).trans (add_le_add hpow (pow_le_pow_left₀ hlin0 hlin m))
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp (by positivity)) heps.le

theorem centered_error_panel_bound {ι : Type*} [DecidableEq ι]
    (jset : Finset ι) (η : ι → ℂ) (m : ℕ) (hm : 2 ≤ m) (hcard : jset.card = m)
    {u a b : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (hη : ∑ j ∈ jset, η j = 0)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (m : ℝ) * (u * (1 - u))) :
    ((m : ℝ) + 1) * (∫ t in a..b, centeredErrorIntegrand jset η m u t) / (1 - u) ≤
      errorPanelBound m u a b := by
  calc
    _ = ∫ t in a..b, ((m : ℝ) + 1) * centeredErrorIntegrand jset η m u t / (1 - u) := by
      rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul]
    _ ≤ ∫ _t in a..b, min (errorPanelInterpolation m u a b) (errorPanelTriangle m u a) := by
      apply intervalIntegral.integral_mono_on hab
        ((continuous_const.mul (continuous_centeredErrorIntegrand jset η m u)).div_const
          (1 - u) |>.intervalIntegrable a b) intervalIntegrable_const
      intro t ht
      exact le_min
        (centered_error_panel_interpolation_pointwise jset η m hm hcard hu0 hu1
          ha ht.1 ht.2 hb hη hV)
        (centered_error_panel_triangle_pointwise jset η m (by omega) hcard hu0 hu1
          ha ht.1 (ht.2.trans hb) hη hV)
    _ = _ := by simp [errorPanelBound, intervalIntegral.integral_const, smul_eq_mul]

private theorem panel_partition_first_le_last {a b : ℝ} {panels : List (ℝ × ℝ)}
    (hp : Certificates.PanelPartition b a panels) : a ≤ b := by
  induction hp with
  | nil => exact le_rfl
  | cons hab _ ih => exact hab.le.trans ih

theorem Certificates.PanelPartition.bounds {α : Type} [LinearOrder α]
    {a b : α} {panels : List (α × α)} (hp : Certificates.PanelPartition b a panels) :
    ∀ ab ∈ panels, a ≤ ab.1 ∧ ab.1 < ab.2 ∧ ab.2 ≤ b := by
  have hend {x y : α} {panels : List (α × α)} (h : Certificates.PanelPartition y x panels) :
      x ≤ y := by
    induction h with
    | nil => exact le_rfl
    | cons hxy _ ih => exact hxy.le.trans ih
  induction hp with
  | nil => simp
  | @cons a c panels hac hp ih =>
      intro ab hab
      rcases List.mem_cons.mp hab with rfl | hab
      · exact ⟨le_rfl, hac, hend hp⟩
      · obtain ⟨hca, hab', hbb⟩ := ih ab hab
        exact ⟨hac.le.trans hca, hab', hbb⟩

theorem centered_error_partition_bound {ι : Type*} [DecidableEq ι]
    (jset : Finset ι) (η : ι → ℂ) (m : ℕ) (hm : 2 ≤ m) (hcard : jset.card = m)
    {u a : ℝ} {panels : List (ℝ × ℝ)} (hu0 : 0 < u) (hu1 : u < 1)
    (hp : Certificates.PanelPartition 1 a panels) (ha : 0 ≤ a)
    (hη : ∑ j ∈ jset, η j = 0)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (m : ℝ) * (u * (1 - u))) :
    ((m : ℝ) + 1) * (∫ t in a..1, centeredErrorIntegrand jset η m u t) / (1 - u) ≤
      (panels.map (fun ab => errorPanelBound m u ab.1 ab.2)).sum := by
  induction hp with
  | nil => simp
  | @cons a b panels hab hp ih =>
      have hc := continuous_centeredErrorIntegrand jset η m u
      have hb : b ≤ 1 := panel_partition_first_le_last hp
      have hfirst := centered_error_panel_bound jset η m hm hcard hu0 hu1 ha hab.le hb hη hV
      have htail := ih (ha.trans hab.le)
      rw [List.map_cons, List.sum_cons,
        ← intervalIntegral.integral_add_adjacent_intervals
          (hc.intervalIntegrable a b) (hc.intervalIntegrable b 1), mul_add, add_div]
      exact add_le_add hfirst htail

theorem centered_error_riemann_bound {ι : Type*} [DecidableEq ι]
    (jset : Finset ι) (η : ι → ℂ) (m : ℕ) (hm : 2 ≤ m) (hcard : jset.card = m)
    {u : ℝ} {panels : List (ℝ × ℝ)} (hu0 : 0 < u) (hu1 : u < 1)
    (hp : Certificates.PanelPartition 1 0 panels)
    (hη : ∑ j ∈ jset, η j = 0)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (m : ℝ) * (u * (1 - u))) :
    centeredErrorIntegral jset η m u / (1 - u) ≤
      (panels.map (fun ab => errorPanelBound m u ab.1 ab.2)).sum := by
  exact centered_error_partition_bound jset η m hm hcard hu0 hu1 hp (by norm_num) hη hV

end Schmeisser

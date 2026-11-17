import Schmeisser.Certificates.ConvexPanelExpressions
import Schmeisser.Certificates.BlockErrorBridge
import Schmeisser.ConvexPanelBounds

open scoped BigOperators

namespace Schmeisser.Certificates.Block

theorem value_convexPanelA (t : Expr) (m : Nat) (x κ : ℝ) :
    (convexPanelA t).value (env x m κ) =
      errorConvexAmplitude x (t.value (env x m κ)) := by
  simp [convexPanelA, errorConvexAmplitude, Expr.value, u, env]

theorem value_convexPanelB (lo hi : Nat) (t : Expr) (ρ : Nat → ℝ) :
    (convexPanelB lo hi t).value ρ =
      ((.rat 5 6) * quadraticFactor lo hi *
        .maximum (.int (lo * (lo + 1)) * (beta t).half (lo - 1))
          (.int (hi * (hi + 1)) * (beta t).half (hi - 1))).value ρ := by
  by_cases h : lo = hi
  · subst hi
    simp [convexPanelB, quadraticFactor, Expr.value]
  · simp only [convexPanelB, ite_eq_right h]

theorem value_convexPanelRaw_envelope (lo hi : Nat) (t : Expr) (ρ : Nat → ℝ) :
    (convexPanelRaw lo hi t).value ρ =
      (rawDegreeEnvelope lo hi t / eps).value ρ := by
  by_cases h : lo = hi
  · subst hi
    simp [convexPanelRaw, rawDegreeEnvelope, linearFactor, Expr.value]
  · simp only [convexPanelRaw, ite_eq_right h]

theorem value_convexPanelRaw (lo hi m : Nat) (t : Expr) (κ : ℝ) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    (convexPanelRaw lo hi t).value (env x m κ) =
      (rawDegreeEnvelope lo hi t).value (env x m κ) / (1 - x) := by
  have heps : eps.value (env x m κ) = 1 - x := by
    simp [eps, Expr.value, u, env, max_eq_right (sub_nonneg.mpr hx1.le),
      min_eq_right (by linarith : 1 - x ≤ 1)]
  simp only [value_convexPanelRaw_envelope, Expr.value_div, heps]

theorem convexPanelB_upper (lo hi m : Nat) (hlo : 1 ≤ lo)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) (t : Expr) (κ : ℝ) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    errorConvexWeight m x (t.value (env x m κ)) ≤
      (convexPanelB lo hi t).value (env x m κ) := by
  have hm1 : 1 ≤ m := hlo.trans hlom
  have hhi1 : 1 ≤ hi := hm1.trans hmhi
  have hβ : 0 ≤ (beta t).value (env x m κ) := by
    rw [value_beta t m κ hx0.le hx1]
    exact (baseQuadratic_pos hx0.le hx1).le
  have hquad := quadratic_degree_endpoint_envelope_nat lo hi m 1
    (baseQuadratic x (t.value (env x m κ))) hlo hlom hmhi (baseQuadratic_pos hx0.le hx1)
  have h := mul_le_mul_of_nonneg_left hquad (by norm_num : (0 : ℝ) ≤ 5 / 6)
  rw [value_convexPanelB]
  simp only [Expr.value, value_quadraticFactor,
    Expr.value_half_rpow _ _ _ hβ, value_beta t m κ hx0.le hx1]
  push_cast
  simpa only [errorConvexWeight, Nat.cast_sub hm1, Nat.cast_sub hlo,
    Nat.cast_sub hhi1, Nat.cast_one, mul_assoc] using h

theorem convexPanelRaw_upper (lo hi m : Nat) (hlo : 1 ≤ lo)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) (t : Expr) (κ : ℝ) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) (ht1 : t.value (env x m κ) ≤ 1) :
    errorPanelTriangle m x (t.value (env x m κ)) ≤
      (convexPanelRaw lo hi t).value (env x m κ) := by
  rw [value_convexPanelRaw lo hi m t κ hx0 hx1]
  exact div_le_div_of_nonneg_right
    (rawDegreeEnvelope_upper lo hi m hlo hlom hmhi t κ hx0 hx1 ht1)
    (sub_pos.mpr hx1).le

theorem convexPanel_upper (lo hi m : Nat) (hlo : 1 ≤ lo)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) (a b : Expr) (κ : ℝ) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1)
    (ha0 : 0 ≤ a.value (env x m κ))
    (hab : a.value (env x m κ) ≤ b.value (env x m κ))
    (hb1 : b.value (env x m κ) ≤ 1) :
    errorConvexPanelBound m x (a.value (env x m κ)) (b.value (env x m κ)) ≤
      (convexPanel lo hi a b).value (env x m κ) := by
  have hBa := convexPanelB_upper lo hi m hlo hlom hmhi a κ hx0 hx1
  have hBb := convexPanelB_upper lo hi m hlo hlom hmhi b κ hx0 hx1
  have hRa := convexPanelRaw_upper lo hi m hlo hlom hmhi a κ hx0 hx1 (hab.trans hb1)
  have hRb := convexPanelRaw_upper lo hi m hlo hlom hmhi b κ hx0 hx1 hb1
  have hAa := errorConvexAmplitude_nonneg hx0.le hx1 (Set.mem_Icc.mpr ⟨ha0, hab.trans hb1⟩)
  have hAb := errorConvexAmplitude_nonneg hx0.le hx1 (Set.mem_Icc.mpr ⟨ha0.trans hab, hb1⟩)
  simp only [errorConvexPanelBound, convexPanel, Expr.value,
    Expr.value_div, Expr.value_sub, value_convexPanelA]
  norm_num only
  apply min_le_min
  · exact mul_le_mul_of_nonneg_left (add_le_add hBa hBb)
      (mul_nonneg (div_nonneg (sub_nonneg.mpr hab) (by norm_num)) (add_nonneg hAa hAb))
  · exact mul_le_mul_of_nonneg_left (add_le_add hRa hRb)
      (div_nonneg (sub_nonneg.mpr hab) (by norm_num))

theorem convexRiemann_error_bound {ι : Type*} [DecidableEq ι]
    (jset : Finset ι) (η : ι → ℂ) (lo hi m : Nat) (hlo : 3 ≤ lo)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) (hcard : jset.card = m)
    (hη : ∑ j ∈ jset, η j = 0) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (m : ℝ) * (x * (1 - x)))
    (panels : List (Rat × Rat)) (hp : PanelPartition (1 : Rat) 0 panels) (κ : ℝ) :
    centeredErrorIntegral jset η m x / (1 - x) ≤
      (convexRiemann lo hi panels).value (env x m κ) := by
  have hpR := hp.map (fun q : Rat => (q : ℝ)) (fun a b hab => by exact_mod_cast hab)
  simp only [Rat.cast_one, Rat.cast_zero] at hpR
  have h := centered_error_convex_riemann_bound jset η m (by omega) hcard hx0 hx1 hpR hη hV
  simp only [List.map_map, Function.comp_def] at h
  refine h.trans ?_
  rw [convexRiemann, Expr.value_sum, List.map_map]
  apply List.sum_le_sum
  intro ab hab
  have hbounds := hp.bounds ab hab
  have h := convexPanel_upper lo hi m (by omega) hlom hmhi
    (Expr.ofRat ab.1) (Expr.ofRat ab.2) κ hx0 hx1
    (by simp only [Expr.value_ofRat]; exact_mod_cast hbounds.1)
    (by simp only [Expr.value_ofRat]; exact_mod_cast hbounds.2.1.le)
    (by simp only [Expr.value_ofRat]; exact_mod_cast hbounds.2.2)
  simpa only [Expr.value_ofRat, Function.comp_def] using h

theorem convexPanel_le_selected (raw : Bool) (lo hi : Nat) (a b : Expr)
    (ρ : Nat → ℝ) :
    (convexPanel lo hi a b).value ρ ≤ (convexPanelSelected raw lo hi a b).value ρ := by
  cases raw
  · change min _ _ ≤ _
    exact min_le_left _ _
  · change min _ _ ≤ _
    exact min_le_right _ _

theorem convexRiemann_le_selected (lo hi : Nat) (panels : List (Rat × Rat))
    (mask : Nat) (ρ : Nat → ℝ) :
    (convexRiemann lo hi panels).value ρ ≤ (convexRiemannSelected lo hi panels mask).value ρ := by
  simp only [convexRiemann, convexRiemannSelected, Expr.value_sum,
    List.mapIdx_eq_zipIdx_map, List.map_map, Function.comp_def]
  let f : Rat × Rat → ℝ := fun ab => (convexPanel lo hi (.ofRat ab.1) (.ofRat ab.2)).value ρ
  have heq : (panels.zipIdx.map (fun abj => f abj.1)).sum = (panels.map f).sum := by
    simpa only [List.map_map, Function.comp_def] using
      congrArg (fun ps : List (Rat × Rat) => (ps.map f).sum) (List.zipIdx_map_fst 0 panels)
  change (panels.map f).sum ≤ _
  rw [← heq]
  apply List.sum_le_sum
  intro abj _
  exact convexPanel_le_selected (mask.testBit abj.2) lo hi (.ofRat abj.1.1) (.ofRat abj.1.2) ρ

theorem convexRiemannSelected_error_bound {ι : Type*} [DecidableEq ι]
    (jset : Finset ι) (η : ι → ℂ) (lo hi m : Nat) (hlo : 3 ≤ lo)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) (hcard : jset.card = m)
    (hη : ∑ j ∈ jset, η j = 0) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (m : ℝ) * (x * (1 - x)))
    (panels : List (Rat × Rat)) (hp : PanelPartition (1 : Rat) 0 panels) (κ : ℝ) (mask : Nat) :
    centeredErrorIntegral jset η m x / (1 - x) ≤
      (convexRiemannSelected lo hi panels mask).value (env x m κ) :=
  (convexRiemann_error_bound jset η lo hi m hlo hlom hmhi hcard hη hx0 hx1 hV panels hp κ).trans
    (convexRiemann_le_selected lo hi panels mask (env x m κ))

end Schmeisser.Certificates.Block

import Schmeisser.Certificates.SplitErrorBridge
import Schmeisser.PanelErrorIntegrals

open scoped BigOperators

namespace Schmeisser.Certificates.Scalar

theorem value_panel (m : Nat) (a b : Expr) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (ha1 : a.value (fun _ => x) ≤ 1) :
    (panel m a b).value (fun _ => x) =
      errorPanelBound m x (a.value (fun _ => x)) (b.value (fun _ => x)) := by
  have hb : 0 ≤ (beta a).value (fun _ => x) := by
    rw [value_beta a hx0.le hx1]
    exact (baseQuadratic_pos hx0.le hx1).le
  simp only [panel, Expr.value_mul, Expr.value_sub, Expr.value, Expr.value_div,
    Expr.value_pow, Expr.value_half_rpow _ _ _ hb,
    value_beta a hx0.le hx1, value_da a hx0.le hx1 ha1]
  simp [errorPanelBound, errorPanelInterpolation, errorPanelTriangle, Expr.value,
    u, eps, max_eq_right (sub_nonneg.mpr hx1.le), mul_assoc]

theorem value_riemann (m : Nat) (panels : List (Rat × Rat))
    (hp : PanelPartition (1 : Rat) 0 panels) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    (riemann m panels).value (fun _ => x) =
      (panels.map (fun ab => errorPanelBound m x (ab.1 : ℝ) (ab.2 : ℝ))).sum := by
  rw [riemann, Expr.value_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro ab hab
  have hbounds := hp.bounds ab hab
  have ha1 : ((ab.1 : Rat) : ℝ) ≤ 1 := by exact_mod_cast hbounds.2.1.le.trans hbounds.2.2
  have h := value_panel m (Expr.ofRat ab.1) (Expr.ofRat ab.2) hx0 hx1
    (by simpa using ha1)
  simpa using h

theorem riemann_error_bound {ι : Type*} [DecidableEq ι]
    (jset : Finset ι) (η : ι → ℂ) (m : ℕ) (hm : 2 ≤ m) (hcard : jset.card = m)
    (hη : ∑ j ∈ jset, η j = 0) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (m : ℝ) * (x * (1 - x)))
    (panels : List (Rat × Rat)) (hp : PanelPartition (1 : Rat) 0 panels) :
    centeredErrorIntegral jset η m x / (1 - x) ≤ (riemann m panels).value (fun _ => x) := by
  have hpR := hp.map (fun q : Rat => (q : ℝ)) (fun a b hab => by exact_mod_cast hab)
  simp only [Rat.cast_one, Rat.cast_zero] at hpR
  have h := centered_error_riemann_bound jset η m hm hcard hx0 hx1 hpR hη hV
  rw [value_riemann m panels hp hx0 hx1]
  simpa [List.map_map, Function.comp_def] using h

end Schmeisser.Certificates.Scalar

import Schmeisser.Certificates.BlockErrorExpressions
import Schmeisser.Certificates.DegreeEnvelope
import Schmeisser.Certificates.RiemannErrorBridge

open scoped BigOperators

namespace Schmeisser.Certificates.Block

theorem value_beta (a : Expr) (m : Nat) (κ : ℝ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    (beta a).value (env x m κ) = baseQuadratic x (a.value (env x m κ)) := by
  simp only [beta, Expr.value_sub, u, Expr.value, env]
  norm_num only
  simp only [ite_true, ite_false]
  have heq : 1 - x * a.value (env x m κ) * (2 - a.value (env x m κ)) =
      baseQuadratic x (a.value (env x m κ)) := by unfold baseQuadratic; ring
  rw [heq, max_eq_right (baseQuadratic_pos hx0 hx1).le]

theorem value_da (a : Expr) (m : Nat) (κ : ℝ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (ha1 : a.value (env x m κ) ≤ 1) :
    (da a).value (env x m κ) = 1 - x * a.value (env x m κ) := by
  simp only [da, Expr.value_sub, u, Expr.value, env]
  norm_num only
  simp only [ite_true, ite_false]
  rw [max_eq_right (by nlinarith : 0 ≤ 1 - x * a.value (env x m κ))]

theorem value_linearFactor (lo hi m : Nat) (x κ : ℝ) :
    (linearFactor lo hi).value (env x m κ) =
      1 + ((hi : ℝ) - lo) ^ 2 / (4 * ((lo : ℝ) + 1) * ((hi : ℝ) + 1)) := by
  simp [linearFactor, Expr.value]

theorem value_quadraticFactor (lo hi m : Nat) (x κ : ℝ) :
    (quadraticFactor lo hi).value (env x m κ) =
      1 + ((hi : ℝ) * ((hi : ℝ) + 1) - (lo : ℝ) * ((lo : ℝ) + 1)) ^ 2 /
        (4 * ((lo : ℝ) * ((lo : ℝ) + 1)) * ((hi : ℝ) * ((hi : ℝ) + 1))) := by
  simp [quadraticFactor, Expr.value]

theorem value_front (lo m : Nat) (a : Expr) (x κ : ℝ) :
    (front lo a).value (env x m κ) =
      40 * (lo : ℝ) / (3 * ((lo : ℝ) - 1) * ((lo : ℝ) + 3) *
        (2 - a.value (env x m κ)) ^ 3 * x ^ 2) := by
  simp [front, Expr.value, u, env]

theorem rawDegreeEnvelope_upper (lo hi m : Nat) (hlo : 1 ≤ lo)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) (a : Expr) (κ : ℝ) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) (ha1 : a.value (env x m κ) ≤ 1) :
    ((m : ℝ) + 1) * (baseQuadratic x (a.value (env x m κ)) ^ ((m : ℝ) / 2) +
      (1 - x * a.value (env x m κ)) ^ m) ≤
      (rawDegreeEnvelope lo hi a).value (env x m κ) := by
  have hb : 0 ≤ (beta a).value (env x m κ) := by
    rw [value_beta a m κ hx0.le hx1]
    exact (baseQuadratic_pos hx0.le hx1).le
  simp only [rawDegreeEnvelope, Expr.value_mul, Expr.value_pow, Expr.value, value_linearFactor,
    Expr.value_half_rpow _ _ _ hb, value_beta a m κ hx0.le hx1,
    value_da a m κ hx0.le hx1 ha1]
  push_cast
  exact linear_degree_endpoint_envelope_nat lo hi m
    (baseQuadratic x (a.value (env x m κ))) (1 - x * a.value (env x m κ)) hlo hlom hmhi
    (baseQuadratic_pos hx0.le hx1) (by nlinarith)

theorem front_degree_antitone {lo m a x : ℝ} (hlo : 1 < lo) (hlom : lo ≤ m)
    (ha : a < 1) (hx : 0 < x) :
    40 * m / (3 * (m - 1) * (m + 3) * (2 - a) ^ 3 * x ^ 2) ≤
      40 * lo / (3 * (lo - 1) * (lo + 3) * (2 - a) ^ 3 * x ^ 2) := by
  have hm : 1 < m := hlo.trans_le hlom
  have hapos : 0 < 2 - a := by linarith
  have hlopos : 0 < lo := by linarith
  have hmpos : 0 < m := by linarith
  have hm1 : 0 < m - 1 := sub_pos.mpr hm
  have hlo1 : 0 < lo - 1 := sub_pos.mpr hlo
  have h₁ : 0 < 3 * (m - 1) * (m + 3) * (2 - a) ^ 3 * x ^ 2 := by positivity
  have h₂ : 0 < 3 * (lo - 1) * (lo + 3) * (2 - a) ^ 3 * x ^ 2 := by positivity
  apply (div_le_div_iff₀ h₁ h₂).2
  have hh : m * ((lo - 1) * (lo + 3)) ≤ lo * ((m - 1) * (m + 3)) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hlom) (show 0 ≤ m * lo + 3 by positivity)]
  have hscale := mul_le_mul_of_nonneg_right hh (show 0 ≤ 120 * (2 - a) ^ 3 * x ^ 2 by positivity)
  nlinarith only [hscale]

theorem splitRaw_error_bound {ι : Type*} [DecidableEq ι]
    (jset : Finset ι) (η : ι → ℂ) (lo hi m : Nat) (hlo : 3 ≤ lo)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) (hcard : jset.card = m)
    (hη : ∑ j ∈ jset, η j = 0) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (m : ℝ) * (x * (1 - x)))
    (a : Expr) (κ : ℝ) (ha0 : 0 ≤ a.value (env x m κ)) (ha1 : a.value (env x m κ) < 1) :
    centeredErrorIntegral jset η m x / (1 - x) ≤ (splitRaw lo hi a).value (env x m κ) := by
  have hactual := centered_error_split_triangle_normalized jset η m (by omega) hcard
    hx0 hx1 ha0 ha1 hη hV
  have hfront := front_degree_antitone (lo := (lo : ℝ)) (m := (m : ℝ))
    (by exact_mod_cast (show 1 < lo by omega)) (by exact_mod_cast hlom) ha1 hx0
  have hraw := rawDegreeEnvelope_upper lo hi m (by omega) hlom hmhi a κ hx0 hx1 ha1.le
  have htail := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hraw (sub_nonneg.mpr ha1.le)) (sub_pos.mpr hx1).le
  have heps : eps.value (env x m κ) = 1 - x := by
    simp [eps, Expr.value, u, env, max_eq_right (sub_nonneg.mpr hx1.le),
      min_eq_right (by linarith : 1 - x ≤ 1)]
  simp only [splitRaw, Expr.value_add, Expr.value_mul, Expr.value_div, Expr.value_sub,
    Expr.value_ofNat, value_front lo m a x κ, heps]
  exact hactual.trans (add_le_add hfront (by simpa only [mul_assoc, Nat.cast_one] using htail))

theorem panel_upper (lo hi m : Nat) (hlo : 2 ≤ lo)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) (a b : Expr) (κ : ℝ) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1)
    (hab : a.value (env x m κ) ≤ b.value (env x m κ))
    (hb1 : b.value (env x m κ) ≤ 1) :
    errorPanelBound m x (a.value (env x m κ)) (b.value (env x m κ)) ≤
      (panel lo hi a b).value (env x m κ) := by
  have hβ : 0 ≤ (beta a).value (env x m κ) := by
    rw [value_beta a m κ hx0.le hx1]
    exact (baseQuadratic_pos hx0.le hx1).le
  have hu : u.value (env x m κ) = x := by simp [u, Expr.value, env]
  have heps : eps.value (env x m κ) = 1 - x := by
    simp [eps, Expr.value, u, env, max_eq_right (sub_nonneg.mpr hx1.le),
      min_eq_right (by linarith : 1 - x ≤ 1)]
  have hlo1 : 1 ≤ lo := by omega
  have hm1 : 1 ≤ m := by omega
  have hhi1 : 1 ≤ hi := by omega
  have hdb : 0 < 1 - x * b.value (env x m κ) := by nlinarith
  have hquad := quadratic_degree_endpoint_envelope_nat lo hi m 1
    (baseQuadratic x (a.value (env x m κ))) hlo1 hlom hmhi (baseQuadratic_pos hx0.le hx1)
  have hraw := rawDegreeEnvelope_upper lo hi m hlo1 hlom hmhi a κ hx0 hx1 (hab.trans hb1)
  simp only [panel, Expr.value_mul, Expr.value_div, Expr.value_sub, Expr.value_pow,
    Expr.value, hu, heps, value_quadraticFactor,
    Expr.value_half_rpow _ _ _ hβ, value_beta a m κ hx0.le hx1,
    errorPanelBound]
  push_cast
  apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hab)
  apply min_le_min
  · have h := mul_le_mul_of_nonneg_left hquad
      (show 0 ≤ (5 / 6 : ℝ) * x * b.value (env x m κ) ^ 2 /
        (1 - x * b.value (env x m κ)) by positivity)
    simpa only [errorPanelInterpolation, Nat.cast_sub hm1, Nat.cast_sub hlo1,
      Nat.cast_sub hhi1, Nat.cast_one, mul_assoc] using h
  · exact div_le_div_of_nonneg_right hraw (sub_nonneg.mpr hx1.le)

theorem riemann_error_bound {ι : Type*} [DecidableEq ι]
    (jset : Finset ι) (η : ι → ℂ) (lo hi m : Nat) (hlo : 2 ≤ lo)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) (hcard : jset.card = m)
    (hη : ∑ j ∈ jset, η j = 0) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (m : ℝ) * (x * (1 - x)))
    (panels : List (Rat × Rat)) (hp : PanelPartition (1 : Rat) 0 panels) (κ : ℝ) :
    centeredErrorIntegral jset η m x / (1 - x) ≤
      (riemann lo hi panels).value (env x m κ) := by
  have hpR := hp.map (fun q : Rat => (q : ℝ)) (fun a b hab => by exact_mod_cast hab)
  simp only [Rat.cast_one, Rat.cast_zero] at hpR
  have h := centered_error_riemann_bound jset η m (by omega) hcard hx0 hx1 hpR hη hV
  simp only [List.map_map, Function.comp_def] at h
  refine h.trans ?_
  rw [riemann, Expr.value_sum, List.map_map]
  apply List.sum_le_sum
  intro ab hab
  have hbounds := hp.bounds ab hab
  have h := panel_upper lo hi m hlo hlom hmhi (Expr.ofRat ab.1) (Expr.ofRat ab.2) κ hx0 hx1
    (by simp only [Expr.value_ofRat]; exact_mod_cast hbounds.2.1.le)
    (by simp only [Expr.value_ofRat]; exact_mod_cast hbounds.2.2)
  simpa only [Expr.value_ofRat, Function.comp_def] using h

end Schmeisser.Certificates.Block

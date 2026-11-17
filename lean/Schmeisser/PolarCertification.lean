import Schmeisser.ScalarIntegrals

namespace Schmeisser

open Set MeasureTheory

theorem polar_integral_scaled_chord {u h H r : ℝ}
    (hu : 0 ≤ u) (hH0 : 0 < H) (hH1 : H ≤ 1) (hh0 : 0 ≤ h) (hhH : h ≤ H)
    (hr : 1 ≤ r) :
    (∫ t in (0 : ℝ)..1, (1 - h + h * (1 + u) * t) ^ r) ≤
      (1 - h / H) + (h / H) * (∫ t in (0 : ℝ)..1, (1 - H + H * (1 + u) * t) ^ r) := by
  have hr0 : 0 ≤ r := by linarith
  have hθ0 : 0 ≤ h / H := div_nonneg hh0 hH0.le
  have hθ1 : h / H ≤ 1 := (div_le_one hH0).mpr hhH
  have hc (v : ℝ) : Continuous (fun t : ℝ ↦ (1 - v + v * (1 + u) * t) ^ r) :=
    (Real.continuous_rpow_const hr0).comp (by fun_prop)
  have hright : Continuous (fun t : ℝ ↦ (1 - h / H) + (h / H) *
      (1 - H + H * (1 + u) * t) ^ r) := continuous_const.add (continuous_const.mul (hc H))
  have hi : (∫ t in (0 : ℝ)..1, (1 - h + h * (1 + u) * t) ^ r) ≤
      ∫ t in (0 : ℝ)..1, (1 - h / H) + (h / H) * (1 - H + H * (1 + u) * t) ^ r := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      ((hc h).intervalIntegrable 0 1) (hright.intervalIntegrable 0 1)
    intro t ht
    have hbase : 0 ≤ 1 - H + H * (1 + u) * t := by
      have hh : 0 ≤ H * (1 + u) * t := mul_nonneg (by positivity) ht.1
      linarith
    have hcv := (convexOn_rpow hr).2 (show (1 : ℝ) ∈ Ici 0 by norm_num)
      (show (1 - H + H * (1 + u) * t) ∈ Ici 0 from hbase)
      (show 0 ≤ 1 - h / H by linarith) hθ0 (show 1 - h / H + h / H = 1 by ring)
    simp only [smul_eq_mul, mul_one, Real.one_rpow] at hcv
    have he : (1 - h / H) + (h / H) * (1 - H + H * (1 + u) * t) =
        1 - h + h * (1 + u) * t := by field_simp; ring
    rw [he] at hcv
    exact hcv
  refine hi.trans_eq ?_
  rw [intervalIntegral.integral_add intervalIntegrable_const
    (((hc H).intervalIntegrable 0 1).const_mul (h / H)),
    intervalIntegral.integral_const_mul]
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_mul]

theorem polar_certification {u h H r : ℝ}
    (hu : 0 ≤ u) (hh : 0 < h) (hH0 : 0 < H) (hH1 : H ≤ 1) (hr : 1 ≤ r)
    (hpolar : 1 ≤ ∫ t in (0 : ℝ)..1, (1 - h + h * (1 + u) * t) ^ r)
    (htest : (∫ t in (0 : ℝ)..1, (1 - H + H * (1 + u) * t) ^ r) < 1) :
    H < h := by
  by_contra hn
  have hle : h ≤ H := le_of_not_gt hn
  have hchord := polar_integral_scaled_chord hu hH0 hH1 hh.le hle hr
  have hstrict := mul_lt_mul_of_pos_left htest (div_pos hh hH0)
  nlinarith

theorem polar_integral_formula {u h r : ℝ} (hu : 0 ≤ u) (hh : 0 < h) (hr : -1 < r) :
    (∫ t in (0 : ℝ)..1, (1 - h + h * (1 + u) * t) ^ r) =
      ((1 + h * u) ^ (r + 1) - (1 - h) ^ (r + 1)) / ((r + 1) * h * (1 + u)) := by
  have hc : h * (1 + u) ≠ 0 := ne_of_gt (by positivity)
  calc
    _ = ∫ t in (0 : ℝ)..1, (h * (1 + u) * t + (1 - h)) ^ r := by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      congr 1
      ring
    _ = (h * (1 + u))⁻¹ *
        ((1 + h * u) ^ (r + 1) - (1 - h) ^ (r + 1)) / (r + 1) := by
      rw [intervalIntegral.integral_comp_mul_add (fun t : ℝ ↦ t ^ r) hc (1 - h)]
      simp only [mul_zero, zero_add, mul_one, smul_eq_mul]
      rw [show h * (1 + u) + (1 - h) = 1 + h * u by ring]
      rw [integral_rpow (Or.inl hr)]
      ring
    _ = _ := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

theorem polar_integral_degree_formula (m : ℕ) {u h : ℝ} (hu : 0 ≤ u) (hh : 0 < h) :
    (∫ t in (0 : ℝ)..1, (1 - h + h * (1 + u) * t) ^ ((m : ℝ) / 2)) =
      2 * ((1 + h * u) ^ (((m : ℝ) + 2) / 2) - (1 - h) ^ (((m : ℝ) + 2) / 2)) /
        (((m : ℝ) + 2) * h * (1 + u)) := by
  have hr0 : 0 ≤ (m : ℝ) / 2 := by positivity
  rw [polar_integral_formula hu hh (by linarith : -1 < (m : ℝ) / 2)]
  rw [show (m : ℝ) / 2 + 1 = ((m : ℝ) + 2) / 2 by ring]
  field_simp
  <;> ring

theorem rpow_three_halves_le_quadratic {x : ℝ} (hx : 0 ≤ x) :
    x ^ (3 / 2 : ℝ) ≤ (x ^ 2 + x) / 2 := by
  have hs : Real.sqrt x ≤ (x + 1) / 2 := by
    have hsq := Real.sq_sqrt hx
    nlinarith [sq_nonneg (Real.sqrt x - 1)]
  have he : x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
    have hh : (3 / 2 : ℝ) = 1 + 1 / 2 := by norm_num
    rw [hh, Real.rpow_add_of_nonneg hx (by norm_num) (by norm_num), Real.rpow_one,
      ← Real.sqrt_eq_rpow]
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_left hs hx]

theorem integral_quadratic (a b c : ℝ) :
    (∫ t in (0 : ℝ)..1, a * t ^ 2 + b * t + c) = a / 3 + b / 2 + c := by
  have h1 : Continuous (fun t : ℝ ↦ a * t ^ 2) := by fun_prop
  have h2 : Continuous (fun t : ℝ ↦ b * t) := by fun_prop
  have h12 : Continuous (fun t : ℝ ↦ a * t ^ 2 + b * t) := by fun_prop
  rw [intervalIntegral.integral_add (h12.intervalIntegrable 0 1) intervalIntegrable_const,
    intervalIntegral.integral_add (h1.intervalIntegrable 0 1) (h2.intervalIntegrable 0 1)]
  simp only [intervalIntegral.integral_const_mul, integral_pow, integral_id,
    intervalIntegral.integral_const, smul_eq_mul]
  rw [intervalIntegral.integral_const_mul b (fun t : ℝ ↦ t), integral_id]
  norm_num
  <;> ring

theorem polar_cubic_quadratic_bound {u h : ℝ} (hu : 0 ≤ u) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) :
    (∫ t in (0 : ℝ)..1, (1 - h + h * (1 + u) * t) ^ (3 / 2 : ℝ)) ≤
      1 - (3 / 4 : ℝ) * h * (1 - u) + h ^ 2 * (u ^ 2 - u + 1) / 6 := by
  let f : ℝ → ℝ := fun t ↦ 1 - h + h * (1 + u) * t
  have hc : Continuous f := by dsimp [f]; fun_prop
  have hp : Continuous (fun t : ℝ ↦ (f t ^ 2 + f t) / 2) := by fun_prop
  have hi : (∫ t in (0 : ℝ)..1, (f t) ^ (3 / 2 : ℝ)) ≤
      ∫ t in (0 : ℝ)..1, (f t ^ 2 + f t) / 2 := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      (((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 3 / 2)).comp hc).intervalIntegrable 0 1)
      (hp.intervalIntegrable 0 1)
    intro t ht
    apply rpow_three_halves_le_quadratic
    dsimp [f]
    have hh : 0 ≤ h * (1 + u) * t := mul_nonneg (by positivity) ht.1
    linarith
  refine hi.trans_eq ?_
  calc
    _ = ∫ t in (0 : ℝ)..1,
        (h ^ 2 * (1 + u) ^ 2 / 2) * t ^ 2 +
          (h * (1 + u) * (3 - 2 * h) / 2) * t + ((1 - h) ^ 2 + (1 - h)) / 2 := by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp [f]
      ring
    _ = _ := by rw [integral_quadratic]; ring

end Schmeisser

import Schmeisser.ErrorBounds

noncomputable section

namespace Schmeisser

open Set MeasureTheory

def centeredErrorIntegrand {ι : Type*} (jset : Finset ι) (η : ι → ℂ)
    (m : ℕ) (u t : ℝ) : ℝ :=
  ‖(∏ j ∈ jset, (((1 - u * t : ℝ) : ℂ) + (t : ℂ) * η j)) -
    ((1 - u * t : ℝ) : ℂ) ^ m‖

theorem continuous_centeredErrorIntegrand {ι : Type*} (jset : Finset ι)
    (η : ι → ℂ) (m : ℕ) (u : ℝ) :
    Continuous (centeredErrorIntegrand jset η m u) := by
  unfold centeredErrorIntegrand
  fun_prop

theorem baseQuadratic_le_front_linear {u t d : ℝ} (hu : 0 ≤ u)
    (ht0 : 0 ≤ t) (htd : t ≤ d) :
    baseQuadratic u t ≤ 1 - ((2 - d) * u) * t := by
  have hh := mul_nonneg (mul_nonneg hu ht0) (sub_nonneg.mpr htd)
  unfold baseQuadratic
  nlinarith

theorem centered_error_front_bound {ι : Type*} [DecidableEq ι]
    (jset : Finset ι) (η : ι → ℂ) (m : ℕ) (hm : 3 ≤ m) (hcard : jset.card = m)
    {u d : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (hd0 : 0 ≤ d) (hd1 : d < 1)
    (hη : ∑ j ∈ jset, η j = 0)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (m : ℝ) * (u * (1 - u))) :
    ((m : ℝ) + 1) * (∫ t in (0 : ℝ)..d, centeredErrorIntegrand jset η m u t) ≤
      40 * (m : ℝ) * (1 - u) /
        (3 * ((m : ℝ) - 1) * ((m : ℝ) + 3) * (2 - d) ^ 3 * u ^ 2) := by
  let r := ((m : ℝ) - 3) / 2
  let c := (2 - d) * u
  let A := (5 * (m : ℝ) / 6) * u * (1 - u)
  have hmR : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have hc : 0 < c := by dsimp [c]; exact mul_pos (by linarith) hu0
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hdc : d ≤ 1 / c := by
    apply (le_div_iff₀ hc).mpr
    have hdd : 0 ≤ d * (2 - d) := mul_nonneg hd0 (by linarith)
    have hdd1 : d * (2 - d) ≤ 1 := by nlinarith [sq_nonneg (1 - d)]
    dsimp [c]
    nlinarith [mul_nonneg (sub_nonneg.mpr hu1.le) hdd]
  have hcont : Continuous (fun t : ℝ ↦ A * (t ^ 2 * (1 - c * t) ^ r)) :=
    continuous_const.mul ((continuous_id.pow 2).mul
      ((Real.continuous_rpow_const hr).comp (by fun_prop)))
  have hi : (∫ t in (0 : ℝ)..d, centeredErrorIntegrand jset η m u t) ≤
      A * (2 / (c ^ 3 * (r + 1) * (r + 2) * (r + 3))) := by
    calc
      _ ≤ ∫ t in (0 : ℝ)..d, A * (t ^ 2 * (1 - c * t) ^ r) := by
        apply intervalIntegral.integral_mono_on hd0
          ((continuous_centeredErrorIntegrand jset η m u).intervalIntegrable 0 d)
          (hcont.intervalIntegrable 0 d)
        intro t ht
        have hb := centered_error_pointwise_majorant jset η m hm hcard hu0.le hu1
          ⟨ht.1, ht.2.trans hd1.le⟩ hη hV
        have hpow := Real.rpow_le_rpow (baseQuadratic_pos (t := t) hu0.le hu1).le
          (baseQuadratic_le_front_linear hu0.le ht.1 ht.2) hr
        exact hb.trans (by
          change A * t ^ 2 * baseQuadratic u t ^ r ≤ A * (t ^ 2 * (1 - c * t) ^ r)
          simpa only [c, mul_assoc] using
            mul_le_mul_of_nonneg_left hpow (mul_nonneg hA (sq_nonneg t)))
      _ = A * (∫ t in (0 : ℝ)..d, t ^ 2 * (1 - c * t) ^ r) := by
        rw [intervalIntegral.integral_const_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left (integral_sq_one_sub_mul_rpow_le hr hc hd0 hdc) hA
  have hfinal := mul_le_mul_of_nonneg_left hi (show 0 ≤ (m : ℝ) + 1 by positivity)
  convert hfinal using 1
  dsimp [A, c, r]
  have hm1 : (m : ℝ) - 1 ≠ 0 := by linarith
  have hmplus : (m : ℝ) + 1 ≠ 0 := by positivity
  have hm3 : (m : ℝ) + 3 ≠ 0 := by positivity
  have hd2 : 2 - d ≠ 0 := by linarith
  rw [show ((m : ℝ) - 3) / 2 + 1 = ((m : ℝ) - 1) / 2 by ring,
    show ((m : ℝ) - 3) / 2 + 2 = ((m : ℝ) + 1) / 2 by ring,
    show ((m : ℝ) - 3) / 2 + 3 = ((m : ℝ) + 3) / 2 by ring]
  field_simp
  <;> ring

theorem centered_error_tail_interpolation {ι : Type*} [DecidableEq ι]
    (jset : Finset ι) (η : ι → ℂ) (m : ℕ) (hm : 3 ≤ m) (hcard : jset.card = m)
    {u d : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hη : ∑ j ∈ jset, η j = 0)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (m : ℝ) * (u * (1 - u))) :
    ((m : ℝ) + 1) * (∫ t in d..1, centeredErrorIntegrand jset η m u t) ≤
      (5 / 6 : ℝ) * ((m : ℝ) + 1) * (m : ℝ) * u * (1 - u) * (1 - d) *
        baseQuadratic u d ^ (((m : ℝ) - 3) / 2) := by
  let r := ((m : ℝ) - 3) / 2
  let A := (5 * (m : ℝ) / 6) * u * (1 - u)
  have hmR : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ baseQuadratic u d ^ r :=
    Real.rpow_nonneg (baseQuadratic_pos hu0.le hu1).le _
  have hi : (∫ t in d..1, centeredErrorIntegrand jset η m u t) ≤
      (1 - d) * (A * baseQuadratic u d ^ r) := by
    calc
      _ ≤ ∫ t in d..1, A * baseQuadratic u d ^ r := by
        apply intervalIntegral.integral_mono_on hd1
          ((continuous_centeredErrorIntegrand jset η m u).intervalIntegrable d 1)
          intervalIntegrable_const
        intro t ht
        have ht0 := hd0.trans ht.1
        have hb := centered_error_pointwise_majorant jset η m hm hcard hu0.le hu1
          ⟨ht0, ht.2⟩ hη hV
        have hpow := Real.rpow_le_rpow (baseQuadratic_pos (t := t) hu0.le hu1).le
          (baseQuadratic_antitone hu0.le hd0 ht.1 ht.2) hr
        refine hb.trans ?_
        change A * t ^ 2 * baseQuadratic u t ^ r ≤ A * baseQuadratic u d ^ r
        calc
          _ ≤ A * t ^ 2 * baseQuadratic u d ^ r :=
            mul_le_mul_of_nonneg_left hpow (mul_nonneg hA (sq_nonneg t))
          _ ≤ _ := by
            have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.2]
            convert mul_le_mul_of_nonneg_left ht2 (mul_nonneg hA hB) using 1 <;> ring
      _ = _ := by simp only [intervalIntegral.integral_const, smul_eq_mul]
  convert mul_le_mul_of_nonneg_left hi (show 0 ≤ (m : ℝ) + 1 by positivity) using 1
  dsimp [A, r]
  ring

theorem centered_error_tail_triangle {ι : Type*}
    (jset : Finset ι) (η : ι → ℂ) (m : ℕ) (hm : 0 < m) (hcard : jset.card = m)
    {u d : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hη : ∑ j ∈ jset, η j = 0)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (m : ℝ) * (u * (1 - u))) :
    ((m : ℝ) + 1) * (∫ t in d..1, centeredErrorIntegrand jset η m u t) ≤
      ((m : ℝ) + 1) * (1 - d) *
        (baseQuadratic u d ^ ((m : ℝ) / 2) + (1 - u * d) ^ m) := by
  have hi : (∫ t in d..1, centeredErrorIntegrand jset η m u t) ≤
      (1 - d) * (baseQuadratic u d ^ ((m : ℝ) / 2) + (1 - u * d) ^ m) := by
    calc
      _ ≤ ∫ t in d..1, baseQuadratic u d ^ ((m : ℝ) / 2) + (1 - u * d) ^ m := by
        apply intervalIntegral.integral_mono_on hd1
          ((continuous_centeredErrorIntegrand jset η m u).intervalIntegrable d 1)
          intervalIntegrable_const
        intro t ht
        have ht0 := hd0.trans ht.1
        have hb := centered_error_pointwise_triangle jset η m hm hcard hu0.le hu1
          ⟨ht0, ht.2⟩ hη hV
        have hpow := Real.rpow_le_rpow (baseQuadratic_pos (t := t) hu0.le hu1).le
          (baseQuadratic_antitone hu0.le hd0 ht.1 ht.2) (by positivity : 0 ≤ (m : ℝ) / 2)
        have hlin0 : 0 ≤ 1 - u * t := by
          nlinarith [mul_nonneg hu0.le (sub_nonneg.mpr ht.2)]
        have hlin : 1 - u * t ≤ 1 - u * d := by nlinarith [ht.1]
        exact hb.trans (add_le_add hpow (pow_le_pow_left₀ hlin0 hlin m))
      _ = _ := by simp only [intervalIntegral.integral_const, smul_eq_mul]
  convert mul_le_mul_of_nonneg_left hi (show 0 ≤ (m : ℝ) + 1 by positivity) using 1 <;> ring

theorem centered_error_split {ι : Type*} (jset : Finset ι) (η : ι → ℂ)
    (m : ℕ) (u d : ℝ) :
    centeredErrorIntegral jset η m u =
      ((m : ℝ) + 1) * (∫ t in (0 : ℝ)..d, centeredErrorIntegrand jset η m u t) +
      ((m : ℝ) + 1) * (∫ t in d..1, centeredErrorIntegrand jset η m u t) := by
  have hc := continuous_centeredErrorIntegrand jset η m u
  rw [← mul_add, intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 d) (hc.intervalIntegrable d 1)]
  rfl

end Schmeisser

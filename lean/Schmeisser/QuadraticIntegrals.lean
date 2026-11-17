import Schmeisser.DecayBounds
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Quadratic moments and their normalized recurrence

All moments in this file are actual real interval integrals. The
recurrence is obtained by differentiating an explicit primitive.
-/

open MeasureTheory Set

namespace Schmeisser

def shiftedQuadratic (c d v t : ℝ) : ℝ := v + d * (t - c) ^ 2

noncomputable def quadraticMoment (m : ℕ) (c d v : ℝ) : ℝ :=
  ((m : ℝ) + 1) * ∫ t : ℝ in 0..1, (shiftedQuadratic c d v t) ^ ((m : ℝ) / 2)

theorem shiftedQuadratic_nonneg (c d v t : ℝ) (hd : 0 ≤ d) (hv : 0 ≤ v) :
    0 ≤ shiftedQuadratic c d v t := by unfold shiftedQuadratic; positivity

theorem shiftedQuadratic_hasDerivAt (c d v t : ℝ) :
    HasDerivAt (shiftedQuadratic c d v) (2 * d * (t - c)) t := by
  unfold shiftedQuadratic
  convert ((((hasDerivAt_id t).sub_const c).pow 2).const_mul d).const_add v using 1 <;>
    norm_num; ring

theorem quadratic_primitive_hasDerivAt (m : ℕ) (hm : 2 ≤ m)
    (c d v t : ℝ) (hd : 0 ≤ d) (hv : 0 ≤ v) :
    HasDerivAt (fun t : ℝ => (t - c) * (shiftedQuadratic c d v t) ^ ((m : ℝ) / 2))
      (((m : ℝ) + 1) * (shiftedQuadratic c d v t) ^ ((m : ℝ) / 2) -
        (m : ℝ) * v * (shiftedQuadratic c d v t) ^ (((m - 2 : ℕ) : ℝ) / 2)) t := by
  have hmr : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hexp : (m : ℝ) / 2 - 1 = ((m - 2 : ℕ) : ℝ) / 2 := by
    rw [Nat.cast_sub hm]
    norm_num
    ring
  have hQ : 0 ≤ shiftedQuadratic c d v t := shiftedQuadratic_nonneg c d v t hd hv
  have hpow : (shiftedQuadratic c d v t) ^ ((m : ℝ) / 2) =
      shiftedQuadratic c d v t *
        (shiftedQuadratic c d v t) ^ (((m - 2 : ℕ) : ℝ) / 2) := by
    have he : (m : ℝ) / 2 = 1 + ((m - 2 : ℕ) : ℝ) / 2 := by linarith
    rw [he, Real.rpow_add_of_nonneg hQ (by norm_num) (by positivity), Real.rpow_one]
  have hp := (shiftedQuadratic_hasDerivAt c d v t).rpow_const
    (Or.inr (show 1 ≤ (m : ℝ) / 2 by linarith))
  convert ((hasDerivAt_id t).sub_const c).mul hp using 1
  · rfl
  · rw [hexp, hpow]
    simp only [id_eq]
    unfold shiftedQuadratic
    ring

theorem quadraticMoment_integrable (m : ℕ) (c d v : ℝ) :
    IntervalIntegrable (fun t : ℝ => (shiftedQuadratic c d v t) ^ ((m : ℝ) / 2)) volume 0 1 := by
  have hQ : Continuous (shiftedQuadratic c d v) := by unfold shiftedQuadratic; fun_prop
  exact ((Real.continuous_rpow_const (by positivity)).comp hQ).intervalIntegrable 0 1

/-- The recurrence, valid even when the quadratic has a zero. -/
theorem quadraticMoment_recurrence (m : ℕ) (hm : 2 ≤ m)
    (c d v : ℝ) (hd : 0 ≤ d) (hv : 0 ≤ v) :
    quadraticMoment m c d v =
      (1 - c) * (shiftedQuadratic c d v 1) ^ ((m : ℝ) / 2) +
        c * (shiftedQuadratic c d v 0) ^ ((m : ℝ) / 2) +
        (m : ℝ) / ((m - 1 : ℕ) : ℝ) * v * quadraticMoment (m - 2) c d v := by
  have hi := quadraticMoment_integrable m c d v
  have hj := quadraticMoment_integrable (m - 2) c d v
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (_ : t ∈ uIcc (0 : ℝ) 1) => quadratic_primitive_hasDerivAt m hm c d v t hd hv)
    ((hi.const_mul ((m : ℝ) + 1)).sub (hj.const_mul ((m : ℝ) * v)))
  rw [intervalIntegral.integral_sub (hi.const_mul _) (hj.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hF
  have hm1 : ((m - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show m - 1 ≠ 0 by omega)
  have hm2 : ((m - 2 : ℕ) : ℝ) + 1 = ((m - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show m - 2 + 1 = m - 1 by omega)
  have htail : (m : ℝ) / ((m - 1 : ℕ) : ℝ) * v * quadraticMoment (m - 2) c d v =
      (m : ℝ) * v * ∫ t : ℝ in 0..1,
        (shiftedQuadratic c d v t) ^ (((m - 2 : ℕ) : ℝ) / 2) := by
    unfold quadraticMoment
    rw [hm2]
    field_simp
  rw [htail]
  unfold quadraticMoment
  linarith

theorem quadraticMoment_zero (c d v : ℝ) : quadraticMoment 0 c d v = 1 := by
  simp [quadraticMoment]

theorem quadraticMoment_two (c d v : ℝ) :
    quadraticMoment 2 c d v = 3 * v + d * (1 - 3 * c + 3 * c ^ 2) := by
  have hpoly : ∀ t : ℝ, shiftedQuadratic c d v t =
      (v + d * c ^ 2) - (2 * d * c) * t + d * t ^ 2 := by intro t; unfold shiftedQuadratic; ring
  have hi0 : IntervalIntegrable (fun _ : ℝ => v + d * c ^ 2) volume 0 1 :=
    continuous_const.intervalIntegrable 0 1
  have hi1 : IntervalIntegrable (fun t : ℝ => (2 * d * c) * t) volume 0 1 :=
    (continuous_const.mul continuous_id).intervalIntegrable 0 1
  have hi2 : IntervalIntegrable (fun t : ℝ => d * t ^ 2) volume 0 1 :=
    (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable 0 1
  simp only [quadraticMoment, Nat.cast_ofNat, show (2 : ℝ) / 2 = 1 by norm_num, Real.rpow_one]
  simp_rw [hpoly]
  rw [intervalIntegral.integral_add (hi0.sub hi1) hi2,
    intervalIntegral.integral_sub hi0 hi1]
  have h1 : (∫ t : ℝ in 0..1, (2 * d * c) * t) = d * c := by
    rw [intervalIntegral.integral_const_mul (2 * d * c) (fun t : ℝ => t), integral_id]
    norm_num
    ring
  have h2 : (∫ t : ℝ in 0..1, d * t ^ 2) = d / 3 := by
    rw [intervalIntegral.integral_const_mul d (fun t : ℝ => t ^ 2), integral_pow]
    norm_num
    ring
  rw [h1, h2]
  norm_num only [intervalIntegral.integral_const, sub_zero, one_smul]
  ring

noncomputable def comparisonDrop (u κ : ℝ) : ℝ := κ * (1 - u) / u
noncomputable def comparisonD (u κ : ℝ) : ℝ := u + comparisonDrop u κ
noncomputable def comparisonB (u κ : ℝ) : ℝ := u + comparisonDrop u κ / 2
noncomputable def comparisonMinimum (u κ : ℝ) : ℝ :=
  1 - (comparisonB u κ) ^ 2 / comparisonD u κ
noncomputable def comparisonTheta (u κ : ℝ) : ℝ :=
  comparisonDrop u κ / (2 * comparisonD u κ)
noncomputable def comparisonQuadratic (u κ t : ℝ) : ℝ :=
  1 - 2 * u * t + u * t ^ 2 - comparisonDrop u κ * t * (1 - t)
noncomputable def comparisonIntegral (m : ℕ) (u κ : ℝ) : ℝ :=
  ((m : ℝ) + 1) * ∫ t : ℝ in 0..1, (comparisonQuadratic u κ t) ^ ((m : ℝ) / 2)
noncomputable def normalizedComparisonIntegral (m : ℕ) (u κ : ℝ) : ℝ :=
  (1 / u - comparisonIntegral m u κ) / (1 - u)

theorem comparisonD_pos {u κ : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) (hκ : 0 ≤ κ) :
    0 < comparisonD u κ := by
  unfold comparisonD comparisonDrop
  exact add_pos_of_pos_of_nonneg hu (div_nonneg (mul_nonneg hκ (sub_nonneg.mpr hu1)) hu.le)

theorem comparisonMinimum_eq (u κ : ℝ) (hD : comparisonD u κ ≠ 0) :
    comparisonMinimum u κ = 1 - u - (comparisonDrop u κ) ^ 2 / (4 * comparisonD u κ) := by
  unfold comparisonMinimum comparisonB comparisonD at *
  field_simp
  ring

theorem comparisonMinimum_bounds {u κ : ℝ} (hu : 0 < u) (hu1 : u ≤ 1)
    (hκ : 0 ≤ κ) (hκ4 : κ / u ≤ 4) :
    0 ≤ comparisonMinimum u κ ∧ comparisonMinimum u κ ≤ 1 - u := by
  have hD := comparisonD_pos hu hu1 hκ
  have hdrop : 0 ≤ comparisonDrop u κ :=
    div_nonneg (mul_nonneg hκ (sub_nonneg.mpr hu1)) hu.le
  have hupp : comparisonDrop u κ ≤ 4 * (1 - u) := by
    unfold comparisonDrop
    convert mul_le_mul_of_nonneg_right hκ4 (sub_nonneg.mpr hu1) using 1; ring
  rw [comparisonMinimum_eq u κ (ne_of_gt hD)]
  refine ⟨?_, sub_le_self _ (by positivity)⟩
  have hsq := mul_le_mul_of_nonneg_right hupp hdrop
  have hdef : comparisonD u κ = u + comparisonDrop u κ := rfl
  have hineq : (comparisonDrop u κ) ^ 2 ≤ (1 - u) * (4 * comparisonD u κ) := by
    nlinarith [mul_nonneg hu.le (sub_nonneg.mpr hu1)]
  have hquot := (div_le_iff₀ (show 0 < 4 * comparisonD u κ by positivity)).2 hineq
  linarith

theorem comparisonMinimum_normalized (u κ : ℝ) (hu : u ≠ 0) (hD : comparisonD u κ ≠ 0) :
    comparisonMinimum u κ =
      (1 - u) * (1 - κ ^ 2 * (1 - u) / (4 * u ^ 2 * comparisonD u κ)) := by
  rw [comparisonMinimum_eq u κ hD]
  unfold comparisonDrop
  field_simp

theorem comparisonTheta_normalized (u κ : ℝ) :
    comparisonTheta u κ = (1 - u) * (κ / (2 * u * comparisonD u κ)) := by
  unfold comparisonTheta comparisonDrop
  ring

theorem comparison_vertex (u κ : ℝ) (hD : comparisonD u κ ≠ 0) :
    comparisonB u κ / comparisonD u κ = 1 - comparisonTheta u κ := by
  unfold comparisonB comparisonTheta comparisonD at *
  field_simp
  ring

theorem comparisonQuadratic_eq_shifted (u κ t : ℝ) (hD : comparisonD u κ ≠ 0) :
    comparisonQuadratic u κ t =
      shiftedQuadratic (comparisonB u κ / comparisonD u κ)
        (comparisonD u κ) (comparisonMinimum u κ) t := by
  unfold comparisonQuadratic shiftedQuadratic comparisonMinimum comparisonB comparisonD at *
  field_simp
  ring

theorem comparisonQuadratic_zero (u κ : ℝ) : comparisonQuadratic u κ 0 = 1 := by
  simp [comparisonQuadratic]

theorem comparisonQuadratic_one (u κ : ℝ) : comparisonQuadratic u κ 1 = 1 - u := by
  unfold comparisonQuadratic
  ring

theorem comparisonIntegral_eq_quadraticMoment (m : ℕ) (u κ : ℝ) (hD : comparisonD u κ ≠ 0) :
    comparisonIntegral m u κ =
      quadraticMoment m (comparisonB u κ / comparisonD u κ)
        (comparisonD u κ) (comparisonMinimum u κ) := by
  unfold comparisonIntegral quadraticMoment
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [comparisonQuadratic_eq_shifted u κ t hD]

theorem comparisonIntegral_recurrence (m : ℕ) (hm : 2 ≤ m) {u κ : ℝ}
    (hu : 0 < u) (hu1 : u ≤ 1) (hκ : 0 ≤ κ) (hκ4 : κ / u ≤ 4) :
    comparisonIntegral m u κ =
      1 - comparisonTheta u κ + comparisonTheta u κ * (1 - u) ^ ((m : ℝ) / 2) +
        (m : ℝ) / ((m - 1 : ℕ) : ℝ) * comparisonMinimum u κ * comparisonIntegral (m - 2) u κ := by
  have hD := comparisonD_pos hu hu1 hκ
  have hv := (comparisonMinimum_bounds hu hu1 hκ hκ4).1
  have hzero : shiftedQuadratic (comparisonB u κ / comparisonD u κ)
      (comparisonD u κ) (comparisonMinimum u κ) 0 = 1 := by
    rw [← comparisonQuadratic_eq_shifted u κ 0 (ne_of_gt hD), comparisonQuadratic_zero]
  have hone : shiftedQuadratic (comparisonB u κ / comparisonD u κ)
      (comparisonD u κ) (comparisonMinimum u κ) 1 = 1 - u := by
    rw [← comparisonQuadratic_eq_shifted u κ 1 (ne_of_gt hD), comparisonQuadratic_one]
  rw [comparisonIntegral_eq_quadraticMoment m u κ (ne_of_gt hD),
    comparisonIntegral_eq_quadraticMoment (m - 2) u κ (ne_of_gt hD),
    quadraticMoment_recurrence m hm _ _ _ hD.le hv, hzero, hone,
    Real.one_rpow, mul_one, comparison_vertex u κ (ne_of_gt hD)]
  ring

private theorem normalize_recurrence_algebra (u A t₀ corr P R : ℝ)
    (hu : u ≠ 0) (he : 1 - u ≠ 0) :
    (1 / u - (1 - (1 - u) * t₀ + (1 - u) * t₀ * P +
      A * ((1 - u) * (1 - u * corr)) * R)) / (1 - u) =
      (1 - A) / u + A * corr + t₀ * (1 - P) +
        A * ((1 - u) * (1 - u * corr)) * ((1 / u - R) / (1 - u)) := by
  field_simp
  ring

/-- The normalized recurrence used by the integer certificate verifier. -/
theorem normalizedComparisonIntegral_recurrence (m : ℕ) (hm : 2 ≤ m) {u κ : ℝ}
    (hu : 0 < u) (hu1 : u < 1) (hκ : 0 ≤ κ) (hκ4 : κ / u ≤ 4) :
    normalizedComparisonIntegral m u κ =
      -1 / (((m - 1 : ℕ) : ℝ) * u) +
        (m : ℝ) / ((m - 1 : ℕ) : ℝ) *
          (κ ^ 2 * (1 - u) / (4 * u ^ 3 * comparisonD u κ)) +
        (κ / (2 * u * comparisonD u κ)) * (1 - (1 - u) ^ ((m : ℝ) / 2)) +
        (m : ℝ) / ((m - 1 : ℕ) : ℝ) * comparisonMinimum u κ *
          normalizedComparisonIntegral (m - 2) u κ := by
  have hD := comparisonD_pos hu hu1.le hκ
  have he : 1 - u ≠ 0 := ne_of_gt (sub_pos.mpr hu1)
  have hm1 : ((m - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show m - 1 ≠ 0 by omega)
  have hmin : comparisonMinimum u κ = (1 - u) *
      (1 - u * (κ ^ 2 * (1 - u) / (4 * u ^ 3 * comparisonD u κ))) := by
    rw [comparisonMinimum_normalized u κ (ne_of_gt hu) (ne_of_gt hD)]
    field_simp
  have hfirst : (1 - (m : ℝ) / ((m - 1 : ℕ) : ℝ)) / u =
      -1 / (((m - 1 : ℕ) : ℝ) * u) := by
    have hrel : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; norm_num
    field_simp
    nlinarith
  unfold normalizedComparisonIntegral
  rw [comparisonIntegral_recurrence m hm hu hu1.le hκ hκ4,
    comparisonTheta_normalized, hmin]
  have h := normalize_recurrence_algebra u ((m : ℝ) / ((m - 1 : ℕ) : ℝ))
    (κ / (2 * u * comparisonD u κ))
    (κ ^ 2 * (1 - u) / (4 * u ^ 3 * comparisonD u κ))
    ((1 - u) ^ ((m : ℝ) / 2)) (comparisonIntegral (m - 2) u κ)
    (ne_of_gt hu) he
  rwa [hfirst] at h

/-- A certified lower bound can be propagated through one recurrence step. -/
theorem normalizedComparisonIntegral_step_lower (m : ℕ) (hm : 2 ≤ m) {u κ L : ℝ}
    (hu : 0 < u) (hu1 : u < 1) (hκ : 0 ≤ κ) (hκ4 : κ / u ≤ 4)
    (hL : L ≤ normalizedComparisonIntegral (m - 2) u κ) :
    -1 / (((m - 1 : ℕ) : ℝ) * u) +
        (m : ℝ) / ((m - 1 : ℕ) : ℝ) *
          (κ ^ 2 * (1 - u) / (4 * u ^ 3 * comparisonD u κ)) +
        (κ / (2 * u * comparisonD u κ)) * (1 - (1 - u) ^ ((m : ℝ) / 2)) +
        (m : ℝ) / ((m - 1 : ℕ) : ℝ) * comparisonMinimum u κ * L ≤
      normalizedComparisonIntegral m u κ := by
  rw [normalizedComparisonIntegral_recurrence m hm hu hu1 hκ hκ4]
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left hL
  exact mul_nonneg (div_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg (m - 1)))
    (comparisonMinimum_bounds hu hu1.le hκ hκ4).1

theorem comparisonIntegral_two (u κ : ℝ) (hD : comparisonD u κ ≠ 0) :
    comparisonIntegral 2 u κ = 1 + 2 * (1 - u) - comparisonDrop u κ / 2 := by
  rw [comparisonIntegral_eq_quadraticMoment 2 u κ hD, quadraticMoment_two]
  unfold comparisonMinimum comparisonB comparisonD at *
  field_simp
  ring

theorem normalizedComparisonIntegral_two {u κ : ℝ} (hu : 0 < u) (hu1 : u < 1) (hκ : 0 ≤ κ) :
    normalizedComparisonIntegral 2 u κ = 1 / u - 2 + κ / (2 * u) := by
  have hD := comparisonD_pos hu hu1.le hκ
  have he : 1 - u ≠ 0 := ne_of_gt (sub_pos.mpr hu1)
  unfold normalizedComparisonIntegral
  rw [comparisonIntegral_two u κ (ne_of_gt hD)]
  unfold comparisonDrop
  field_simp
  ring

noncomputable def auxiliaryMoment (m : ℕ) (α : ℝ) : ℝ := quadraticMoment m 0 α (1 - α)

theorem auxiliaryMoment_zero (α : ℝ) : auxiliaryMoment 0 α = 1 := by
  exact quadraticMoment_zero 0 α (1 - α)

theorem auxiliaryMoment_two (α : ℝ) : auxiliaryMoment 2 α = 1 + 2 * (1 - α) := by
  rw [auxiliaryMoment, quadraticMoment_two]
  ring

theorem auxiliaryMoment_recurrence (m : ℕ) (hm : 2 ≤ m) {α : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    auxiliaryMoment m α = 1 + (m : ℝ) / ((m - 1 : ℕ) : ℝ) *
      (1 - α) * auxiliaryMoment (m - 2) α := by
  have h := quadraticMoment_recurrence m hm 0 α (1 - α) hα (sub_nonneg.mpr hα1)
  simpa [auxiliaryMoment, shiftedQuadratic] using h

theorem auxiliaryMoment_le_trivial (m : ℕ) {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    auxiliaryMoment m α ≤ (m : ℝ) + 1 := by
  have hpoint : ∀ t ∈ Icc (0 : ℝ) 1,
      (shiftedQuadratic 0 α (1 - α) t) ^ ((m : ℝ) / 2) ≤ 1 := by
    intro t ht
    have hq0 := shiftedQuadratic_nonneg 0 α (1 - α) t hα (sub_nonneg.mpr hα1)
    have hq1 : shiftedQuadratic 0 α (1 - α) t ≤ 1 := by
      unfold shiftedQuadratic
      nlinarith [mul_nonneg hα (show 0 ≤ 1 - t ^ 2 by nlinarith [ht.1, ht.2])]
    simpa using Real.rpow_le_rpow hq0 hq1 (show 0 ≤ (m : ℝ) / 2 by positivity)
  have hI : (∫ t : ℝ in 0..1, (shiftedQuadratic 0 α (1 - α) t) ^ ((m : ℝ) / 2)) ≤ 1 := by
    calc
      _ ≤ ∫ _ : ℝ in 0..1, (1 : ℝ) :=
        intervalIntegral.integral_mono_on (by norm_num)
          (quadraticMoment_integrable m 0 α (1 - α)) intervalIntegrable_const hpoint
      _ = 1 := by simp
  unfold auxiliaryMoment quadraticMoment
  simpa using mul_le_mul_of_nonneg_left hI (show 0 ≤ (m : ℝ) + 1 by positivity)

theorem auxiliaryMoment_le_linear (m : ℕ) (hm : 2 ≤ m) {α : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    auxiliaryMoment m α ≤ 1 + (m : ℝ) * (1 - α) := by
  have hmreal : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hpoint : ∀ t ∈ Icc (0 : ℝ) 1,
      (shiftedQuadratic 0 α (1 - α) t) ^ ((m : ℝ) / 2) ≤ α * t ^ m + (1 - α) := by
    intro t ht
    have htpow : (t ^ 2) ^ ((m : ℝ) / 2) = t ^ m := by
      rw [← Real.rpow_natCast t 2, ← Real.rpow_natCast t m, ← Real.rpow_mul ht.1]
      congr 1
      norm_num
      ring
    have hc := (convexOn_rpow (show 1 ≤ (m : ℝ) / 2 by linarith)).2
      (show t ^ 2 ∈ Ici (0 : ℝ) from sq_nonneg t)
      (show (1 : ℝ) ∈ Ici 0 by norm_num) hα (sub_nonneg.mpr hα1)
      (show α + (1 - α) = 1 by ring)
    calc
      _ = (α * t ^ 2 + (1 - α) * 1) ^ ((m : ℝ) / 2) := by
        congr 1
        unfold shiftedQuadratic
        ring
      _ ≤ α * (t ^ 2) ^ ((m : ℝ) / 2) + (1 - α) * (1 : ℝ) ^ ((m : ℝ) / 2) := hc
      _ = _ := by rw [htpow, Real.one_rpow, mul_one]
  have hi : IntervalIntegrable (fun t : ℝ => α * t ^ m) volume 0 1 :=
    (continuous_const.mul (continuous_id.pow m)).intervalIntegrable 0 1
  have hI := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
    (quadraticMoment_integrable m 0 α (1 - α)) (hi.add intervalIntegrable_const) hpoint
  rw [intervalIntegral.integral_add hi intervalIntegrable_const,
    intervalIntegral.integral_const_mul α (fun t : ℝ => t ^ m), integral_pow] at hI
  simp only [one_pow, zero_pow (by omega : m + 1 ≠ 0), sub_zero,
    intervalIntegral.integral_const, one_smul] at hI
  have hmul := mul_le_mul_of_nonneg_left hI (show 0 ≤ (m : ℝ) + 1 by positivity)
  have hm0 : (m : ℝ) + 1 ≠ 0 := by positivity
  have he : ((m : ℝ) + 1) * (α * (1 / ((m : ℝ) + 1)) + (1 - α)) =
      1 + (m : ℝ) * (1 - α) := by field_simp; ring
  rw [he] at hmul
  exact hmul

theorem comparisonIntegral_le_auxiliary (m : ℕ) {u κ : ℝ}
    (hu : 0 < u) (hu1 : u ≤ 1) (hκ : 0 ≤ κ) (hκ4 : κ / u ≤ 4) :
    comparisonIntegral m u κ ≤ auxiliaryMoment m u := by
  have hD := comparisonD_pos hu hu1 hκ
  have hv := (comparisonMinimum_bounds hu hu1 hκ hκ4).1
  have hdrop : 0 ≤ comparisonDrop u κ :=
    div_nonneg (mul_nonneg hκ (sub_nonneg.mpr hu1)) hu.le
  have hcont : Continuous (fun t : ℝ => (comparisonQuadratic u κ t) ^ ((m : ℝ) / 2)) :=
    (Real.continuous_rpow_const (by positivity)).comp (by unfold comparisonQuadratic; fun_prop)
  have hrefcont : Continuous (fun t : ℝ =>
      (shiftedQuadratic 0 u (1 - u) (1 - t)) ^ ((m : ℝ) / 2)) :=
    (Real.continuous_rpow_const (by positivity)).comp (by unfold shiftedQuadratic; fun_prop)
  have hI : (∫ t : ℝ in 0..1, (comparisonQuadratic u κ t) ^ ((m : ℝ) / 2)) ≤
      ∫ t : ℝ in 0..1, (shiftedQuadratic 0 u (1 - u) (1 - t)) ^ ((m : ℝ) / 2) := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      (hcont.intervalIntegrable 0 1) (hrefcont.intervalIntegrable 0 1)
    intro t ht
    have hq0 : 0 ≤ comparisonQuadratic u κ t := by
      rw [comparisonQuadratic_eq_shifted u κ t (ne_of_gt hD)]
      exact shiftedQuadratic_nonneg _ _ _ _ hD.le hv
    have hq1 : comparisonQuadratic u κ t ≤ shiftedQuadratic 0 u (1 - u) (1 - t) := by
      unfold comparisonQuadratic shiftedQuadratic
      nlinarith [mul_nonneg (mul_nonneg hdrop ht.1) (sub_nonneg.mpr ht.2)]
    exact Real.rpow_le_rpow hq0 hq1 (by positivity)
  have he : (∫ t : ℝ in 0..1, (shiftedQuadratic 0 u (1 - u) (1 - t)) ^ ((m : ℝ) / 2)) =
      ∫ t : ℝ in 0..1, (shiftedQuadratic 0 u (1 - u) t) ^ ((m : ℝ) / 2) := by
    simpa using intervalIntegral.integral_comp_sub_left
      (fun t : ℝ => (shiftedQuadratic 0 u (1 - u) t) ^ ((m : ℝ) / 2))
      (a := (0 : ℝ)) (b := (1 : ℝ)) 1
  rw [he] at hI
  exact mul_le_mul_of_nonneg_left hI (by positivity)

theorem auxiliaryMoment_le_two_div (m : ℕ) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    auxiliaryMoment m α ≤ 2 / α := by
  let r : ℝ := (m : ℝ) / 2
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hcont : Continuous (fun t : ℝ => (1 - α + α * t) ^ r) :=
    (Real.continuous_rpow_const hr).comp (by fun_prop)
  have hI : (∫ t : ℝ in 0..1, (shiftedQuadratic 0 α (1 - α) t) ^ r) ≤
      ∫ t : ℝ in 0..1, (1 - α + α * t) ^ r := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      (quadraticMoment_integrable m 0 α (1 - α)) (hcont.intervalIntegrable 0 1)
    intro t ht
    apply Real.rpow_le_rpow (shiftedQuadratic_nonneg 0 α (1 - α) t hα.le (sub_nonneg.mpr hα1)) _ hr
    unfold shiftedQuadratic
    nlinarith [mul_nonneg hα.le (show 0 ≤ t - t ^ 2 by nlinarith [ht.1, ht.2])]
  have hchange : (∫ t : ℝ in 0..1, (1 - α + α * t) ^ r) =
      α⁻¹ * ∫ t : ℝ in (1 - α)..1, t ^ r := by
    have h := intervalIntegral.integral_comp_mul_add (fun t : ℝ => t ^ r)
      (a := (0 : ℝ)) (b := (1 : ℝ)) (ne_of_gt hα) (1 - α)
    have he : α * 1 + (1 - α) = 1 := by ring
    simpa only [mul_zero, zero_add, he, smul_eq_mul, add_comm] using h
  have hmono : (∫ t : ℝ in (1 - α)..1, t ^ r) ≤ ∫ t : ℝ in 0..1, t ^ r := by
    apply intervalIntegral.integral_mono_interval (sub_nonneg.mpr hα1)
      (by linarith : 1 - α ≤ 1) le_rfl
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact Real.rpow_nonneg ht.1.le r
    · exact (Real.continuous_rpow_const hr).intervalIntegrable 0 1
  have heval : (∫ t : ℝ in 0..1, t ^ r) = 1 / (r + 1) := by
    have h := integral_rpow (a := (0 : ℝ)) (b := (1 : ℝ)) (Or.inl (show -1 < r by linarith))
    simpa [Real.zero_rpow (show r + 1 ≠ 0 by linarith)] using h
  have hI' : (∫ t : ℝ in 0..1, (shiftedQuadratic 0 α (1 - α) t) ^ r) ≤
      α⁻¹ * (1 / (r + 1)) := by
    rw [hchange] at hI
    exact hI.trans (mul_le_mul_of_nonneg_left (hmono.trans_eq heval) (inv_nonneg.mpr hα.le))
  have hm0 : (m : ℝ) + 2 ≠ 0 := by positivity
  have hr0 : r + 1 ≠ 0 := by linarith
  have hcoeff : ((m : ℝ) + 1) * (α⁻¹ * (1 / (r + 1))) =
      (((m : ℝ) + 1) / ((m : ℝ) + 2)) * (2 / α) := by
    dsimp [r]
    field_simp
  have hratio : ((m : ℝ) + 1) / ((m : ℝ) + 2) ≤ 1 :=
    (div_le_one (by positivity : 0 < (m : ℝ) + 2)).2 (by linarith)
  calc
    auxiliaryMoment m α ≤ ((m : ℝ) + 1) * (α⁻¹ * (1 / (r + 1))) :=
      mul_le_mul_of_nonneg_left hI' (by positivity)
    _ = (((m : ℝ) + 1) / ((m : ℝ) + 2)) * (2 / α) := hcoeff
    _ ≤ 1 * (2 / α) := mul_le_mul_of_nonneg_right hratio (by positivity)
    _ = 2 / α := one_mul _

theorem auxiliaryMoment_le_three (m : ℕ) (hm : 2 ≤ m) {α : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (heps : 1 - α ≤ 1 / 4) :
    auxiliaryMoment m α ≤ 1 + 3 * (1 - α) := by
  have he0 : 0 ≤ 1 - α := sub_nonneg.mpr hα1
  have hall : ∀ k : ℕ, 2 ≤ k → auxiliaryMoment k α ≤ 1 + 3 * (1 - α) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      by_cases hk2 : k = 2
      · subst k
        rw [auxiliaryMoment_two]
        linarith
      by_cases hk3 : k = 3
      · subst k
        have h1 := auxiliaryMoment_le_trivial 1 hα hα1
        have hrec := auxiliaryMoment_recurrence 3 (by decide) hα hα1
        norm_num at h1 hrec
        have hp := mul_le_mul_of_nonneg_left h1 he0
        nlinarith
      have hk4 : 4 ≤ k := by omega
      have hprev := ih (k - 2) (by omega) (by omega)
      have hk1 : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < k - 1 by omega)
      have hfrac : (k : ℝ) / ((k - 1 : ℕ) : ℝ) ≤ 4 / 3 := by
        apply (div_le_iff₀ hk1).2
        have hcast : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk4
        rw [Nat.cast_sub (by omega : 1 ≤ k)]
        norm_num
        linarith
      have hsq : (1 - α) ^ 2 ≤ (1 - α) / 4 := by
        nlinarith [mul_nonneg he0 (show 0 ≤ 1 / 4 - (1 - α) by linarith)]
      have hscale := mul_le_mul_of_nonneg_right hfrac
        (mul_nonneg he0 (show 0 ≤ 1 + 3 * (1 - α) by positivity))
      calc
        auxiliaryMoment k α = 1 + (k : ℝ) / ((k - 1 : ℕ) : ℝ) *
            (1 - α) * auxiliaryMoment (k - 2) α := auxiliaryMoment_recurrence k hk hα hα1
        _ ≤ 1 + (k : ℝ) / ((k - 1 : ℕ) : ℝ) * (1 - α) * (1 + 3 * (1 - α)) := by
          apply add_le_add le_rfl
          exact mul_le_mul_of_nonneg_left hprev (mul_nonneg (by positivity) he0)
        _ ≤ 1 + 3 * (1 - α) := by nlinarith
  exact hall m hm

private theorem normalizedComparisonIntegral_ge_of_upper (m : ℕ) {u κ C : ℝ}
    (hu : 0 < u) (hu1 : u < 1)
    (hR : comparisonIntegral m u κ ≤ 1 + C * (1 - u)) :
    1 / u - C ≤ normalizedComparisonIntegral m u κ := by
  unfold normalizedComparisonIntegral
  apply (le_div_iff₀ (sub_pos.mpr hu1)).2
  have hinv : (1 / u) * u = 1 := one_div_mul_cancel (ne_of_gt hu)
  nlinarith

theorem normalizedComparisonIntegral_ge_linear (m : ℕ) (hm : 2 ≤ m) {u κ : ℝ}
    (hu : 0 < u) (hu1 : u < 1) (hκ : 0 ≤ κ) (hκ4 : κ / u ≤ 4) :
    1 / u - (m : ℝ) ≤ normalizedComparisonIntegral m u κ := by
  apply normalizedComparisonIntegral_ge_of_upper m hu hu1
  exact (comparisonIntegral_le_auxiliary m hu hu1.le hκ hκ4).trans
    (auxiliaryMoment_le_linear m hm hu.le hu1.le)

theorem normalizedComparisonIntegral_ge_negative (m : ℕ) {u κ : ℝ}
    (hu : 0 < u) (hu1 : u < 1) (hκ : 0 ≤ κ) (hκ4 : κ / u ≤ 4) :
    -1 / (u * (1 - u)) ≤ normalizedComparisonIntegral m u κ := by
  have he : 1 - u ≠ 0 := ne_of_gt (sub_pos.mpr hu1)
  have hR := (comparisonIntegral_le_auxiliary m hu hu1.le hκ hκ4).trans
    (auxiliaryMoment_le_two_div m hu hu1.le)
  unfold normalizedComparisonIntegral
  apply (le_div_iff₀ (sub_pos.mpr hu1)).2
  have hcancel : (-1 / (u * (1 - u))) * (1 - u) = -1 / u := by field_simp
  rw [hcancel]
  have htwo : (2 : ℝ) / u = 1 / u + 1 / u := by ring
  rw [htwo] at hR
  simp only [neg_div] at *
  linarith

theorem normalizedComparisonIntegral_ge_three (m : ℕ) (hm : 2 ≤ m) {u κ : ℝ}
    (hu : 0 < u) (hu1 : u < 1) (hκ : 0 ≤ κ) (hκ4 : κ / u ≤ 4)
    (heps : 1 - u ≤ 1 / 4) :
    1 / u - 3 ≤ normalizedComparisonIntegral m u κ := by
  apply normalizedComparisonIntegral_ge_of_upper m hu hu1
  exact (comparisonIntegral_le_auxiliary m hu hu1.le hκ hκ4).trans
    (auxiliaryMoment_le_three m hm hu.le hu1.le heps)

theorem rpow_half_eq_natPow_sqrt (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    x ^ ((m : ℝ) / 2) = x ^ (m / 2) * (if m % 2 = 0 then 1 else Real.sqrt x) := by
  have hdiv : m = 2 * (m / 2) + m % 2 := by omega
  by_cases heven : m % 2 = 0
  · rw [ite_eq_left heven, mul_one]
    have hm : (m : ℝ) / 2 = ((m / 2 : ℕ) : ℝ) := by
      have hcast : (m : ℝ) = 2 * ((m / 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : m = 2 * (m / 2))
      linarith
    rw [hm, Real.rpow_natCast]
  · rw [ite_eq_right heven]
    have hm : (m : ℝ) / 2 = ((m / 2 : ℕ) : ℝ) + 1 / 2 := by
      have hcast : (m : ℝ) = 2 * ((m / 2 : ℕ) : ℝ) + 1 := by
        exact_mod_cast (by omega : m = 2 * (m / 2) + 1)
      linarith
    rw [hm, Real.rpow_add_of_nonneg hx (by positivity) (by norm_num),
      Real.rpow_natCast, ← Real.sqrt_eq_rpow]

open scoped BigOperators

noncomputable def momentCoefficient (m j : ℕ) : ℝ :=
  ∏ l ∈ Finset.range j, ((m : ℝ) - 2 * l) / ((m : ℝ) - 2 * l - 1)

theorem momentCoefficient_zero (m : ℕ) : momentCoefficient m 0 = 1 := by
  simp [momentCoefficient]

theorem momentCoefficient_succ (m j : ℕ) :
    momentCoefficient m (j + 1) = momentCoefficient m j *
      (((m : ℝ) - 2 * j) / ((m : ℝ) - 2 * j - 1)) := by
  simp only [momentCoefficient, Finset.prod_range_succ]

theorem momentCoefficient_nonneg (m j : ℕ) (hj : 2 * j ≤ m) :
    0 ≤ momentCoefficient m j := by
  unfold momentCoefficient
  apply Finset.prod_nonneg
  intro l hl
  have hlm : 2 * l + 2 ≤ m := by have := Finset.mem_range.mp hl; omega
  have hlm' : (2 : ℝ) * l + 2 ≤ m := by exact_mod_cast hlm
  exact div_nonneg (by linarith) (by linarith)

theorem auxiliaryMoment_at_zero (m : ℕ) : auxiliaryMoment m 0 = (m : ℝ) + 1 := by
  simp [auxiliaryMoment, quadraticMoment, shiftedQuadratic]

theorem auxiliaryMoment_expansion (m k : ℕ) (hk : 2 * k ≤ m) {α : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    auxiliaryMoment m α =
      (∑ j ∈ Finset.range k, momentCoefficient m j * (1 - α) ^ j) +
      momentCoefficient m k * (1 - α) ^ k * auxiliaryMoment (m - 2 * k) α := by
  induction k with
  | zero => simp [momentCoefficient_zero]
  | succ k ih =>
    have hk' : 2 * k ≤ m := by omega
    have hrem : 2 ≤ m - 2 * k := by omega
    have hcast : ((m - 2 * k : ℕ) : ℝ) = (m : ℝ) - 2 * k := by
      rw [Nat.cast_sub hk']; push_cast; rfl
    have hcast1 : ((m - 2 * k - 1 : ℕ) : ℝ) = (m : ℝ) - 2 * k - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ m - 2 * k), hcast]; norm_num
    have hsub : m - 2 * k - 2 = m - 2 * (k + 1) := by omega
    rw [ih hk', auxiliaryMoment_recurrence (m - 2 * k) hrem hα hα1]
    rw [hcast, hcast1, hsub, Finset.sum_range_succ, momentCoefficient_succ, pow_succ]
    ring

theorem momentCoefficient_mass (m k : ℕ) (hk : 2 * k ≤ m) :
    (∑ j ∈ Finset.range k, momentCoefficient m j) +
      momentCoefficient m k * ((m : ℝ) - 2 * k + 1) = (m : ℝ) + 1 := by
  have h := auxiliaryMoment_expansion m k hk (α := 0) (by norm_num) (by norm_num)
  have hcast : ((m - 2 * k : ℕ) : ℝ) = (m : ℝ) - 2 * k := by
    rw [Nat.cast_sub hk]; push_cast; rfl
  simpa [auxiliaryMoment_at_zero, hcast] using h.symm

theorem auxiliaryMoment_truncated (m k : ℕ) (hk : 2 * (k + 1) ≤ m) {α : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    auxiliaryMoment m α ≤
      (∑ j ∈ Finset.range (k + 1), momentCoefficient m j * (1 - α) ^ j) +
      ((m : ℝ) + 1) * (1 - α) ^ (k + 1) := by
  have hr : 0 ≤ 1 - α := sub_nonneg.mpr hα1
  have hc := momentCoefficient_nonneg m (k + 1) hk
  have hF := auxiliaryMoment_le_trivial (m - 2 * (k + 1)) hα hα1
  have hcast : ((m - 2 * (k + 1) : ℕ) : ℝ) = (m : ℝ) - 2 * (k + 1) := by
    rw [Nat.cast_sub hk]; push_cast; ring
  rw [hcast] at hF
  have hmass := momentCoefficient_mass m (k + 1) hk
  have hsum : 0 ≤ ∑ j ∈ Finset.range (k + 1), momentCoefficient m j := by
    apply Finset.sum_nonneg
    intro j hj
    exact momentCoefficient_nonneg m j (by have := Finset.mem_range.mp hj; omega)
  have hrest : momentCoefficient m (k + 1) * ((m : ℝ) - 2 * (k + 1) + 1) ≤ (m : ℝ) + 1 := by
    push_cast at hmass
    linarith
  rw [auxiliaryMoment_expansion m (k + 1) hk hα hα1]
  apply add_le_add le_rfl
  calc
    momentCoefficient m (k + 1) * (1 - α) ^ (k + 1) * auxiliaryMoment (m - 2 * (k + 1)) α
      ≤ momentCoefficient m (k + 1) * (1 - α) ^ (k + 1) * ((m : ℝ) - 2 * (k + 1) + 1) :=
        mul_le_mul_of_nonneg_left hF (mul_nonneg hc (pow_nonneg hr _))
    _ = (momentCoefficient m (k + 1) * ((m : ℝ) - 2 * (k + 1) + 1)) * (1 - α) ^ (k + 1) := by ring
    _ ≤ ((m : ℝ) + 1) * (1 - α) ^ (k + 1) := mul_le_mul_of_nonneg_right hrest (pow_nonneg hr _)

theorem momentCoefficient_le (m j : ℕ) (hm : 0 < m) (hj : 4 * j ≤ m) :
    momentCoefficient m j ≤ 1 + (j : ℝ) / m + 4 * (j : ℝ) ^ 2 / (m : ℝ) ^ 2 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  induction j with
  | zero => simp [momentCoefficient_zero]
  | succ j ih =>
    have hj' : (4 : ℝ) * j + 4 ≤ m := by exact_mod_cast (show 4 * j + 4 ≤ m by omega)
    have hprev := ih (by omega)
    have hd : 0 < (m : ℝ) - 2 * j - 1 := by nlinarith
    have hn : 0 ≤ (m : ℝ) - 2 * j := by linarith
    rw [momentCoefficient_succ]
    calc
      momentCoefficient m j * (((m : ℝ) - 2 * j) / ((m : ℝ) - 2 * j - 1))
        ≤ (1 + (j : ℝ) / m + 4 * (j : ℝ) ^ 2 / (m : ℝ) ^ 2) *
          (((m : ℝ) - 2 * j) / ((m : ℝ) - 2 * j - 1)) :=
          mul_le_mul_of_nonneg_right hprev (div_nonneg hn hd.le)
      _ ≤ 1 + ((j + 1 : ℕ) : ℝ) / m + 4 * ((j + 1 : ℕ) : ℝ) ^ 2 / (m : ℝ) ^ 2 := by
        rw [Nat.cast_add, Nat.cast_one]
        rw [← mul_div_assoc]
        apply (div_le_iff₀ hd).2
        apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hm')).mp
        field_simp [ne_of_gt hm']
        nlinarith [mul_nonneg (show 0 ≤ 5 * (j : ℝ) + 3 by positivity)
          (show 0 ≤ (m : ℝ) - (4 * j + 4) by linarith)]

theorem moment_polynomial_hasSum (m : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun j : ℕ => (1 + (j : ℝ) / m + 4 * (j : ℝ) ^ 2 / (m : ℝ) ^ 2) * r ^ j)
      (1 / (1 - r) + r / ((m : ℝ) * (1 - r) ^ 2) +
        4 * r * (1 + r) / ((m : ℝ) ^ 2 * (1 - r) ^ 3)) := by
  have hn : ‖r‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hr]
  have h0 := hasSum_geometric_of_lt_one hr hr1
  have h1 := (hasSum_coe_mul_geometric_of_norm_lt_one hn).mul_left (1 / (m : ℝ))
  have h2 := (hasSum_sq_mul_geometric_of_norm_lt_one hn).mul_left (4 / (m : ℝ) ^ 2)
  convert (h0.add h1).add h2 using 1
  · funext j
    ring
  · simp only [div_eq_mul_inv, mul_inv_rev]
    ring

theorem auxiliaryMoment_series_bound (m : ℕ) (hm : 4 ≤ m) {α : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) :
    auxiliaryMoment m α ≤ 1 / α + (1 - α) / ((m : ℝ) * α ^ 2) *
      (1 + 8 / ((m : ℝ) * α)) + ((m : ℝ) + 1) * (1 - α) ^ (m / 4 + 1) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hr : 0 ≤ 1 - α := sub_nonneg.mpr hα1
  have hk : 2 * (m / 4 + 1) ≤ m := by omega
  have hcut := auxiliaryMoment_truncated m (m / 4) hk hα.le hα1
  have hsum := moment_polynomial_hasSum m hr (by linarith : 1 - α < 1)
  have hfinite : (∑ j ∈ Finset.range (m / 4 + 1), momentCoefficient m j * (1 - α) ^ j) ≤
      ∑ j ∈ Finset.range (m / 4 + 1),
        (1 + (j : ℝ) / m + 4 * (j : ℝ) ^ 2 / (m : ℝ) ^ 2) * (1 - α) ^ j := by
    apply Finset.sum_le_sum
    intro j hj
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hr j)
    exact momentCoefficient_le m j (by omega) (by have := Finset.mem_range.mp hj; omega)
  have hsumle := sum_le_hasSum (Finset.range (m / 4 + 1))
    (fun j _ => by positivity) hsum
  have he : 1 - (1 - α) = α := by ring
  rw [he] at hsumle
  have hquadratic : 4 * (1 - α) * (1 + (1 - α)) / ((m : ℝ) ^ 2 * α ^ 3) ≤
      (1 - α) / ((m : ℝ) * α ^ 2) * (8 / ((m : ℝ) * α)) := by
    have hden : 0 < (m : ℝ) ^ 2 * α ^ 3 := by positivity
    have heq : (1 - α) / ((m : ℝ) * α ^ 2) * (8 / ((m : ℝ) * α)) =
        8 * (1 - α) / ((m : ℝ) ^ 2 * α ^ 3) := by ring
    rw [heq]
    apply (div_le_div_iff_of_pos_right hden).2
    nlinarith
  linarith

theorem moment_series_tail_bound (m : ℕ) {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hlarge : 90 ≤ (m : ℝ) * α) :
    ((m : ℝ) + 1) * (1 - α) ^ (m / 4 + 1) ≤
      ((1 - α) / ((m : ℝ) * α ^ 2)) / 1000 := by
  have hm90 : (90 : ℝ) ≤ m := by nlinarith [show (0 : ℝ) ≤ m by positivity]
  have hm : (0 : ℝ) < m := by linarith
  have hr : 0 < 1 - α := sub_pos.mpr hα1
  have hfloor : (m : ℝ) / 4 - 1 ≤ ((m / 4 : ℕ) : ℝ) := by
    have hnat : m ≤ 4 * (m / 4) + 3 := by omega
    have hreal : (m : ℝ) ≤ 4 * ((m / 4 : ℕ) : ℝ) + 3 := by exact_mod_cast hnat
    linarith
  have hpow : (1 - α) ^ (m / 4) ≤ Real.exp (-(((m / 4 : ℕ) : ℝ) * α)) := by
    simpa only [Real.rpow_natCast, neg_mul] using one_sub_rpow_le_exp hα1
      (show (0 : ℝ) ≤ ((m / 4 : ℕ) : ℝ) by positivity)
  have hexp : Real.exp (-(((m / 4 : ℕ) : ℝ) * α)) ≤
      3 * Real.exp (-((m : ℝ) * α / 4)) := by
    have h1 : -(((m / 4 : ℕ) : ℝ) * α) ≤ α + -((m : ℝ) * α / 4) := by
      nlinarith [mul_le_mul_of_nonneg_right hfloor hα.le]
    have h2 : Real.exp α ≤ 3 :=
      ((Real.exp_le_exp.mpr hα1.le).trans_lt
        (Real.exp_one_lt_d9.trans (by norm_num))).le
    calc
      Real.exp (-(((m / 4 : ℕ) : ℝ) * α)) ≤ Real.exp (α + -((m : ℝ) * α / 4)) :=
        Real.exp_le_exp.mpr h1
      _ = Real.exp α * Real.exp (-((m : ℝ) * α / 4)) := Real.exp_add _ _
      _ ≤ 3 * Real.exp (-((m : ℝ) * α / 4)) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
  have hcoeff : (0 : ℝ) < (1 - α) / ((m : ℝ) * α ^ 2) := by positivity
  have hrescale : ((1 - α) / ((m : ℝ) * α ^ 2)) *
      (6 * ((m : ℝ) * α) ^ 2 * Real.exp (-((m : ℝ) * α / 4))) =
      6 * (m : ℝ) * (1 - α) * Real.exp (-((m : ℝ) * α / 4)) := by
    field_simp
  have hdecay := moment_tail_decay hlarge
  calc
    ((m : ℝ) + 1) * (1 - α) ^ (m / 4 + 1) =
        ((m : ℝ) + 1) * (1 - α) * (1 - α) ^ (m / 4) := by rw [pow_succ]; ring
    _ ≤ ((m : ℝ) + 1) * (1 - α) * (3 * Real.exp (-((m : ℝ) * α / 4))) :=
      mul_le_mul_of_nonneg_left (hpow.trans hexp) (by positivity)
    _ ≤ 6 * (m : ℝ) * (1 - α) * Real.exp (-((m : ℝ) * α / 4)) := by
      nlinarith [mul_nonneg (show 0 ≤ (m : ℝ) - 1 by linarith)
        (mul_nonneg hr.le ((Real.exp_pos (-((m : ℝ) * α / 4))).le))]
    _ = ((1 - α) / ((m : ℝ) * α ^ 2)) *
        (6 * ((m : ℝ) * α) ^ 2 * Real.exp (-((m : ℝ) * α / 4))) := hrescale.symm
    _ ≤ ((1 - α) / ((m : ℝ) * α ^ 2)) * (1 / 1000) :=
      mul_le_mul_of_nonneg_left hdecay.le hcoeff.le
    _ = ((1 - α) / ((m : ℝ) * α ^ 2)) / 1000 := by ring

theorem auxiliaryMoment_sharp_bound (m : ℕ) {α : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hlarge : 90 ≤ (m : ℝ) * α) :
    auxiliaryMoment m α ≤ 1 / α + (11 / 10 : ℝ) * (1 - α) / ((m : ℝ) * α ^ 2) := by
  have hm90 : (90 : ℝ) ≤ m := by nlinarith [show (0 : ℝ) ≤ m by positivity]
  have hm4 : 4 ≤ m := by exact_mod_cast (show (4 : ℝ) ≤ m by linarith)
  have hseries := auxiliaryMoment_series_bound m hm4 hα hα1
  by_cases he : α = 1
  · subst α
    simpa using hseries
  have hαlt : α < 1 := lt_of_le_of_ne hα1 he
  have htail := moment_series_tail_bound m hα hαlt hlarge
  have hdiv : 8 / ((m : ℝ) * α) ≤ (8 / 90 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hlarge
  have hfactor : 1 + 8 / ((m : ℝ) * α) + (1 / 1000 : ℝ) ≤ 11 / 10 := by linarith
  have hnonneg : 0 ≤ (1 - α) / ((m : ℝ) * α ^ 2) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hfactor hnonneg
  calc
    auxiliaryMoment m α ≤ 1 / α + (1 - α) / ((m : ℝ) * α ^ 2) *
        (1 + 8 / ((m : ℝ) * α)) + ((m : ℝ) + 1) * (1 - α) ^ (m / 4 + 1) := hseries
    _ ≤ 1 / α + (1 - α) / ((m : ℝ) * α ^ 2) *
        (1 + 8 / ((m : ℝ) * α)) + ((1 - α) / ((m : ℝ) * α ^ 2)) / 1000 :=
      add_le_add le_rfl htail
    _ = 1 / α + ((1 - α) / ((m : ℝ) * α ^ 2)) *
        (1 + 8 / ((m : ℝ) * α) + 1 / 1000) := by ring
    _ ≤ 1 / α + ((1 - α) / ((m : ℝ) * α ^ 2)) * (11 / 10) := add_le_add le_rfl hscaled
    _ = 1 / α + (11 / 10 : ℝ) * (1 - α) / ((m : ℝ) * α ^ 2) := by ring

theorem quadraticMoment_split (m : ℕ) {c d v : ℝ}
    (_hc : 0 < c) (hc1 : c ≤ 1) (hd : 0 ≤ d) (hv : 0 ≤ v)
    (hzero : v + d * c ^ 2 = 1) :
    quadraticMoment m c d v ≤ c * auxiliaryMoment m (d * c ^ 2) +
      ((m : ℝ) + 1) * (1 - c) * (shiftedQuadratic c d v 1) ^ ((m : ℝ) / 2) := by
  have hcont : Continuous (fun t : ℝ => (shiftedQuadratic c d v t) ^ ((m : ℝ) / 2)) :=
    (Real.continuous_rpow_const (by positivity)).comp (by unfold shiftedQuadratic; fun_prop)
  have hscale := intervalIntegral.smul_integral_comp_sub_mul
    (fun t : ℝ => (shiftedQuadratic c d v t) ^ ((m : ℝ) / 2))
    (a := (0 : ℝ)) (b := (1 : ℝ)) c c
  simp only [smul_eq_mul, mul_one, sub_self, mul_zero, sub_zero] at hscale
  have htransform : (fun t : ℝ => (shiftedQuadratic c d v (c - c * t)) ^ ((m : ℝ) / 2)) =
      (fun t : ℝ => (shiftedQuadratic 0 (d * c ^ 2) (1 - d * c ^ 2) t) ^ ((m : ℝ) / 2)) := by
    funext t
    congr 1
    unfold shiftedQuadratic
    have hv' : v = 1 - d * c ^ 2 := by linarith
    rw [hv']
    ring
  rw [htransform] at hscale
  have hleft : ((m : ℝ) + 1) *
      (∫ t : ℝ in 0..c, (shiftedQuadratic c d v t) ^ ((m : ℝ) / 2)) =
      c * auxiliaryMoment m (d * c ^ 2) := by
    rw [← hscale]
    unfold auxiliaryMoment quadraticMoment
    ring
  have hright : (∫ t : ℝ in c..1, (shiftedQuadratic c d v t) ^ ((m : ℝ) / 2)) ≤
      (1 - c) * (shiftedQuadratic c d v 1) ^ ((m : ℝ) / 2) := by
    have hmono : (∫ t : ℝ in c..1, (shiftedQuadratic c d v t) ^ ((m : ℝ) / 2)) ≤
        ∫ _t : ℝ in c..1, (shiftedQuadratic c d v 1) ^ ((m : ℝ) / 2) := by
      apply intervalIntegral.integral_mono_on hc1 (hcont.intervalIntegrable c 1)
        (intervalIntegrable_const)
      intro t ht
      apply Real.rpow_le_rpow (shiftedQuadratic_nonneg c d v t hd hv) _ (by positivity)
      have hs : (t - c) ^ 2 ≤ (1 - c) ^ 2 := by nlinarith [ht.1, ht.2]
      unfold shiftedQuadratic
      nlinarith [mul_le_mul_of_nonneg_left hs hd]
    simpa [intervalIntegral.integral_const, smul_eq_mul] using hmono
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (μ := MeasureTheory.volume)
    (hcont.intervalIntegrable 0 c) (hcont.intervalIntegrable c 1)
  unfold quadraticMoment
  rw [← hsplit, mul_add, hleft]
  apply add_le_add le_rfl
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hright
    (show 0 ≤ (m : ℝ) + 1 by positivity)

theorem comparisonIntegral_split (m : ℕ) {u κ : ℝ}
    (hu : 0 < u) (hu1 : u ≤ 1) (hκ : 0 ≤ κ) (hκ4 : κ / u ≤ 4) :
    comparisonIntegral m u κ ≤
      (comparisonB u κ / comparisonD u κ) *
        auxiliaryMoment m ((comparisonB u κ) ^ 2 / comparisonD u κ) +
      ((m : ℝ) + 1) * comparisonTheta u κ * (1 - u) ^ ((m : ℝ) / 2) := by
  have hD := comparisonD_pos hu hu1 hκ
  have hv := (comparisonMinimum_bounds hu hu1 hκ hκ4).1
  have hdrop : 0 ≤ comparisonDrop u κ :=
    div_nonneg (mul_nonneg hκ (sub_nonneg.mpr hu1)) hu.le
  have hb : 0 < comparisonB u κ := by unfold comparisonB; linarith
  have hbd : comparisonB u κ ≤ comparisonD u κ := by
    unfold comparisonB comparisonD
    linarith
  have hzero : comparisonMinimum u κ + comparisonD u κ *
      (comparisonB u κ / comparisonD u κ) ^ 2 = 1 := by
    unfold comparisonMinimum
    field_simp
    ring
  have hα : comparisonD u κ * (comparisonB u κ / comparisonD u κ) ^ 2 =
      (comparisonB u κ) ^ 2 / comparisonD u κ := by
    field_simp
  have h1 : shiftedQuadratic (comparisonB u κ / comparisonD u κ)
      (comparisonD u κ) (comparisonMinimum u κ) 1 = 1 - u := by
    rw [← comparisonQuadratic_eq_shifted u κ 1 (ne_of_gt hD), comparisonQuadratic_one]
  have hc1 : comparisonB u κ / comparisonD u κ ≤ 1 :=
    (div_le_one hD).2 hbd
  have h := quadraticMoment_split m (div_pos hb hD) hc1 hD.le hv hzero
  rw [hα, h1, comparison_vertex u κ (ne_of_gt hD)] at h
  have he : 1 - (1 - comparisonTheta u κ) = comparisonTheta u κ := by ring
  rw [he] at h
  rw [comparisonIntegral_eq_quadraticMoment m u κ (ne_of_gt hD)]
  simpa only [comparison_vertex u κ (ne_of_gt hD)] using h

theorem comparisonIntegral_sharp_bound (m : ℕ) {u κ : ℝ}
    (hu : 0 < u) (hu1 : u ≤ 1) (hκ : 0 ≤ κ) (hκ4 : κ / u ≤ 4)
    (hlarge : 90 ≤ (m : ℝ) * ((comparisonB u κ) ^ 2 / comparisonD u κ)) :
    comparisonIntegral m u κ ≤ 1 / comparisonB u κ +
      (11 / 10 : ℝ) * (comparisonMinimum u κ * comparisonD u κ) /
        ((m : ℝ) * (comparisonB u κ) ^ 3) +
      ((m : ℝ) + 1) * comparisonTheta u κ * (1 - u) ^ ((m : ℝ) / 2) := by
  have hD := comparisonD_pos hu hu1 hκ
  have hv := (comparisonMinimum_bounds hu hu1 hκ hκ4).1
  have hdrop : 0 ≤ comparisonDrop u κ :=
    div_nonneg (mul_nonneg hκ (sub_nonneg.mpr hu1)) hu.le
  have hb : 0 < comparisonB u κ := by unfold comparisonB; linarith
  have hα : 0 < (comparisonB u κ) ^ 2 / comparisonD u κ := by positivity
  have hα1 : (comparisonB u κ) ^ 2 / comparisonD u κ ≤ 1 := by
    unfold comparisonMinimum at hv
    linarith
  have hsharp := auxiliaryMoment_sharp_bound m hα hα1 hlarge
  have hsplit := comparisonIntegral_split m hu hu1 hκ hκ4
  have hscale := mul_le_mul_of_nonneg_left hsharp (div_nonneg hb.le hD.le)
  have heq : (comparisonB u κ / comparisonD u κ) *
      (1 / ((comparisonB u κ) ^ 2 / comparisonD u κ) +
        (11 / 10 : ℝ) * (1 - (comparisonB u κ) ^ 2 / comparisonD u κ) /
          ((m : ℝ) * ((comparisonB u κ) ^ 2 / comparisonD u κ) ^ 2)) =
      1 / comparisonB u κ + (11 / 10 : ℝ) *
        (comparisonMinimum u κ * comparisonD u κ) / ((m : ℝ) * (comparisonB u κ) ^ 3) := by
    unfold comparisonMinimum
    field_simp
  rw [heq] at hscale
  exact hsplit.trans (add_le_add hscale le_rfl)

end Schmeisser


import Schmeisser.NecessaryIntegrals
import Schmeisser.BetaIntegrals

noncomputable section

namespace Schmeisser

open Set MeasureTheory
open scoped BigOperators

def baseQuadratic (u t : ℝ) : ℝ := 1 - 2 * u * t + u * t ^ 2

theorem baseQuadratic_eq (u t : ℝ) :
    baseQuadratic u t = (1 - u * t) ^ 2 + t ^ 2 * (u * (1 - u)) := by
  unfold baseQuadratic
  ring

theorem baseQuadratic_pos {u t : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    0 < baseQuadratic u t := by
  have hh : baseQuadratic u t = (1 - u) + u * (1 - t) ^ 2 := by
    unfold baseQuadratic
    ring
  rw [hh]
  positivity

theorem baseQuadratic_le_linear {u t : ℝ} (hu0 : 0 ≤ u)
    (ht : t ∈ Icc (0 : ℝ) 1) : baseQuadratic u t ≤ 1 - u * t := by
  have hh : 0 ≤ u * t * (1 - t) :=
    mul_nonneg (mul_nonneg hu0 ht.1) (sub_nonneg.mpr ht.2)
  unfold baseQuadratic
  nlinarith

theorem baseQuadratic_antitone {u t d : ℝ} (hu0 : 0 ≤ u)
    (hd0 : 0 ≤ d) (hdt : d ≤ t) (ht1 : t ≤ 1) :
    baseQuadratic u t ≤ baseQuadratic u d := by
  have hh : 0 ≤ u * (t - d) * (2 - t - d) :=
    mul_nonneg (mul_nonneg hu0 (sub_nonneg.mpr hdt)) (by linarith)
  unfold baseQuadratic
  nlinarith

theorem centered_scaled_data {ι : Type*} (jset : Finset ι) (η : ι → ℂ)
    (m : ℕ) (V t : ℝ) (hη : ∑ j ∈ jset, η j = 0)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (m : ℝ) * V) :
    (∑ j ∈ jset, (t : ℂ) * η j) = 0 ∧
      (∑ j ∈ jset, ‖(t : ℂ) * η j‖ ^ 2) ≤ (m : ℝ) * (t ^ 2 * V) := by
  constructor
  · rw [← Finset.mul_sum, hη, mul_zero]
  · have he : (∑ j ∈ jset, ‖(t : ℂ) * η j‖ ^ 2) =
        t ^ 2 * (∑ j ∈ jset, ‖η j‖ ^ 2) := by
      simp only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
        Finset.mul_sum]
    rw [he]
    convert mul_le_mul_of_nonneg_left hV (sq_nonneg t) using 1 <;> ring

theorem centered_error_pointwise_interpolation {ι : Type*} [DecidableEq ι]
    (jset : Finset ι) (η : ι → ℂ) (m : ℕ) (hm : 2 ≤ m) (hcard : jset.card = m)
    {u t : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hη : ∑ j ∈ jset, η j = 0)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (m : ℝ) * (u * (1 - u))) :
    ‖(∏ j ∈ jset, (((1 - u * t : ℝ) : ℂ) + (t : ℂ) * η j)) -
        ((1 - u * t : ℝ) : ℂ) ^ m‖ ≤
      (5 * (m : ℝ) / 6) * (t ^ 2 * (u * (1 - u)) / (1 - u * t)) *
        baseQuadratic u t ^ (((m - 1 : ℕ) : ℝ) / 2) := by
  have hd : 0 < 1 - u * t := by nlinarith [mul_nonneg hu0 (sub_nonneg.mpr ht.2)]
  obtain ⟨hsum, hsq⟩ := centered_scaled_data jset η m (u * (1 - u)) t hη hV
  have hb := centred_product_interpolation jset m hm hcard
    ((1 - u * t : ℝ) : ℂ) (by exact_mod_cast hd.ne')
    (fun j ↦ (t : ℂ) * η j) (t ^ 2 * (u * (1 - u)))
    (by positivity) hsum hsq
  simpa only [Complex.norm_real, Real.norm_of_nonneg hd.le, ← baseQuadratic_eq] using hb

theorem centered_error_pointwise_majorant {ι : Type*} [DecidableEq ι]
    (jset : Finset ι) (η : ι → ℂ) (m : ℕ) (hm : 3 ≤ m) (hcard : jset.card = m)
    {u t : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hη : ∑ j ∈ jset, η j = 0)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (m : ℝ) * (u * (1 - u))) :
    ‖(∏ j ∈ jset, (((1 - u * t : ℝ) : ℂ) + (t : ℂ) * η j)) -
        ((1 - u * t : ℝ) : ℂ) ^ m‖ ≤
      (5 * (m : ℝ) / 6) * u * (1 - u) * t ^ 2 *
        baseQuadratic u t ^ (((m : ℝ) - 3) / 2) := by
  have hd : 0 < 1 - u * t := by nlinarith [mul_nonneg hu0 (sub_nonneg.mpr ht.2)]
  have hB := baseQuadratic_pos (t := t) hu0 hu1
  have hBd := baseQuadratic_le_linear hu0 ht
  have hexp : (((m - 1 : ℕ) : ℝ) / 2) = ((m : ℝ) - 3) / 2 + 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ m)]
    push_cast
    ring
  have hpower : baseQuadratic u t ^ (((m - 1 : ℕ) : ℝ) / 2) =
      baseQuadratic u t ^ (((m : ℝ) - 3) / 2) * baseQuadratic u t := by
    rw [hexp, Real.rpow_add hB, Real.rpow_one]
  have hh := centered_error_pointwise_interpolation jset η m (by omega) hcard hu0 hu1 ht hη hV
  rw [hpower] at hh
  refine hh.trans ?_
  have hratio : baseQuadratic u t / (1 - u * t) ≤ 1 :=
    (div_le_one hd).mpr hBd
  have hn : 0 ≤ (5 * (m : ℝ) / 6) * u * (1 - u) * t ^ 2 *
      baseQuadratic u t ^ (((m : ℝ) - 3) / 2) := by positivity
  convert mul_le_mul_of_nonneg_left hratio hn using 1 <;> ring

theorem centered_error_pointwise_triangle {ι : Type*}
    (jset : Finset ι) (η : ι → ℂ) (m : ℕ) (hm : 0 < m) (hcard : jset.card = m)
    {u t : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hη : ∑ j ∈ jset, η j = 0)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (m : ℝ) * (u * (1 - u))) :
    ‖(∏ j ∈ jset, (((1 - u * t : ℝ) : ℂ) + (t : ℂ) * η j)) -
        ((1 - u * t : ℝ) : ℂ) ^ m‖ ≤
      baseQuadratic u t ^ ((m : ℝ) / 2) + (1 - u * t) ^ m := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hd : 0 < 1 - u * t := by nlinarith [mul_nonneg hu0 (sub_nonneg.mpr ht.2)]
  have hsq := sum_norm_sq_centered jset ((1 - u * t : ℝ) : ℂ) η t hη
  simp only [Complex.real_smul, Complex.norm_real, Real.norm_of_nonneg hd.le, hcard] at hsq
  have hmean : (∑ j ∈ jset, ‖((1 - u * t : ℝ) : ℂ) + (t : ℂ) * η j‖ ^ 2) /
      (m : ℝ) ≤ baseQuadratic u t := by
    rw [div_le_iff₀ hm0, hsq, baseQuadratic_eq]
    have hmul := mul_le_mul_of_nonneg_left hV (sq_nonneg t)
    nlinarith
  have hprod := norm_prod_le_rpow_mean_sq jset
    (fun j ↦ ((1 - u * t : ℝ) : ℂ) + (t : ℂ) * η j)
  rw [hcard] at hprod
  have hp := hprod.trans (Real.rpow_le_rpow (by positivity) hmean (by positivity))
  have hnorm : ‖((1 - u * t : ℝ) : ℂ) ^ m‖ = (1 - u * t) ^ m := by
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hd.le]
  exact (norm_sub_le _ _).trans (by rw [hnorm]; exact add_le_add hp le_rfl)

end Schmeisser

import Schmeisser.ErrorIntegrals

open scoped BigOperators
open MeasureTheory Set

namespace Schmeisser

theorem centered_error_front_normalized {ι : Type*} [DecidableEq ι]
    (jset : Finset ι) (η : ι → ℂ) (m : ℕ) (hm : 3 ≤ m) (hcard : jset.card = m)
    {u d : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (hd0 : 0 ≤ d) (hd1 : d < 1)
    (hη : ∑ j ∈ jset, η j = 0)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (m : ℝ) * (u * (1 - u))) :
    (((m : ℝ) + 1) * (∫ t in (0 : ℝ)..d, centeredErrorIntegrand jset η m u t)) /
        (1 - u) ≤
      40 * (m : ℝ) / (3 * ((m : ℝ) - 1) * ((m : ℝ) + 3) * (2 - d) ^ 3 * u ^ 2) := by
  have heps : 0 < 1 - u := by linarith
  have h := div_le_div_of_nonneg_right
    (centered_error_front_bound jset η m hm hcard hu0 hu1 hd0 hd1 hη hV) heps.le
  convert h using 1
  field_simp

theorem centered_error_split_triangle_normalized {ι : Type*} [DecidableEq ι]
    (jset : Finset ι) (η : ι → ℂ) (m : ℕ) (hm : 3 ≤ m) (hcard : jset.card = m)
    {u d : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (hd0 : 0 ≤ d) (hd1 : d < 1)
    (hη : ∑ j ∈ jset, η j = 0)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (m : ℝ) * (u * (1 - u))) :
    centeredErrorIntegral jset η m u / (1 - u) ≤
      40 * (m : ℝ) / (3 * ((m : ℝ) - 1) * ((m : ℝ) + 3) * (2 - d) ^ 3 * u ^ 2) +
      (1 - d) * ((m : ℝ) + 1) *
        (baseQuadratic u d ^ ((m : ℝ) / 2) + (1 - u * d) ^ m) / (1 - u) := by
  have heps : 0 < 1 - u := by linarith
  rw [centered_error_split jset η m u d, add_div]
  apply add_le_add (centered_error_front_normalized jset η m hm hcard hu0 hu1 hd0 hd1 hη hV)
  have h := div_le_div_of_nonneg_right
    (centered_error_tail_triangle jset η m (by omega) hcard hu0 hu1 hd0 hd1.le hη hV) heps.le
  convert h using 1
  ring

theorem centered_error_split_interpolation_normalized {ι : Type*} [DecidableEq ι]
    (jset : Finset ι) (η : ι → ℂ) (m : ℕ) (hm : 3 ≤ m) (hcard : jset.card = m)
    {u d : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (hd0 : 0 ≤ d) (hd1 : d < 1)
    (hη : ∑ j ∈ jset, η j = 0)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (m : ℝ) * (u * (1 - u))) :
    centeredErrorIntegral jset η m u / (1 - u) ≤
      40 * (m : ℝ) / (3 * ((m : ℝ) - 1) * ((m : ℝ) + 3) * (2 - d) ^ 3 * u ^ 2) +
      (5 / 6 : ℝ) * (1 - d) * u * (m : ℝ) * ((m : ℝ) + 1) *
        baseQuadratic u d ^ (((m : ℝ) - 3) / 2) := by
  have heps : 0 < 1 - u := by linarith
  rw [centered_error_split jset η m u d, add_div]
  apply add_le_add (centered_error_front_normalized jset η m hm hcard hu0 hu1 hd0 hd1 hη hV)
  have h := div_le_div_of_nonneg_right
    (centered_error_tail_interpolation jset η m hm hcard hu0 hu1 hd0 hd1.le hη hV) heps.le
  convert h using 1
  field_simp

end Schmeisser

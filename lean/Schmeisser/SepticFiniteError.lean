import Schmeisser.SexticFiniteError
import Schmeisser.Certificates.CoefficientCertificates

namespace Schmeisser

def septicCoefficientTable : Certificates.CoefficientTable where
  scale := 40
  normalizedNewton := [1, 0, 3 / 5, 2 / 5, 12 / 25, 12 / 25, 62 / 125]
  upper := [0, 0, 8, 9, 18, 26, 40]

theorem septicCoefficientTable_checked : septicCoefficientTable.check 6 = true := by
  decide +kernel

noncomputable def septicErrorBound (u : ℝ) : ℝ :=
  let e := 1 - u
  u / 5 * (1 + 3 * e + 6 * e ^ 2 + 10 * e ^ 3 + 15 * e ^ 4) +
    (9 / 20 : ℝ) * u ^ 2 * e * (1 + 5 * e + 15 * e ^ 2) + u ^ 3 * e ^ 2 +
    Real.sqrt e * (5 * u / 8 + 2 / 5) *
      ((9 / 40 : ℝ) * u * (1 + 4 * e + 10 * e ^ 2 + 20 * e ^ 3) +
        (13 / 20 : ℝ) * u ^ 2 * e * (1 + 6 * e))

theorem septic_finite_error_bound {ι : Type*} (jset : Finset ι) (η : ι → ℂ)
    (hcard : jset.card = 6) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (hη : ∑ j ∈ jset, η j = 0)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (6 : ℝ) * (u * (1 - u))) :
    centeredErrorIntegral jset η 6 u / (1 - u) ≤ septicErrorBound u := by
  classical
  have heps : 0 < 1 - u := by linarith
  let c : ℕ → ℝ := fun k => (septicCoefficientTable.upperRat k : ℝ) * ((6 : ℕ).choose k : ℝ)
  have hc (k : ℕ) (hk : k ∈ Finset.Ico 2 (6 + 1)) :
      ‖(centredGeneratingPolynomial jset η).coeff k‖ ≤
        c k * (u * (1 - u)) ^ ((k : ℝ) / 2) := by
    exact septicCoefficientTable.coeff_norm_bound 6 septicCoefficientTable_checked
      jset η (u * (1 - u)) hcard (by positivity) hη hV k
      (Finset.mem_Ico.mp hk).1 (by have := (Finset.mem_Ico.mp hk).2; omega)
  have hE := centeredErrorIntegral_finite_bound jset η 6 (by norm_num)
    hcard hη hu0 hu1 c hc
  have hset : Finset.Ico 2 (6 + 1) = ({2, 3, 4, 5, 6} : Finset ℕ) := by decide
  rw [hset] at hE
  norm_num [c, septicCoefficientTable, Certificates.CoefficientTable.upperRat,
    Certificates.CoefficientTable.numerator, Finset.sum_insert, Finset.sum_singleton,
    Nat.choose, finiteBetaPolynomial, Finset.sum_range_succ, ← Real.sqrt_eq_rpow] at hE
  rw [rpow_three_halves_eq_mul_sqrt hu0.le, rpow_five_halves_eq_mul_sqrt hu0.le,
    rpow_three_halves_eq_mul_sqrt heps.le] at hE
  have hE' : centeredErrorIntegral jset η 6 u / (1 - u) ≤
      u / 5 * (1 + 3 * (1 - u) + 6 * (1 - u) ^ 2 + 10 * (1 - u) ^ 3 +
        15 * (1 - u) ^ 4) +
      (9 / 20 : ℝ) * u ^ 2 * (1 - u) * (1 + 5 * (1 - u) + 15 * (1 - u) ^ 2) +
      u ^ 3 * (1 - u) ^ 2 +
      Real.sqrt (1 - u) * Real.sqrt u *
        ((9 / 40 : ℝ) * u * (1 + 4 * (1 - u) + 10 * (1 - u) ^ 2 + 20 * (1 - u) ^ 3) +
          (13 / 20 : ℝ) * u ^ 2 * (1 - u) * (1 + 6 * (1 - u))) := by
    convert hE using 1
    ring
  have hs : Real.sqrt u ≤ 5 * u / 8 + 2 / 5 := by
    nlinarith [Real.sq_sqrt hu0.le, sq_nonneg (Real.sqrt u - 4 / 5)]
  have hb : 0 ≤ (9 / 40 : ℝ) * u *
      (1 + 4 * (1 - u) + 10 * (1 - u) ^ 2 + 20 * (1 - u) ^ 3) +
        (13 / 20 : ℝ) * u ^ 2 * (1 - u) * (1 + 6 * (1 - u)) := by positivity
  unfold septicErrorBound
  refine hE'.trans (add_le_add le_rfl ?_)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg _)) hb

end Schmeisser

import Schmeisser.Geometry
import Schmeisser.CentredProduct

namespace Schmeisser

open scoped BigOperators ComplexConjugate

theorem affine_norm_sq (A B q : ℂ) :
    ‖A + B * q‖ ^ 2 = ‖A‖ ^ 2 + ‖B‖ ^ 2 * ‖q‖ ^ 2 +
      2 * ((conj A * B) * q).re := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

theorem affine_moment_identity {ι : Type*} (t : Finset ι)
    (q : ι → ℂ) (μ A B : ℂ) (m s : ℝ)
    (hcard : (t.card : ℝ) = m)
    (hmean : ∑ j ∈ t, q j = (m : ℂ) * μ)
    (hnorm : ∑ j ∈ t, ‖q j‖ ^ 2 = m * s) :
    ∑ j ∈ t, ‖A + B * q j‖ ^ 2 =
      m * (‖A + B * μ‖ ^ 2 + ‖B‖ ^ 2 * (s - ‖μ‖ ^ 2)) := by
  have hlin : (∑ j ∈ t, ((conj A * B) * q j).re) =
      m * ((conj A * B) * μ).re := by
    rw [← Complex.re_sum, ← Finset.mul_sum, hmean]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  calc
    (∑ j ∈ t, ‖A + B * q j‖ ^ 2) =
        ∑ j ∈ t, (‖A‖ ^ 2 + ‖B‖ ^ 2 * ‖q j‖ ^ 2 +
          2 * ((conj A * B) * q j).re) := by
      apply Finset.sum_congr rfl
      intro j _
      exact affine_norm_sq A B (q j)
    _ = m * ‖A‖ ^ 2 + ‖B‖ ^ 2 * (m * s) +
        2 * (m * ((conj A * B) * μ).re) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
        ← Finset.mul_sum, hcard, hnorm, hlin]
    _ = _ := by
      rw [affine_norm_sq]
      ring

theorem sum_centered_eq_zero {ι : Type*} (t : Finset ι)
    (q : ι → ℂ) (μ : ℂ) (m : ℝ)
    (hcard : (t.card : ℝ) = m)
    (hmean : ∑ j ∈ t, q j = (m : ℂ) * μ) :
    ∑ j ∈ t, (q j - μ) = 0 := by
  have hcardC : (t.card : ℂ) = (m : ℂ) := by exact_mod_cast hcard
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hmean, hcardC,
    sub_self]

theorem centered_second_moment {ι : Type*} (t : Finset ι)
    (q : ι → ℂ) (μ : ℂ) (m s : ℝ)
    (hcard : (t.card : ℝ) = m)
    (hmean : ∑ j ∈ t, q j = (m : ℂ) * μ)
    (hnorm : ∑ j ∈ t, ‖q j‖ ^ 2 = m * s) :
    ∑ j ∈ t, ‖q j - μ‖ ^ 2 = m * (s - ‖μ‖ ^ 2) := by
  simpa [neg_add_eq_sub] using affine_moment_identity t q μ (-μ) 1 m s hcard hmean hnorm

theorem scaled_centered_sum_eq_zero {ι : Type*} (t : Finset ι)
    (q : ι → ℂ) (μ c : ℂ) (m : ℝ)
    (hcard : (t.card : ℝ) = m)
    (hmean : ∑ j ∈ t, q j = (m : ℂ) * μ) :
    ∑ j ∈ t, c * (q j - μ) = 0 := by
  rw [← Finset.mul_sum, sum_centered_eq_zero t q μ m hcard hmean, mul_zero]

theorem scaled_centered_second_moment {ι : Type*} (t : Finset ι)
    (q : ι → ℂ) (μ c : ℂ) (m s : ℝ)
    (hcard : (t.card : ℝ) = m)
    (hmean : ∑ j ∈ t, q j = (m : ℂ) * μ)
    (hnorm : ∑ j ∈ t, ‖q j‖ ^ 2 = m * s) :
    ∑ j ∈ t, ‖c * (q j - μ)‖ ^ 2 = ‖c‖ ^ 2 * m * (s - ‖μ‖ ^ 2) := by
  simp only [norm_mul, mul_pow, ← Finset.mul_sum,
    centered_second_moment t q μ m s hcard hmean hnorm]
  ring

theorem reciprocal_centering_second_moment_bound {ι : Type*} (t : Finset ι)
    (q : ι → ℂ) (μ : ℂ) (m s σ : ℝ)
    (hm : 0 ≤ m) (hσ : σ ≠ 0) (hsσ : s ≤ σ)
    (hcard : (t.card : ℝ) = m)
    (hmean : ∑ j ∈ t, q j = (m : ℂ) * μ)
    (hnorm : ∑ j ∈ t, ‖q j‖ ^ 2 = m * s) :
    ∑ j ∈ t, ‖(-conj μ / (σ : ℂ)) * (q j - μ)‖ ^ 2 ≤
      m * (‖μ‖ ^ 2 / σ) * (1 - ‖μ‖ ^ 2 / σ) := by
  have hc : ‖-conj μ / (σ : ℂ)‖ ^ 2 = ‖μ‖ ^ 2 / σ ^ 2 := by
    simp [div_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  calc
    (∑ j ∈ t, ‖(-conj μ / (σ : ℂ)) * (q j - μ)‖ ^ 2) =
        ‖-conj μ / (σ : ℂ)‖ ^ 2 * m * (s - ‖μ‖ ^ 2) :=
      scaled_centered_second_moment t q μ _ m s hcard hmean hnorm
    _ ≤ ‖-conj μ / (σ : ℂ)‖ ^ 2 * m * (σ - ‖μ‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_right hsσ _) (mul_nonneg (sq_nonneg _) hm)
    _ = _ := by
      rw [hc]
      field_simp

theorem reciprocal_centering_factor_identity (a σ t : ℝ) (μ q : ℂ) :
    1 + (((a : ℂ) - conj μ / (σ : ℂ)) - (a : ℂ)) * (t : ℂ) * q =
      ((1 - (‖μ‖ ^ 2 / σ) * t : ℝ) : ℂ) +
        (t : ℂ) * ((-conj μ / (σ : ℂ)) * (q - μ)) := by
  have hn : ((‖μ‖ ^ 2 : ℝ) : ℂ) = conj μ * μ := by
    rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
  simp only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_div]
  rw [hn]
  ring

theorem norm_affine_product_le {ι : Type*} (t : Finset ι)
    (q : ι → ℂ) (μ A B : ℂ) (m s : ℝ) (hm : 0 < m)
    (hcard : (t.card : ℝ) = m)
    (hmean : ∑ j ∈ t, q j = (m : ℂ) * μ)
    (hnorm : ∑ j ∈ t, ‖q j‖ ^ 2 = m * s) :
    ‖∏ j ∈ t, (A + B * q j)‖ ≤
      (‖A + B * μ‖ ^ 2 + ‖B‖ ^ 2 * (s - ‖μ‖ ^ 2)) ^ (m / 2) := by
  have h := norm_prod_le_rpow_mean_sq t (fun j ↦ A + B * q j)
  rw [hcard, affine_moment_identity t q μ A B m s hcard hmean hnorm,
    mul_div_cancel_left₀ _ hm.ne'] at h
  exact h

end Schmeisser

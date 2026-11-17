import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

/-!
# Geometric reductions for Schmeisser's conjecture

The diameter-disk covering uses only the defining property of the real
convex hull. It therefore holds for arbitrary sets in real inner product
spaces, without a finiteness or compactness assumption.
-/

open scoped BigOperators

namespace Schmeisser

section RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The closed ball with diameter from the origin to `a`. -/
def diameterBall (a : E) : Set E :=
  {z | ‖z - (1 / 2 : ℝ) • a‖ ≤ ‖a‖ / 2}

theorem mem_diameterBall_iff (z a : E) :
    z ∈ diameterBall a ↔ ‖z‖ ^ 2 ≤ inner ℝ z a := by
  have hhalf : ‖(1 / 2 : ℝ) • a‖ = ‖a‖ / 2 := by
    rw [norm_smul, Real.norm_eq_abs]
    norm_num
    ring
  change ‖z - (1 / 2 : ℝ) • a‖ ≤ ‖a‖ / 2 ↔ _
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ ‖a‖ / 2)]
  rw [norm_sub_sq_real, real_inner_smul_right, hhalf]
  constructor <;> intro h <;> nlinarith

/-- A point of a convex hull has a generating point with at least its
own value under the corresponding real inner-product functional. -/
theorem exists_inner_ge_of_mem_convexHull {s : Set E} {z : E}
    (hz : z ∈ convexHull ℝ s) :
    ∃ a ∈ s, ‖z‖ ^ 2 ≤ inner ℝ z a := by
  by_contra h
  push Not at h
  have hs : s ⊆ {a : E | inner ℝ z a < ‖z‖ ^ 2} := h
  have hc : Convex ℝ {a : E | inner ℝ z a < ‖z‖ ^ 2} :=
    (convex_Iio (𝕜 := ℝ) (‖z‖ ^ 2)).linear_preimage (innerₗ E z)
  have hh : inner ℝ z z < ‖z‖ ^ 2 := convexHull_min hs hc hz
  rw [real_inner_self_eq_norm_sq] at hh
  exact (lt_irrefl _) hh

/-- Diameter balls centred at half the generating points cover the
real convex hull. -/
theorem convexHull_covered_by_diameterBalls {s : Set E} {z : E}
    (hz : z ∈ convexHull ℝ s) :
    ∃ a ∈ s, z ∈ diameterBall a := by
  obtain ⟨a, ha, hza⟩ := exists_inner_ge_of_mem_convexHull hz
  exact ⟨a, ha, (mem_diameterBall_iff z a).2 hza⟩

/-- Every point in the diameter ball lies within distance `‖a‖` of
the endpoint `a`. This includes the multiple-zero case of the paper. -/
theorem norm_sub_le_of_mem_diameterBall {z a : E}
    (hz : z ∈ diameterBall a) : ‖z - a‖ ≤ ‖a‖ := by
  have hh := (mem_diameterBall_iff z a).1 hz
  have hnorm := norm_sub_sq_real z a
  have hz0 := sq_nonneg ‖z‖
  have hn : ‖z - a‖ ^ 2 ≤ ‖a‖ ^ 2 := by nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hn

end RealInnerProductSpace

/-- Complex-plane form of the diameter-ball covering. -/
theorem convexHull_covered_by_diameter_disks {s : Set ℂ} {z : ℂ}
    (hz : z ∈ convexHull ℝ s) :
    ∃ a ∈ s, ‖z - a / 2‖ ≤ ‖a‖ / 2 := by
  obtain ⟨a, ha, hza⟩ := convexHull_covered_by_diameterBalls hz
  refine ⟨a, ha, ?_⟩
  change ‖z - (1 / 2 : ℝ) • a‖ ≤ ‖a‖ / 2 at hza
  simpa [Complex.real_smul, div_eq_mul_inv, mul_comm] using hza

/-- A weighted mean cannot lie below every value with positive weight. -/
theorem exists_le_of_weighted_sum_le {ι : Type*} (t : Finset ι)
    (w v : ι → ℝ) (b : ℝ)
    (hw : ∀ i ∈ t, 0 ≤ w i) (hs : ∑ i ∈ t, w i = 1)
    (hb : ∑ i ∈ t, w i * v i ≤ b) :
    ∃ i ∈ t, v i ≤ b := by
  by_contra h
  push Not at h
  have hp : ∃ i ∈ t, 0 < w i := by
    by_contra hp
    push Not at hp
    have hsum : ∑ i ∈ t, w i ≤ 0 := Finset.sum_nonpos hp
    linarith
  obtain ⟨j, hj, hwj⟩ := hp
  have hlt : (∑ i ∈ t, w i * b) < ∑ i ∈ t, w i * v i := by
    refine Finset.sum_lt_sum (fun i hi =>
      mul_le_mul_of_nonneg_left (h i hi).le (hw i hi)) ?_
    exact ⟨j, hj, mul_lt_mul_of_pos_left (h j hj) hwj⟩
  rw [← Finset.sum_mul, hs, one_mul] at hlt
  exact (not_lt_of_ge hb) hlt

/-- The last step of the weighted covering argument. -/
theorem exists_norm_sub_le_of_weighted_sq_le {ι E : Type*}
    [SeminormedAddCommGroup E] (t : Finset ι) (w : ι → ℝ)
    (a : ι → E) (z : E)
    (hw : ∀ i ∈ t, 0 ≤ w i) (hs : ∑ i ∈ t, w i = 1)
    (hb : ∑ i ∈ t, w i * ‖z - a i‖ ^ 2 ≤ 1) :
    ∃ i ∈ t, ‖z - a i‖ ≤ 1 := by
  obtain ⟨i, hi, hle⟩ := exists_le_of_weighted_sum_le t w
    (fun i => ‖z - a i‖ ^ 2) 1 hw hs hb
  refine ⟨i, hi, ?_⟩
  nlinarith [norm_nonneg (z - a i)]

/-- The scalar form of the positive-semidefinite matrix criterion.
The proof is algebraic and avoids parametrizing the boundary circle. -/
theorem covering_scalar_inequality (a s x y u v : ℝ)
    (hs : 1 ≤ s)
    (hd : 0 ≤ (1 - a ^ 2) * s + 2 * a * x - 1)
    (hdet : a ^ 2 * y ^ 2 ≤
      (s - 1) * ((1 - a ^ 2) * s + 2 * a * x - 1))
    (hz : (u - a / 2) ^ 2 + v ^ 2 ≤ (a / 2) ^ 2) :
    s * ((u - a) ^ 2 + v ^ 2) + 2 * ((u - a) * x - v * y) + 1 ≤ s := by
  let d := (1 - a ^ 2) * s + 2 * a * x - 1
  let b := x - a * s / 2
  let c := (s - 1 + d) / 2
  let U := u - a / 2
  have hc : 0 ≤ c := by dsimp [c, d]; linarith
  have hid : c ^ 2 - a ^ 2 * (b ^ 2 + y ^ 2) =
      (s - 1) * d - a ^ 2 * y ^ 2 := by dsimp [c, b, d]; ring
  have hab : a ^ 2 * (b ^ 2 + y ^ 2) ≤ c ^ 2 := by
    change a ^ 2 * y ^ 2 ≤ (s - 1) * d at hdet
    linarith
  have hz' : U ^ 2 + v ^ 2 ≤ (a / 2) ^ 2 := hz
  have hprod := mul_le_mul_of_nonneg_right hz'
    (show 0 ≤ b ^ 2 + y ^ 2 by positivity)
  have hsq : (2 * (U * b - v * y)) ^ 2 ≤ c ^ 2 := by
    nlinarith [sq_nonneg (U * y + v * b)]
  have hlin : 2 * (U * b - v * y) ≤ c := le_of_sq_le_sq hsq hc
  have hneg : s * (U ^ 2 + v ^ 2 - (a / 2) ^ 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (sub_nonpos.mpr hz')
  have hid' : s * ((u - a) ^ 2 + v ^ 2) + 2 * ((u - a) * x - v * y) + 1 - s =
      s * (U ^ 2 + v ^ 2 - (a / 2) ^ 2) + 2 * (U * b - v * y) - c := by
    dsimp [U, b, c, d]
    ring
  linarith

/-- The boundary-zero argument only needs the first-moment bound and
the usual second-moment inequality. -/
theorem boundary_scalar_criterion (s x y : ℝ)
    (hx : 1 ≤ x) (hs : x ^ 2 + y ^ 2 ≤ s) :
    1 ≤ s ∧ 0 ≤ 2 * x - 1 ∧ y ^ 2 ≤ (s - 1) * (2 * x - 1) := by
  have hx2 : 1 ≤ x ^ 2 := by nlinarith
  have hsy : y ^ 2 ≤ s - 1 := by linarith
  have hs1 : 0 ≤ s - 1 := le_trans (sq_nonneg y) hsy
  refine ⟨by linarith, by linarith, ?_⟩
  nlinarith [mul_nonneg hs1 (show 0 ≤ 2 * x - 2 by linarith)]

/-- The matrix criterion bounds the reciprocal-moment expression on
the entire diameter disk. -/
theorem weighted_expression_le_one (a s : ℝ) (μ z : ℂ)
    (ha : 0 ≤ a) (hs : 1 ≤ s)
    (hd : 0 ≤ (1 - a ^ 2) * s + 2 * a * μ.re - 1)
    (hdet : a ^ 2 * μ.im ^ 2 ≤
      (s - 1) * ((1 - a ^ 2) * s + 2 * a * μ.re - 1))
    (hz : ‖z - ((a / 2 : ℝ) : ℂ)‖ ≤ a / 2) :
    ‖z - (a : ℂ)‖ ^ 2 + (2 * ((z - (a : ℂ)) * μ).re + 1) / s ≤ 1 := by
  have hs0 : 0 < s := by linarith
  have hzsq := (sq_le_sq₀ (norm_nonneg _)
    (show 0 ≤ a / 2 by positivity)).2 hz
  have hz' : (z.re - a / 2) ^ 2 + z.im ^ 2 ≤ (a / 2) ^ 2 := by
    rw [Complex.sq_norm] at hzsq
    simpa [Complex.normSq_apply, pow_two] using hzsq
  have hscalar := covering_scalar_inequality a s μ.re μ.im z.re z.im hs hd hdet hz'
  have hbound : s * ‖z - (a : ℂ)‖ ^ 2 +
      2 * ((z - (a : ℂ)) * μ).re + 1 ≤ s := by
    rw [Complex.sq_norm]
    simpa [Complex.normSq_apply, Complex.mul_re, pow_two] using hscalar
  have hdiv : (s * ‖z - (a : ℂ)‖ ^ 2 +
      2 * ((z - (a : ℂ)) * μ).re + 1) / s ≤ 1 := by
    exact (div_le_iff₀ hs0).2 (by simpa using hbound)
  convert hdiv using 1; field_simp; ring

/-- The identity for one summand in the reciprocal-weight formula. -/
theorem reciprocal_weight_identity (a z ζ q : ℂ)
    (hq : q * (a - ζ) = 1) :
    ‖q‖ ^ 2 * ‖z - ζ‖ ^ 2 =
      ‖z - a‖ ^ 2 * ‖q‖ ^ 2 + 2 * ((z - a) * q).re + 1 := by
  have heq : q * (z - ζ) = (z - a) * q + 1 := by
    calc
      q * (z - ζ) = (z - a) * q + q * (a - ζ) := by ring
      _ = (z - a) * q + 1 := by rw [hq]
  calc
    ‖q‖ ^ 2 * ‖z - ζ‖ ^ 2 = ‖q * (z - ζ)‖ ^ 2 := by rw [norm_mul, mul_pow]
    _ = ‖(z - a) * q + 1‖ ^ 2 := by rw [heq]
    _ = ‖z - a‖ ^ 2 * ‖q‖ ^ 2 + 2 * ((z - a) * q).re + 1 := by
      rw [norm_add_sq_real]
      simp [Complex.inner, mul_pow]
      ring

/-- The reciprocal-weight identity for a finite family. The two moment
hypotheses specify the ordinary first and second moments explicitly. -/
theorem reciprocal_weight_sum_identity {ι : Type*} (t : Finset ι)
    (a z μ : ℂ) (q ζ : ι → ℂ) (m s : ℝ)
    (hm : m ≠ 0) (hs : s ≠ 0)
    (hcard : (t.card : ℝ) = m)
    (hq : ∀ j ∈ t, q j * (a - ζ j) = 1)
    (hnorm : ∑ j ∈ t, ‖q j‖ ^ 2 = m * s)
    (hmean : ∑ j ∈ t, q j = (m : ℂ) * μ) :
    (∑ j ∈ t, (‖q j‖ ^ 2 / (m * s)) * ‖z - ζ j‖ ^ 2) =
      ‖z - a‖ ^ 2 + (2 * ((z - a) * μ).re + 1) / s := by
  have hre : (∑ j ∈ t, ((z - a) * q j).re) = m * ((z - a) * μ).re := by
    rw [← Complex.re_sum, ← Finset.mul_sum, hmean]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hsum : (∑ j ∈ t, ‖q j‖ ^ 2 * ‖z - ζ j‖ ^ 2) =
      ‖z - a‖ ^ 2 * (m * s) + 2 * (m * ((z - a) * μ).re) + m := by
    calc
      (∑ j ∈ t, ‖q j‖ ^ 2 * ‖z - ζ j‖ ^ 2) =
          ∑ j ∈ t, (‖z - a‖ ^ 2 * ‖q j‖ ^ 2 +
            2 * ((z - a) * q j).re + 1) := by
        exact Finset.sum_congr rfl (fun j hj => reciprocal_weight_identity a z (ζ j) (q j) (hq j hj))
      _ = ‖z - a‖ ^ 2 * (∑ j ∈ t, ‖q j‖ ^ 2) +
          2 * (∑ j ∈ t, ((z - a) * q j).re) + (t.card : ℝ) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
          nsmul_eq_mul, mul_one]
      _ = _ := by rw [hnorm, hre, hcard]
  calc
    (∑ j ∈ t, (‖q j‖ ^ 2 / (m * s)) * ‖z - ζ j‖ ^ 2) =
        (∑ j ∈ t, ‖q j‖ ^ 2 * ‖z - ζ j‖ ^ 2) / (m * s) := by
      simp_rw [div_mul_eq_mul_div]
      rw [Finset.sum_div]
    _ = (‖z - a‖ ^ 2 * (m * s) + 2 * (m * ((z - a) * μ).re) + m) / (m * s) := by
      rw [hsum]
    _ = ‖z - a‖ ^ 2 + (2 * ((z - a) * μ).re + 1) / s := by
      field_simp
      ring

/-- A finite critical-point family satisfying the reciprocal-moment
matrix criterion covers the complete diameter disk. -/
theorem reciprocal_moment_covering {ι : Type*} (t : Finset ι)
    (a m s : ℝ) (μ z : ℂ) (q ζ : ι → ℂ)
    (ha : 0 ≤ a) (hm : 0 < m) (hs : 1 ≤ s)
    (hcard : (t.card : ℝ) = m)
    (hq : ∀ j ∈ t, q j * ((a : ℂ) - ζ j) = 1)
    (hnorm : ∑ j ∈ t, ‖q j‖ ^ 2 = m * s)
    (hmean : ∑ j ∈ t, q j = (m : ℂ) * μ)
    (hd : 0 ≤ (1 - a ^ 2) * s + 2 * a * μ.re - 1)
    (hdet : a ^ 2 * μ.im ^ 2 ≤
      (s - 1) * ((1 - a ^ 2) * s + 2 * a * μ.re - 1))
    (hz : ‖z - ((a / 2 : ℝ) : ℂ)‖ ≤ a / 2) :
    ∃ j ∈ t, ‖z - ζ j‖ ≤ 1 := by
  have hs0 : 0 < s := by linarith
  let w : ι → ℝ := fun j => ‖q j‖ ^ 2 / (m * s)
  have hw : ∀ j ∈ t, 0 ≤ w j := by
    intro j hj
    dsimp [w]
    positivity
  have hwsum : ∑ j ∈ t, w j = 1 := by
    dsimp [w]
    rw [← Finset.sum_div, hnorm, div_self (mul_ne_zero (ne_of_gt hm) (ne_of_gt hs0))]
  apply exists_norm_sub_le_of_weighted_sq_le t w ζ z hw hwsum
  change (∑ j ∈ t, (‖q j‖ ^ 2 / (m * s)) * ‖z - ζ j‖ ^ 2) ≤ 1
  rw [reciprocal_weight_sum_identity t (a : ℂ) z μ q ζ m s
    (ne_of_gt hm) (ne_of_gt hs0) hcard hq hnorm hmean]
  exact weighted_expression_le_one a s μ z ha hs hd hdet hz

/-- A point of the closed unit disk distinct from `1` has its
reciprocal displacement in the half-plane with real part at least one half. -/
theorem reciprocal_displacement_re_ge_half (z : ℂ)
    (hz : ‖z‖ ≤ 1) (hz1 : z ≠ 1) :
    (1 / 2 : ℝ) ≤ (1 / (1 - z)).re := by
  have hd : 0 < Complex.normSq (1 - z) :=
    Complex.normSq_pos.mpr (sub_ne_zero.mpr hz1.symm)
  have hsq : Complex.normSq z ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg z]
  rw [one_div (1 - z), Complex.inv_re]
  apply (le_div_iff₀ hd).2
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im] at hsq ⊢
  nlinarith

/-- The ordinary complex second moment dominates the squared modulus
of the first moment. -/
theorem complex_moment_bound {ι : Type*} (t : Finset ι)
    (q : ι → ℂ) (μ : ℂ) (m s : ℝ)
    (hm : 0 < m) (hcard : (t.card : ℝ) = m)
    (hnorm : ∑ j ∈ t, ‖q j‖ ^ 2 = m * s)
    (hmean : ∑ j ∈ t, q j = (m : ℂ) * μ) :
    ‖μ‖ ^ 2 ≤ s := by
  have hre : (∑ j ∈ t, (q j).re) = m * μ.re := by
    simpa [Complex.re_sum, Complex.mul_re] using congrArg Complex.re hmean
  have him : (∑ j ∈ t, (q j).im) = m * μ.im := by
    simpa [Complex.im_sum, Complex.mul_im] using congrArg Complex.im hmean
  have hcr := sq_sum_le_card_mul_sum_sq (s := t) (f := fun j => (q j).re)
  have hci := sq_sum_le_card_mul_sum_sq (s := t) (f := fun j => (q j).im)
  rw [hcard, hre] at hcr
  rw [hcard, him] at hci
  have hcoord : (∑ j ∈ t, (q j).re ^ 2) + (∑ j ∈ t, (q j).im ^ 2) = m * s := by
    rw [← Finset.sum_add_distrib]
    convert hnorm using 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hmul : m ^ 2 * (μ.re ^ 2 + μ.im ^ 2) ≤ m ^ 2 * s := by
    nlinarith
  have hle : μ.re ^ 2 + μ.im ^ 2 ≤ s :=
    (mul_le_mul_iff_right₀ (sq_pos_of_pos hm)).mp (by simpa [mul_comm] using hmul)
  rw [Complex.sq_norm, Complex.normSq_apply]
  nlinarith

end Schmeisser

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Tactic

/-!
# Reflected polynomials on the closed unit disk

Reflection conjugates the coefficients and reverses their order. The
pointwise comparison follows from the exact identity for a linear factor,
then multiplication over all zeros with their multiplicities.
-/

noncomputable section

namespace Schmeisser

open Polynomial
open scoped ComplexConjugate

/-- Coefficient conjugation followed by the usual polynomial reversal. -/
def reflectedPolynomial (p : Polynomial ℂ) : Polynomial ℂ :=
  (p.map (starRingEnd ℂ)).reverse

@[simp]
theorem reflectedPolynomial_C (c : ℂ) :
    reflectedPolynomial (C c) = C (conj c) := by
  simp [reflectedPolynomial]

@[simp]
theorem reflectedPolynomial_mul (p q : Polynomial ℂ) :
    reflectedPolynomial (p * q) = reflectedPolynomial p * reflectedPolynomial q := by
  simp [reflectedPolynomial]

@[simp]
theorem reflectedPolynomial_one : reflectedPolynomial 1 = 1 := by
  simpa using reflectedPolynomial_C 1

@[simp]
theorem reflectedPolynomial_X_sub_C (a : ℂ) :
    reflectedPolynomial (X - C a) = 1 - C (conj a) * X := by
  simp only [reflectedPolynomial, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  rw [sub_eq_add_neg, ← Polynomial.C_neg, Polynomial.reverse_add_C]
  simp [Polynomial.reverse, sub_eq_add_neg]

theorem reflectedPolynomial_multiset_prod (s : Multiset (Polynomial ℂ)) :
    reflectedPolynomial s.prod = (s.map reflectedPolynomial).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons p s ih => simp [ih]

theorem reflectedPolynomial_eval_roots (p : Polynomial ℂ) (z : ℂ) :
    (reflectedPolynomial p).eval z =
      conj p.leadingCoeff * (p.roots.map (fun a => 1 - conj a * z)).prod := by
  have hs : p.Splits := IsAlgClosed.splits p
  conv_lhs => rw [hs.eq_prod_roots]
  simp [reflectedPolynomial_multiset_prod, Polynomial.eval_multiset_prod,
    Multiset.map_map]

/-- The coefficient definition agrees away from zero with the usual formula
`z^deg(p) * conj (p (1 / conj z))`. The polynomial definition also covers zero. -/
theorem reflectedPolynomial_eval (p : Polynomial ℂ) {z : ℂ} (hz : z ≠ 0) :
    (reflectedPolynomial p).eval z = z ^ p.natDegree * conj (p.eval ((conj z)⁻¹)) := by
  let _ : Invertible (z⁻¹) := invertibleOfNonzero (inv_ne_zero hz)
  have h := Polynomial.eval₂_reverse_mul_pow (RingHom.id ℂ) (z⁻¹)
    (p.map (starRingEnd ℂ))
  have hm : (p.map (starRingEnd ℂ)).eval (z⁻¹) = conj (p.eval ((conj z)⁻¹)) := by
    simpa using Polynomial.eval_map_apply (p := p) (starRingEnd ℂ) ((conj z)⁻¹)
  simp only [invOf_eq_inv, inv_inv, Polynomial.eval₂_id, Polynomial.natDegree_map] at h
  rw [hm] at h
  change (reflectedPolynomial p).eval z * (z⁻¹) ^ p.natDegree = _ at h
  calc
    (reflectedPolynomial p).eval z =
        (reflectedPolynomial p).eval z * ((z⁻¹) ^ p.natDegree * z ^ p.natDegree) := by
      rw [← mul_pow, inv_mul_cancel₀ hz, one_pow, mul_one]
    _ = conj (p.eval ((conj z)⁻¹)) * z ^ p.natDegree := by rw [← mul_assoc, h]
    _ = z ^ p.natDegree * conj (p.eval ((conj z)⁻¹)) := mul_comm _ _

theorem reflection_factor_sq_identity (a z : ℂ) :
    ‖1 - conj a * z‖ ^ 2 - ‖z - a‖ ^ 2 =
      (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im]
  ring

theorem norm_sub_le_reflection_factor {a z : ℂ} (ha : ‖a‖ ≤ 1) (hz : ‖z‖ ≤ 1) :
    ‖z - a‖ ≤ ‖1 - conj a * z‖ := by
  have ha2 : 0 ≤ 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have hz2 : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hsq := reflection_factor_sq_identity a z
  nlinarith [mul_nonneg ha2 hz2, norm_nonneg (z - a), norm_nonneg (1 - conj a * z)]

theorem norm_eval_root_product_le_reflected (s : Multiset ℂ)
    (hs : ∀ a ∈ s, ‖a‖ ≤ 1) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖((s.map (X - C ·)).prod).eval z‖ ≤
      ‖(reflectedPolynomial ((s.map (X - C ·)).prod)).eval z‖ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
      have ha : ‖a‖ ≤ 1 := hs a (by simp)
      have hs' : ∀ b ∈ s, ‖b‖ ≤ 1 := fun b hb => hs b (by simp [hb])
      simpa only [Multiset.map_cons, Multiset.prod_cons, Polynomial.eval_mul,
        Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
        reflectedPolynomial_mul, reflectedPolynomial_X_sub_C, Polynomial.eval_one,
        norm_mul] using
        mul_le_mul (norm_sub_le_reflection_factor ha hz) (ih hs')
          (norm_nonneg _) (norm_nonneg _)

/-- A polynomial whose zeros lie in the closed unit disk is bounded there by
the norm of its reflected polynomial. No monicity or simple-root hypothesis
is needed. -/
theorem norm_eval_le_reflected {p : Polynomial ℂ}
    (hroots : ∀ a : ℂ, p.eval a = 0 → ‖a‖ ≤ 1)
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖p.eval z‖ ≤ ‖(reflectedPolynomial p).eval z‖ := by
  have hs : p.Splits := IsAlgClosed.splits p
  have hprod := norm_eval_root_product_le_reflected p.roots
    (fun a ha => hroots a ((Polynomial.mem_roots').mp ha).2) hz
  calc
    ‖p.eval z‖ = ‖p.leadingCoeff‖ * ‖((p.roots.map (X - C ·)).prod).eval z‖ := by
      conv_lhs => rw [hs.eq_prod_roots]
      simp only [Polynomial.eval_mul, Polynomial.eval_C, norm_mul]
    _ ≤ ‖p.leadingCoeff‖ *
        ‖(reflectedPolynomial ((p.roots.map (X - C ·)).prod)).eval z‖ :=
      mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = ‖(reflectedPolynomial p).eval z‖ := by
      conv_rhs => rw [hs.eq_prod_roots]
      simp only [reflectedPolynomial_mul, reflectedPolynomial_C,
        Polynomial.eval_mul, Polynomial.eval_C, norm_mul, Complex.norm_conj]

end Schmeisser

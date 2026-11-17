import Schmeisser.Basic
import Schmeisser.Geometry
import Mathlib.Data.Multiset.Fintype

/-!
# Polynomial roots and reciprocal moments

Roots are enumerated with multiplicity by `Multiset.toEnumFinset`.
The natural-number component distinguishes repeated occurrences of the
same complex root; no distinctness assumption is imposed.
-/

open Polynomial
open scoped BigOperators

namespace Schmeisser

noncomputable def rootIndices (p : Polynomial ℂ) : Finset (ℂ × ℕ) :=
  p.roots.toEnumFinset

theorem rootIndices_card (p : Polynomial ℂ) : (rootIndices p).card = p.natDegree := by
  rw [rootIndices, Multiset.card_toEnumFinset]
  exact (IsAlgClosed.splits p).natDegree_eq_card_roots.symm

theorem eval_eq_zero_of_mem_rootIndices {p : Polynomial ℂ} {j : ℂ × ℕ}
    (hj : j ∈ rootIndices p) : p.eval j.1 = 0 := by
  exact Polynomial.isRoot_of_mem_roots (Multiset.mem_of_mem_toEnumFinset hj)

theorem sum_rootIndices {M : Type*} [AddCommMonoid M] (p : Polynomial ℂ) (f : ℂ → M) :
    ∑ j ∈ rootIndices p, f j.1 = (p.roots.map f).sum := by
  exact (p.roots.sum_map_eq_sum_toEnumFinset f).symm

theorem prod_rootIndices {M : Type*} [CommMonoid M] (p : Polynomial ℂ) (f : ℂ → M) :
    ∏ j ∈ rootIndices p, f j.1 = (p.roots.map f).prod := by
  exact (p.roots.prod_map_eq_prod_toEnumFinset f).symm

theorem eval_factorization (p : Polynomial ℂ) (a : ℂ) :
    p.eval a = p.leadingCoeff * ∏ j ∈ rootIndices p, (a - j.1) := by
  rw [prod_rootIndices p (fun z => a - z)]
  exact (IsAlgClosed.splits p).eval_eq_prod_roots a

noncomputable def rootQuotient (p : Polynomial ℂ) (a : ℂ) : Polynomial ℂ :=
  p /ₘ (X - C a)

theorem factor_at_root {p : Polynomial ℂ} {a : ℂ} (ha : p.eval a = 0) :
    p = (X - C a) * rootQuotient p a :=
  (Polynomial.mul_divByMonic_eq_iff_isRoot.mpr ha).symm

theorem rootQuotient_natDegree (p : Polynomial ℂ) (a : ℂ) :
    (rootQuotient p a).natDegree = p.natDegree - 1 := by
  simp only [rootQuotient, Polynomial.natDegree_divByMonic p (monic_X_sub_C a),
    natDegree_X_sub_C]

theorem eval_derivative_at_root {p : Polynomial ℂ} {a : ℂ} (ha : p.eval a = 0) :
    p.derivative.eval a = (rootQuotient p a).eval a := by
  calc
    p.derivative.eval a = ((X - C a) * rootQuotient p a).derivative.eval a :=
      congrArg (fun f : Polynomial ℂ => f.derivative.eval a) (factor_at_root ha)
    _ = _ := by simp [Polynomial.derivative_mul]

theorem eval_second_derivative_at_root {p : Polynomial ℂ} {a : ℂ} (ha : p.eval a = 0) :
    p.derivative.derivative.eval a = 2 * (rootQuotient p a).derivative.eval a := by
  calc
    p.derivative.derivative.eval a =
        ((X - C a) * rootQuotient p a).derivative.derivative.eval a :=
      congrArg (fun f : Polynomial ℂ => f.derivative.derivative.eval a) (factor_at_root ha)
    _ = _ := by simp [Polynomial.derivative_mul, Polynomial.derivative_add]; ring

/-- The Meir--Sharma identity, with the quotient defined by monic division. -/
theorem meir_sharma_identity {p : Polynomial ℂ} {a : ℂ} (ha : p.eval a = 0) :
    p.derivative.derivative.eval a / p.derivative.eval a =
      2 * ((rootQuotient p a).derivative.eval a / (rootQuotient p a).eval a) := by
  rw [eval_derivative_at_root ha, eval_second_derivative_at_root ha]
  ring

theorem rootQuotient_root_is_root {p : Polynomial ℂ} {a z : ℂ}
    (ha : p.eval a = 0) (hz : (rootQuotient p a).eval z = 0) : p.eval z = 0 := by
  calc
    p.eval z = ((X - C a) * rootQuotient p a).eval z :=
      congrArg (fun f : Polynomial ℂ => f.eval z) (factor_at_root ha)
    _ = 0 := by simp [hz]

theorem rootQuotient_eval_ne_zero {p : Polynomial ℂ} {a : ℂ}
    (ha : p.eval a = 0) (hpa : p.derivative.eval a ≠ 0) :
    (rootQuotient p a).eval a ≠ 0 := by
  rwa [eval_derivative_at_root ha] at hpa

theorem logarithmic_derivative_sum (p : Polynomial ℂ) (a : ℂ) (ha : p.eval a ≠ 0) :
    p.derivative.eval a / p.eval a = ∑ j ∈ rootIndices p, 1 / (a - j.1) := by
  rw [sum_rootIndices p (fun z => 1 / (a - z))]
  exact (IsAlgClosed.splits p).eval_derivative_div_eval_of_ne_zero ha

theorem logarithmic_derivative_at_one_re_ge (p : Polynomial ℂ)
    (hroots : ∀ z : ℂ, p.eval z = 0 → ‖z‖ ≤ 1) (hp1 : p.eval 1 ≠ 0) :
    (p.natDegree : ℝ) / 2 ≤ (p.derivative.eval 1 / p.eval 1).re := by
  rw [logarithmic_derivative_sum p 1 hp1, Complex.re_sum]
  have hi : ∀ j ∈ rootIndices p, (1 / 2 : ℝ) ≤ (1 / (1 - j.1)).re := by
    intro j hj
    have hjroot := eval_eq_zero_of_mem_rootIndices hj
    refine reciprocal_displacement_re_ge_half j.1 (hroots j.1 hjroot) ?_
    intro hj1
    exact hp1 (hj1 ▸ hjroot)
  have hsum := Finset.sum_le_sum hi
  simpa [rootIndices_card, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv] using hsum

/-- The first reciprocal moment of the critical points, with multiplicity. -/
noncomputable def criticalReciprocalMean (p : Polynomial ℂ) (a : ℂ) : ℂ :=
  (∑ j ∈ rootIndices p.derivative, 1 / (a - j.1)) / ((p.natDegree - 1 : ℕ) : ℂ)

/-- The second reciprocal moment of the critical points, with multiplicity. -/
noncomputable def criticalReciprocalSecondMoment (p : Polynomial ℂ) (a : ℂ) : ℝ :=
  (∑ j ∈ rootIndices p.derivative, ‖1 / (a - j.1)‖ ^ 2) /
    ((p.natDegree - 1 : ℕ) : ℝ)

theorem critical_rootIndices_card (p : Polynomial ℂ) :
    (rootIndices p.derivative).card = p.natDegree - 1 := by
  rw [rootIndices_card, Polynomial.natDegree_derivative]

theorem critical_reciprocal_relation {p : Polynomial ℂ} {a : ℂ}
    (ha : p.derivative.eval a ≠ 0) {j : ℂ × ℕ}
    (hj : j ∈ rootIndices p.derivative) :
    (1 / (a - j.1)) * (a - j.1) = 1 := by
  have hne : a - j.1 ≠ 0 := by
    intro h
    apply ha
    rw [sub_eq_zero.mp h]
    exact eval_eq_zero_of_mem_rootIndices hj
  simp [hne]

theorem critical_reciprocal_first_moment (p : Polynomial ℂ) (a : ℂ)
    (hn : 2 ≤ p.natDegree) :
    (∑ j ∈ rootIndices p.derivative, 1 / (a - j.1)) =
      (((p.natDegree - 1 : ℕ) : ℝ) : ℂ) * criticalReciprocalMean p a := by
  have hm : ((p.natDegree - 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show p.natDegree - 1 ≠ 0 by omega)
  simp only [criticalReciprocalMean, Complex.ofReal_natCast]
  field_simp

theorem critical_reciprocal_second_moment (p : Polynomial ℂ) (a : ℂ)
    (hn : 2 ≤ p.natDegree) :
    (∑ j ∈ rootIndices p.derivative, ‖1 / (a - j.1)‖ ^ 2) =
      ((p.natDegree - 1 : ℕ) : ℝ) * criticalReciprocalSecondMoment p a := by
  have hm : ((p.natDegree - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show p.natDegree - 1 ≠ 0 by omega)
  simp only [criticalReciprocalSecondMoment]
  field_simp

theorem critical_reciprocal_mean_bound (p : Polynomial ℂ) (a : ℂ)
    (hn : 2 ≤ p.natDegree) :
    ‖criticalReciprocalMean p a‖ ^ 2 ≤ criticalReciprocalSecondMoment p a := by
  apply complex_moment_bound (rootIndices p.derivative) (fun j => 1 / (a - j.1))
    (criticalReciprocalMean p a) ((p.natDegree - 1 : ℕ) : ℝ)
    (criticalReciprocalSecondMoment p a)
  · exact_mod_cast (show 0 < p.natDegree - 1 by omega)
  · exact_mod_cast critical_rootIndices_card p
  · exact critical_reciprocal_second_moment p a hn
  · exact critical_reciprocal_first_moment p a hn

theorem critical_reciprocal_mean_at_one_re_ge (p : Polynomial ℂ)
    (hn : 2 ≤ p.natDegree)
    (hroots : ∀ z : ℂ, p.eval z = 0 → ‖z‖ ≤ 1)
    (hp1 : p.eval 1 = 0) (hpd1 : p.derivative.eval 1 ≠ 0) :
    1 ≤ (criticalReciprocalMean p 1).re := by
  have hg1 := rootQuotient_eval_ne_zero hp1 hpd1
  have hgroots : ∀ z : ℂ, (rootQuotient p 1).eval z = 0 → ‖z‖ ≤ 1 := by
    intro z hz
    exact hroots z (rootQuotient_root_is_root hp1 hz)
  have hlog := logarithmic_derivative_at_one_re_ge (rootQuotient p 1) hgroots hg1
  rw [rootQuotient_natDegree] at hlog
  have hsum : (∑ j ∈ rootIndices p.derivative, 1 / (1 - j.1)) =
      2 * ((rootQuotient p 1).derivative.eval 1 / (rootQuotient p 1).eval 1) := by
    rw [← logarithmic_derivative_sum p.derivative 1 hpd1]
    exact meir_sharma_identity hp1
  have hm : (0 : ℝ) < ((p.natDegree - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < p.natDegree - 1 by omega)
  rw [criticalReciprocalMean, Complex.div_natCast_re, hsum]
  apply (le_div_iff₀ hm).2
  norm_num only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul,
    sub_zero, one_mul]
  linarith

/-- The diameter disk at a simple boundary zero is covered by the
unit disks centred at the actual critical points of the polynomial. -/
theorem simple_unit_root_diameter_covered (p : Polynomial ℂ)
    (hn : 2 ≤ p.natDegree)
    (hroots : ∀ z : ℂ, p.eval z = 0 → ‖z‖ ≤ 1)
    (hp1 : p.eval 1 = 0) (hpd1 : p.derivative.eval 1 ≠ 0)
    (ξ : ℂ) (hξ : ‖ξ - (1 / 2 : ℂ)‖ ≤ (1 / 2 : ℝ)) :
    ∃ ζ : ℂ, p.derivative.eval ζ = 0 ∧ ‖ξ - ζ‖ ≤ 1 := by
  let μ := criticalReciprocalMean p 1
  let s := criticalReciprocalSecondMoment p 1
  let m : ℝ := ((p.natDegree - 1 : ℕ) : ℝ)
  have hm : 0 < m := by dsimp [m]; exact_mod_cast (show 0 < p.natDegree - 1 by omega)
  have hx : 1 ≤ μ.re := critical_reciprocal_mean_at_one_re_ge p hn hroots hp1 hpd1
  have hvar : μ.re ^ 2 + μ.im ^ 2 ≤ s := by
    have h := critical_reciprocal_mean_bound p 1 hn
    change ‖μ‖ ^ 2 ≤ s at h
    rw [Complex.sq_norm, Complex.normSq_apply] at h
    nlinarith
  obtain ⟨hs, hd, hdet⟩ := boundary_scalar_criterion s μ.re μ.im hx hvar
  have hd' : 0 ≤ (1 - (1 : ℝ) ^ 2) * s + 2 * 1 * μ.re - 1 := by simpa using hd
  have hdet' : (1 : ℝ) ^ 2 * μ.im ^ 2 ≤
      (s - 1) * ((1 - (1 : ℝ) ^ 2) * s + 2 * 1 * μ.re - 1) := by simpa using hdet
  have hξ' : ‖ξ - (((1 : ℝ) / 2 : ℝ) : ℂ)‖ ≤ (1 : ℝ) / 2 := by simpa using hξ
  obtain ⟨j, hj, hdist⟩ := reciprocal_moment_covering (rootIndices p.derivative)
    1 m s μ ξ (fun j => 1 / (1 - j.1)) Prod.fst (by norm_num) hm hs
    (by dsimp [m]; exact_mod_cast critical_rootIndices_card p)
    (fun j hj => critical_reciprocal_relation hpd1 hj)
    (critical_reciprocal_second_moment p 1 hn)
    (critical_reciprocal_first_moment p 1 hn) hd' hdet' hξ'
  exact ⟨j.1, eval_eq_zero_of_mem_rootIndices hj, hdist⟩

/-- The complete boundary-zero case, including multiple zeros. -/
theorem unit_root_diameter_covered (p : Polynomial ℂ)
    (hn : 2 ≤ p.natDegree)
    (hroots : ∀ z : ℂ, p.eval z = 0 → ‖z‖ ≤ 1)
    (hp1 : p.eval 1 = 0)
    (ξ : ℂ) (hξ : ‖ξ - (1 / 2 : ℂ)‖ ≤ (1 / 2 : ℝ)) :
    ∃ ζ : ℂ, p.derivative.eval ζ = 0 ∧ ‖ξ - ζ‖ ≤ 1 := by
  by_cases hpd1 : p.derivative.eval 1 = 0
  · refine ⟨1, hpd1, ?_⟩
    have hball : ξ ∈ diameterBall (1 : ℂ) := by
      simpa [diameterBall, Complex.real_smul] using hξ
    simpa using norm_sub_le_of_mem_diameterBall hball
  · exact simple_unit_root_diameter_covered p hn hroots hp1 hpd1 ξ hξ

theorem critical_reciprocal_second_moment_pos (p : Polynomial ℂ) (a : ℂ)
    (hn : 2 ≤ p.natDegree) (hpa : p.derivative.eval a ≠ 0) :
    0 < criticalReciprocalSecondMoment p a := by
  have hm : (0 : ℝ) < ((p.natDegree - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < p.natDegree - 1 by omega)
  have ht : (rootIndices p.derivative).Nonempty := by
    apply Finset.card_pos.mp
    rw [critical_rootIndices_card]
    omega
  unfold criticalReciprocalSecondMoment
  apply div_pos _ hm
  apply Finset.sum_pos _ ht
  intro j hj
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  intro hq
  have h := critical_reciprocal_relation hpa hj
  rw [hq, zero_mul] at h
  exact zero_ne_one h

theorem reciprocal_disk_defect_identity (a : ℝ) (ζ q : ℂ)
    (hq : q * ((a : ℂ) - ζ) = 1) :
    (1 - ‖ζ‖ ^ 2) * ‖q‖ ^ 2 =
      (1 - a ^ 2) * ‖q‖ ^ 2 + 2 * a * q.re - 1 := by
  have h := reciprocal_weight_identity (a : ℂ) 0 ζ q hq
  simp [Complex.mul_re, Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
  nlinarith

/-- The Gauss--Lucas deficit identity, before using its sign. -/
theorem critical_reciprocal_defect_identity (p : Polynomial ℂ) (a : ℝ)
    (hn : 2 ≤ p.natDegree) (hpa : p.derivative.eval (a : ℂ) ≠ 0) :
    ((p.natDegree - 1 : ℕ) : ℝ) *
        ((1 - a ^ 2) * criticalReciprocalSecondMoment p (a : ℂ) +
          2 * a * (criticalReciprocalMean p (a : ℂ)).re - 1) =
      ∑ j ∈ rootIndices p.derivative,
        (1 - ‖j.1‖ ^ 2) * ‖1 / ((a : ℂ) - j.1)‖ ^ 2 := by
  have hsum : (∑ j ∈ rootIndices p.derivative,
        (1 - ‖j.1‖ ^ 2) * ‖1 / ((a : ℂ) - j.1)‖ ^ 2) =
      (1 - a ^ 2) * (∑ j ∈ rootIndices p.derivative, ‖1 / ((a : ℂ) - j.1)‖ ^ 2) +
        2 * a * (∑ j ∈ rootIndices p.derivative, 1 / ((a : ℂ) - j.1)).re -
        ((rootIndices p.derivative).card : ℝ) := by
    calc
      _ = ∑ j ∈ rootIndices p.derivative,
          ((1 - a ^ 2) * ‖1 / ((a : ℂ) - j.1)‖ ^ 2 +
            2 * a * (1 / ((a : ℂ) - j.1)).re - 1) := by
        exact Finset.sum_congr rfl (fun j hj =>
          reciprocal_disk_defect_identity a j.1 (1 / ((a : ℂ) - j.1))
            (critical_reciprocal_relation hpa hj))
      _ = _ := by
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
          Finset.sum_const, nsmul_eq_mul, mul_one, Complex.re_sum]
  rw [critical_reciprocal_second_moment p (a : ℂ) hn,
    critical_reciprocal_first_moment p (a : ℂ) hn,
    Complex.re_ofReal_mul, critical_rootIndices_card] at hsum
  nlinarith [hsum]

theorem critical_reciprocal_delta_nonneg (p : Polynomial ℂ) (a : ℝ)
    (hn : 2 ≤ p.natDegree)
    (hroots : ∀ z : ℂ, p.eval z = 0 → ‖z‖ ≤ 1)
    (hpa : p.derivative.eval (a : ℂ) ≠ 0) :
    0 ≤ (1 - a ^ 2) * criticalReciprocalSecondMoment p (a : ℂ) +
      2 * a * (criticalReciprocalMean p (a : ℂ)).re - 1 := by
  have hm : (0 : ℝ) < ((p.natDegree - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < p.natDegree - 1 by omega)
  have hsum : 0 ≤ ∑ j ∈ rootIndices p.derivative,
      (1 - ‖j.1‖ ^ 2) * ‖1 / ((a : ℂ) - j.1)‖ ^ 2 := by
    apply Finset.sum_nonneg
    intro j hj
    have hjnorm := critical_point_norm_le_one hn hroots (eval_eq_zero_of_mem_rootIndices hj)
    exact mul_nonneg (by nlinarith [norm_nonneg j.1]) (sq_nonneg _)
  rw [← critical_reciprocal_defect_identity p a hn hpa] at hsum
  exact nonneg_of_mul_nonneg_right hsum hm

end Schmeisser

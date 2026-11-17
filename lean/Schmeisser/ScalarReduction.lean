import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
The algebraic part of the comparison-point construction, corresponding to
Step 1 of the necessary-integral-inequalities lemma in the manuscript.
Only existence of an enlarged second moment is needed; no choice of a
smallest root is required.
-/

namespace Schmeisser

open scoped ComplexConjugate

theorem enlarge_second_moment {b c y s : ℝ}
    (hb : 0 < b) (hdelta : 0 ≤ b * s + c)
    (hfail : ¬ (1 ≤ s ∧ y ^ 2 ≤ (s - 1) * (b * s + c))) :
    ∃ σ : ℝ, 1 ≤ σ ∧ s < σ ∧ 0 < b * σ + c ∧
      (σ - 1) * (b * σ + c) = y ^ 2 := by
  let r : ℝ := max 1 s
  let t : ℝ := r + 1 + y ^ 2 / b
  let f : ℝ → ℝ := fun v ↦ (v - 1) * (b * v + c) - y ^ 2
  have hr1 : 1 ≤ r := le_max_left _ _
  have hrs : s ≤ r := le_max_right _ _
  have hdr : 0 ≤ b * r + c := by nlinarith
  have hfr : f r ≤ 0 := by
    by_cases hs : 1 ≤ s
    · have hdet : ¬ y ^ 2 ≤ (s - 1) * (b * s + c) := fun h ↦ hfail ⟨hs, h⟩
      dsimp [f, r]
      rw [max_eq_right hs]
      linarith
    · dsimp [f, r]
      rw [max_eq_left (le_of_not_ge hs)]
      nlinarith [sq_nonneg y]
  have hquot : 0 ≤ y ^ 2 / b := div_nonneg (sq_nonneg y) hb.le
  have hqt : b * (y ^ 2 / b) = y ^ 2 := by field_simp
  have hrt : r ≤ t := by dsimp [t]; linarith
  have ht1 : 1 ≤ t - 1 := by dsimp [t]; linarith
  have hdt : b + y ^ 2 ≤ b * t + c := by dsimp [t]; nlinarith
  have hft : 0 ≤ f t := by
    have hdt0 : 0 ≤ b * t + c := by nlinarith [sq_nonneg y]
    have hprod := mul_le_mul_of_nonneg_right ht1 hdt0
    dsimp [f]
    nlinarith
  have hcont : ContinuousOn f (Set.Icc r t) := by
    dsimp [f]
    fun_prop
  obtain ⟨σ, hσ, heq⟩ := intermediate_value_Icc hrt hcont ⟨hfr, hft⟩
  have hσ1 : 1 ≤ σ := hr1.trans hσ.1
  have hsσ : s ≤ σ := hrs.trans hσ.1
  have hboundary : (σ - 1) * (b * σ + c) = y ^ 2 := by
    dsimp [f] at heq
    linarith
  have hslt : s < σ := by
    refine lt_of_le_of_ne hsσ ?_
    intro he
    subst σ
    exact hfail ⟨hσ1, hboundary.ge⟩
  have hpositive : 0 < b * σ + c := by nlinarith
  exact ⟨σ, hσ1, hslt, hpositive, hboundary⟩

theorem boundary_moment_identity (a x y σ : ℝ) :
    let δ := (1 - a ^ 2) * σ + 2 * a * x - 1
    4 * a ^ 2 * (x ^ 2 + y ^ 2 - σ * δ) -
        (1 - δ - (1 - a ^ 2) * σ) ^ 2 =
      4 * ((a * y) ^ 2 - (σ - 1) * δ) := by
  dsimp
  ring

theorem boundary_moment_parameters {a x y σ : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hσ : 1 ≤ σ)
    (hvariance : x ^ 2 + y ^ 2 ≤ σ)
    (hdelta : 0 < (1 - a ^ 2) * σ + 2 * a * x - 1)
    (hboundary : (σ - 1) * ((1 - a ^ 2) * σ + 2 * a * x - 1) = (a * y) ^ 2) :
    let δ := (1 - a ^ 2) * σ + 2 * a * x - 1
    let u := (x ^ 2 + y ^ 2) / σ
    let h := (1 - a ^ 2) * (1 - u + δ)
    0 < u ∧ u ≤ 1 ∧ δ ≤ u ∧ 0 < h ∧ h < 1 := by
  dsimp
  let δ := (1 - a ^ 2) * σ + 2 * a * x - 1
  let u := (x ^ 2 + y ^ 2) / σ
  have hσpos : 0 < σ := by linarith
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hb : 0 < 1 - a ^ 2 := by nlinarith
  have hid := boundary_moment_identity a x y σ
  change 4 * a ^ 2 * (x ^ 2 + y ^ 2 - σ * δ) -
    (1 - δ - (1 - a ^ 2) * σ) ^ 2 =
    4 * ((a * y) ^ 2 - (σ - 1) * δ) at hid
  have hzero : (σ - 1) * δ = (a * y) ^ 2 := hboundary
  have hnonneg : 0 ≤ x ^ 2 + y ^ 2 - σ * δ := by
    nlinarith [sq_nonneg (1 - δ - (1 - a ^ 2) * σ)]
  have hdu : δ ≤ u := (le_div_iff₀ hσpos).2 (by nlinarith)
  have hu1 : u ≤ 1 := (div_le_one hσpos).2 hvariance
  have hdpos : 0 < δ := hdelta
  have hu0 : 0 < u := hdpos.trans_le hdu
  have hfactor : 0 < 1 - u + δ := by linarith
  have hfactor1 : 1 - u + δ ≤ 1 := by linarith
  have hh0 : 0 < (1 - a ^ 2) * (1 - u + δ) := mul_pos hb hfactor
  have hh1 : (1 - a ^ 2) * (1 - u + δ) < 1 := by
    have := mul_le_mul_of_nonneg_left hfactor1 hb.le
    nlinarith
  exact ⟨hu0, hu1, hdu, hh0, hh1⟩

theorem comparison_point_defect (a σ : ℝ) (μ : ℂ) (hσ : σ ≠ 0) :
    1 - ‖(a : ℂ) - conj μ / (σ : ℂ)‖ ^ 2 =
      (1 - ‖μ‖ ^ 2 / σ + ((1 - a ^ 2) * σ + 2 * a * μ.re - 1)) / σ := by
  simp [Complex.sq_norm, Complex.normSq_apply]
  field_simp
  ring

/-- Failure of the moment criterion produces all the parameters required
by the reflected-polynomial argument. This statement only uses the two
elementary moment constraints. -/
theorem comparison_parameters_of_failure {a s : ℝ} {μ : ℂ}
    (ha : 0 < a) (ha1 : a < 1) (hvariance : ‖μ‖ ^ 2 ≤ s)
    (hdelta : 0 ≤ (1 - a ^ 2) * s + 2 * a * μ.re - 1)
    (hfail : ¬ (1 ≤ s ∧ (a * μ.im) ^ 2 ≤
      (s - 1) * ((1 - a ^ 2) * s + 2 * a * μ.re - 1))) :
    ∃ σ : ℝ, 1 ≤ σ ∧ s < σ ∧
      let δ := (1 - a ^ 2) * σ + 2 * a * μ.re - 1
      let u := ‖μ‖ ^ 2 / σ
      let h := (1 - a ^ 2) * (1 - u + δ)
      let γ := (a : ℂ) - conj μ / (σ : ℂ)
      0 < δ ∧ (σ - 1) * δ = (a * μ.im) ^ 2 ∧
        0 < u ∧ u ≤ 1 ∧ δ ≤ u ∧ 0 < h ∧ h < 1 ∧ ‖γ‖ < 1 := by
  have hb : 0 < 1 - a ^ 2 := by nlinarith
  have hδ : 0 ≤ (1 - a ^ 2) * s + (2 * a * μ.re - 1) := by linarith
  have hf : ¬ (1 ≤ s ∧ (a * μ.im) ^ 2 ≤
      (s - 1) * ((1 - a ^ 2) * s + (2 * a * μ.re - 1))) := by
    intro hc
    apply hfail
    refine ⟨hc.1, ?_⟩
    convert hc.2 using 1
    ring
  obtain ⟨σ, hσ, hsσ, hdσ, heq⟩ := enlarge_second_moment hb hδ hf
  have hσpos : 0 < σ := by linarith
  have hd : 0 < (1 - a ^ 2) * σ + 2 * a * μ.re - 1 := by linarith
  have he : (σ - 1) * ((1 - a ^ 2) * σ + 2 * a * μ.re - 1) =
      (a * μ.im) ^ 2 := by simpa [add_sub_assoc] using heq
  have hv : μ.re ^ 2 + μ.im ^ 2 ≤ σ := by
    have hn : ‖μ‖ ^ 2 = μ.re ^ 2 + μ.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    rw [hn] at hvariance
    linarith
  obtain ⟨hu0, hu1, hdu, hh0, hh1⟩ := boundary_moment_parameters ha ha1 hσ hv hd he
  have hn : μ.re ^ 2 + μ.im ^ 2 = ‖μ‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [hn] at hu0 hu1 hdu hh0 hh1
  refine ⟨σ, hσ, hsσ, hd, he, hu0, hu1, hdu, hh0, hh1, ?_⟩
  have hfactor : 0 < 1 - ‖μ‖ ^ 2 / σ +
      ((1 - a ^ 2) * σ + 2 * a * μ.re - 1) := by linarith
  have hdef := comparison_point_defect a σ μ hσpos.ne'
  have hpos := div_pos hfactor hσpos
  nlinarith [norm_nonneg ((a : ℂ) - conj μ / (σ : ℂ))]

end Schmeisser

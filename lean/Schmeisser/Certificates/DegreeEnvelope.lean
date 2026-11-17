import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic

namespace Schmeisser.Certificates

theorem convex_factor_product_endpoint_bound
    {a b θ p x x₀ x₁ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hx₀ : 0 ≤ x₀) (_hx₁ : 0 ≤ x₁)
    (hx : 0 ≤ x) (hp : p ≤ (1 - θ) * a + θ * b)
    (hxc : x ≤ (1 - θ) * x₀ + θ * x₁) :
    p * x ≤ (1 + (b - a) ^ 2 / (4 * a * b)) * max (a * x₀) (b * x₁) := by
  let M := max (a * x₀) (b * x₁)
  have hM : 0 ≤ M := le_trans (mul_nonneg ha.le hx₀) (le_max_left _ _)
  have hA : 0 ≤ (1 - θ) * a + θ * b := by positivity
  have h₀ : x₀ ≤ M / a := (le_div_iff₀ ha).2
    (by simpa only [mul_comm] using (show a * x₀ ≤ M from le_max_left _ _))
  have h₁ : x₁ ≤ M / b := (le_div_iff₀ hb).2
    (by simpa only [mul_comm] using (show b * x₁ ≤ M from le_max_right _ _))
  have hxc' : (1 - θ) * x₀ + θ * x₁ ≤ M * ((1 - θ) / a + θ / b) := by
    have h0' := mul_le_mul_of_nonneg_left h₀ (sub_nonneg.mpr hθ1)
    have h1' := mul_le_mul_of_nonneg_left h₁ hθ
    calc
      (1 - θ) * x₀ + θ * x₁ ≤ (1 - θ) * (M / a) + θ * (M / b) := add_le_add h0' h1'
      _ = M * ((1 - θ) / a + θ / b) := by ring
  have hid : ((1 - θ) * a + θ * b) * ((1 - θ) / a + θ / b) =
      1 + θ * (1 - θ) * (b - a) ^ 2 / (a * b) := by
    field_simp
    ring
  have hθbound : θ * (1 - θ) ≤ (1 / 4 : ℝ) := by nlinarith [sq_nonneg (θ - 1 / 2)]
  have hfactor : 1 + θ * (1 - θ) * (b - a) ^ 2 / (a * b) ≤
      1 + (b - a) ^ 2 / (4 * a * b) := by
    have h := mul_le_mul_of_nonneg_right hθbound (sq_nonneg (b - a))
    have hh := div_le_div_of_nonneg_right h (mul_pos ha hb).le
    calc
      1 + θ * (1 - θ) * (b - a) ^ 2 / (a * b) ≤
          1 + ((1 / 4 : ℝ) * (b - a) ^ 2) / (a * b) := add_le_add le_rfl hh
      _ = 1 + (b - a) ^ 2 / (4 * a * b) := by ring
  calc
    p * x ≤ ((1 - θ) * a + θ * b) * ((1 - θ) * x₀ + θ * x₁) :=
      mul_le_mul hp hxc hx hA
    _ ≤ ((1 - θ) * a + θ * b) * (M * ((1 - θ) / a + θ / b)) :=
      mul_le_mul_of_nonneg_left hxc' hA
    _ = (1 + θ * (1 - θ) * (b - a) ^ 2 / (a * b)) * M := by rw [← hid]; ring
    _ ≤ (1 + (b - a) ^ 2 / (4 * a * b)) * M := mul_le_mul_of_nonneg_right hfactor hM

theorem rpow_affine_le_chord {β θ lo hi m c : ℝ}
    (hβ : 0 < β) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hm : m = (1 - θ) * lo + θ * hi) :
    β ^ ((m - c) / 2) ≤ (1 - θ) * β ^ ((lo - c) / 2) + θ * β ^ ((hi - c) / 2) := by
  have h := (convexOn_rpow_left hβ).2
    (Set.mem_univ ((lo - c) / 2)) (Set.mem_univ ((hi - c) / 2))
    (sub_nonneg.mpr hθ1) hθ (by ring : 1 - θ + θ = 1)
  simp only [smul_eq_mul] at h
  have he : (m - c) / 2 = (1 - θ) * ((lo - c) / 2) + θ * ((hi - c) / 2) := by rw [hm]; ring
  rwa [← he] at h

theorem quadratic_degree_endpoint_envelope {lo hi m c β : ℝ}
    (hlo : 1 ≤ lo) (hlom : lo ≤ m) (hmhi : m ≤ hi) (hβ : 0 < β) :
    m * (m + 1) * β ^ ((m - c) / 2) ≤
      (1 + (hi * (hi + 1) - lo * (lo + 1)) ^ 2 /
        (4 * (lo * (lo + 1)) * (hi * (hi + 1)))) *
      max (lo * (lo + 1) * β ^ ((lo - c) / 2))
        (hi * (hi + 1) * β ^ ((hi - c) / 2)) := by
  by_cases he : lo = hi
  · have hm : m = lo := by linarith
    rw [hm, ← he]
    simp
  have hspan : 0 < hi - lo := sub_pos.mpr (lt_of_le_of_ne (hlom.trans hmhi) he)
  let θ := (m - lo) / (hi - lo)
  have hθ : 0 ≤ θ := div_nonneg (sub_nonneg.mpr hlom) hspan.le
  have hθ1 : θ ≤ 1 := (div_le_one hspan).2 (by linarith)
  have hm : m = (1 - θ) * lo + θ * hi := by dsimp [θ]; field_simp; ring
  have hp : m * (m + 1) ≤ (1 - θ) * (lo * (lo + 1)) + θ * (hi * (hi + 1)) := by
    rw [hm]
    nlinarith [mul_nonneg (mul_nonneg hθ (sub_nonneg.mpr hθ1)) (sq_nonneg (hi - lo))]
  exact convex_factor_product_endpoint_bound
    (by nlinarith : 0 < lo * (lo + 1)) (by nlinarith : 0 < hi * (hi + 1))
    hθ hθ1 (Real.rpow_nonneg hβ.le _) (Real.rpow_nonneg hβ.le _)
    (Real.rpow_nonneg hβ.le _) hp (rpow_affine_le_chord hβ hθ hθ1 hm)

theorem linear_degree_endpoint_envelope {lo hi m β d : ℝ}
    (hlo : 1 ≤ lo) (hlom : lo ≤ m) (hmhi : m ≤ hi) (hβ : 0 < β) (hd : 0 ≤ d) :
    (m + 1) * (β ^ (m / 2) + d ^ m) ≤
      (1 + (hi - lo) ^ 2 / (4 * (lo + 1) * (hi + 1))) *
      max ((lo + 1) * (β ^ (lo / 2) + d ^ lo))
        ((hi + 1) * (β ^ (hi / 2) + d ^ hi)) := by
  by_cases he : lo = hi
  · have hm : m = lo := by linarith
    rw [hm, ← he]
    simp
  have hspan : 0 < hi - lo := sub_pos.mpr (lt_of_le_of_ne (hlom.trans hmhi) he)
  let θ := (m - lo) / (hi - lo)
  have hθ : 0 ≤ θ := div_nonneg (sub_nonneg.mpr hlom) hspan.le
  have hθ1 : θ ≤ 1 := (div_le_one hspan).2 (by linarith)
  have hm : m = (1 - θ) * lo + θ * hi := by dsimp [θ]; field_simp; ring
  have hp : m + 1 ≤ (1 - θ) * (lo + 1) + θ * (hi + 1) := le_of_eq (by rw [hm]; ring)
  have hβc : β ^ (m / 2) ≤ (1 - θ) * β ^ (lo / 2) + θ * β ^ (hi / 2) := by
    simpa only [sub_zero] using rpow_affine_le_chord (c := 0) hβ hθ hθ1 hm
  have hdc : d ^ m ≤ (1 - θ) * d ^ lo + θ * d ^ hi := by
    by_cases hd0 : d = 0
    · subst d
      simp [Real.zero_rpow (show m ≠ 0 by linarith),
        Real.zero_rpow (show lo ≠ 0 by linarith), Real.zero_rpow (show hi ≠ 0 by linarith)]
    have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
    have h := (convexOn_rpow_left hdpos).2 (Set.mem_univ lo) (Set.mem_univ hi)
      (sub_nonneg.mpr hθ1) hθ (by ring : 1 - θ + θ = 1)
    simpa only [smul_eq_mul, ← hm] using h
  have hxc : β ^ (m / 2) + d ^ m ≤
      (1 - θ) * (β ^ (lo / 2) + d ^ lo) + θ * (β ^ (hi / 2) + d ^ hi) := by linarith
  have h := convex_factor_product_endpoint_bound
    (by linarith : 0 < lo + 1) (by linarith : 0 < hi + 1)
    hθ hθ1 (add_nonneg (Real.rpow_nonneg hβ.le _) (Real.rpow_nonneg hd _))
    (add_nonneg (Real.rpow_nonneg hβ.le _) (Real.rpow_nonneg hd _))
    (add_nonneg (Real.rpow_nonneg hβ.le _) (Real.rpow_nonneg hd _)) hp hxc
  have heq : (hi + 1) - (lo + 1) = hi - lo := by ring
  simpa only [heq] using h

theorem quadratic_degree_endpoint_envelope_nat (lo hi m : ℕ) (c β : ℝ)
    (hlo : 1 ≤ lo) (hlom : lo ≤ m) (hmhi : m ≤ hi) (hβ : 0 < β) :
    (m : ℝ) * ((m : ℝ) + 1) * β ^ (((m : ℝ) - c) / 2) ≤
      (1 + ((hi : ℝ) * ((hi : ℝ) + 1) - (lo : ℝ) * ((lo : ℝ) + 1)) ^ 2 /
        (4 * ((lo : ℝ) * ((lo : ℝ) + 1)) * ((hi : ℝ) * ((hi : ℝ) + 1)))) *
      max ((lo : ℝ) * ((lo : ℝ) + 1) * β ^ (((lo : ℝ) - c) / 2))
        ((hi : ℝ) * ((hi : ℝ) + 1) * β ^ (((hi : ℝ) - c) / 2)) :=
  quadratic_degree_endpoint_envelope (by exact_mod_cast hlo) (by exact_mod_cast hlom)
    (by exact_mod_cast hmhi) hβ

theorem linear_degree_endpoint_envelope_nat (lo hi m : ℕ) (β d : ℝ)
    (hlo : 1 ≤ lo) (hlom : lo ≤ m) (hmhi : m ≤ hi) (hβ : 0 < β) (hd : 0 ≤ d) :
    ((m : ℝ) + 1) * (β ^ ((m : ℝ) / 2) + d ^ m) ≤
      (1 + ((hi : ℝ) - lo) ^ 2 / (4 * ((lo : ℝ) + 1) * ((hi : ℝ) + 1))) *
      max (((lo : ℝ) + 1) * (β ^ ((lo : ℝ) / 2) + d ^ lo))
        (((hi : ℝ) + 1) * (β ^ ((hi : ℝ) / 2) + d ^ hi)) := by
  simpa only [Real.rpow_natCast] using linear_degree_endpoint_envelope
    (lo := (lo : ℝ)) (hi := (hi : ℝ)) (m := (m : ℝ))
    (by exact_mod_cast hlo) (by exact_mod_cast hlom) (by exact_mod_cast hmhi) hβ hd

end Schmeisser.Certificates

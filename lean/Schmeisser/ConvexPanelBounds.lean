import Schmeisser.PanelErrorIntegrals
import Schmeisser.QuadraticTrapezoid
import Schmeisser.PolarCertification
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

open scoped BigOperators
open Set MeasureTheory

namespace Schmeisser

/-- Integrating the two affine majorants of nonnegative convex functions. -/
theorem convexOn_integral_mul_le_chords {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hfcont : ContinuousOn f (Icc a b)) (hgcont : ContinuousOn g (Icc a b))
    (hf : ConvexOn ℝ (Icc a b) f) (hg : ConvexOn ℝ (Icc a b) g)
    (hf0 : ∀ t ∈ Icc a b, 0 ≤ f t) (hg0 : ∀ t ∈ Icc a b, 0 ≤ g t) :
    (∫ t : ℝ in a..b, f t * g t) ≤
      (b - a) / 6 * (2 * f a * g a + f a * g b + f b * g a + 2 * f b * g b) := by
  by_cases he : a = b
  · subst b
    simp
  have hba : 0 < b - a := sub_pos.mpr (lt_of_le_of_ne hab he)
  let T : ℝ → ℝ := fun s => (b - a) * s + a
  let F : ℝ → ℝ := fun s => (1 - s) * f a + s * f b
  let G : ℝ → ℝ := fun s => (1 - s) * g a + s * g b
  have hmap : MapsTo T (Icc (0 : ℝ) 1) (Icc a b) := by
    intro s hs
    dsimp [T]
    constructor <;> nlinarith [hs.1, hs.2]
  have hTf : ContinuousOn (fun s => f (T s)) (Icc (0 : ℝ) 1) :=
    hfcont.comp (by dsimp [T]; fun_prop) hmap
  have hTg : ContinuousOn (fun s => g (T s)) (Icc (0 : ℝ) 1) :=
    hgcont.comp (by dsimp [T]; fun_prop) hmap
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hG : Continuous G := by dsimp [G]; fun_prop
  have hi : (∫ s : ℝ in 0..1, f (T s) * g (T s)) ≤
      ∫ s : ℝ in 0..1, F s * G s := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      ((hTf.mul hTg).intervalIntegrable_of_Icc (by norm_num))
      ((hF.mul hG).intervalIntegrable 0 1)
    intro s hs
    have hsm : 0 ≤ 1 - s := by linarith [hs.2]
    have heq : T s = (1 - s) * a + s * b := by dsimp [T]; ring
    have hff := hf.2 (show a ∈ Icc a b from ⟨le_rfl, hab⟩)
      (show b ∈ Icc a b from ⟨hab, le_rfl⟩) hsm hs.1 (by ring : 1 - s + s = 1)
    have hgg := hg.2 (show a ∈ Icc a b from ⟨le_rfl, hab⟩)
      (show b ∈ Icc a b from ⟨hab, le_rfl⟩) hsm hs.1 (by ring : 1 - s + s = 1)
    simp only [smul_eq_mul, ← heq] at hff hgg
    apply mul_le_mul hff hgg (hg0 _ (hmap hs))
    exact add_nonneg (mul_nonneg hsm (hf0 a ⟨le_rfl, hab⟩))
      (mul_nonneg hs.1 (hf0 b ⟨hab, le_rfl⟩))
  have hpoly : (∫ s : ℝ in 0..1, F s * G s) =
      (2 * f a * g a + f a * g b + f b * g a + 2 * f b * g b) / 6 := by
    calc
      _ = ∫ s : ℝ in 0..1, ((f b - f a) * (g b - g a)) * s ^ 2 +
          (f a * (g b - g a) + (f b - f a) * g a) * s + f a * g a := by
        apply intervalIntegral.integral_congr
        intro s _
        dsimp [F, G]
        ring
      _ = _ := by rw [integral_quadratic]; ring
  rw [hpoly] at hi
  have hchange := intervalIntegral.smul_integral_comp_mul_add (fun t => f t * g t)
    (a := (0 : ℝ)) (b := (1 : ℝ)) (b - a) a
  have he1 : (b - a) * 1 + a = b := by ring
  simp only [smul_eq_mul, mul_zero, zero_add, he1] at hchange
  rw [← hchange]
  convert mul_le_mul_of_nonneg_left hi hba.le using 1 <;> ring

/-- Opposite endpoint ordering improves the product of chord averages. -/
theorem convexOn_integral_mul_le_endpoint_averages {f g : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hfcont : ContinuousOn f (Icc a b)) (hgcont : ContinuousOn g (Icc a b))
    (hf : ConvexOn ℝ (Icc a b) f) (hg : ConvexOn ℝ (Icc a b) g)
    (hf0 : ∀ t ∈ Icc a b, 0 ≤ f t) (hg0 : ∀ t ∈ Icc a b, 0 ≤ g t)
    (hop : (f b - f a) * (g b - g a) ≤ 0) :
    (∫ t : ℝ in a..b, f t * g t) ≤
      (b - a) / 4 * (f a + f b) * (g a + g b) := by
  refine (convexOn_integral_mul_le_chords hab hfcont hgcont hf hg hf0 hg0).trans ?_
  have h := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hab) hop
  nlinarith

/-- Trapezoid inequality with continuity and convexity only on the interval. -/
theorem convexOn_integral_le_trapezoid_Icc {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn f (Icc a b)) (hconv : ConvexOn ℝ (Icc a b) f)
    (hf0 : ∀ t ∈ Icc a b, 0 ≤ f t) :
    (∫ t : ℝ in a..b, f t) ≤ (b - a) / 2 * (f a + f b) := by
  have h := convexOn_integral_mul_le_endpoint_averages (f := f) (g := fun _ => 1)
    hab hcont continuousOn_const hconv (convexOn_const 1 (convex_Icc a b)) hf0
    (by intros; norm_num) (by simp)
  simp only [mul_one] at h
  convert h using 1 <;> ring

noncomputable def errorConvexAmplitude (u t : ℝ) : ℝ := u * t ^ 2 / (1 - u * t)

noncomputable def errorConvexWeight (m : ℕ) (u t : ℝ) : ℝ :=
  (5 / 6 : ℝ) * (m : ℝ) * ((m : ℝ) + 1) *
    baseQuadratic u t ^ (((m - 1 : ℕ) : ℝ) / 2)

noncomputable def errorConvexPanelBound (m : ℕ) (u a b : ℝ) : ℝ :=
  min ((b - a) / 4 * (errorConvexAmplitude u a + errorConvexAmplitude u b) *
      (errorConvexWeight m u a + errorConvexWeight m u b))
    ((b - a) / 2 * (errorPanelTriangle m u a + errorPanelTriangle m u b))

theorem panel_linear_pos {u t : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    0 < 1 - u * t := by nlinarith [mul_nonneg hu0 (sub_nonneg.mpr ht.2)]

theorem errorConvexAmplitude_nonneg {u t : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (ht : t ∈ Icc (0 : ℝ) 1) : 0 ≤ errorConvexAmplitude u t :=
  div_nonneg (mul_nonneg hu0 (sq_nonneg t)) (panel_linear_pos hu0 hu1 ht).le

theorem continuousOn_errorConvexAmplitude {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    ContinuousOn (errorConvexAmplitude u) (Icc (0 : ℝ) 1) := by
  unfold errorConvexAmplitude
  exact (by fun_prop : ContinuousOn (fun t : ℝ => u * t ^ 2) (Icc (0 : ℝ) 1)).div
    (by fun_prop) (fun t ht => (panel_linear_pos hu0 hu1 ht).ne')

theorem errorConvexAmplitude_monotoneOn {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    MonotoneOn (errorConvexAmplitude u) (Icc (0 : ℝ) 1) := by
  intro a ha b hb hab
  have haD := panel_linear_pos hu0 hu1 ha
  have hbD := panel_linear_pos hu0 hu1 hb
  unfold errorConvexAmplitude
  apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    (by nlinarith [ha.1] : a ^ 2 ≤ b ^ 2) hu0) haD.le).trans
  exact div_le_div_of_nonneg_left (by positivity) hbD (by nlinarith)

theorem convexOn_errorConvexAmplitude {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    ConvexOn ℝ (Icc (0 : ℝ) 1) (errorConvexAmplitude u) := by
  have hid (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (1 - u * t)⁻¹ = u * errorConvexAmplitude u t + 1 + u * t := by
    have hd := panel_linear_pos hu0.le hu1 ht
    unfold errorConvexAmplitude
    field_simp
    ring
  refine ⟨convex_Icc 0 1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hz : a * x + b * y ∈ Icc (0 : ℝ) 1 := by
    simpa only [smul_eq_mul] using (convex_Icc (0 : ℝ) 1) hx hy ha hb hab
  have hxD := panel_linear_pos hu0.le hu1 hx
  have hyD := panel_linear_pos hu0.le hu1 hy
  have hi := (convexOn_zpow (-1 : ℤ)).2 (show 1 - u * x ∈ Ioi (0 : ℝ) from hxD)
    (show 1 - u * y ∈ Ioi (0 : ℝ) from hyD) ha hb hab
  simp only [smul_eq_mul, zpow_neg_one] at hi
  have hden : a * (1 - u * x) + b * (1 - u * y) = 1 - u * (a * x + b * y) := by
    nlinarith only [hab]
  rw [hden, hid _ hz, hid _ hx, hid _ hy] at hi
  simp only [smul_eq_mul]
  have hmul : u * errorConvexAmplitude u (a * x + b * y) ≤
      u * (a * errorConvexAmplitude u x + b * errorConvexAmplitude u y) := by
    nlinarith only [hi, hab]
  exact (mul_le_mul_iff_right₀ hu0).1 hmul

theorem convexOn_baseQuadratic (u : ℝ) (hu : 0 ≤ u) :
    ConvexOn ℝ univ (baseQuadratic u) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  have he : a * baseQuadratic u x + b * baseQuadratic u y -
      baseQuadratic u (a * x + b * y) = u * a * b * (x - y) ^ 2 := by
    have hb' : b = 1 - a := by linarith
    rw [hb']
    unfold baseQuadratic
    ring
  have hp : 0 ≤ u * a * b * (x - y) ^ 2 := by positivity
  linarith

theorem convexOn_rpow_baseQuadratic {u r : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (hr : 1 ≤ r) :
    ConvexOn ℝ univ (fun t : ℝ => baseQuadratic u t ^ r) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hq := (convexOn_baseQuadratic u hu0).2 hx hy ha hb hab
  have hp := (convexOn_rpow hr).2
    (show baseQuadratic u x ∈ Ici (0 : ℝ) from (baseQuadratic_pos hu0 hu1).le)
    (show baseQuadratic u y ∈ Ici (0 : ℝ) from (baseQuadratic_pos hu0 hu1).le)
    ha hb hab
  simp only [smul_eq_mul] at hq hp ⊢
  exact (Real.rpow_le_rpow (baseQuadratic_pos hu0 hu1).le hq (by linarith)).trans hp

theorem continuous_errorConvexWeight (m : ℕ) (u : ℝ) : Continuous (errorConvexWeight m u) := by
  unfold errorConvexWeight
  exact continuous_const.mul
    ((Real.continuous_rpow_const (by positivity : 0 ≤ (((m - 1 : ℕ) : ℝ) / 2))).comp
      (by unfold baseQuadratic; fun_prop))

theorem errorConvexWeight_nonneg (m : ℕ) {u t : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    0 ≤ errorConvexWeight m u t := by
  unfold errorConvexWeight
  exact mul_nonneg (by positivity) (Real.rpow_nonneg (baseQuadratic_pos hu0 hu1).le _)

theorem errorConvexWeight_antitoneOn (m : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    AntitoneOn (errorConvexWeight m u) (Icc (0 : ℝ) 1) := by
  intro a ha b hb hab
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (baseQuadratic_pos hu0 hu1).le
      (baseQuadratic_antitone hu0 ha.1 hab hb.2) (by positivity)) (by positivity)

theorem convexOn_errorConvexWeight (m : ℕ) (hm : 3 ≤ m) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) : ConvexOn ℝ univ (errorConvexWeight m u) := by
  have hr : 1 ≤ (((m - 1 : ℕ) : ℝ) / 2) := by
    have hn : (2 : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ m - 1 by omega)
    linarith
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hp := (convexOn_rpow_baseQuadratic hu0 hu1 hr).2 hx hy ha hb hab
  simp only [smul_eq_mul] at hp ⊢
  have hh := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ (5 / 6 : ℝ) * (m : ℝ) * ((m : ℝ) + 1) by positivity)
  convert hh using 1 <;> unfold errorConvexWeight <;> ring

theorem continuous_errorPanelTriangle (m : ℕ) (u : ℝ) : Continuous (errorPanelTriangle m u) := by
  unfold errorPanelTriangle
  exact (continuous_const.mul
    (((Real.continuous_rpow_const (by positivity : 0 ≤ (m : ℝ) / 2)).comp
      (by unfold baseQuadratic; fun_prop)).add (by fun_prop))).div_const _

theorem errorPanelTriangle_nonneg (m : ℕ) {u t : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (ht : t ∈ Icc (0 : ℝ) 1) : 0 ≤ errorPanelTriangle m u t := by
  have hd := panel_linear_pos hu0 hu1 ht
  have hb := (baseQuadratic_pos (t := t) hu0 hu1).le
  unfold errorPanelTriangle
  positivity

theorem convexOn_errorPanelTriangle (m : ℕ) (hm : 2 ≤ m) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) :
    ConvexOn ℝ (Icc (0 : ℝ) 1) (errorPanelTriangle m u) := by
  have hr : 1 ≤ (m : ℝ) / 2 := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hlin : ConvexOn ℝ (Icc (0 : ℝ) 1) (fun t : ℝ => 1 - u * t) := by
    refine ⟨convex_Icc 0 1, ?_⟩
    intro x hx y hy a b ha hb hab
    simp only [smul_eq_mul]
    nlinarith only [hab]
  have hp := hlin.pow (fun t ht => (panel_linear_pos hu0 hu1 ht).le) m
  refine ⟨convex_Icc 0 1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hbq := (convexOn_rpow_baseQuadratic hu0 hu1 hr).2 (mem_univ x) (mem_univ y) ha hb hab
  have hpl := hp.2 hx hy ha hb hab
  simp only [smul_eq_mul, Pi.pow_apply] at hbq hpl ⊢
  have hh := mul_le_mul_of_nonneg_left (add_le_add hbq hpl)
    (show 0 ≤ ((m : ℝ) + 1) / (1 - u) by positivity)
  convert hh using 1 <;> unfold errorPanelTriangle <;> ring

theorem centered_error_convex_panel_bound {ι : Type*} [DecidableEq ι]
    (jset : Finset ι) (η : ι → ℂ) (m : ℕ) (hm : 3 ≤ m) (hcard : jset.card = m)
    {u a b : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (hη : ∑ j ∈ jset, η j = 0)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (m : ℝ) * (u * (1 - u))) :
    ((m : ℝ) + 1) * (∫ t in a..b, centeredErrorIntegrand jset η m u t) / (1 - u) ≤
      errorConvexPanelBound m u a b := by
  let F : ℝ → ℝ := fun t => ((m : ℝ) + 1) * centeredErrorIntegrand jset η m u t / (1 - u)
  have hF : Continuous F :=
    (continuous_const.mul (continuous_centeredErrorIntegrand jset η m u)).div_const _
  have hsub : Icc a b ⊆ Icc (0 : ℝ) 1 :=
    fun t ht => ⟨ha.trans ht.1, ht.2.trans hb⟩
  have haI : a ∈ Icc (0 : ℝ) 1 := ⟨ha, hab.trans hb⟩
  have hbI : b ∈ Icc (0 : ℝ) 1 := ⟨ha.trans hab, hb⟩
  have hAcont := (continuousOn_errorConvexAmplitude hu0.le hu1).mono hsub
  have hBcont := (continuous_errorConvexWeight m u).continuousOn (s := Icc a b)
  have hAconv := (convexOn_errorConvexAmplitude hu0 hu1).subset hsub (convex_Icc a b)
  have hBconv := (convexOn_errorConvexWeight m hm hu0.le hu1).subset
    (subset_univ (Icc a b)) (convex_Icc a b)
  have hA0 (t : ℝ) (ht : t ∈ Icc a b) : 0 ≤ errorConvexAmplitude u t :=
    errorConvexAmplitude_nonneg hu0.le hu1 (hsub ht)
  have hB0 (t : ℝ) (_ht : t ∈ Icc a b) : 0 ≤ errorConvexWeight m u t :=
    errorConvexWeight_nonneg m hu0.le hu1
  have horder : (errorConvexAmplitude u b - errorConvexAmplitude u a) *
      (errorConvexWeight m u b - errorConvexWeight m u a) ≤ 0 := by
    exact mul_nonpos_of_nonneg_of_nonpos
      (sub_nonneg.mpr (errorConvexAmplitude_monotoneOn hu0.le hu1 haI hbI hab))
      (sub_nonpos.mpr (errorConvexWeight_antitoneOn m hu0.le hu1 haI hbI hab))
  have hinterp : (∫ t in a..b, F t) ≤
      (b - a) / 4 * (errorConvexAmplitude u a + errorConvexAmplitude u b) *
        (errorConvexWeight m u a + errorConvexWeight m u b) := by
    refine (intervalIntegral.integral_mono_on hab (hF.intervalIntegrable a b)
      ((hAcont.mul hBcont).intervalIntegrable_of_Icc hab) ?_).trans
      (convexOn_integral_mul_le_endpoint_averages hab hAcont hBcont hAconv hBconv hA0 hB0 horder)
    intro t ht
    have htI := hsub ht
    have hp := centered_error_panel_interpolation_pointwise jset η m (by omega) hcard
      hu0 hu1 htI.1 (le_refl t) (le_refl t) htI.2 hη hV
    refine hp.trans_eq ?_
    change errorPanelInterpolation m u t t = errorConvexAmplitude u t * errorConvexWeight m u t
    unfold errorPanelInterpolation errorConvexAmplitude errorConvexWeight
    ring
  have hraw : (∫ t in a..b, F t) ≤
      (b - a) / 2 * (errorPanelTriangle m u a + errorPanelTriangle m u b) := by
    have hcont := (continuous_errorPanelTriangle m u).continuousOn (s := Icc a b)
    refine (intervalIntegral.integral_mono_on hab (hF.intervalIntegrable a b)
      ((continuous_errorPanelTriangle m u).intervalIntegrable a b) ?_).trans
      (convexOn_integral_le_trapezoid_Icc hab hcont
        ((convexOn_errorPanelTriangle m (by omega) hu0.le hu1).subset hsub (convex_Icc a b))
        (fun t ht => errorPanelTriangle_nonneg m hu0.le hu1 (hsub ht)))
    intro t ht
    have htI := hsub ht
    exact centered_error_panel_triangle_pointwise jset η m (by omega) hcard
      hu0 hu1 htI.1 (le_refl t) htI.2 hη hV
  unfold errorConvexPanelBound
  have hi := le_min hinterp hraw
  simpa only [F, intervalIntegral.integral_div, intervalIntegral.integral_const_mul] using hi

private theorem convex_panel_partition_first_le_last {a b : ℝ} {panels : List (ℝ × ℝ)}
    (hp : Certificates.PanelPartition b a panels) : a ≤ b := by
  induction hp with
  | nil => exact le_rfl
  | cons hab _ ih => exact hab.le.trans ih

theorem centered_error_convex_partition_bound {ι : Type*} [DecidableEq ι]
    (jset : Finset ι) (η : ι → ℂ) (m : ℕ) (hm : 3 ≤ m) (hcard : jset.card = m)
    {u a : ℝ} {panels : List (ℝ × ℝ)} (hu0 : 0 < u) (hu1 : u < 1)
    (hp : Certificates.PanelPartition 1 a panels) (ha : 0 ≤ a)
    (hη : ∑ j ∈ jset, η j = 0)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (m : ℝ) * (u * (1 - u))) :
    ((m : ℝ) + 1) * (∫ t in a..1, centeredErrorIntegrand jset η m u t) / (1 - u) ≤
      (panels.map (fun ab => errorConvexPanelBound m u ab.1 ab.2)).sum := by
  induction hp with
  | nil => simp
  | @cons a b panels hab hp ih =>
      have hc := continuous_centeredErrorIntegrand jset η m u
      have hb : b ≤ 1 := convex_panel_partition_first_le_last hp
      have hfirst := centered_error_convex_panel_bound jset η m hm hcard hu0 hu1 ha hab.le hb hη hV
      have htail := ih (ha.trans hab.le)
      rw [List.map_cons, List.sum_cons,
        ← intervalIntegral.integral_add_adjacent_intervals
          (hc.intervalIntegrable a b) (hc.intervalIntegrable b 1), mul_add, add_div]
      exact add_le_add hfirst htail

theorem centered_error_convex_riemann_bound {ι : Type*} [DecidableEq ι]
    (jset : Finset ι) (η : ι → ℂ) (m : ℕ) (hm : 3 ≤ m) (hcard : jset.card = m)
    {u : ℝ} {panels : List (ℝ × ℝ)} (hu0 : 0 < u) (hu1 : u < 1)
    (hp : Certificates.PanelPartition 1 0 panels)
    (hη : ∑ j ∈ jset, η j = 0)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (m : ℝ) * (u * (1 - u))) :
    centeredErrorIntegral jset η m u / (1 - u) ≤
      (panels.map (fun ab => errorConvexPanelBound m u ab.1 ab.2)).sum := by
  exact centered_error_convex_partition_bound jset η m hm hcard hu0 hu1 hp (by norm_num) hη hV

end Schmeisser

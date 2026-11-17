import Schmeisser.Certificates.CoefficientCertificates
import Schmeisser.GeometricErrorIntegrals

namespace Schmeisser.Certificates

def CommonCauchyValid (lo hi s : Nat) (upper : List Int) : Prop :=
  11 ≤ lo ∧ lo ≤ hi ∧ 0 < s ∧
    ∀ j : Fin (hi - lo + 1), ∀ q : Fin 8,
      let m := lo + (j : Nat)
      let k := (q : Nat) + 3
      let a := upper[k]?.getD 0
      0 ≤ a ∧ (m : Int) ^ m * (s : Int) ^ 2 ≤
        a ^ 2 * (Nat.fast_choose m k : Int) ^ 2 * (k : Int) ^ k *
          ((m - k : Nat) : Int) ^ (m - k)

instance (lo hi s : Nat) (upper : List Int) : Decidable (CommonCauchyValid lo hi s upper) := by
  unfold CommonCauchyValid
  infer_instance

def checkCommonCauchy (lo hi s : Nat) (upper : List Int) : Bool :=
  decide (CommonCauchyValid lo hi s upper)

theorem checkCommonCauchy_sound (lo hi s : Nat) (upper : List Int)
    (h : checkCommonCauchy lo hi s upper = true) : CommonCauchyValid lo hi s upper :=
  of_decide_eq_true h

theorem commonCauchy_coefficient_bound {lo hi s m k : Nat} {upper : List Int}
    (hcheck : checkCommonCauchy lo hi s upper = true)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) (hk3 : 3 ≤ k) (hk10 : k ≤ 10) :
    normalizedCauchyCoefficient m k ≤ ((upper[k]?.getD 0 : Int) : ℝ) / s := by
  rcases checkCommonCauchy_sound lo hi s upper hcheck with ⟨hlo, hlohi, hs, hcells⟩
  have hkm : k < m := by omega
  have h := hcells ⟨m - lo, by omega⟩ ⟨k - 3, by omega⟩
  have hm : lo + (m - lo) = m := by omega
  have hk : k - 3 + 3 = k := by omega
  simp only [hm, hk, ← Nat.choose_eq_fast_choose] at h
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have ha : (0 : ℝ) ≤ (upper[k]?.getD 0 : Int) := by exact_mod_cast h.1
  have hc : (0 : ℝ) < m.choose k := by exact_mod_cast Nat.choose_pos hkm.le
  have hkp : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hmp : (0 : ℝ) < ((m - k : Nat) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hkm
  have hden : 0 < (k : ℝ) ^ k * ((m - k : Nat) : ℝ) ^ (m - k) := by positivity
  have hsquare : (m : ℝ) ^ m * (s : ℝ) ^ 2 ≤
      ((upper[k]?.getD 0 : Int) : ℝ) ^ 2 * (m.choose k : ℝ) ^ 2 * (k : ℝ) ^ k *
        ((m - k : Nat) : ℝ) ^ (m - k) := by exact_mod_cast h.2
  have hratio : (m : ℝ) ^ m / ((k : ℝ) ^ k * ((m - k : Nat) : ℝ) ^ (m - k)) ≤
      ((((upper[k]?.getD 0 : Int) : ℝ) / s) * (m.choose k : ℝ)) ^ 2 := by
    apply (div_le_iff₀ hden).2
    apply (mul_le_mul_iff_of_pos_right (pow_pos hsR 2)).1
    convert hsquare using 1 <;> field_simp <;> ring
  have hsqrt := Real.sqrt_le_sqrt hratio
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (mul_nonneg (div_nonneg ha hsR.le) hc.le)] at hsqrt
  unfold normalizedCauchyCoefficient
  exact (div_le_iff₀ hc).2 hsqrt

theorem commonCauchy_coeff_norm_bound {lo hi s m k : Nat} {upper : List Int}
    (hcheck : checkCommonCauchy lo hi s upper = true)
    (hlom : lo ≤ m) (hmhi : m ≤ hi) (hk3 : 3 ≤ k) (hk10 : k ≤ 10)
    {ι : Type*} (jset : Finset ι) (η : ι → ℂ) {V : ℝ}
    (hcard : jset.card = m) (hV : 0 < V) (hη : ∑ j ∈ jset, η j = 0)
    (hvariance : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (m : ℝ) * V) :
    ‖(centredGeneratingPolynomial jset η).coeff k‖ ≤
      (((upper[k]?.getD 0 : Int) : ℝ) / s) * (m.choose k : ℝ) * V ^ ((k : ℝ) / 2) := by
  have hlo := (checkCommonCauchy_sound lo hi s upper hcheck).1
  have hkm : k < m := by omega
  have hc : (0 : ℝ) < m.choose k := by exact_mod_cast Nat.choose_pos hkm.le
  have hbound := commonCauchy_coefficient_bound hcheck hlom hmhi hk3 hk10
  unfold normalizedCauchyCoefficient at hbound
  have hraw := (div_le_iff₀ hc).1 hbound
  have hvar : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (jset.card : ℝ) * V := by simpa [hcard] using hvariance
  have hcoeff := centredGeneratingPolynomial_coeff_cauchy jset η V hV hη hvar k
    (by omega) (by simpa [hcard] using hkm)
  rw [hcard] at hcoeff
  exact hcoeff.trans (mul_le_mul_of_nonneg_right hraw (Real.rpow_nonneg hV.le _))

end Schmeisser.Certificates

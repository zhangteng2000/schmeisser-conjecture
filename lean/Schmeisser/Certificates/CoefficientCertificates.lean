import Schmeisser.NewtonCoefficients
import Schmeisser.NormalizedCoefficients

open scoped BigOperators

namespace Schmeisser.Certificates

structure CoefficientTable where
  scale : Nat
  normalizedNewton : List Rat
  upper : List Int
  deriving DecidableEq, Repr

namespace CoefficientTable

def newton (t : CoefficientTable) (k : Nat) : Rat := t.normalizedNewton[k]?.getD 0

def numerator (t : CoefficientTable) (k : Nat) : Int := t.upper[k]?.getD 0

def upperRat (t : CoefficientTable) (k : Nat) : Rat := (t.numerator k : Rat) / t.scale

def Valid (t : CoefficientTable) (m : Nat) : Prop :=
  2 ≤ m ∧ 0 < t.scale ∧ t.normalizedNewton.length = m + 1 ∧ t.upper.length = m + 1 ∧
    t.newton 0 = 1 ∧ t.newton 1 = 0 ∧
    ∀ k : Fin (m + 1), 2 ≤ (k : Nat) →
      (k : Rat) * ((m - 1 : Nat) : Rat) * t.newton k =
        (m : Rat) * ∑ j ∈ Finset.range ((k : Nat) - 1), t.newton j ∧
      0 ≤ t.numerator k ∧
      (((m - 1 : Nat) : Rat) ^ (k : Nat) * (t.newton k) ^ 2 ≤
          (t.upperRat k * (Nat.fast_choose m k : Rat)) ^ 2 ∨
        (m : Rat) ^ m ≤ (t.upperRat k) ^ 2 * (Nat.fast_choose m k : Rat) ^ 2 *
          (k : Rat) ^ (k : Nat) * ((m - k : Nat) : Rat) ^ (m - k))

instance (t : CoefficientTable) (m : Nat) : Decidable (t.Valid m) := by
  unfold Valid
  infer_instance

def check (t : CoefficientTable) (m : Nat) : Bool := decide (t.Valid m)

theorem check_sound (t : CoefficientTable) (m : Nat) (h : t.check m = true) : t.Valid m :=
  of_decide_eq_true h

theorem newton_identity (t : CoefficientTable) (m : Nat) (h : t.Valid m)
    (k : Nat) (hkm : k ≤ m) :
    newtonMajorant m k = ((m : ℝ) - 1) ^ ((k : ℝ) / 2) * (t.newton k : ℝ) := by
  rcases h with ⟨hm, hs, hlen, halen, h0, h1, hrec⟩
  have hm1 : 1 ≤ m := by omega
  have hM : 0 ≤ (m : ℝ) - 1 := sub_nonneg.mpr (by exact_mod_cast hm1)
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => simp [newtonMajorant, h0]
    | succ k =>
      cases k with
      | zero => simp [newtonMajorant, h1]
      | succ k =>
        have hK : (0 : ℝ) < (k : ℝ) + 2 := by positivity
        have hrecRat := (hrec ⟨k + 2, by omega⟩ (by change 2 ≤ k + 2; omega)).1
        have hrecR : ((k : ℝ) + 2) * ((m : ℝ) - 1) * (t.newton (k + 2) : ℝ) =
            (m : ℝ) * ∑ j ∈ Finset.range (k + 1), (t.newton j : ℝ) := by
          have hr : (((k + 2 : Nat) : ℝ) * ((m - 1 : Nat) : ℝ)) * (t.newton (k + 2) : ℝ) =
              (m : ℝ) * ∑ j ∈ Finset.range (k + 2 - 1), (t.newton j : ℝ) := by
            exact_mod_cast hrecRat
          have he : k + 2 - 1 = k + 1 := by omega
          rw [he, Nat.cast_sub hm1, Nat.cast_one] at hr
          norm_num at hr
          exact hr
        have hsum : (∑ j ∈ Finset.range (k + 1),
            ((m : ℝ) - 1) ^ (((k - j : Nat) : ℝ) / 2) * newtonMajorant m j) =
            ((m : ℝ) - 1) ^ ((k : ℝ) / 2) *
              ∑ j ∈ Finset.range (k + 1), (t.newton j : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          have hjk : j ≤ k := by have := Finset.mem_range.mp hj; omega
          rw [ih j (by omega) (by omega)]
          rw [← mul_assoc, ← Real.rpow_add_of_nonneg hM (by positivity) (by positivity)]
          congr 2
          rw [Nat.cast_sub hjk]
          ring
        have hpow : ((m : ℝ) - 1) ^ (((k + 2 : Nat) : ℝ) / 2) =
            ((m : ℝ) - 1) ^ ((k : ℝ) / 2) * ((m : ℝ) - 1) := by
          have he : (((k + 2 : Nat) : ℝ) / 2) = (k : ℝ) / 2 + 1 := by push_cast; ring
          rw [he, Real.rpow_add_of_nonneg hM (by positivity) (by norm_num), Real.rpow_one]
        have hcoeff : (m : ℝ) / ((k : ℝ) + 2) *
            (∑ j ∈ Finset.range (k + 1), (t.newton j : ℝ)) =
            ((m : ℝ) - 1) * (t.newton (k + 2) : ℝ) := by
          rw [div_mul_eq_mul_div]
          apply (div_eq_iff (ne_of_gt hK)).2
          nlinarith only [hrecR]
        rw [newtonMajorant_recurrence, hsum, hpow]
        calc
          (m : ℝ) / ((k : ℝ) + 2) *
              (((m : ℝ) - 1) ^ ((k : ℝ) / 2) *
                ∑ j ∈ Finset.range (k + 1), (t.newton j : ℝ)) =
              ((m : ℝ) - 1) ^ ((k : ℝ) / 2) *
                ((m : ℝ) / ((k : ℝ) + 2) * ∑ j ∈ Finset.range (k + 1), (t.newton j : ℝ)) := by ring
          _ = ((m : ℝ) - 1) ^ ((k : ℝ) / 2) *
              (((m : ℝ) - 1) * (t.newton (k + 2) : ℝ)) := by rw [hcoeff]
          _ = _ := by ring

theorem newton_sq_identity (t : CoefficientTable) (m : Nat) (h : t.Valid m)
    (k : Nat) (hkm : k ≤ m) :
    (newtonMajorant m k) ^ 2 = ((m : ℝ) - 1) ^ k * (t.newton k : ℝ) ^ 2 := by
  have hm1 : 0 ≤ (m : ℝ) - 1 := sub_nonneg.mpr (by exact_mod_cast (show 1 ≤ m from Nat.le_trans (by decide) h.1))
  rw [t.newton_identity m h k hkm, mul_pow]
  congr 1
  calc
    (((m : ℝ) - 1) ^ ((k : ℝ) / 2)) ^ 2 =
        ((m : ℝ) - 1) ^ (((k : ℝ) / 2) * 2) := by rw [Real.rpow_mul hm1, Real.rpow_two]
    _ = ((m : ℝ) - 1) ^ (k : ℝ) := by congr 1; ring
    _ = ((m : ℝ) - 1) ^ k := Real.rpow_natCast _ _

theorem coeff_norm_bound (t : CoefficientTable) (m : Nat) (ht : t.check m = true)
    {ι : Type*} (jset : Finset ι) (η : ι → ℂ) (V : ℝ)
    (hcard : jset.card = m) (hV0 : 0 ≤ V) (hη : ∑ j ∈ jset, η j = 0)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (m : ℝ) * V)
    (k : Nat) (hk2 : 2 ≤ k) (hkm : k ≤ m) :
    ‖(centredGeneratingPolynomial jset η).coeff k‖ ≤
      (t.upperRat k : ℝ) * (m.choose k : ℝ) * V ^ ((k : ℝ) / 2) := by
  have hv := t.check_sound m ht
  have hm : 2 ≤ m := hv.1
  have hcpos : (0 : ℝ) < m.choose k := by exact_mod_cast Nat.choose_pos hkm
  have hcell := hv.2.2.2.2.2.2 ⟨k, by omega⟩ (by change 2 ≤ k; exact hk2)
  have haRat : 0 ≤ t.upperRat k := by
    unfold upperRat
    exact div_nonneg (by exact_mod_cast hcell.2.1) (by positivity)
  have ha : (0 : ℝ) ≤ (t.upperRat k : ℝ) := by exact_mod_cast haRat
  have hV' : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (jset.card : ℝ) * V := by simpa only [hcard] using hV
  by_cases hVz : V = 0
  · subst V
    have hp : centredGeneratingPolynomial jset η = 1 :=
      centredGeneratingPolynomial_eq_one_of_variance_zero jset η (by simpa using hV)
    rw [hp]
    simp only [Polynomial.coeff_one, ite_eq_right (by omega : k ≠ 0), norm_zero]
    positivity
  have hVpos : 0 < V := lt_of_le_of_ne hV0 (Ne.symm hVz)
  rcases hcell.2.2 with hnew | hcauchy
  · rw [← Nat.choose_eq_fast_choose] at hnew
    have hsquare : ((m : ℝ) - 1) ^ k * (t.newton k : ℝ) ^ 2 ≤
        ((t.upperRat k : ℝ) * (m.choose k : ℝ)) ^ 2 := by
      have hs : (((m - 1 : Nat) : ℝ) ^ k) * (t.newton k : ℝ) ^ 2 ≤
          ((t.upperRat k : ℝ) * (m.choose k : ℝ)) ^ 2 := by exact_mod_cast hnew
      simpa only [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one] using hs
    rw [← t.newton_sq_identity m hv k hkm] at hsquare
    have hmajor : newtonMajorant m k ≤ (t.upperRat k : ℝ) * (m.choose k : ℝ) := by
      have hnonneg := newtonMajorant_nonneg m k (by omega)
      nlinarith [mul_nonneg ha hcpos.le]
    have hcoeff := coeff_norm_le_newtonMajorant jset η V (by omega) hV0 hη hV' k
    rw [hcard] at hcoeff
    exact hcoeff.trans (mul_le_mul_of_nonneg_right hmajor (Real.rpow_nonneg hV0 _))
  · rw [← Nat.choose_eq_fast_choose] at hcauchy
    have hsquare : (m : ℝ) ^ m ≤ (t.upperRat k : ℝ) ^ 2 * (m.choose k : ℝ) ^ 2 *
        (k : ℝ) ^ k * ((m - k : Nat) : ℝ) ^ (m - k) := by exact_mod_cast hcauchy
    by_cases hkeq : k = m
    · subst k
      have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
      have hp : (0 : ℝ) < (m : ℝ) ^ m := pow_pos hmpos _
      simp only [Nat.choose_self, Nat.cast_one, Nat.sub_self, Nat.cast_zero, pow_zero,
        one_pow, mul_one] at hsquare
      have ha2 : (1 : ℝ) ≤ (t.upperRat m : ℝ) ^ 2 :=
        (mul_le_mul_iff_left₀ hp).mp (by simpa only [one_mul] using hsquare)
      have ha1 : (1 : ℝ) ≤ (t.upperRat m : ℝ) := by nlinarith
      have hcoeff := centredGeneratingPolynomial_coeff_card_bound jset η V hV0 hV'
      rw [hcard] at hcoeff
      simp only [Nat.choose_self, Nat.cast_one, mul_one]
      exact hcoeff.trans (by nlinarith [mul_le_mul_of_nonneg_right ha1 (Real.rpow_nonneg hV0 ((m : ℝ) / 2))])
    have hklt : k < m := lt_of_le_of_ne hkm hkeq
    have hkp : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hlp : (0 : ℝ) < ((m - k : Nat) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hklt
    have hden : 0 < (k : ℝ) ^ k * ((m - k : Nat) : ℝ) ^ (m - k) := by positivity
    have hratio : (m : ℝ) ^ m / ((k : ℝ) ^ k * ((m - k : Nat) : ℝ) ^ (m - k)) ≤
        ((t.upperRat k : ℝ) * (m.choose k : ℝ)) ^ 2 := by
      apply (div_le_iff₀ hden).2
      nlinarith only [hsquare]
    have hsqrt : Real.sqrt ((m : ℝ) ^ m /
        ((k : ℝ) ^ k * ((m - k : Nat) : ℝ) ^ (m - k))) ≤
        (t.upperRat k : ℝ) * (m.choose k : ℝ) := by
      simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (mul_nonneg ha hcpos.le)] using Real.sqrt_le_sqrt hratio
    have hcoeff := centredGeneratingPolynomial_coeff_cauchy jset η V hVpos hη hV' k
      (by omega) (by omega)
    rw [hcard] at hcoeff
    exact hcoeff.trans (mul_le_mul_of_nonneg_right hsqrt (Real.rpow_nonneg hV0 _))

end CoefficientTable

end Schmeisser.Certificates

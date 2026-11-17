import Schmeisser.Certificates.BlockExpressions
import Schmeisser.QuadraticTrapezoid
import Schmeisser.FiniteReduction
import Schmeisser.Certificates.GeometricErrorBridge

namespace Schmeisser.Certificates.Block

@[simp] theorem value_u (x : ℝ) (m : Nat) (κ : ℝ) : u.value (env x m κ) = x := rfl
@[simp] theorem value_degree (x : ℝ) (m : Nat) (κ : ℝ) : degree.value (env x m κ) = m := rfl
@[simp] theorem value_kap (x : ℝ) (m : Nat) (κ : ℝ) : kap.value (env x m κ) = κ := rfl

theorem value_index (x : ℝ) (m offset : Nat) (κ : ℝ) (hoff : offset ≤ m) :
    (index offset).value (env x m κ) = ((m - offset : Nat) : ℝ) := by
  simp [index, Expr.value, env, Nat.cast_sub hoff]

theorem value_eps (m : Nat) (κ : ℝ) {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    eps.value (env x m κ) = 1 - x := by
  simp [eps, Expr.value, env, max_eq_right (sub_nonneg.mpr hx1), min_eq_right (by linarith : 1 - x ≤ 1)]

theorem value_h (m : Nat) (κ : ℝ) {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    h.value (env x m κ) = comparisonDrop x κ := by
  simp [h, value_eps m κ hx hx1, comparisonDrop]

theorem value_d (m : Nat) (κ : ℝ) {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    d.value (env x m κ) = comparisonD x κ := by
  simp [d, value_h m κ hx hx1, comparisonD]

theorem value_b (m : Nat) (κ : ℝ) {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    b.value (env x m κ) = comparisonB x κ := by
  simp [b, value_h m κ hx hx1, comparisonB]

theorem value_mt (m : Nat) {x κ : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (hk : 0 ≤ κ) (hk4 : κ / x ≤ 4) :
    mt.value (env x m κ) =
      1 - κ ^ 2 * (1 - x) / (4 * x ^ 2 * comparisonD x κ) := by
  have hd := comparisonD_pos hx hx1.le hk
  have he : 0 < 1 - x := sub_pos.mpr hx1
  let t : ℝ := 1 - κ ^ 2 * (1 - x) / (4 * x ^ 2 * comparisonD x κ)
  have hident : comparisonMinimum x κ = (1 - x) * t :=
    comparisonMinimum_normalized x κ hx.ne' hd.ne'
  have hbounds := comparisonMinimum_bounds hx hx1.le hk hk4
  have ht0 : 0 ≤ t := by
    apply nonneg_of_mul_nonneg_left _ he
    rw [mul_comm, ← hident]
    exact hbounds.1
  have ht1 : t ≤ 1 := by
    apply (mul_le_mul_iff_of_pos_left he).mp
    simpa only [mul_one, ← hident] using hbounds.2
  simp only [mt, Expr.value, Expr.value_sub, Expr.value_div, Expr.value_pow,
    Int.cast_zero, Int.cast_one, Nat.cast_zero, Nat.cast_one,
    value_kap, value_u, value_eps m κ hx.le hx1.le, value_d m κ hx.le hx1.le]
  change min (max 0 t) 1 = t
  rw [max_eq_right ht0, min_eq_left ht1]

theorem value_mass (m : Nat) {x κ : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (hk : 0 ≤ κ) (hk4 : κ / x ≤ 4) :
    mass.value (env x m κ) = comparisonMinimum x κ := by
  have hd := comparisonD_pos hx hx1.le hk
  rw [mass, Expr.value_mul, value_eps m κ hx.le hx1.le, value_mt m hx hx1 hk hk4]
  exact (comparisonMinimum_normalized x κ hx.ne' hd.ne').symm

theorem value_mt_quotient (m : Nat) {x κ : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (hk : 0 ≤ κ) (hk4 : κ / x ≤ 4) :
    mt.value (env x m κ) = comparisonMinimum x κ / (1 - x) := by
  have he : 1 - x ≠ 0 := ne_of_gt (sub_pos.mpr hx1)
  have hm := value_mass m hx hx1 hk hk4
  rw [mass, Expr.value_mul, value_eps m κ hx.le hx1.le] at hm
  rw [← hm]
  field_simp

theorem value_te (m : Nat) (κ : ℝ) {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    te.value (env x m κ) = κ / (2 * x * comparisonD x κ) := by
  simp [te, value_d m κ hx hx1]

theorem value_correction (m : Nat) (κ : ℝ) {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    correction.value (env x m κ) = κ ^ 2 * (1 - x) / (4 * x ^ 3 * comparisonD x κ) := by
  simp [correction, value_eps m κ hx hx1, value_d m κ hx hx1]

theorem value_ac (m offset : Nat) (κ x : ℝ) (hoff : offset + 2 ≤ m) :
    (ac offset).value (env x m κ) =
      ((m - offset : Nat) : ℝ) / ((m - offset - 1 : Nat) : ℝ) := by
  have hm1 : (0 : ℝ) < ((m - offset : Nat) : ℝ) - 1 := by
    have hnat : 2 ≤ m - offset := by omega
    have hreal : (2 : ℝ) ≤ ((m - offset : Nat) : ℝ) := by exact_mod_cast hnat
    linarith
  simp only [ac, Expr.value_add, Expr.value_div, Expr.value_sub, Expr.value_ofNat,
    value_index x m offset κ (by omega), Nat.cast_one,
    Nat.cast_sub (by omega : 1 ≤ m - offset)]
  field_simp
  <;> ring

theorem value_epsHalf (lo hi m offset : Nat) (κ : ℝ) {x : ℝ}
    (hoff : offset ≤ m) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    (epsHalf lo hi offset).value (env x m κ) =
      (1 - x) ^ (((m - offset : Nat) : ℝ) / 2) := by
  simp only [epsHalf, Expr.value, value_eps m κ hx hx1, value_index x m offset κ hoff]

theorem basic_le_integral (m offset : Nat) (hoff : offset + 2 ≤ m)
    (quarter invEps : Bool) {x κ : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (hk : 0 ≤ κ) (hk4 : κ / x ≤ 4)
    (hquarter : quarter = true → (3 : ℝ) / 4 ≤ x) :
    (basic offset quarter invEps).value (env x m κ) ≤
      normalizedComparisonIntegral (m - offset) x κ := by
  have hlin := normalizedComparisonIntegral_ge_linear (m - offset) (by omega) hx hx1 hk hk4
  have hneg := normalizedComparisonIntegral_ge_negative (m - offset) hx hx1 hk hk4
  have hthree (h : quarter = true) := normalizedComparisonIntegral_ge_three
    (m - offset) (by omega) hx hx1 hk hk4 (by linarith [hquarter h])
  have hlin' : x⁻¹ ≤ normalizedComparisonIntegral (m - offset) x κ + (m - offset : Nat) := by
    simpa only [one_div, sub_le_iff_le_add] using hlin
  have hneg' : -((1 - x)⁻¹ * x⁻¹) ≤ normalizedComparisonIntegral (m - offset) x κ := by
    simpa only [neg_div, one_div, mul_inv_rev] using hneg
  have hthree' (h : quarter = true) : x⁻¹ ≤ normalizedComparisonIntegral (m - offset) x κ + 3 := by
    simpa only [one_div, sub_le_iff_le_add] using hthree h
  cases hq : quarter <;> cases hi : invEps
  · simpa [basic, Expr.value, value_index x m offset κ (by omega)] using hlin'
  · simpa [basic, Expr.value, value_index x m offset κ (by omega), value_eps m κ hx.le hx1.le] using
      And.intro hlin' hneg'
  · simpa [basic, Expr.value, value_index x m offset κ (by omega)] using
      And.intro hlin' (hthree' hq)
  · simpa [basic, Expr.value, value_index x m offset κ (by omega), value_eps m κ hx.le hx1.le] using
      And.intro (And.intro hlin' hneg') (hthree' hq)

theorem value_baseTwo (m : Nat) {x κ : ℝ} (hx : 0 < x) (hx1 : x < 1) (hk : 0 ≤ κ) :
    baseTwo.value (env x m κ) = normalizedComparisonIntegral 2 x κ := by
  rw [normalizedComparisonIntegral_two hx hx1 hk]
  simp [baseTwo]

theorem recurrence_le_integral (lo hi m offset steps : Nat) (kind : BaseKind)
    (hindex : offset + 2 * steps + 2 ≤ m)
    {x κ : ℝ} (hx : 0 < x) (hx1 : x < 1) (hk : 0 ≤ κ) (hk4 : κ / x ≤ 4)
    (hbase : (base (offset + 2 * steps) kind).value (env x m κ) ≤
      normalizedComparisonIntegral (m - (offset + 2 * steps)) x κ) :
    (recurrence lo hi offset steps kind).value (env x m κ) ≤
      normalizedComparisonIntegral (m - offset) x κ := by
  induction steps generalizing offset with
  | zero => simpa [recurrence] using hbase
  | succ steps ih =>
    have hshift : (offset + 2) + 2 * steps = offset + 2 * (steps + 1) := by omega
    have hprev := ih (offset + 2) (by omega) (by rw [hshift]; exact hbase)
    have hprev' : (recurrence lo hi (offset + 2) steps kind).value (env x m κ) ≤
        normalizedComparisonIntegral (m - offset - 2) x κ := by
      simpa only [Nat.sub_sub] using hprev
    have hstep := normalizedComparisonIntegral_step_lower (m - offset) (by omega)
      hx hx1 hk hk4 hprev'
    simpa only [recurrence, Expr.value_add, Expr.value_neg, Expr.value_mul, Expr.value_div,
      Expr.value_sub, Expr.value_ofNat, value_index x m offset κ (by omega),
      value_ac m offset κ x (by omega), value_u, value_correction m κ hx.le hx1.le,
      value_te m κ hx.le hx1.le, value_mass m hx hx1 hk hk4,
      value_epsHalf lo hi m offset κ (by omega) hx.le hx1.le,
      Nat.cast_sub (by omega : 1 ≤ m - offset), Nat.cast_one, neg_div] using hstep

theorem value_quadratic (m : Nat) (a : Expr) {x κ : ℝ}
    (hx : 0 < x) (hx1 : x < 1) (hk : 0 ≤ κ) (hk4 : κ / x ≤ 4) :
    (quadratic a).value (env x m κ) = comparisonQuadratic x κ (a.value (env x m κ)) := by
  have hd := comparisonD_pos hx hx1.le hk
  have hmin := (comparisonMinimum_bounds hx hx1.le hk hk4).1
  have hQ : 0 ≤ comparisonQuadratic x κ (a.value (env x m κ)) := by
    rw [comparisonQuadratic_eq_shifted _ _ _ hd.ne']
    exact shiftedQuadratic_nonneg _ _ _ _ hd.le hmin
  simp only [quadratic, Expr.value, Expr.value_add, Expr.value_sub, Expr.value_mul,
    Expr.value_pow, Expr.value_ofNat, value_u, value_h m κ hx.le hx1.le]
  norm_num only [Int.cast_natCast, Nat.cast_ofNat]
  change max 0 (comparisonQuadratic x κ (a.value (env x m κ))) = _
  exact max_eq_right hQ

theorem value_trapezoidPhi (m j : Nat) (hj : j < 16) {x κ : ℝ}
    (hx : 0 < x) (hx1 : x < 1) (hk : 0 ≤ κ) (hk4 : κ / x ≤ 4) :
    (trapezoidPhi j).value (env x m κ) =
      Real.sqrt (comparisonQuadratic x κ ((j : ℝ) / 16)) - (1 - (j : ℝ) / 16) := by
  let t : ℝ := (j : ℝ) / 16
  have ht : t < 1 := by
    apply (div_lt_one (by norm_num : (0 : ℝ) < 16)).mpr
    exact_mod_cast hj
  have hd := comparisonD_pos hx hx1.le hk
  have hmin := (comparisonMinimum_bounds hx hx1.le hk hk4).1
  have hQ : 0 ≤ comparisonQuadratic x κ t := by
    rw [comparisonQuadratic_eq_shifted _ _ _ hd.ne']
    exact shiftedQuadratic_nonneg _ _ _ _ hd.le hmin
  have hden : 0 < Real.sqrt (comparisonQuadratic x κ t) + 1 - t := by
    have hh := Real.sqrt_nonneg (comparisonQuadratic x κ t)
    linarith
  have hnum : (1 - x) * (t * (2 - t) - κ / x * t * (1 - t)) =
      comparisonQuadratic x κ t - (1 - t) ^ 2 := by
    unfold comparisonQuadratic comparisonDrop
    field_simp
    <;> ring
  have hrat : ((Expr.rat j 16).value (env x m κ)) = t := by simp [Expr.value, t]
  simp only [trapezoidPhi, Expr.value_div, Expr.value_mul, Expr.value_sub, Expr.value_add,
    Expr.value_ofNat, value_eps m κ hx.le hx1.le, value_kap, value_u,
    Expr.value, value_quadratic m (.rat j 16) hx hx1 hk hk4, hrat]
  norm_num only [Int.cast_natCast, Nat.cast_ofNat]
  change (1 - x) * (t * (2 - t) - κ / x * t * (1 - t)) /
    (Real.sqrt (comparisonQuadratic x κ t) + 1 - t) =
      Real.sqrt (comparisonQuadratic x κ t) - (1 - t)
  rw [hnum]
  apply (div_eq_iff hden.ne').mpr
  nlinarith [Real.sq_sqrt hQ]

theorem trapezoidCorrection_upper (m : Nat) {x κ : ℝ}
    (hx : 0 < x) (hx1 : x < 1) (hk : 0 ≤ κ) (hk4 : κ / x ≤ 4) :
    comparisonIntegral 1 x κ ≤ 1 + trapezoidCorrection.value (env x m κ) := by
  have ht := comparisonIntegral_one_le_composite_trapezoid hx hx1.le hk hk4 16 (by decide)
  have hsum : (Expr.sum ((List.range 15).map fun j => trapezoidPhi (j + 1))).value (env x m κ) =
      ∑ j ∈ Finset.range 15,
        (Real.sqrt (comparisonQuadratic x κ (((j : ℝ) + 1) / 16)) - (1 - ((j : ℝ) + 1) / 16)) := by
    rw [Expr.value_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    have hj0 : j < 15 := Finset.mem_range.mp hj
    simpa only [Nat.cast_add, Nat.cast_one] using value_trapezoidPhi m (j + 1) (by omega) hx hx1 hk hk4
  have hlin : (∑ j ∈ Finset.range 15, (1 - ((j : ℝ) + 1) / 16)) = 15 / 2 := by
    norm_num [Finset.sum_range_succ]
  simp only [trapezoidCorrection, Expr.value_div, Expr.value_add, Expr.value_mul,
    Expr.value_ofNat, Expr.value, value_eps m κ hx.le hx1.le, hsum, Finset.sum_sub_distrib, hlin]
  norm_num only [Nat.reduceSub, Nat.cast_ofNat] at ht
  exact ht.trans_eq (by ring)

theorem baseThree_le_integral (m : Nat) {x κ : ℝ}
    (hx : 0 < x) (hx1 : x < 1) (hk : 0 ≤ κ) (hk4 : κ / x ≤ 4) :
    baseThree.value (env x m κ) ≤ normalizedComparisonIntegral 3 x κ := by
  have ht := trapezoidCorrection_upper m hx hx1 hk hk4
  have hbound := normalizedComparisonIntegral_three_lower hx hx1 hk hk4 ht
  have he : (eps.half 3).value (env x m κ) = (1 - x) ^ (3 / 2 : ℝ) := by
    rw [Expr.value_half, value_eps m κ hx.le hx1.le]
    exact (rpow_half_eq_natPow_sqrt 3 (sub_nonneg.mpr hx1.le)).symm
  simpa only [baseThree, Expr.value_add, Expr.value_sub, Expr.value_div, Expr.value_mul,
    Expr.value_ofNat, value_u, value_te m κ hx.le hx1.le,
    value_mt_quotient m hx hx1 hk hk4, he, Nat.cast_ofNat, Nat.cast_one] using hbound

def BaseValid (n : Nat) (x : ℝ) : BaseKind → Prop
  | .basic quarter _ => quarter = true → (3 : ℝ) / 4 ≤ x
  | .exactTwo => n = 2
  | .trapezoidThree => n = 3

theorem base_le_integral (m offset : Nat) (kind : BaseKind)
    (hoff : offset + 2 ≤ m) {x κ : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (hk : 0 ≤ κ) (hk4 : κ / x ≤ 4) (hvalid : BaseValid (m - offset) x kind) :
    (base offset kind).value (env x m κ) ≤ normalizedComparisonIntegral (m - offset) x κ := by
  cases kind with
  | basic quarter invEps => exact basic_le_integral m offset hoff quarter invEps hx hx1 hk hk4 hvalid
  | exactTwo =>
    change m - offset = 2 at hvalid
    rw [hvalid]
    exact (value_baseTwo m hx hx1 hk).le
  | trapezoidThree =>
    change m - offset = 3 at hvalid
    rw [hvalid]
    exact baseThree_le_integral m hx hx1 hk hk4

theorem recurrence_valid_le_integral (lo hi m offset steps : Nat) (kind : BaseKind)
    (hindex : offset + 2 * steps + 2 ≤ m)
    {x κ : ℝ} (hx : 0 < x) (hx1 : x < 1) (hk : 0 ≤ κ) (hk4 : κ / x ≤ 4)
    (hvalid : BaseValid (m - (offset + 2 * steps)) x kind) :
    (recurrence lo hi offset steps kind).value (env x m κ) ≤
      normalizedComparisonIntegral (m - offset) x κ :=
  recurrence_le_integral lo hi m offset steps kind hindex hx hx1 hk hk4
    (base_le_integral m (offset + 2 * steps) kind (by omega) hx hx1 hk hk4 hvalid)

end Schmeisser.Certificates.Block

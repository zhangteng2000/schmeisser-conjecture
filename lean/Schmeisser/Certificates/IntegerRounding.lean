import Lean.Elab.Tactic.Omega

/-!
The integer rounding used by the independent scalar verifier.

These statements cover negative numerators as well as positive ones.
They do not trust any external arithmetic routine.
-/

namespace Schmeisser.Certificates

/-- Integer ceiling division, for use with a positive divisor. -/
def ceilDiv (a b : Int) : Int := -((-a) / b)

theorem floor_mul_le (a : Int) {b : Int} (hb : 0 < b) :
    a / b * b ≤ a :=
  Int.ediv_mul_le a (Int.ne_of_gt hb)

theorem lt_floor_add_one_mul (a : Int) {b : Int} (hb : 0 < b) :
    a < (a / b + 1) * b := by
  have h := Int.lt_ediv_mul a hb
  rw [Int.add_mul, Int.one_mul]
  omega

theorem le_ceil_mul (a : Int) {b : Int} (hb : 0 < b) :
    a ≤ ceilDiv a b * b := by
  have h := floor_mul_le (-a) hb
  simp only [ceilDiv, Int.neg_mul]
  omega

theorem ceil_sub_one_mul_lt (a : Int) {b : Int} (hb : 0 < b) :
    (ceilDiv a b - 1) * b < a := by
  have h := Int.lt_ediv_mul (-a) hb
  simp only [ceilDiv, Int.sub_mul, Int.neg_mul, Int.one_mul]
  omega

theorem floor_le_ceil (a : Int) {b : Int} (hb : 0 < b) :
    a / b ≤ ceilDiv a b := by
  apply Int.le_of_mul_le_mul_right _ hb
  exact Int.le_trans (floor_mul_le a hb) (le_ceil_mul a hb)

theorem ceil_le_iff (a c : Int) {b : Int} (hb : 0 < b) :
    ceilDiv a b ≤ c ↔ a ≤ c * b := by
  constructor
  · intro h
    exact Int.le_trans (le_ceil_mul a hb)
      (Int.mul_le_mul_of_nonneg_right h (Int.le_of_lt hb))
  · intro h
    have h' : (-c) * b ≤ -a := by
      rw [Int.neg_mul]
      omega
    have h'' := (Int.le_ediv_iff_mul_le hb).mpr h'
    unfold ceilDiv
    omega

theorem floor_mono {a c b : Int} (hb : 0 < b) (hac : a ≤ c) :
    a / b ≤ c / b := by
  apply (Int.le_ediv_iff_mul_le hb).mpr
  exact Int.le_trans (floor_mul_le a hb) hac

theorem ceil_mono {a c b : Int} (hb : 0 < b) (hac : a ≤ c) :
    ceilDiv a b ≤ ceilDiv c b := by
  apply (ceil_le_iff a (ceilDiv c b) hb).mpr
  exact Int.le_trans hac (le_ceil_mul c hb)

theorem rounded_width_le_one (a : Int) {b : Int} (hb : 0 < b) :
    ceilDiv a b ≤ a / b + 1 := by
  apply (ceil_le_iff a (a / b + 1) hb).mpr
  exact Int.le_of_lt (lt_floor_add_one_mul a hb)

end Schmeisser.Certificates

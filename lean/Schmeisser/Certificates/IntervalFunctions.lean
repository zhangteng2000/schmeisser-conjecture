import Schmeisser.Certificates.Interval
import Mathlib.Data.Nat.Sqrt

namespace Schmeisser.Certificates.Interval

def rational (s a b : Int) : Interval :=
  ⟨a * s / b, ceilDiv (a * s) b⟩

theorem contains_rational {s b : Int} (hs : 0 < s) (hb : 0 < b) (a : Int) :
    (rational s a b).Contains s ((a : ℝ) / b) := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  constructor
  · apply (div_le_div_iff₀ hs' hb').mpr
    exact_mod_cast floor_mul_le (a * s) hb
  · apply (div_le_div_iff₀ hb' hs').mpr
    exact_mod_cast le_ceil_mul (a * s) hb

def invPos (s : Int) (i : Interval) : Interval :=
  ⟨s * s / i.hi, ceilDiv (s * s) i.lo⟩

theorem contains_invPos {s : Int} (hs : 0 < s) {i : Interval} {x : ℝ}
    (hx : i.Contains s x) (hi : 0 < i.lo) :
    (i.invPos s).Contains s (1 / x) := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hlo' : (0 : ℝ) < i.lo := by exact_mod_cast hi
  have hlohi : i.lo ≤ i.hi := by
    obtain ⟨hxl, hxu⟩ := (contains_iff_scaled hs i x).mp hx
    exact_mod_cast hxl.trans hxu
  have hhi : 0 < i.hi := hi.trans_le hlohi
  have hlo : 0 < i.lower s := div_pos hlo' hs'
  have hxpos : 0 < x := hlo.trans_le hx.1
  constructor
  · calc
      (i.invPos s).lower s ≤ (s : ℝ) / i.hi := (contains_rational hs hhi s).1
      _ = 1 / i.upper s := by simp only [upper, one_div_div]
      _ ≤ 1 / x := one_div_le_one_div_of_le hxpos hx.2
  · calc
      1 / x ≤ 1 / i.lower s := one_div_le_one_div_of_le hlo hx.1
      _ = (s : ℝ) / i.lo := by simp only [lower, one_div_div]
      _ ≤ (i.invPos s).upper s := (contains_rational hs hi s).2

def inv (s : Int) (i : Interval) : Interval :=
  if 0 < i.lo then i.invPos s else (i.neg.invPos s).neg

theorem contains_inv {s : Int} (hs : 0 < s) {i : Interval} {x : ℝ}
    (hx : i.Contains s x) (hi : 0 < i.lo ∨ i.hi < 0) :
    (i.inv s).Contains s (1 / x) := by
  unfold inv
  split
  · rename_i hpos
    exact contains_invPos hs hx hpos
  · rename_i hnot
    have hneg : i.hi < 0 := hi.resolve_left hnot
    have hneglo : 0 < i.neg.lo := by change 0 < -i.hi; omega
    have h := contains_neg (contains_invPos hs (contains_neg hx) hneglo)
    simpa only [div_neg, neg_neg] using h

def div (s : Int) (i j : Interval) : Interval := i.mul s (j.inv s)

theorem contains_div {s : Int} (hs : 0 < s) {i j : Interval} {x y : ℝ}
    (hx : i.Contains s x) (hy : j.Contains s y) (hj : 0 < j.lo ∨ j.hi < 0) :
    (i.div s j).Contains s (x / y) := by
  change (i.mul s (j.inv s)).Contains s (x / y)
  rw [div_eq_mul_one_div]
  exact contains_mul hs hx (contains_inv hs hy hj)

/-- Exponentiation by squaring; all integer calculations remain executable. -/
def pow (s : Int) (i : Interval) (n : Nat) : Interval :=
  if hn : n = 0 then point s 1 else
    let q := i.pow s (n / 2)
    if n % 2 = 0 then q.mul s q else i.mul s (q.mul s q)
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)

theorem contains_pow {s : Int} (hs : 0 < s) {i : Interval} {x : ℝ}
    (hx : i.Contains s x) (n : Nat) : (i.pow s n).Contains s (x ^ n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simpa only [pow, ↓reduceDIte, pow_zero, Int.cast_one] using contains_point hs 1
    · have hn2 : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)
      have hq := ih (n / 2) hn2
      have hprod := contains_mul hs hq hq
      rw [pow, dite_eq_right hn]
      dsimp only
      split
      · rename_i heven
        have hn' : n / 2 + n / 2 = n := by omega
        simpa only [← pow_add, hn'] using hprod
      · rename_i hodd
        have hn' : n / 2 + n / 2 + 1 = n := by omega
        have hoddprod := contains_mul hs hx hprod
        simpa only [← pow_add, ← pow_succ', hn'] using hoddprod

/-- A square-root enclosure, rounded outward by at most one grid unit.
The upper endpoint always uses the successor of the integer square root. -/
def sqrt (s : Int) (i : Interval) : Interval :=
  ⟨Nat.sqrt (i.lo * s).toNat, Nat.sqrt (i.hi * s).toNat + 1⟩

theorem contains_sqrt {s : Int} (hs : 0 < s) {i : Interval} {x : ℝ}
    (hx : i.Contains s x) (hi : 0 ≤ i.lo) :
    (i.sqrt s).Contains s (Real.sqrt x) := by
  have hlohi : i.lo ≤ i.hi := by
    obtain ⟨hxl, hxu⟩ := (contains_iff_scaled hs i x).mp hx
    exact_mod_cast hxl.trans hxu
  have hlo : 0 ≤ i.lo * s := mul_nonneg hi hs.le
  have hhi : 0 ≤ i.hi * s := mul_nonneg (hi.trans hlohi) hs.le
  apply contains_sqrt_of_witness hs hx
  · omega
  · have h := Nat.sqrt_le (i.lo * s).toNat
    have h' : (Nat.sqrt (i.lo * s).toNat : Int) * Nat.sqrt (i.lo * s).toNat ≤
        ((i.lo * s).toNat : Int) := by exact_mod_cast h
    simpa only [Int.toNat_of_nonneg hlo] using h'
  · have h := Nat.le_of_lt (Nat.lt_succ_sqrt (i.hi * s).toNat)
    have h' : ((i.hi * s).toNat : Int) ≤
        ((Nat.sqrt (i.hi * s).toNat : Int) + 1) *
        ((Nat.sqrt (i.hi * s).toNat : Int) + 1) := by exact_mod_cast h
    simpa only [Int.toNat_of_nonneg hhi] using h'

def positive (i : Interval) : Interval := ⟨max 0 i.lo, max 0 i.hi⟩

theorem contains_positive {s : Int} (hs : 0 < s) {i : Interval} {x : ℝ}
    (hx : i.Contains s x) (hx0 : 0 ≤ x) : i.positive.Contains s x := by
  have h := contains_floor hs (contains_point hs 0) hx
  simpa only [floor, point, zero_mul, Int.cast_zero, max_eq_right hx0, positive] using h

end Schmeisser.Certificates.Interval

import Schmeisser.Certificates.IntegerRounding
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
Sound fixed-point interval operations.  Each interval has integer endpoints;
the positive scale is a parameter. The numerical certificates use `2^64`.
-/

namespace Schmeisser.Certificates

structure Interval where
  lo : Int
  hi : Int
  deriving Repr, DecidableEq

namespace Interval

noncomputable def lower (s : Int) (i : Interval) : ℝ := (i.lo : ℝ) / (s : ℝ)
noncomputable def upper (s : Int) (i : Interval) : ℝ := (i.hi : ℝ) / (s : ℝ)

def Contains (s : Int) (i : Interval) (x : ℝ) : Prop :=
  i.lower s ≤ x ∧ x ≤ i.upper s

def Lower (s : Int) (i : Interval) (x : ℝ) : Prop := i.lower s ≤ x
def Upper (s : Int) (i : Interval) (x : ℝ) : Prop := x ≤ i.upper s

def point (s a : Int) : Interval := ⟨a * s, a * s⟩
def add (i j : Interval) : Interval := ⟨i.lo + j.lo, i.hi + j.hi⟩
def neg (i : Interval) : Interval := ⟨-i.hi, -i.lo⟩
def sub (i j : Interval) : Interval := i.add j.neg
def cap (i j : Interval) : Interval := ⟨min i.lo j.lo, min i.hi j.hi⟩
def floor (i j : Interval) : Interval := ⟨max i.lo j.lo, max i.hi j.hi⟩
def meet (i j : Interval) : Interval := ⟨max i.lo j.lo, min i.hi j.hi⟩
def hull (i j : Interval) : Interval := ⟨min i.lo j.lo, max i.hi j.hi⟩

def min4 (a b c d : Int) : Int := min (min a b) (min c d)
def max4 (a b c d : Int) : Int := max (max a b) (max c d)

def prodLo (i j : Interval) : Int :=
  min4 (i.lo * j.lo) (i.lo * j.hi) (i.hi * j.lo) (i.hi * j.hi)
def prodHi (i j : Interval) : Int :=
  max4 (i.lo * j.lo) (i.lo * j.hi) (i.hi * j.lo) (i.hi * j.hi)
def mul (s : Int) (i j : Interval) : Interval :=
  ⟨i.prodLo j / s, ceilDiv (i.prodHi j) s⟩

theorem contains_iff_scaled {s : Int} (hs : 0 < s) (i : Interval) (x : ℝ) :
    i.Contains s x ↔ (i.lo : ℝ) ≤ x * s ∧ x * s ≤ i.hi := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  exact and_congr (div_le_iff₀ hs') (le_div_iff₀ hs')

theorem contains_point {s : Int} (hs : 0 < s) (a : Int) :
    (point s a).Contains s (a : ℝ) := by
  rw [contains_iff_scaled hs]
  simp [point]

theorem contains_add {s : Int} {i j : Interval} {x y : ℝ}
    (hx : i.Contains s x) (hy : j.Contains s y) :
    (i.add j).Contains s (x + y) := by
  simpa only [Contains, lower, upper, add, Int.cast_add, add_div] using
    And.intro (add_le_add hx.1 hy.1) (add_le_add hx.2 hy.2)

theorem contains_neg {s : Int} {i : Interval} {x : ℝ}
    (hx : i.Contains s x) : i.neg.Contains s (-x) := by
  simpa only [Contains, lower, upper, neg, Int.cast_neg, neg_div] using
    And.intro (neg_le_neg hx.2) (neg_le_neg hx.1)

theorem contains_sub {s : Int} {i j : Interval} {x y : ℝ}
    (hx : i.Contains s x) (hy : j.Contains s y) :
    (i.sub j).Contains s (x - y) := by
  simpa only [sub, sub_eq_add_neg] using contains_add hx (contains_neg hy)

theorem lower_cap {s : Int} (hs : 0 < s) (i j : Interval) :
    (i.cap j).lower s = min (i.lower s) (j.lower s) := by
  have hs' : (0 : ℝ) ≤ s := le_of_lt (by exact_mod_cast hs)
  simp only [lower, cap, Int.cast_min, min_div_div_right hs']

theorem upper_cap {s : Int} (hs : 0 < s) (i j : Interval) :
    (i.cap j).upper s = min (i.upper s) (j.upper s) := by
  have hs' : (0 : ℝ) ≤ s := le_of_lt (by exact_mod_cast hs)
  simp only [upper, cap, Int.cast_min, min_div_div_right hs']

theorem lower_floor {s : Int} (hs : 0 < s) (i j : Interval) :
    (i.floor j).lower s = max (i.lower s) (j.lower s) := by
  have hs' : (0 : ℝ) ≤ s := le_of_lt (by exact_mod_cast hs)
  simp only [lower, floor, Int.cast_max, max_div_div_right hs']

theorem upper_floor {s : Int} (hs : 0 < s) (i j : Interval) :
    (i.floor j).upper s = max (i.upper s) (j.upper s) := by
  have hs' : (0 : ℝ) ≤ s := le_of_lt (by exact_mod_cast hs)
  simp only [upper, floor, Int.cast_max, max_div_div_right hs']

theorem contains_cap {s : Int} (hs : 0 < s) {i j : Interval} {x y : ℝ}
    (hx : i.Contains s x) (hy : j.Contains s y) :
    (i.cap j).Contains s (min x y) := by
  exact ⟨by rw [lower_cap hs]; exact min_le_min hx.1 hy.1,
    by rw [upper_cap hs]; exact min_le_min hx.2 hy.2⟩

theorem contains_floor {s : Int} (hs : 0 < s) {i j : Interval} {x y : ℝ}
    (hx : i.Contains s x) (hy : j.Contains s y) :
    (i.floor j).Contains s (max x y) := by
  exact ⟨by rw [lower_floor hs]; exact max_le_max hx.1 hy.1,
    by rw [upper_floor hs]; exact max_le_max hx.2 hy.2⟩

theorem upper_cap_bound {s : Int} (hs : 0 < s) {i j : Interval} {x : ℝ}
    (hi : i.Upper s x) (hj : j.Upper s x) : (i.cap j).Upper s x := by
  unfold Upper at *
  rw [upper_cap hs]
  exact le_min hi hj

theorem lower_floor_bound {s : Int} (hs : 0 < s) {i j : Interval} {x : ℝ}
    (hi : i.Lower s x) (hj : j.Lower s x) : (i.floor j).Lower s x := by
  unfold Lower at *
  rw [lower_floor hs]
  exact max_le hi hj

theorem contains_meet {s : Int} (hs : 0 < s) {i j : Interval} {x : ℝ}
    (hi : i.Contains s x) (hj : j.Contains s x) :
    (i.meet j).Contains s x := by
  have hs' : (0 : ℝ) ≤ s := le_of_lt (by exact_mod_cast hs)
  constructor
  · simpa only [lower, meet, Int.cast_max, ← max_div_div_right hs'] using
      max_le hi.1 hj.1
  · simpa only [upper, meet, Int.cast_min, ← min_div_div_right hs'] using
      le_min hi.2 hj.2

private theorem linear_lower {a b x t z : ℝ} (ha : a ≤ x) (hb : x ≤ b)
    (hza : z ≤ a * t) (hzb : z ≤ b * t) : z ≤ x * t := by
  rcases le_total 0 t with ht | ht
  · exact hza.trans (mul_le_mul_of_nonneg_right ha ht)
  · exact hzb.trans (mul_le_mul_of_nonpos_right hb ht)

private theorem linear_upper {a b x t z : ℝ} (ha : a ≤ x) (hb : x ≤ b)
    (haz : a * t ≤ z) (hbz : b * t ≤ z) : x * t ≤ z := by
  rcases le_total 0 t with ht | ht
  · exact (mul_le_mul_of_nonneg_right hb ht).trans hbz
  · exact (mul_le_mul_of_nonpos_right ha ht).trans haz

private theorem corner_lower {a b c d x y z : ℝ}
    (ha : a ≤ x) (hb : x ≤ b) (hc : c ≤ y) (hd : y ≤ d)
    (hac : z ≤ a * c) (had : z ≤ a * d)
    (hbc : z ≤ b * c) (hbd : z ≤ b * d) : z ≤ x * y := by
  apply linear_lower ha hb
  · simpa only [mul_comm] using
      linear_lower (t := a) (z := z) hc hd (by simpa only [mul_comm] using hac)
        (by simpa only [mul_comm] using had)
  · simpa only [mul_comm] using
      linear_lower (t := b) (z := z) hc hd (by simpa only [mul_comm] using hbc)
        (by simpa only [mul_comm] using hbd)

private theorem corner_upper {a b c d x y z : ℝ}
    (ha : a ≤ x) (hb : x ≤ b) (hc : c ≤ y) (hd : y ≤ d)
    (hac : a * c ≤ z) (had : a * d ≤ z)
    (hbc : b * c ≤ z) (hbd : b * d ≤ z) : x * y ≤ z := by
  apply linear_upper ha hb
  · simpa only [mul_comm] using
      linear_upper (t := a) (z := z) hc hd (by simpa only [mul_comm] using hac)
        (by simpa only [mul_comm] using had)
  · simpa only [mul_comm] using
      linear_upper (t := b) (z := z) hc hd (by simpa only [mul_comm] using hbc)
        (by simpa only [mul_comm] using hbd)

theorem contains_mul {s : Int} (hs : 0 < s) {i j : Interval} {x y : ℝ}
    (hx : i.Contains s x) (hy : j.Contains s y) :
    (i.mul s j).Contains s (x * y) := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  obtain ⟨hxl, hxu⟩ := (contains_iff_scaled hs i x).mp hx
  obtain ⟨hyl, hyu⟩ := (contains_iff_scaled hs j y).mp hy
  have hlow : (i.prodLo j : ℝ) ≤ (x * s) * (y * s) := by
    apply corner_lower hxl hxu hyl hyu
    all_goals
      simp only [prodLo, min4, Int.cast_min, Int.cast_mul]
    · exact (min_le_left _ _).trans (min_le_left _ _)
    · exact (min_le_left _ _).trans (min_le_right _ _)
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  have hupp : (x * s) * (y * s) ≤ (i.prodHi j : ℝ) := by
    apply corner_upper hxl hxu hyl hyu
    all_goals
      simp only [prodHi, max4, Int.cast_max, Int.cast_mul]
    · exact (le_max_left _ _).trans (le_max_left _ _)
    · exact (le_max_right _ _).trans (le_max_left _ _)
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
  rw [contains_iff_scaled hs]
  constructor
  · apply (mul_le_mul_iff_of_pos_right hs').mp
    calc
      ((i.mul s j).lo : ℝ) * s ≤ (i.prodLo j : ℝ) := by
        exact_mod_cast floor_mul_le (i.prodLo j) hs
      _ ≤ (x * s) * (y * s) := hlow
      _ = (x * y * s) * s := by ring
  · apply (mul_le_mul_iff_of_pos_right hs').mp
    calc
      (x * y * s) * s = (x * s) * (y * s) := by ring
      _ ≤ (i.prodHi j : ℝ) := hupp
      _ ≤ ((i.mul s j).hi : ℝ) * s := by
        exact_mod_cast le_ceil_mul (i.prodHi j) hs

/-- Square-root witnesses can be produced externally. Only their integer
inequalities enter this theorem. -/
theorem contains_sqrt_of_witness {s : Int} (hs : 0 < s) {i : Interval}
    {x : ℝ} (hx : i.Contains s x) {a b : Int} (hb : 0 ≤ b)
    (ha2 : a * a ≤ i.lo * s) (hb2 : i.hi * s ≤ b * b) :
    (⟨a, b⟩ : Interval).Contains s (Real.sqrt x) := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  obtain ⟨hxl, hxu⟩ := (contains_iff_scaled hs i x).mp hx
  constructor
  · apply Real.le_sqrt_of_sq_le
    change ((a : ℝ) / s) ^ 2 ≤ x
    rw [div_pow]
    apply (div_le_iff₀ (pow_pos hs' 2)).mpr
    calc
      (a : ℝ) ^ 2 ≤ (i.lo : ℝ) * s := by
        rw [pow_two]
        exact_mod_cast ha2
      _ ≤ (x * s) * s := mul_le_mul_of_nonneg_right hxl hs'.le
      _ = x * (s : ℝ) ^ 2 := by ring
  · apply Real.sqrt_le_iff.mpr
    constructor
    · change 0 ≤ (b : ℝ) / s
      exact div_nonneg (by exact_mod_cast hb) hs'.le
    · change x ≤ ((b : ℝ) / s) ^ 2
      rw [div_pow]
      apply (le_div_iff₀ (pow_pos hs' 2)).mpr
      calc
        x * (s : ℝ) ^ 2 = (x * s) * s := by ring
        _ ≤ (i.hi : ℝ) * s := mul_le_mul_of_nonneg_right hxu hs'.le
        _ ≤ (b : ℝ) ^ 2 := by
          rw [pow_two]
          exact_mod_cast hb2

theorem strict_of_bounds {s : Int} (hs : 0 < s) {i j : Interval}
    {x y : ℝ} (hx : i.Lower s x) (hy : j.Upper s y) (hij : j.hi < i.lo) :
    y < x := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  apply lt_of_le_of_lt hy
  apply lt_of_lt_of_le _ hx
  exact (div_lt_div_iff_of_pos_right hs').mpr (by exact_mod_cast hij)

end Interval
end Schmeisser.Certificates

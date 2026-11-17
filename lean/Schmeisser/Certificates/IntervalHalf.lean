import Schmeisser.Certificates.IntervalFunctions
import Schmeisser.QuadraticIntegrals

namespace Schmeisser.Certificates.Interval

/-- A fixed half-integral power, using only integer arithmetic. -/
def half (s : Int) (i : Interval) (n : Nat) : Interval :=
  if n % 2 = 0 then i.pow s (n / 2)
  else (i.pow s (n / 2)).mul s (i.sqrt s)

theorem contains_half {s : Int} (hs : 0 < s) {i : Interval} {x : ℝ}
    (hx : i.Contains s x) (hi : 0 ≤ i.lo) (n : Nat) :
    (i.half s n).Contains s (x ^ ((n : ℝ) / 2)) := by
  have hx0 : 0 ≤ x := (div_nonneg (by exact_mod_cast hi)
    (by exact_mod_cast hs.le)).trans hx.1
  rw [Schmeisser.rpow_half_eq_natPow_sqrt n hx0]
  by_cases hn : n % 2 = 0
  · simpa only [half, hn, ↓reduceIte, mul_one] using contains_pow hs hx (n / 2)
  · simpa only [half, hn, ↓reduceIte] using
      contains_mul hs (contains_pow hs hx (n / 2)) (contains_sqrt hs hx hi)

/-- For a base in `[0,1]`, the larger exponent gives the lower endpoint. -/
def halfRange (s : Int) (i : Interval) (lo hi : Nat) : Interval :=
  ⟨(i.half s hi).lo, (i.half s lo).hi⟩

theorem contains_halfRange {s : Int} (hs : 0 < s) {i j : Interval}
    {x y : ℝ} (hx : i.Contains s x) (hy : j.Contains s y)
    (lo hi : Nat) (hi0 : 0 ≤ i.lo) (hi1 : i.hi ≤ s)
    (hj0 : (lo : Int) * s ≤ j.lo) (hj1 : j.hi ≤ (hi : Int) * s) :
    (i.halfRange s lo hi).Contains s (x ^ (y / 2)) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hx0 : 0 ≤ x := (div_nonneg (by exact_mod_cast hi0) hsR.le).trans hx.1
  have hx1 : x ≤ 1 := hx.2.trans (by
    rw [upper, div_le_one hsR]
    exact_mod_cast hi1)
  have hylo : (lo : ℝ) ≤ y := by
    have h := (contains_iff_scaled hs j y).mp hy
    apply (mul_le_mul_iff_of_pos_right hsR).mp
    have hcast : (lo : ℝ) * s ≤ j.lo := by exact_mod_cast hj0
    exact hcast.trans h.1
  have hyhi : y ≤ (hi : ℝ) := by
    have h := (contains_iff_scaled hs j y).mp hy
    apply (mul_le_mul_iff_of_pos_right hsR).mp
    exact h.2.trans (by exact_mod_cast hj1)
  constructor
  · exact (contains_half hs hx hi0 hi).1.trans
      (Real.rpow_le_rpow_of_exponent_ge' hx0 hx1
        (by have := (Nat.cast_nonneg lo : (0 : ℝ) ≤ lo); linarith : 0 ≤ y / 2)
        (by linarith))
  · exact (Real.rpow_le_rpow_of_exponent_ge' hx0 hx1
      (by positivity : 0 ≤ (lo : ℝ) / 2) (by linarith)).trans
      (contains_half hs hx hi0 lo).2

end Schmeisser.Certificates.Interval

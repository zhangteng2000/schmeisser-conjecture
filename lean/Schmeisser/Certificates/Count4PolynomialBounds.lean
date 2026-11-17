import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-! Exact polynomial inequalities for critical-point count four. -/

namespace Schmeisser

noncomputable def quinticGapPolynomial (u : ℝ) : ℝ :=
  -54 * u ^ 5 + 216 * u ^ 4 - 180 * u ^ 3 - 84 * u ^ 2 + 152 * u - 32

noncomputable def quinticSquaredGapPolynomial (u : ℝ) : ℝ :=
  quinticGapPolynomial u ^ 2 - 243 * u ^ 7 * (1 - u) * (5 - 4 * u) ^ 2

theorem quinticGapPolynomial_bernstein (t : ℝ) :
    (11 : ℝ) ^ 5 * quinticGapPolynomial ((8 + 3 * t) / 11) =
      2305632 * (1 - t) ^ 5 +
      11572968 * t * (1 - t) ^ 4 +
      23247972 * t ^ 2 * (1 - t) ^ 3 +
      23894112 * t ^ 3 * (1 - t) ^ 2 +
      12825516 * t ^ 4 * (1 - t) +
      2898918 * t ^ 5 := by
  unfold quinticGapPolynomial
  ring

theorem quinticSquaredGapPolynomial_bernstein (t : ℝ) :
    (11 : ℝ) ^ 10 * quinticSquaredGapPolynomial ((8 + 3 * t) / 11) =
      4507191124992 * (1 - t) ^ 10 +
      44808228343296 * t * (1 - t) ^ 9 +
      201395568078144 * t ^ 2 * (1 - t) ^ 8 +
      542198896024896 * t ^ 3 * (1 - t) ^ 7 +
      973752031465488 * t ^ 4 * (1 - t) ^ 6 +
      1224120955381632 * t ^ 5 * (1 - t) ^ 5 +
      1093115963639304 * t ^ 6 * (1 - t) ^ 4 +
      684493409577285 * t ^ 7 * (1 - t) ^ 3 +
      287088705734490 * t ^ 8 * (1 - t) ^ 2 +
      72641294516637 * t ^ 9 * (1 - t) +
      8403725570724 * t ^ 10 := by
  unfold quinticSquaredGapPolynomial quinticGapPolynomial
  ring

theorem quinticGapPolynomial_pos {u : ℝ} (hu : 8 / 11 ≤ u) (hu1 : u < 1) :
    0 < quinticGapPolynomial u := by
  let t := (11 * u - 8) / 3
  have ht0 : 0 ≤ t := by dsimp [t]; linarith
  have ht1 : 0 < 1 - t := by dsimp [t]; linarith
  have he : (8 + 3 * t) / 11 = u := by dsimp [t]; ring
  have hid := quinticGapPolynomial_bernstein t
  rw [he] at hid
  have hp : 0 < (11 : ℝ) ^ 5 * quinticGapPolynomial u := by
    rw [hid]
    positivity
  exact pos_of_mul_pos_right hp (by positivity)

theorem quinticSquaredGapPolynomial_pos {u : ℝ} (hu : 8 / 11 ≤ u) (hu1 : u < 1) :
    0 < quinticSquaredGapPolynomial u := by
  let t := (11 * u - 8) / 3
  have ht0 : 0 ≤ t := by dsimp [t]; linarith
  have ht1 : 0 < 1 - t := by dsimp [t]; linarith
  have he : (8 + 3 * t) / 11 = u := by dsimp [t]; ring
  have hid := quinticSquaredGapPolynomial_bernstein t
  rw [he] at hid
  have hp : 0 < (11 : ℝ) ^ 10 * quinticSquaredGapPolynomial u := by
    rw [hid]
    positivity
  exact pos_of_mul_pos_right hp (by positivity)

theorem quinticGapPolynomial_squared_gt {u : ℝ} (hu : 8 / 11 ≤ u) (hu1 : u < 1) :
    243 * u ^ 7 * (1 - u) * (5 - 4 * u) ^ 2 < quinticGapPolynomial u ^ 2 := by
  exact sub_pos.mp (quinticSquaredGapPolynomial_pos hu hu1)

end Schmeisser

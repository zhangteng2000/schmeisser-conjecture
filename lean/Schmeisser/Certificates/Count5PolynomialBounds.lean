import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-! An exact polynomial inequality for critical-point count five. -/

namespace Schmeisser

noncomputable def sexticGapPolynomial (t : ℝ) : ℝ :=
  -573440 * t ^ 20 + 573440 * t ^ 19 + 2007040 * t ^ 18 + 1089536 * t ^ 17 -
    5794816 * t ^ 16 - 2855936 * t ^ 15 + 7402496 * t ^ 14 + 6430720 * t ^ 13 -
    9216000 * t ^ 12 - 8044032 * t ^ 11 + 5388672 * t ^ 10 + 7448832 * t ^ 9 -
    1283632 * t ^ 8 - 5409200 * t ^ 7 - 953185 * t ^ 6 + 2510896 * t ^ 5 +
    2315344 * t ^ 4 - 1396096 * t ^ 3 - 17024 * t ^ 2 - 348160 * t + 184320

theorem sexticGapPolynomial_bernstein (x : ℝ) :
    19073486328125 * sexticGapPolynomial (3 * x / 5) =
      3515625000000000000 * (1 - x) ^ 20 +
      66328125000000000000 * x * (1 - x) ^ 19 +
      592148730468750000000 * x ^ 2 * (1 - x) ^ 18 +
      3318628535156250000000 * x ^ 3 * (1 - x) ^ 17 +
      13062402689941406250000 * x ^ 4 * (1 - x) ^ 16 +
      38280487866503906250000 * x ^ 5 * (1 - x) ^ 15 +
      86408248144207763671875 * x ^ 6 * (1 - x) ^ 14 +
      153317837723400878906250 * x ^ 7 * (1 - x) ^ 13 +
      216332605996170556640625 * x ^ 8 * (1 - x) ^ 12 +
      243979176291012070312500 * x ^ 9 * (1 - x) ^ 11 +
      219819406148155435546875 * x ^ 10 * (1 - x) ^ 10 +
      157252371044248221093750 * x ^ 11 * (1 - x) ^ 9 +
      88191178670915581640625 * x ^ 12 * (1 - x) ^ 8 +
      37957326444651155625000 * x ^ 13 * (1 - x) ^ 7 +
      12131943833716769840625 * x ^ 14 * (1 - x) ^ 6 +
      2755168752290909073750 * x ^ 15 * (1 - x) ^ 5 +
      438271842245977654875 * x ^ 16 * (1 - x) ^ 4 +
      64743486931076303700 * x ^ 17 * (1 - x) ^ 3 +
      15297185538184979025 * x ^ 18 * (1 - x) ^ 2 +
      3249109583598477930 * x ^ 19 * (1 - x) +
      298112525310436467 * x ^ 20 := by
  unfold sexticGapPolynomial
  ring

theorem sexticGapPolynomial_pos {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 3 / 5) :
    0 < sexticGapPolynomial t := by
  let x := 5 * t / 3
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx1 : 0 < 1 - x := by dsimp [x]; linarith
  have he : 3 * x / 5 = t := by dsimp [x]; ring
  have hid := sexticGapPolynomial_bernstein x
  rw [he] at hid
  have hp : 0 < 19073486328125 * sexticGapPolynomial t := by
    rw [hid]
    positivity
  exact pos_of_mul_pos_right hp (by positivity)

end Schmeisser

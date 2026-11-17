import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

namespace Schmeisser

noncomputable def septicGapPolynomial (t : ℝ) : ℝ :=
  64800 * t ^ 17 +
    302400 * t ^ 16 +
    228528 * t ^ 15 -
    2332800 * t ^ 14 -
    2368872 * t ^ 13 +
    5097600 * t ^ 12 +
    5643972 * t ^ 11 -
    3430080 * t ^ 10 -
    5765580 * t ^ 9 -
    787680 * t ^ 8 +
    2372760 * t ^ 7 +
    1586040 * t ^ 6 -
    44928 * t ^ 5 -
    376115 * t ^ 4 -
    90828 * t ^ 3 -
    88080 * t ^ 2 -
    39852 * t +
    53280

theorem septicGapPolynomial_bernstein_left (x : ℝ) :
    2147483648000000000000000 * septicGapPolynomial (13 * x / 40) =
      114417928765440000000000000000 * (1 - x) ^ 17 +
      1917290795551948800000000000000 * x * (1 - x) ^ 16 +
      15095835409986355200000000000000 * x ^ 2 * (1 - x) ^ 15 +
      74160131486817189888000000000000 * x ^ 3 * (1 - x) ^ 14 +
      254538286586522501120000000000000 * x ^ 4 * (1 - x) ^ 13 +
      647579417328813520977920000000000 * x ^ 5 * (1 - x) ^ 12 +
      1264133103030068544798720000000000 * x ^ 6 * (1 - x) ^ 11 +
      1933211810603715958145024000000000 * x ^ 7 * (1 - x) ^ 10 +
      2343627994265735335352729600000000 * x ^ 8 * (1 - x) ^ 9 +
      2263838547294110530255749120000000 * x ^ 9 * (1 - x) ^ 8 +
      1741269724392934899635257344000000 * x ^ 10 * (1 - x) ^ 7 +
      1059644828076522424010062663680000 * x ^ 11 * (1 - x) ^ 6 +
      503540054396834444990011514880000 * x ^ 12 * (1 - x) ^ 5 +
      182773412815793082127884503628800 * x ^ 13 * (1 - x) ^ 4 +
      48894969170569477335069308979200 * x ^ 14 * (1 - x) ^ 3 +
      9075930171546516795018827796192 * x ^ 15 * (1 - x) ^ 2 +
      1042772423141631833520982045904 * x ^ 16 * (1 - x) +
      55789032388142955119523172685 * x ^ 17 := by
  unfold septicGapPolynomial
  ring

theorem septicGapPolynomial_bernstein_right (x : ℝ) :
    2147483648000000000000000 * septicGapPolynomial ((13 + 13 * x) / 40) =
      55789032388142955119523172685 * (1 - x) ^ 17 +
      854054678055228640542805825386 * x * (1 - x) ^ 16 +
      6056446250164065707368008267904 * x ^ 2 * (1 - x) ^ 15 +
      26344509059340422275630202279040 * x ^ 3 * (1 - x) ^ 14 +
      78430845755357887431294376806720 * x ^ 4 * (1 - x) ^ 13 +
      168773800642013483054793674847360 * x ^ 5 * (1 - x) ^ 12 +
      270078975394876613200338561442816 * x ^ 6 * (1 - x) ^ 11 +
      325383096219488003030791397351424 * x ^ 7 * (1 - x) ^ 10 +
      295018665250860678084855309800960 * x ^ 8 * (1 - x) ^ 9 +
      198647212298475548580293774535680 * x ^ 9 * (1 - x) ^ 8 +
      96458343010217820814556531589120 * x ^ 10 * (1 - x) ^ 7 +
      32158139153161182221661668933632 * x ^ 11 * (1 - x) ^ 6 +
      7108235680927155607327000117248 * x ^ 12 * (1 - x) ^ 5 +
      1487071953529196907506546933760 * x ^ 13 * (1 - x) ^ 4 +
      669910509473368590748888596480 * x ^ 14 * (1 - x) ^ 3 +
      289499778694827246750694113280 * x ^ 15 * (1 - x) ^ 2 +
      66262550260613088053096153088 * x ^ 16 * (1 - x) +
      6089652469137211160419500032 * x ^ 17 := by
  unfold septicGapPolynomial
  ring

theorem septicGapPolynomial_pos {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 13 / 20) :
    0 < septicGapPolynomial t := by
  by_cases hhalf : t < 13 / 40
  · let x := 40 * t / 13
    have hx0 : 0 ≤ x := by dsimp [x]; positivity
    have hx1 : 0 < 1 - x := by dsimp [x]; linarith
    have he : 13 * x / 40 = t := by dsimp [x]; ring
    have hid := septicGapPolynomial_bernstein_left x
    rw [he] at hid
    have hp : 0 < 2147483648000000000000000 * septicGapPolynomial t := by
      rw [hid]
      positivity
    exact pos_of_mul_pos_right hp (by positivity)
  · let x := 40 * t / 13 - 1
    have hx0 : 0 ≤ x := by dsimp [x]; linarith
    have hx1 : 0 < 1 - x := by dsimp [x]; linarith
    have he : (13 + 13 * x) / 40 = t := by dsimp [x]; ring
    have hid := septicGapPolynomial_bernstein_right x
    rw [he] at hid
    have hp : 0 < 2147483648000000000000000 * septicGapPolynomial t := by
      rw [hid]
      positivity
    exact pos_of_mul_pos_right hp (by positivity)

end Schmeisser

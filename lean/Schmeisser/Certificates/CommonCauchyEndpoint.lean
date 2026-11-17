import Schmeisser.Certificates.CommonCoefficients
import Schmeisser.CauchyMonotonicity

namespace Schmeisser.Certificates

/-- A degree block needs only the eight coefficient checks at its left endpoint. -/
theorem checkCommonCauchy_of_endpoint (lo hi s : ℕ) (upper : List Int)
    (hlohi : lo ≤ hi) (hendpoint : checkCommonCauchy lo lo s upper = true) :
    checkCommonCauchy lo hi s upper = true := by
  rw [checkCommonCauchy, decide_eq_true_eq]
  rcases checkCommonCauchy_sound lo lo s upper hendpoint with ⟨hlo, _, hs, hcells⟩
  refine ⟨hlo, hlohi, hs, ?_⟩
  intro j q
  have hcell := hcells ⟨0, by omega⟩ q
  simp only [Nat.add_zero] at hcell
  have hmlo : lo ≤ lo + (j : ℕ) := Nat.le_add_right _ _
  have hk : 1 ≤ (q : ℕ) + 3 := by omega
  have hklo : (q : ℕ) + 3 < lo := by have := q.isLt; omega
  have hkm : (q : ℕ) + 3 < lo + (j : ℕ) := hklo.trans_le hmlo
  have hcoef := commonCauchy_coefficient_bound hendpoint le_rfl le_rfl
    (show 3 ≤ (q : ℕ) + 3 by omega) (show (q : ℕ) + 3 ≤ 10 by have := q.isLt; omega)
  have hmono := normalizedCauchyCoefficient_antitone hk hklo hmlo
  have ha : (0 : ℝ) ≤ (upper[(q : ℕ) + 3]?.getD 0 : Int) := by exact_mod_cast hcell.1
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hsquare := (normalizedCauchyCoefficient_le_iff_sq hk hkm ha hsR).1 (hmono.trans hcoef)
  dsimp only
  refine ⟨hcell.1, ?_⟩
  rw [← Nat.choose_eq_fast_choose]
  exact_mod_cast hsquare

end Schmeisser.Certificates

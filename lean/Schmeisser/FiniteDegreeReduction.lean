import Schmeisser.Certificates.VerifiedCoverage
import Schmeisser.Certificates.BlockVerification
import Schmeisser.QuarticAnalytic
import Schmeisser.QuinticAnalytic
import Schmeisser.SexticAnalytic
import Schmeisser.SepticAnalytic

namespace Schmeisser

open MeasureTheory

theorem finite_degree_scalar_exclusion_of_verified_blocks
    (blocks : List Certificates.Finite.VerifiedBlock)
    (hcoverage : Certificates.Finite.checkCoverageFrom 7 blocks = true)
    {ι : Type*} [DecidableEq ι]
    (jset : Finset ι) (η : ι → ℂ) (m : ℕ) (hm3 : 3 ≤ m) (hm6000 : m < 6000)
    (hcard : jset.card = m) {u h : ℝ}
    (hu0 : 0 < u) (hu1 : u < 1) (hh0 : 0 < h) (hh1 : h < 1)
    (hη : ∑ j ∈ jset, η j = 0)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (m : ℝ) * (u * (1 - u)))
    (hpolar : 1 ≤ ∫ t : ℝ in 0..1, (1 - h + h * (1 + u) * t) ^ ((m : ℝ) / 2)) :
    ((m : ℝ) + 1) * (∫ t : ℝ in 0..1,
      (max (1 - 2 * u * t + u * t ^ 2 - h * t * (1 - t)) 0) ^ ((m : ℝ) / 2)) <
      (((m : ℝ) + 1) * ∫ t : ℝ in 0..1, (1 - u * t) ^ m) -
        centeredErrorIntegral jset η m u := by
  by_cases hm : m = 3
  · rw [hm] at hcard hV hpolar ⊢
    simpa only [Nat.cast_ofNat, show (3 : ℝ) + 1 = 4 by norm_num] using
      quartic_scalar_exclusion jset η hcard hu0 hu1 hh0 hh1 hη hV hpolar
  by_cases hm4 : m = 4
  · rw [hm4] at hcard hV hpolar ⊢
    simpa only [Nat.cast_ofNat, show (4 : ℝ) + 1 = 5 by norm_num,
      show (4 : ℝ) / 2 = 2 by norm_num] using
      quintic_scalar_exclusion jset η hcard hu0 hu1 hh0 hh1 hη hV
        (by simpa only [Nat.cast_ofNat, show (4 : ℝ) / 2 = 2 by norm_num] using hpolar)
  by_cases hm5 : m = 5
  · rw [hm5] at hcard hV hpolar ⊢
    simpa only [Nat.cast_ofNat, show (5 : ℝ) + 1 = 6 by norm_num] using
      sextic_scalar_exclusion jset η hcard hu0 hu1 hh0 hh1 hη hV hpolar
  by_cases hm6 : m = 6
  · rw [hm6] at hcard hV hpolar ⊢
    simpa only [Nat.cast_ofNat, show (6 : ℝ) + 1 = 7 by norm_num,
      show (6 : ℝ) / 2 = 3 by norm_num] using
      septic_scalar_exclusion jset η hcard hu0 hu1 hh0 hh1 hη hV
        (by simpa only [Nat.cast_ofNat, show (6 : ℝ) / 2 = 3 by norm_num] using hpolar)
  obtain ⟨block, _, hlo, hhi⟩ :=
    Certificates.Finite.checkCoverageFrom_sound 7 blocks hcoverage m (by omega) hm6000
  exact block.scalar_exclusion jset η m hlo hhi hcard hη hu0 hu1 hh0 hh1 hV hpolar

end Schmeisser

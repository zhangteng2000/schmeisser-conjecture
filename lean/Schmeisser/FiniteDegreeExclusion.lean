import Schmeisser.Certificates.Generated.AllVerified
import Schmeisser.FiniteDegreeReduction

namespace Schmeisser

open MeasureTheory

theorem finite_degree_scalar_exclusion {ι : Type*} [DecidableEq ι]
    (jset : Finset ι) (η : ι → ℂ) (m : ℕ) (hm3 : 3 ≤ m) (hm6000 : m < 6000)
    (hcard : jset.card = m) {u h : ℝ}
    (hu0 : 0 < u) (hu1 : u < 1) (hh0 : 0 < h) (hh1 : h < 1)
    (hη : ∑ j ∈ jset, η j = 0)
    (hV : ∑ j ∈ jset, ‖η j‖ ^ 2 ≤ (m : ℝ) * (u * (1 - u)))
    (hpolar : 1 ≤ ∫ t : ℝ in 0..1, (1 - h + h * (1 + u) * t) ^ ((m : ℝ) / 2)) :
    ((m : ℝ) + 1) * (∫ t : ℝ in 0..1,
      (max (1 - 2 * u * t + u * t ^ 2 - h * t * (1 - t)) 0) ^ ((m : ℝ) / 2)) <
      (((m : ℝ) + 1) * ∫ t : ℝ in 0..1, (1 - u * t) ^ m) -
        centeredErrorIntegral jset η m u :=
  finite_degree_scalar_exclusion_of_verified_blocks
    Certificates.Finite.Generated.blocks Certificates.Finite.Generated.coverage_checked
    jset η m hm3 hm6000 hcard hu0 hu1 hh0 hh1 hη hV hpolar

end Schmeisser

import Schmeisser.Certificates.BlockSoundness
import Schmeisser.Certificates.CommonCoefficients

namespace Schmeisser.Certificates.Finite

/-- The upper coefficients come either from a full single-degree table or
from the common Cauchy bounds for a nontrivial degree block. -/
def Data.CoefficientsValid (data : Data) : Prop :=
  (data.lo = data.hi ∧ ∃ table : CoefficientTable,
    table.scale = scaleNat ∧ table.upper = data.upper ∧ table.check data.lo = true) ∨
  (data.lo < data.hi ∧ checkCommonCauchy data.lo data.hi scaleNat data.upper = true)

structure VerifiedBlock where
  data : Data
  segments : List Segment
  data_checked : data.check = true
  coefficients_valid : data.CoefficientsValid
  segments_checked : checkSegments data 0 scale segments = true

end Schmeisser.Certificates.Finite

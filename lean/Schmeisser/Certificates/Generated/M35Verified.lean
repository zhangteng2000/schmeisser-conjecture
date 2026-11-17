import Schmeisser.Certificates.VerifiedBlock
import Schmeisser.Certificates.Generated.M35Chunk0
import Schmeisser.Certificates.Generated.M35Chunk1

namespace Schmeisser.Certificates.Finite.Generated.M35

set_option maxHeartbeats 0
set_option maxRecDepth 65536

def segments : List Segment := segments0 ++ segments1

theorem segments_checked : checkSegments data 0 scale segments = true := by
  unfold segments
  apply checkSegments_append data segments0 (segments1) 0 9223372036854775808 scale segments0_checked
  exact segments1_checked

def verified : VerifiedBlock where
  data := data
  segments := segments
  data_checked := data_checked
  coefficients_valid := by
    left
    refine ⟨rfl, coefficients, ?_, rfl, coefficients_checked⟩
    decide
  segments_checked := segments_checked

end Schmeisser.Certificates.Finite.Generated.M35

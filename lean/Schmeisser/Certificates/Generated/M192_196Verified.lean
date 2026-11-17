import Schmeisser.Certificates.VerifiedBlock
import Schmeisser.Certificates.Generated.M192_196Chunk0

namespace Schmeisser.Certificates.Finite.Generated.M192_196

set_option maxHeartbeats 0
set_option maxRecDepth 65536

def segments : List Segment := segments0

theorem segments_checked : checkSegments data 0 scale segments = true := by
  unfold segments
  exact segments0_checked

def verified : VerifiedBlock where
  data := data
  segments := segments
  data_checked := data_checked
  coefficients_valid := by
    right
    exact ⟨by decide, common_coefficients_checked⟩
  segments_checked := segments_checked

end Schmeisser.Certificates.Finite.Generated.M192_196

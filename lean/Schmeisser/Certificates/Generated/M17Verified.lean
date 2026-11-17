import Schmeisser.Certificates.VerifiedBlock
import Schmeisser.Certificates.Generated.M17Chunk0
import Schmeisser.Certificates.Generated.M17Chunk1
import Schmeisser.Certificates.Generated.M17Chunk2

namespace Schmeisser.Certificates.Finite.Generated.M17

set_option maxHeartbeats 0
set_option maxRecDepth 65536

def segments : List Segment := segments0 ++ segments1 ++ segments2

theorem segments_checked : checkSegments data 0 scale segments = true := by
  unfold segments
  apply checkSegments_append data segments0 (segments1 ++ segments2) 0 9511602413006487552 scale segments0_checked
  apply checkSegments_append data segments1 (segments2) 9511602413006487552 16140901064495857664 scale segments1_checked
  exact segments2_checked

def verified : VerifiedBlock where
  data := data
  segments := segments
  data_checked := data_checked
  coefficients_valid := by
    left
    refine ⟨rfl, coefficients, ?_, rfl, coefficients_checked⟩
    decide
  segments_checked := segments_checked

end Schmeisser.Certificates.Finite.Generated.M17

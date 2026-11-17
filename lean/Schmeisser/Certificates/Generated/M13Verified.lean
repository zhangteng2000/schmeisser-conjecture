import Schmeisser.Certificates.VerifiedBlock
import Schmeisser.Certificates.Generated.M13Chunk0
import Schmeisser.Certificates.Generated.M13Chunk1
import Schmeisser.Certificates.Generated.M13Chunk2
import Schmeisser.Certificates.Generated.M13Chunk3

namespace Schmeisser.Certificates.Finite.Generated.M13

set_option maxHeartbeats 0
set_option maxRecDepth 65536

def segments : List Segment := segments0 ++ segments1 ++ segments2 ++ segments3

theorem segments_checked : checkSegments data 0 scale segments = true := by
  unfold segments
  apply checkSegments_append data segments0 (segments1 ++ segments2 ++ segments3) 0 8935141660703064064 scale segments0_checked
  apply checkSegments_append data segments1 (segments2 ++ segments3) 8935141660703064064 11240984669916758016 scale segments1_checked
  apply checkSegments_append data segments2 (segments3) 11240984669916758016 13546827679130451968 scale segments2_checked
  exact segments3_checked

def verified : VerifiedBlock where
  data := data
  segments := segments
  data_checked := data_checked
  coefficients_valid := by
    left
    refine ⟨rfl, coefficients, ?_, rfl, coefficients_checked⟩
    decide
  segments_checked := segments_checked

end Schmeisser.Certificates.Finite.Generated.M13

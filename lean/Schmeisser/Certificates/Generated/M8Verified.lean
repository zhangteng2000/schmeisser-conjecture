import Schmeisser.Certificates.VerifiedBlock
import Schmeisser.Certificates.Generated.M8Chunk0
import Schmeisser.Certificates.Generated.M8Chunk1
import Schmeisser.Certificates.Generated.M8Chunk2
import Schmeisser.Certificates.Generated.M8Chunk3
import Schmeisser.Certificates.Generated.M8Chunk4
import Schmeisser.Certificates.Generated.M8Chunk5

namespace Schmeisser.Certificates.Finite.Generated.M8

set_option maxHeartbeats 0
set_option maxRecDepth 65536

def segments : List Segment := segments0 ++ segments1 ++ segments2 ++ segments3 ++ segments4 ++ segments5

theorem segments_checked : checkSegments data 0 scale segments = true := by
  unfold segments
  apply checkSegments_append data segments0 (segments1 ++ segments2 ++ segments3 ++ segments4 ++ segments5) 0 11421128655011577856 scale segments0_checked
  apply checkSegments_append data segments1 (segments2 ++ segments3 ++ segments4 ++ segments5) 11421128655011577856 12574050159618424832 scale segments1_checked
  apply checkSegments_append data segments2 (segments3 ++ segments4 ++ segments5) 12574050159618424832 13726971664225271808 scale segments2_checked
  apply checkSegments_append data segments3 (segments4 ++ segments5) 13726971664225271808 15150109146474348544 scale segments3_checked
  apply checkSegments_append data segments4 (segments5) 15150109146474348544 16429131440647569408 scale segments4_checked
  exact segments5_checked

def verified : VerifiedBlock where
  data := data
  segments := segments
  data_checked := data_checked
  coefficients_valid := by
    left
    refine ⟨rfl, coefficients, ?_, rfl, coefficients_checked⟩
    decide
  segments_checked := segments_checked

end Schmeisser.Certificates.Finite.Generated.M8

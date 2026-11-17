import Schmeisser.Certificates.VerifiedBlock
import Schmeisser.Certificates.Generated.M11Chunk0
import Schmeisser.Certificates.Generated.M11Chunk1
import Schmeisser.Certificates.Generated.M11Chunk2
import Schmeisser.Certificates.Generated.M11Chunk3
import Schmeisser.Certificates.Generated.M11Chunk4
import Schmeisser.Certificates.Generated.M11Chunk5
import Schmeisser.Certificates.Generated.M11Chunk6

namespace Schmeisser.Certificates.Finite.Generated.M11

set_option maxHeartbeats 0
set_option maxRecDepth 65536

def segments : List Segment := segments0 ++ segments1 ++ segments2 ++ segments3 ++ segments4 ++ segments5 ++ segments6

theorem segments_checked : checkSegments data 0 scale segments = true := by
  unfold segments
  apply checkSegments_append data segments0 (segments1 ++ segments2 ++ segments3 ++ segments4 ++ segments5 ++ segments6) 0 9511602413006487552 scale segments0_checked
  apply checkSegments_append data segments1 (segments2 ++ segments3 ++ segments4 ++ segments5 ++ segments6) 9511602413006487552 10808639105689190400 scale segments1_checked
  apply checkSegments_append data segments2 (segments3 ++ segments4 ++ segments5 ++ segments6) 10808639105689190400 11961560610296037376 scale segments2_checked
  apply checkSegments_append data segments3 (segments4 ++ segments5 ++ segments6) 11961560610296037376 13114482114902884352 scale segments3_checked
  apply checkSegments_append data segments4 (segments5 ++ segments6) 13114482114902884352 13744986062734753792 scale segments4_checked
  apply checkSegments_append data segments5 (segments6) 13744986062734753792 15276209936040722432 scale segments5_checked
  exact segments6_checked

def verified : VerifiedBlock where
  data := data
  segments := segments
  data_checked := data_checked
  coefficients_valid := by
    left
    refine ⟨rfl, coefficients, ?_, rfl, coefficients_checked⟩
    decide
  segments_checked := segments_checked

end Schmeisser.Certificates.Finite.Generated.M11

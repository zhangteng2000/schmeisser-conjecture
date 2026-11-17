import Schmeisser.Certificates.VerifiedBlock
import Schmeisser.Certificates.Generated.M9Chunk0
import Schmeisser.Certificates.Generated.M9Chunk1
import Schmeisser.Certificates.Generated.M9Chunk2
import Schmeisser.Certificates.Generated.M9Chunk3
import Schmeisser.Certificates.Generated.M9Chunk4
import Schmeisser.Certificates.Generated.M9Chunk5
import Schmeisser.Certificates.Generated.M9Chunk6
import Schmeisser.Certificates.Generated.M9Chunk7
import Schmeisser.Certificates.Generated.M9Chunk8
import Schmeisser.Certificates.Generated.M9Chunk9
import Schmeisser.Certificates.Generated.M9Chunk10

namespace Schmeisser.Certificates.Finite.Generated.M9

set_option maxHeartbeats 0
set_option maxRecDepth 65536

def segments : List Segment := segments0 ++ segments1 ++ segments2 ++ segments3 ++ segments4 ++ segments5 ++ segments6 ++ segments7 ++ segments8 ++ segments9 ++ segments10

theorem segments_checked : checkSegments data 0 scale segments = true := by
  unfold segments
  apply checkSegments_append data segments0 (segments1 ++ segments2 ++ segments3 ++ segments4 ++ segments5 ++ segments6 ++ segments7 ++ segments8 ++ segments9 ++ segments10) 0 9511602413006487552 scale segments0_checked
  apply checkSegments_append data segments1 (segments2 ++ segments3 ++ segments4 ++ segments5 ++ segments6 ++ segments7 ++ segments8 ++ segments9 ++ segments10) 9511602413006487552 10664523917613334528 scale segments1_checked
  apply checkSegments_append data segments2 (segments3 ++ segments4 ++ segments5 ++ segments6 ++ segments7 ++ segments8 ++ segments9 ++ segments10) 10664523917613334528 11817445422220181504 scale segments2_checked
  apply checkSegments_append data segments3 (segments4 ++ segments5 ++ segments6 ++ segments7 ++ segments8 ++ segments9 ++ segments10) 11817445422220181504 12646107753656352768 scale segments3_checked
  apply checkSegments_append data segments4 (segments5 ++ segments6 ++ segments7 ++ segments8 ++ segments9 ++ segments10) 12646107753656352768 13222568505959776256 scale segments4_checked
  apply checkSegments_append data segments5 (segments6 ++ segments7 ++ segments8 ++ segments9 ++ segments10) 13222568505959776256 13799029258263199744 scale segments5_checked
  apply checkSegments_append data segments6 (segments7 ++ segments8 ++ segments9 ++ segments10) 13799029258263199744 14375490010566623232 scale segments6_checked
  apply checkSegments_append data segments7 (segments8 ++ segments9 ++ segments10) 14375490010566623232 14861878770322636800 scale segments7_checked
  apply checkSegments_append data segments8 (segments9 ++ segments10) 14861878770322636800 15114080349455384576 scale segments8_checked
  apply checkSegments_append data segments9 (segments10) 15114080349455384576 15564440312192434176 scale segments9_checked
  exact segments10_checked

def verified : VerifiedBlock where
  data := data
  segments := segments
  data_checked := data_checked
  coefficients_valid := by
    left
    refine ⟨rfl, coefficients, ?_, rfl, coefficients_checked⟩
    decide
  segments_checked := segments_checked

end Schmeisser.Certificates.Finite.Generated.M9

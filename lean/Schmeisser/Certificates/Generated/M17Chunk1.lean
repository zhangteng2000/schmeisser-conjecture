import Schmeisser.Certificates.Generated.M17Data

namespace Schmeisser.Certificates.Finite.Generated.M17

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

theorem segments1_checked :
    checkSegments data 9511602413006487552 16140901064495857664 segments1 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M17

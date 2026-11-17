import Schmeisser.Certificates.Generated.M10Data

namespace Schmeisser.Certificates.Finite.Generated.M10

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

theorem segments0_checked :
    checkSegments data 0 10664523917613334528 segments0 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M10

import Schmeisser.Certificates.Generated.M55Data

namespace Schmeisser.Certificates.Finite.Generated.M55

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

theorem segments0_checked :
    checkSegments data 0 10376293541461622784 segments0 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M55

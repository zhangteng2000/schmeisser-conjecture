import Schmeisser.Certificates.Generated.M7Data

namespace Schmeisser.Certificates.Finite.Generated.M7

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

theorem segments4_checked :
    checkSegments data 12790222941732208640 13366683694035632128 segments4 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M7

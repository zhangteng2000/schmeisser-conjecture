import Schmeisser.Certificates.Generated.M7Data

namespace Schmeisser.Certificates.Finite.Generated.M7

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

theorem segments5_checked :
    checkSegments data 13366683694035632128 13943144446339055616 segments5 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M7

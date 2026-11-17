import Schmeisser.Certificates.Generated.M9Data

namespace Schmeisser.Certificates.Finite.Generated.M9

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

theorem segments3_checked :
    checkSegments data 11817445422220181504 12646107753656352768 segments3 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M9

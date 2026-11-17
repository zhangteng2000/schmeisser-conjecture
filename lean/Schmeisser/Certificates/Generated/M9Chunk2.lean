import Schmeisser.Certificates.Generated.M9Data

namespace Schmeisser.Certificates.Finite.Generated.M9

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

theorem segments2_checked :
    checkSegments data 10664523917613334528 11817445422220181504 segments2 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M9

import Schmeisser.Certificates.Generated.M7Data

namespace Schmeisser.Certificates.Finite.Generated.M7

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

theorem segments11_checked :
    checkSegments data 15474368319645024256 15762598695796736000 segments11 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M7

import Schmeisser.Certificates.Generated.M7Data

namespace Schmeisser.Certificates.Finite.Generated.M7

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

theorem segments10_checked :
    checkSegments data 15186137943493312512 15474368319645024256 segments10 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M7

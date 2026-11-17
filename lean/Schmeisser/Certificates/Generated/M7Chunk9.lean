import Schmeisser.Certificates.Generated.M7Data

namespace Schmeisser.Certificates.Finite.Generated.M7

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

theorem segments9_checked :
    checkSegments data 14897907567341600768 15186137943493312512 segments9 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M7

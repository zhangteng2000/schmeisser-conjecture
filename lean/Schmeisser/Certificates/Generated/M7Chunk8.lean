import Schmeisser.Certificates.Generated.M7Data

namespace Schmeisser.Certificates.Finite.Generated.M7

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

theorem segments8_checked :
    checkSegments data 14609677191189889024 14897907567341600768 segments8 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M7

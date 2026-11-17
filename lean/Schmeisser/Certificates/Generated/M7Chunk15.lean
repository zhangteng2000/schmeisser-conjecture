import Schmeisser.Certificates.Generated.M7Data

namespace Schmeisser.Certificates.Finite.Generated.M7

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

theorem segments15_checked :
    checkSegments data 16203951459279044608 16348066647354900480 segments15 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M7

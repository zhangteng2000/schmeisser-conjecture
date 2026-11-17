import Schmeisser.Certificates.Generated.M7Data

namespace Schmeisser.Certificates.Finite.Generated.M7

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

theorem segments2_checked :
    checkSegments data 11637301437125361664 12213762189428785152 segments2 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M7

import Schmeisser.Certificates.Generated.M8Data

namespace Schmeisser.Certificates.Finite.Generated.M8

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

theorem segments1_checked :
    checkSegments data 11421128655011577856 12574050159618424832 segments1 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M8

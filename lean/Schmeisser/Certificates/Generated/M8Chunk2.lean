import Schmeisser.Certificates.Generated.M8Data

namespace Schmeisser.Certificates.Finite.Generated.M8

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

theorem segments2_checked :
    checkSegments data 12574050159618424832 13726971664225271808 segments2 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M8

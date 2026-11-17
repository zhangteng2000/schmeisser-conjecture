import Schmeisser.Certificates.Generated.M8Data

namespace Schmeisser.Certificates.Finite.Generated.M8

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

theorem segments3_checked :
    checkSegments data 13726971664225271808 15150109146474348544 segments3 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M8

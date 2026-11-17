import Schmeisser.Certificates.Generated.M8Data

namespace Schmeisser.Certificates.Finite.Generated.M8

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

theorem segments4_checked :
    checkSegments data 15150109146474348544 16429131440647569408 segments4 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M8

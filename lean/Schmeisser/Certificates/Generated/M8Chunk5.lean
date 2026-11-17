import Schmeisser.Certificates.Generated.M8Data

namespace Schmeisser.Certificates.Finite.Generated.M8

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

theorem segments5_checked :
    checkSegments data 16429131440647569408 18446744073709551616 segments5 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M8

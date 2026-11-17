import Schmeisser.Certificates.Generated.M9Data

namespace Schmeisser.Certificates.Finite.Generated.M9

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

theorem segments10_checked :
    checkSegments data 15564440312192434176 18446744073709551616 segments10 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M9

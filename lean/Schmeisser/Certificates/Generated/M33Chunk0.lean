import Schmeisser.Certificates.Generated.M33Data

namespace Schmeisser.Certificates.Finite.Generated.M33

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

theorem segments0_checked :
    checkSegments data 0 9223372036854775808 segments0 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M33

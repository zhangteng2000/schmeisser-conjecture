import Schmeisser.Certificates.Generated.M17Data

namespace Schmeisser.Certificates.Finite.Generated.M17

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

theorem segments2_checked :
    checkSegments data 16140901064495857664 18446744073709551616 segments2 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M17

import Schmeisser.Certificates.Generated.M47Data

namespace Schmeisser.Certificates.Finite.Generated.M47

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

theorem segments0_checked :
    checkSegments data 0 18446744073709551616 segments0 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M47

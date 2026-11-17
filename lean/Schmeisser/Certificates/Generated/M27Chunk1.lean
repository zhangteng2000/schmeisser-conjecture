import Schmeisser.Certificates.Generated.M27Data

namespace Schmeisser.Certificates.Finite.Generated.M27

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

theorem segments1_checked :
    checkSegments data 7782220156096217088 18446744073709551616 segments1 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M27

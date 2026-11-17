import Schmeisser.Certificates.Generated.M23Data

namespace Schmeisser.Certificates.Finite.Generated.M23

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

theorem segments1_checked :
    checkSegments data 8935141660703064064 18446744073709551616 segments1 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M23

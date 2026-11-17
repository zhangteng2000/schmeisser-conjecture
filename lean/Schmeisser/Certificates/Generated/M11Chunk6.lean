import Schmeisser.Certificates.Generated.M11Data

namespace Schmeisser.Certificates.Finite.Generated.M11

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

theorem segments6_checked :
    checkSegments data 15276209936040722432 18446744073709551616 segments6 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M11

import Schmeisser.Certificates.Generated.M11Data

namespace Schmeisser.Certificates.Finite.Generated.M11

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

theorem segments5_checked :
    checkSegments data 13744986062734753792 15276209936040722432 segments5 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M11

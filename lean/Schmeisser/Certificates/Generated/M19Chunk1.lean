import Schmeisser.Certificates.Generated.M19Data

namespace Schmeisser.Certificates.Finite.Generated.M19

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

theorem segments1_checked :
    checkSegments data 9511602413006487552 18446744073709551616 segments1 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M19

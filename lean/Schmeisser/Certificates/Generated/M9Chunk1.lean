import Schmeisser.Certificates.Generated.M9Data

namespace Schmeisser.Certificates.Finite.Generated.M9

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

theorem segments1_checked :
    checkSegments data 9511602413006487552 10664523917613334528 segments1 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M9

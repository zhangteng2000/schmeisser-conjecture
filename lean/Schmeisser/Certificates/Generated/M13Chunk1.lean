import Schmeisser.Certificates.Generated.M13Data

namespace Schmeisser.Certificates.Finite.Generated.M13

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

theorem segments1_checked :
    checkSegments data 8935141660703064064 11240984669916758016 segments1 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M13

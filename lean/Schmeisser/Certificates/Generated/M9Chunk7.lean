import Schmeisser.Certificates.Generated.M9Data

namespace Schmeisser.Certificates.Finite.Generated.M9

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

theorem segments7_checked :
    checkSegments data 14375490010566623232 14861878770322636800 segments7 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M9

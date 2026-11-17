import Schmeisser.Certificates.Generated.M9Data

namespace Schmeisser.Certificates.Finite.Generated.M9

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

theorem segments6_checked :
    checkSegments data 13799029258263199744 14375490010566623232 segments6 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M9

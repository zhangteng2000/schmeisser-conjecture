import Schmeisser.Certificates.Generated.M9Data

namespace Schmeisser.Certificates.Finite.Generated.M9

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

theorem segments5_checked :
    checkSegments data 13222568505959776256 13799029258263199744 segments5 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M9

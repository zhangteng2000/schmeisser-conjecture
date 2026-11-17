import Schmeisser.Certificates.Generated.M11Data

namespace Schmeisser.Certificates.Finite.Generated.M11

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

theorem segments2_checked :
    checkSegments data 10808639105689190400 11961560610296037376 segments2 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M11

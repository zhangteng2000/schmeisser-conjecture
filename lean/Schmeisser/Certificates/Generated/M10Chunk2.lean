import Schmeisser.Certificates.Generated.M10Data

namespace Schmeisser.Certificates.Finite.Generated.M10

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

theorem segments2_checked :
    checkSegments data 14087259634414911488 18446744073709551616 segments2 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M10

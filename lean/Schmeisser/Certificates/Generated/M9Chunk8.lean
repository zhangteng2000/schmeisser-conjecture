import Schmeisser.Certificates.Generated.M9Data

namespace Schmeisser.Certificates.Finite.Generated.M9

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

theorem segments8_checked :
    checkSegments data 14861878770322636800 15114080349455384576 segments8 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M9

import Schmeisser.Certificates.Generated.M11Data

namespace Schmeisser.Certificates.Finite.Generated.M11

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

theorem segments3_checked :
    checkSegments data 11961560610296037376 13114482114902884352 segments3 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M11

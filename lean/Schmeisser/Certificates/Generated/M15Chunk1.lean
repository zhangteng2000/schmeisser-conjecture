import Schmeisser.Certificates.Generated.M15Data

namespace Schmeisser.Certificates.Finite.Generated.M15

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

theorem segments1_checked :
    checkSegments data 8358680908399640576 12105675798371893248 segments1 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M15

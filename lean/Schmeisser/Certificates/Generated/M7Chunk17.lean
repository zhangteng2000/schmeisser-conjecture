import Schmeisser.Certificates.Generated.M7Data

namespace Schmeisser.Certificates.Finite.Generated.M7

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

theorem segments17_checked :
    checkSegments data 16420124241392828416 16492181835430756352 segments17 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M7

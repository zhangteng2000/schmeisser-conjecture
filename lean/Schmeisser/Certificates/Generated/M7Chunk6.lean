import Schmeisser.Certificates.Generated.M7Data

namespace Schmeisser.Certificates.Finite.Generated.M7

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

theorem segments6_checked :
    checkSegments data 13943144446339055616 14321446815038177280 segments6 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M7

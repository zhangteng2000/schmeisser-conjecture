import Schmeisser.Certificates.Generated.M7Data

namespace Schmeisser.Certificates.Finite.Generated.M7

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

theorem segments14_checked :
    checkSegments data 16059836271203188736 16203951459279044608 segments14 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M7

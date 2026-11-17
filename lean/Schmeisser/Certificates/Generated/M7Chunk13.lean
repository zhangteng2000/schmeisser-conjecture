import Schmeisser.Certificates.Generated.M7Data

namespace Schmeisser.Certificates.Finite.Generated.M7

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

theorem segments13_checked :
    checkSegments data 15915721083127332864 16059836271203188736 segments13 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M7

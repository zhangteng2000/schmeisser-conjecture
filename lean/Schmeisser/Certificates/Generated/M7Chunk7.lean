import Schmeisser.Certificates.Generated.M7Data

namespace Schmeisser.Certificates.Finite.Generated.M7

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

theorem segments7_checked :
    checkSegments data 14321446815038177280 14609677191189889024 segments7 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M7

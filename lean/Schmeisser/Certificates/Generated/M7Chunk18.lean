import Schmeisser.Certificates.Generated.M7Data

namespace Schmeisser.Certificates.Finite.Generated.M7

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

theorem segments18_checked :
    checkSegments data 16492181835430756352 16609275425742389248 segments18 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M7

import Schmeisser.Certificates.Generated.M7Data

namespace Schmeisser.Certificates.Finite.Generated.M7

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

theorem segments19_checked :
    checkSegments data 16609275425742389248 18446744073709551616 segments19 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M7

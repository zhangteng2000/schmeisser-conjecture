import Schmeisser.Certificates.Generated.M13Data

namespace Schmeisser.Certificates.Finite.Generated.M13

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

theorem segments3_checked :
    checkSegments data 13546827679130451968 18446744073709551616 segments3 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M13

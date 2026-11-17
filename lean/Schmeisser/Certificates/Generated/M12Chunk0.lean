import Schmeisser.Certificates.Generated.M12Data

namespace Schmeisser.Certificates.Finite.Generated.M12

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

theorem segments0_checked :
    checkSegments data 0 11313042263954685952 segments0 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M12

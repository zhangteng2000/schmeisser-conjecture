import Schmeisser.Certificates.VerifiedBlock
import Schmeisser.Certificates.Generated.M7Chunk0
import Schmeisser.Certificates.Generated.M7Chunk1
import Schmeisser.Certificates.Generated.M7Chunk2
import Schmeisser.Certificates.Generated.M7Chunk3
import Schmeisser.Certificates.Generated.M7Chunk4
import Schmeisser.Certificates.Generated.M7Chunk5
import Schmeisser.Certificates.Generated.M7Chunk6
import Schmeisser.Certificates.Generated.M7Chunk7
import Schmeisser.Certificates.Generated.M7Chunk8
import Schmeisser.Certificates.Generated.M7Chunk9
import Schmeisser.Certificates.Generated.M7Chunk10
import Schmeisser.Certificates.Generated.M7Chunk11
import Schmeisser.Certificates.Generated.M7Chunk12
import Schmeisser.Certificates.Generated.M7Chunk13
import Schmeisser.Certificates.Generated.M7Chunk14
import Schmeisser.Certificates.Generated.M7Chunk15
import Schmeisser.Certificates.Generated.M7Chunk16
import Schmeisser.Certificates.Generated.M7Chunk17
import Schmeisser.Certificates.Generated.M7Chunk18
import Schmeisser.Certificates.Generated.M7Chunk19

namespace Schmeisser.Certificates.Finite.Generated.M7

set_option maxHeartbeats 0
set_option maxRecDepth 65536

def segments : List Segment := segments0 ++ segments1 ++ segments2 ++ segments3 ++ segments4 ++ segments5 ++ segments6 ++ segments7 ++ segments8 ++ segments9 ++ segments10 ++ segments11 ++ segments12 ++ segments13 ++ segments14 ++ segments15 ++ segments16 ++ segments17 ++ segments18 ++ segments19

theorem segments_checked : checkSegments data 0 scale segments = true := by
  unfold segments
  apply checkSegments_append data segments0 (segments1 ++ segments2 ++ segments3 ++ segments4 ++ segments5 ++ segments6 ++ segments7 ++ segments8 ++ segments9 ++ segments10 ++ segments11 ++ segments12 ++ segments13 ++ segments14 ++ segments15 ++ segments16 ++ segments17 ++ segments18 ++ segments19) 0 10952754293765046272 scale segments0_checked
  apply checkSegments_append data segments1 (segments2 ++ segments3 ++ segments4 ++ segments5 ++ segments6 ++ segments7 ++ segments8 ++ segments9 ++ segments10 ++ segments11 ++ segments12 ++ segments13 ++ segments14 ++ segments15 ++ segments16 ++ segments17 ++ segments18 ++ segments19) 10952754293765046272 11637301437125361664 scale segments1_checked
  apply checkSegments_append data segments2 (segments3 ++ segments4 ++ segments5 ++ segments6 ++ segments7 ++ segments8 ++ segments9 ++ segments10 ++ segments11 ++ segments12 ++ segments13 ++ segments14 ++ segments15 ++ segments16 ++ segments17 ++ segments18 ++ segments19) 11637301437125361664 12213762189428785152 scale segments2_checked
  apply checkSegments_append data segments3 (segments4 ++ segments5 ++ segments6 ++ segments7 ++ segments8 ++ segments9 ++ segments10 ++ segments11 ++ segments12 ++ segments13 ++ segments14 ++ segments15 ++ segments16 ++ segments17 ++ segments18 ++ segments19) 12213762189428785152 12790222941732208640 scale segments3_checked
  apply checkSegments_append data segments4 (segments5 ++ segments6 ++ segments7 ++ segments8 ++ segments9 ++ segments10 ++ segments11 ++ segments12 ++ segments13 ++ segments14 ++ segments15 ++ segments16 ++ segments17 ++ segments18 ++ segments19) 12790222941732208640 13366683694035632128 scale segments4_checked
  apply checkSegments_append data segments5 (segments6 ++ segments7 ++ segments8 ++ segments9 ++ segments10 ++ segments11 ++ segments12 ++ segments13 ++ segments14 ++ segments15 ++ segments16 ++ segments17 ++ segments18 ++ segments19) 13366683694035632128 13943144446339055616 scale segments5_checked
  apply checkSegments_append data segments6 (segments7 ++ segments8 ++ segments9 ++ segments10 ++ segments11 ++ segments12 ++ segments13 ++ segments14 ++ segments15 ++ segments16 ++ segments17 ++ segments18 ++ segments19) 13943144446339055616 14321446815038177280 scale segments6_checked
  apply checkSegments_append data segments7 (segments8 ++ segments9 ++ segments10 ++ segments11 ++ segments12 ++ segments13 ++ segments14 ++ segments15 ++ segments16 ++ segments17 ++ segments18 ++ segments19) 14321446815038177280 14609677191189889024 scale segments7_checked
  apply checkSegments_append data segments8 (segments9 ++ segments10 ++ segments11 ++ segments12 ++ segments13 ++ segments14 ++ segments15 ++ segments16 ++ segments17 ++ segments18 ++ segments19) 14609677191189889024 14897907567341600768 scale segments8_checked
  apply checkSegments_append data segments9 (segments10 ++ segments11 ++ segments12 ++ segments13 ++ segments14 ++ segments15 ++ segments16 ++ segments17 ++ segments18 ++ segments19) 14897907567341600768 15186137943493312512 scale segments9_checked
  apply checkSegments_append data segments10 (segments11 ++ segments12 ++ segments13 ++ segments14 ++ segments15 ++ segments16 ++ segments17 ++ segments18 ++ segments19) 15186137943493312512 15474368319645024256 scale segments10_checked
  apply checkSegments_append data segments11 (segments12 ++ segments13 ++ segments14 ++ segments15 ++ segments16 ++ segments17 ++ segments18 ++ segments19) 15474368319645024256 15762598695796736000 scale segments11_checked
  apply checkSegments_append data segments12 (segments13 ++ segments14 ++ segments15 ++ segments16 ++ segments17 ++ segments18 ++ segments19) 15762598695796736000 15915721083127332864 scale segments12_checked
  apply checkSegments_append data segments13 (segments14 ++ segments15 ++ segments16 ++ segments17 ++ segments18 ++ segments19) 15915721083127332864 16059836271203188736 scale segments13_checked
  apply checkSegments_append data segments14 (segments15 ++ segments16 ++ segments17 ++ segments18 ++ segments19) 16059836271203188736 16203951459279044608 scale segments14_checked
  apply checkSegments_append data segments15 (segments16 ++ segments17 ++ segments18 ++ segments19) 16203951459279044608 16348066647354900480 scale segments15_checked
  apply checkSegments_append data segments16 (segments17 ++ segments18 ++ segments19) 16348066647354900480 16420124241392828416 scale segments16_checked
  apply checkSegments_append data segments17 (segments18 ++ segments19) 16420124241392828416 16492181835430756352 scale segments17_checked
  apply checkSegments_append data segments18 (segments19) 16492181835430756352 16609275425742389248 scale segments18_checked
  exact segments19_checked

def verified : VerifiedBlock where
  data := data
  segments := segments
  data_checked := data_checked
  coefficients_valid := by
    left
    refine ⟨rfl, coefficients, ?_, rfl, coefficients_checked⟩
    decide
  segments_checked := segments_checked

end Schmeisser.Certificates.Finite.Generated.M7

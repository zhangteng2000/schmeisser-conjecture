import Schmeisser.Certificates.CoefficientCertificates

namespace Schmeisser.Certificates.Finite.Generated.M11

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

def coefficients : CoefficientTable where
  scale := 18446744073709551616
  normalizedNewton := [
    (mkRat 1 1),
    (mkRat 0 1),
    (mkRat 11 20),
    (mkRat 11 30),
    (mkRat 341 800),
    (mkRat 253 600),
    (mkRat 61853 144000),
    (mkRat 14597 33600),
    (mkRat 5059483 11520000),
    (mkRat 40233391 90720000),
    (mkRat 3608251471 8064000000),
    (mkRat 3274072877 7257600000)
  ]
  upper := [
    0,
    0,
    1844674407370955162,
    1296305037491892419,
    2056375534623360376,
    1766276754416149377,
    1766276754416149377,
    2056375534623360376,
    2805780655226322586,
    4550881354677445784,
    8957499770411616536,
    18446744073709551616
  ]

theorem coefficients_checked : coefficients.check 11 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M11

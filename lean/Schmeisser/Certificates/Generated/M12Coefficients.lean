import Schmeisser.Certificates.CoefficientCertificates

namespace Schmeisser.Certificates.Finite.Generated.M12

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

def coefficients : CoefficientTable where
  scale := 18446744073709551616
  normalizedNewton := [
    (mkRat 1 1),
    (mkRat 0 1),
    (mkRat 6 11),
    (mkRat 4 11),
    (mkRat 51 121),
    (mkRat 252 605),
    (mkRat 564 1331),
    (mkRat 19944 46585),
    (mkRat 31653 73205),
    (mkRat 223544 512435),
    (mkRat 12394854 28183925),
    (mkRat 2497476 5636785),
    (mkRat 19758467 44289025)
  ]
  upper := [
    0,
    0,
    1676976733973595602,
    1112380521749211932,
    1697938943148265547,
    1370925536840304500,
    1277696559217977602,
    1370925536840304500,
    1697938943148265547,
    2447999605025235386,
    4172854746681177408,
    8593422890509835495,
    18446744073709551616
  ]

theorem coefficients_checked : coefficients.check 12 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M12

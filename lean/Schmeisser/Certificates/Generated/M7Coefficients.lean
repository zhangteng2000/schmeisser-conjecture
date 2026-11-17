import Schmeisser.Certificates.CoefficientCertificates

namespace Schmeisser.Certificates.Finite.Generated.M7

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

def coefficients : CoefficientTable where
  scale := 18446744073709551616
  normalizedNewton := [
    (mkRat 1 1),
    (mkRat 0 1),
    (mkRat 7 12),
    (mkRat 7 18),
    (mkRat 133 288),
    (mkRat 497 1080),
    (mkRat 4907 10368),
    (mkRat 12503 25920)
  ]
  upper := [
    0,
    0,
    3074457345618258603,
    3012340693086528301,
    5752981182110210431,
    7129984098994401143,
    11071617447113938115,
    18446744073709551616
  ]

theorem coefficients_checked : coefficients.check 7 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M7

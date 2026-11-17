import Schmeisser.Certificates.CoefficientCertificates

namespace Schmeisser.Certificates.Finite.Generated.M8

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

def coefficients : CoefficientTable where
  scale := 18446744073709551616
  normalizedNewton := [
    (mkRat 1 1),
    (mkRat 0 1),
    (mkRat 4 7),
    (mkRat 8 21),
    (mkRat 22 49),
    (mkRat 328 735),
    (mkRat 1412 3087),
    (mkRat 2392 5145),
    (mkRat 51013 108045)
  ]
  upper := [
    0,
    0,
    2635249153387078803,
    2324071300851905377,
    4216398645419326084,
    4644989648975804127,
    6246516511732334939,
    10407502968246433408,
    18446744073709551616
  ]

theorem coefficients_checked : coefficients.check 8 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M8

import Schmeisser.Certificates.CoefficientCertificates

namespace Schmeisser.Certificates.Finite.Generated.M9

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

def coefficients : CoefficientTable where
  scale := 18446744073709551616
  normalizedNewton := [
    (mkRat 1 1),
    (mkRat 0 1),
    (mkRat 9 16),
    (mkRat 3 8),
    (mkRat 225 512),
    (mkRat 279 640),
    (mkRat 3651 8192),
    (mkRat 64809 143360),
    (mkRat 1201239 2621440),
    (mkRat 212783 458752)
  ]
  upper := [
    0,
    0,
    2305843009213693952,
    1863402546476111745,
    3221776996747230699,
    3221776996747230699,
    3851200201727213462,
    5556935788953845182,
    9849372385059274752,
    18446744073709551616
  ]

theorem coefficients_checked : coefficients.check 9 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M9

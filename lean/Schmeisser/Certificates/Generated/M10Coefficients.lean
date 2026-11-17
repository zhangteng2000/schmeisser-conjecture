import Schmeisser.Certificates.CoefficientCertificates

namespace Schmeisser.Certificates.Finite.Generated.M10

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

def coefficients : CoefficientTable where
  scale := 18446744073709551616
  normalizedNewton := [
    (mkRat 1 1),
    (mkRat 0 1),
    (mkRat 5 9),
    (mkRat 10 27),
    (mkRat 35 81),
    (mkRat 104 243),
    (mkRat 955 2187),
    (mkRat 6770 15309),
    (mkRat 8810 19683),
    (mkRat 20780 45927),
    (mkRat 566624 1240029)
  ]
  upper := [
    0,
    0,
    2049638230412172402,
    1537228672809129302,
    2541714075411920142,
    2342443691899625603,
    2541714075411920142,
    3259968880375926375,
    5003999585967217778,
    9371916920037368093,
    18446744073709551616
  ]

theorem coefficients_checked : coefficients.check 10 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M10

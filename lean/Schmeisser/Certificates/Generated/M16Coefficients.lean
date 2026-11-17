import Schmeisser.Certificates.CoefficientCertificates

namespace Schmeisser.Certificates.Finite.Generated.M16

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

def coefficients : CoefficientTable where
  scale := 18446744073709551616
  normalizedNewton := [
    (mkRat 1 1),
    (mkRat 0 1),
    (mkRat 8 15),
    (mkRat 16 45),
    (mkRat 92 225),
    (mkRat 272 675),
    (mkRat 4136 10125),
    (mkRat 29168 70875),
    (mkRat 62962 151875),
    (mkRat 798512 1913625),
    (mkRat 33470072 79734375),
    (mkRat 666342256 1578740625),
    (mkRat 4566279964 10764140625),
    (mkRat 656056335728 1539272109375),
    (mkRat 5322255154792 12432582421875),
    (mkRat 29775107079248 69267244921875),
    (mkRat 1046185018050121 2424353572265625)
  ]
  upper := [
    0,
    0,
    1229782938247303442,
    680418405611690058,
    911172778919360539,
    607452291695877930,
    458038272573863276,
    387720823742755264,
    366928242647214081,
    387720823742755264,
    458038272573863276,
    607452291695877930,
    911172778919360539,
    1564508347417931656,
    3131641879672596217,
    7482989884916580415,
    18446744073709551616
  ]

theorem coefficients_checked : coefficients.check 16 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M16

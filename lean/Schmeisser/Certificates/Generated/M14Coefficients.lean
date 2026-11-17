import Schmeisser.Certificates.CoefficientCertificates

namespace Schmeisser.Certificates.Finite.Generated.M14

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

def coefficients : CoefficientTable where
  scale := 18446744073709551616
  normalizedNewton := [
    (mkRat 1 1),
    (mkRat 0 1),
    (mkRat 7 13),
    (mkRat 14 39),
    (mkRat 70 169),
    (mkRat 1036 2535),
    (mkRat 8204 19773),
    (mkRat 13792 32955),
    (mkRat 542437 1285245),
    (mkRat 983752 2313441),
    (mkRat 35768999 83540925),
    (mkRat 712704622 1654110315),
    (mkRat 12708173576 29322864675),
    (mkRat 46849920068 107517170475),
    (mkRat 367285260074 838633929705)
  ]
  upper := [
    0,
    0,
    1418980313362273202,
    852701046450272559,
    1214120835540058763,
    882745669636998908,
    731891900282153479,
    687990454963526401,
    731891900282153479,
    882745669636998908,
    1214120835540058763,
    1924743838970805690,
    3578138179157194785,
    7980978604894040065,
    18446744073709551616
  ]

theorem coefficients_checked : coefficients.check 14 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M14

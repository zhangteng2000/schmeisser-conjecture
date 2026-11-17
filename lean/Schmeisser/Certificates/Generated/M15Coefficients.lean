import Schmeisser.Certificates.CoefficientCertificates

namespace Schmeisser.Certificates.Finite.Generated.M15

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

def coefficients : CoefficientTable where
  scale := 18446744073709551616
  normalizedNewton := [
    (mkRat 1 1),
    (mkRat 0 1),
    (mkRat 15 28),
    (mkRat 5 14),
    (mkRat 645 1568),
    (mkRat 159 392),
    (mkRat 18065 43904),
    (mkRat 9105 21952),
    (mkRat 2055555 4917248),
    (mkRat 258745 614656),
    (mkRat 58329657 137682944),
    (mkRat 322697685 757256192),
    (mkRat 3303493345 7710244864),
    (mkRat 118696210935 275641253888),
    (mkRat 7192064214285 16623287926784),
    (mkRat 6707907162787 15435910217728)
  ]
  upper := [
    0,
    0,
    1317624576693539402,
    758476881596964516,
    1046385620720691325,
    727149688438005339,
    573660622662666039,
    510331676671362994,
    510331676671362994,
    573660622662666039,
    727149688438005339,
    1046385620720691325,
    1729113137060980686,
    3340050865261295472,
    7719988557150789633,
    18446744073709551616
  ]

theorem coefficients_checked : coefficients.check 15 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M15

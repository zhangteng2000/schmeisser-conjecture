import Schmeisser.Certificates.CoefficientCertificates

namespace Schmeisser.Certificates.Finite.Generated.M13

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

def coefficients : CoefficientTable where
  scale := 18446744073709551616
  normalizedNewton := [
    (mkRat 1 1),
    (mkRat 0 1),
    (mkRat 13 24),
    (mkRat 13 36),
    (mkRat 481 1152),
    (mkRat 1781 4320),
    (mkRat 429 1024),
    (mkRat 613847 1451520),
    (mkRat 5663671 13271040),
    (mkRat 134897113 313528320),
    (mkRat 1610700559 3715891200),
    (mkRat 144496045031 331085905920),
    (mkRat 6345197697449 14447384985600),
    (mkRat 17552000759219 39730308710400)
  ]
  upper := [
    0,
    0,
    1537228672809129302,
    968202968784394855,
    1425719847762811115,
    1089401594965025905,
    954415179104864266,
    954415179104864266,
    1089401594965025905,
    1425719847762811115,
    2160247928131247650,
    3852717324078687227,
    8270288960655369159,
    18446744073709551616
  ]

theorem coefficients_checked : coefficients.check 13 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M13

import Schmeisser.Certificates.CoefficientCertificates

namespace Schmeisser.Certificates.Finite.Generated.M18

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

def coefficients : CoefficientTable where
  scale := 18446744073709551616
  normalizedNewton := [
    (mkRat 1 1),
    (mkRat 0 1),
    (mkRat 9 17),
    (mkRat 6 17),
    (mkRat 117 289),
    (mkRat 576 1445),
    (mkRat 1983 4913),
    (mkRat 69858 171955),
    (mkRat 170757 417605),
    (mkRat 1202204 2923235),
    (mkRat 102726297 248474975),
    (mkRat 227092266 546644945),
    (mkRat 1762659663 4224074575),
    (mkRat 253109379456 604042664225),
    (mkRat 2325933032013 5529313618675),
    (mkRat 21676742554182 51343626459125),
    (mkRat 517679088833376 1221978309727175),
    (mkRat 199753831079172 469991657587375),
    (mkRat 44281458964414058 103868156326809875)
  ]
  upper := [
    0,
    0,
    1085102592571150096,
    559249075475302155,
    705316685171247562,
    438971181563192932,
    305604314468548926,
    237199950588716213,
    204152572372320677,
    194256128460289808,
    204152572372320677,
    237199950588716213,
    305604314468548926,
    438971181563192932,
    708981021009027015,
    1304114683069222569,
    2784139428066430736,
    7067794791923044678,
    18446744073709551616
  ]

theorem coefficients_checked : coefficients.check 18 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M18

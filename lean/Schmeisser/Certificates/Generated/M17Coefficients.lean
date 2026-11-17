import Schmeisser.Certificates.CoefficientCertificates

namespace Schmeisser.Certificates.Finite.Generated.M17

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

def coefficients : CoefficientTable where
  scale := 18446744073709551616
  normalizedNewton := [
    (mkRat 1 1),
    (mkRat 0 1),
    (mkRat 17 32),
    (mkRat 17 48),
    (mkRat 833 2048),
    (mkRat 3077 7680),
    (mkRat 239411 589824),
    (mkRat 1406291 3440640),
    (mkRat 155353871 377487360),
    (mkRat 1230918779 2972712960),
    (mkRat 176044714361 422785843200),
    (mkRat 250258197599 597939978240),
    (mkRat 307224022608113 730573937049600),
    (mkRat 3677271503832053 8706006083174400),
    (mkRat 763487020963471307 1800134180890214400),
    (mkRat 10675494659306865803 25073297519542272000),
    (mkRat 2560041435317665098719 5990846554002633523200),
    (mkRat 2408317015216471208347 5616418644377468928000)
  ]
  upper := [
    0,
    0,
    1152921504606846976,
    614891469123651721,
    800583849210684006,
    513656469069630965,
    371570933892103982,
    300619721637668983,
    270706918298164679,
    270706918298164679,
    300619721637668983,
    371570933892103982,
    513656469069630965,
    800583849210684006,
    1424454264293578571,
    2947692709220550215,
    7266524992173928049,
    18446744073709551616
  ]

theorem coefficients_checked : coefficients.check 17 = true := by
  decide +kernel

end Schmeisser.Certificates.Finite.Generated.M17

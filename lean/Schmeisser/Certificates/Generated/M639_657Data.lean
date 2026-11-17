import Schmeisser.Certificates.BlockSoundness
import Schmeisser.Certificates.CommonCauchyEndpoint

namespace Schmeisser.Certificates.Finite.Generated.M639_657

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

def data : Data where
  lo := 639
  hi := 657
  cutoff := 328449658104709120
  upper := [0, 0, 0, 5916835933486814, 502295512380568, 47012525353978, 4778233412704, 521494563354, 60595417448, 7445799735, 962292674]
  panels := [
    ((mkRat 0 1), (mkRat 1 1))
  ]

theorem data_checked : data.check = true := by
  decide +kernel

theorem common_coefficients_checked : checkCommonCauchy 639 657 scaleNat data.upper = true := by
  exact checkCommonCauchy_of_endpoint 639 657 scaleNat data.upper (by decide) (by decide +kernel)

def segments0 : List Segment := [
  ⟨288230376151711744, .threshold⟩,
  ⟨360287970189639680, (.numeric ⟨24576, (.recurrence 16 (.basic false true)), (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨396316767208603648, (.numeric ⟨24576, (.recurrence 16 (.basic false true)), (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨432345564227567616, (.numeric ⟨24576, (.recurrence 16 (.basic false true)), (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨504403158265495552, (.numeric ⟨24576, (.recurrence 32 (.basic false true)), (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨576460752303423488, (.numeric ⟨24576, (.recurrence 32 (.basic false true)), (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨648518346341351424, (.numeric ⟨24576, (.recurrence 16 (.basic false true)), (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨720575940379279360, (.numeric ⟨24576, (.recurrence 16 (.basic false true)), (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨1008806316530991104, (.numeric ⟨24576, (.recurrence 32 (.basic false true)), (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨1441151880758558720, (.numeric ⟨24576, (.recurrence 32 (.basic false true)), (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨1729382256910270464, (.numeric ⟨24576, (.recurrence 32 (.basic false true)), (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨2305843009213693952, (.numeric ⟨24576, (.recurrence 32 (.basic false true)), (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨3458764513820540928, (.numeric ⟨24576, (.recurrence 32 (.basic false true)), (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨4611686018427387904, (.numeric ⟨24576, (.recurrence 32 (.basic false true)), (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨5764607523034234880, (.numeric ⟨24576, .moment, (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨6917529027641081856, (.numeric ⟨24576, .moment, (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨8070450532247928832, (.numeric ⟨24576, .moment, (.splitRaw (mkRat 1 4))⟩)⟩,
  ⟨9223372036854775808, (.numeric ⟨24576, .moment, (.splitRaw (mkRat 1 4))⟩)⟩,
  ⟨10376293541461622784, (.numeric ⟨24576, .moment, (.splitRaw (mkRat 1 4))⟩)⟩,
  ⟨11529215046068469760, (.numeric ⟨24576, .moment, (.splitRaw (mkRat 1 4))⟩)⟩,
  ⟨12682136550675316736, (.numeric ⟨24576, .moment, (.splitRaw (mkRat 1 16))⟩)⟩,
  ⟨13835058055282163712, (.numeric ⟨24576, .moment, (.splitRaw (mkRat 1 16))⟩)⟩,
  ⟨14987979559889010688, (.numeric ⟨24576, .moment, (.splitRaw (mkRat 1 16))⟩)⟩,
  ⟨16140901064495857664, (.numeric ⟨24576, (.recurrence 8 (.basic true true)), (.splitRaw (mkRat 1 16))⟩)⟩,
  ⟨18446744073709551616, (.numeric ⟨24576, (.recurrence 8 (.basic true false)), .geometric⟩)⟩
]

end Schmeisser.Certificates.Finite.Generated.M639_657

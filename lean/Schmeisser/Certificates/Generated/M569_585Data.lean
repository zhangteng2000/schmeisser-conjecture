import Schmeisser.Certificates.BlockSoundness
import Schmeisser.Certificates.CommonCauchyEndpoint

namespace Schmeisser.Certificates.Finite.Generated.M569_585

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

def data : Data where
  lo := 569
  hi := 585
  cutoff := 361835097555009536
  upper := [0, 0, 0, 7042635197919967, 633729858733526, 62878168586777, 6775439357166, 784054396719, 96606233613, 12588920035, 1725595494]
  panels := [
    ((mkRat 0 1), (mkRat 1 1))
  ]

theorem data_checked : data.check = true := by
  decide +kernel

theorem common_coefficients_checked : checkCommonCauchy 569 585 scaleNat data.upper = true := by
  exact checkCommonCauchy_of_endpoint 569 585 scaleNat data.upper (by decide) (by decide +kernel)

def segments0 : List Segment := [
  ⟨360287970189639680, .threshold⟩,
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

end Schmeisser.Certificates.Finite.Generated.M569_585

import Schmeisser.Certificates.BlockSoundness
import Schmeisser.Certificates.CommonCauchyEndpoint

namespace Schmeisser.Certificates.Finite.Generated.M1669_1718

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

def data : Data where
  lo := 1669
  hi := 1718
  cutoff := 145675105593327616
  upper := [0, 0, 0, 1400688318973370, 73486566562042, 4248619445504, 266609524855, 17956435401, 1286944143, 97491760, 7764026]
  panels := [
    ((mkRat 0 1), (mkRat 1 1))
  ]

theorem data_checked : data.check = true := by
  decide +kernel

theorem common_coefficients_checked : checkCommonCauchy 1669 1718 scaleNat data.upper = true := by
  exact checkCommonCauchy_of_endpoint 1669 1718 scaleNat data.upper (by decide) (by decide +kernel)

def segments0 : List Segment := [
  ⟨144115188075855872, .threshold⟩,
  ⟨180143985094819840, (.numeric ⟨24576, .moment, (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨216172782113783808, (.numeric ⟨24576, .moment, (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨252201579132747776, (.numeric ⟨24576, .moment, (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨288230376151711744, (.numeric ⟨24576, .moment, (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨360287970189639680, (.numeric ⟨24576, (.recurrence 32 (.basic false true)), (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨432345564227567616, (.numeric ⟨24576, (.recurrence 32 (.basic false true)), (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨504403158265495552, (.numeric ⟨24576, (.recurrence 32 (.basic false true)), (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨576460752303423488, (.numeric ⟨24576, (.recurrence 32 (.basic false true)), (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨720575940379279360, (.numeric ⟨24576, (.recurrence 64 (.basic false true)), (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨864691128455135232, (.numeric ⟨24576, (.recurrence 32 (.basic false true)), (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨1152921504606846976, (.numeric ⟨24576, (.recurrence 64 (.basic false true)), (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨1441151880758558720, (.numeric ⟨24576, (.recurrence 32 (.basic false true)), (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨1729382256910270464, (.numeric ⟨24576, .moment, (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨2305843009213693952, (.numeric ⟨24576, .moment, (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨3458764513820540928, (.numeric ⟨24576, .moment, (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨4611686018427387904, (.numeric ⟨24576, .moment, (.splitRaw (mkRat 1 2))⟩)⟩,
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
  ⟨17293822569102704640, (.numeric ⟨24576, .moment, .geometric⟩)⟩,
  ⟨18446744073709551616, (.numeric ⟨24576, .moment, .geometric⟩)⟩
]

end Schmeisser.Certificates.Finite.Generated.M1669_1718

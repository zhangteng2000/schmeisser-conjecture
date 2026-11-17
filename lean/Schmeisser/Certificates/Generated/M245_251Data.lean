import Schmeisser.Certificates.BlockSoundness
import Schmeisser.Certificates.CommonCauchyEndpoint

namespace Schmeisser.Certificates.Finite.Generated.M245_251

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

def data : Data where
  lo := 245
  hi := 251
  cutoff := 725345429839675392
  upper := [0, 0, 0, 24969678899139749, 3434196455585915, 521408004578406, 86077333417717, 15278855666592, 2891118800410, 579283833502, 122239969127]
  panels := [
    ((mkRat 0 1), (mkRat 1 1))
  ]

theorem data_checked : data.check = true := by
  decide +kernel

theorem common_coefficients_checked : checkCommonCauchy 245 251 scaleNat data.upper = true := by
  exact checkCommonCauchy_of_endpoint 245 251 scaleNat data.upper (by decide) (by decide +kernel)

def segments0 : List Segment := [
  ⟨720575940379279360, .threshold⟩,
  ⟨792633534417207296, (.numeric ⟨24576, (.recurrence 16 (.basic false true)), (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨864691128455135232, (.numeric ⟨24576, (.recurrence 16 (.basic false true)), (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨936748722493063168, (.numeric ⟨24576, (.recurrence 16 (.basic false true)), (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨1008806316530991104, (.numeric ⟨24576, (.recurrence 16 (.basic false true)), (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨1152921504606846976, (.numeric ⟨24576, (.recurrence 32 (.basic false true)), (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨1297036692682702848, (.numeric ⟨24576, (.recurrence 16 (.basic false true)), (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨1441151880758558720, (.numeric ⟨24576, (.recurrence 16 (.basic false true)), (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨1729382256910270464, (.numeric ⟨24576, (.recurrence 32 (.basic false true)), (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨2017612633061982208, (.numeric ⟨24576, (.recurrence 16 (.basic false true)), (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨2305843009213693952, (.numeric ⟨24576, (.recurrence 16 (.basic false true)), (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨2882303761517117440, (.numeric ⟨24576, (.recurrence 32 (.basic false true)), (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨3458764513820540928, (.numeric ⟨24576, (.recurrence 16 (.basic false true)), (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨4035225266123964416, (.numeric ⟨24576, (.recurrence 16 (.basic false true)), (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨4611686018427387904, (.numeric ⟨24576, (.recurrence 16 (.basic false true)), (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨5764607523034234880, (.numeric ⟨24576, (.recurrence 16 (.basic false true)), (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨6917529027641081856, (.numeric ⟨24576, (.recurrence 16 (.basic false true)), (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨8070450532247928832, (.numeric ⟨24576, (.recurrence 16 (.basic false true)), (.splitRaw (mkRat 1 4))⟩)⟩,
  ⟨9223372036854775808, (.numeric ⟨24576, .moment, (.splitRaw (mkRat 1 4))⟩)⟩,
  ⟨10376293541461622784, (.numeric ⟨24576, .moment, (.splitRaw (mkRat 1 4))⟩)⟩,
  ⟨11529215046068469760, (.numeric ⟨24576, .moment, (.splitRaw (mkRat 1 4))⟩)⟩,
  ⟨12682136550675316736, (.numeric ⟨24576, (.recurrence 16 (.basic false true)), (.splitRaw (mkRat 1 4))⟩)⟩,
  ⟨13258597302978740224, (.numeric ⟨24576, .moment, (.splitRaw (mkRat 1 4))⟩)⟩,
  ⟨13835058055282163712, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), (.splitRaw (mkRat 1 4))⟩)⟩,
  ⟨14411518807585587200, (.numeric ⟨24576, (.recurrence 8 (.basic true true)), (.splitRaw (mkRat 1 4))⟩)⟩,
  ⟨14699749183737298944, (.numeric ⟨24576, (.recurrence 8 (.basic true true)), (.splitRaw (mkRat 1 4))⟩)⟩,
  ⟨14987979559889010688, (.numeric ⟨24576, .moment, .geometric⟩)⟩,
  ⟨16140901064495857664, (.numeric ⟨24576, (.recurrence 8 (.basic true true)), .geometric⟩)⟩,
  ⟨18446744073709551616, (.numeric ⟨24576, (.recurrence 8 (.basic true false)), .geometric⟩)⟩
]

end Schmeisser.Certificates.Finite.Generated.M245_251

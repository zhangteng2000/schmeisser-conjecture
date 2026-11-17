import Schmeisser.Certificates.BlockSoundness
import Schmeisser.Certificates.CommonCauchyEndpoint

namespace Schmeisser.Certificates.Finite.Generated.M238_244

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

def data : Data where
  lo := 238
  hi := 244
  cutoff := 742156485628854272
  upper := [0, 0, 0, 26081697738799012, 3640058689879831, 560851676204138, 93966524353853, 16928418984631, 3251323133801, 661274654320, 141653678593]
  panels := [
    ((mkRat 0 1), (mkRat 1 1024)),
    ((mkRat 1 1024), (mkRat 1 256)),
    ((mkRat 1 256), (mkRat 9 1024)),
    ((mkRat 9 1024), (mkRat 1 64)),
    ((mkRat 1 64), (mkRat 25 1024)),
    ((mkRat 25 1024), (mkRat 9 256)),
    ((mkRat 9 256), (mkRat 49 1024)),
    ((mkRat 49 1024), (mkRat 1 16)),
    ((mkRat 1 16), (mkRat 81 1024)),
    ((mkRat 81 1024), (mkRat 25 256)),
    ((mkRat 25 256), (mkRat 121 1024)),
    ((mkRat 121 1024), (mkRat 9 64)),
    ((mkRat 9 64), (mkRat 169 1024)),
    ((mkRat 169 1024), (mkRat 49 256)),
    ((mkRat 49 256), (mkRat 225 1024)),
    ((mkRat 225 1024), (mkRat 1 4)),
    ((mkRat 1 4), (mkRat 289 1024)),
    ((mkRat 289 1024), (mkRat 81 256)),
    ((mkRat 81 256), (mkRat 361 1024)),
    ((mkRat 361 1024), (mkRat 25 64)),
    ((mkRat 25 64), (mkRat 441 1024)),
    ((mkRat 441 1024), (mkRat 121 256)),
    ((mkRat 121 256), (mkRat 529 1024)),
    ((mkRat 529 1024), (mkRat 9 16)),
    ((mkRat 9 16), (mkRat 625 1024)),
    ((mkRat 625 1024), (mkRat 169 256)),
    ((mkRat 169 256), (mkRat 729 1024)),
    ((mkRat 729 1024), (mkRat 49 64)),
    ((mkRat 49 64), (mkRat 841 1024)),
    ((mkRat 841 1024), (mkRat 225 256)),
    ((mkRat 225 256), (mkRat 961 1024)),
    ((mkRat 961 1024), (mkRat 1 1))
  ]

theorem data_checked : data.check = true := by
  decide +kernel

theorem common_coefficients_checked : checkCommonCauchy 238 244 scaleNat data.upper = true := by
  exact checkCommonCauchy_of_endpoint 238 244 scaleNat data.upper (by decide) (by decide +kernel)

def segments0 : List Segment := [
  ⟨720575940379279360, .threshold⟩,
  ⟨792633534417207296, (.numeric ⟨24576, (.recurrence 16 (.basic false true)), (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨864691128455135232, (.numeric ⟨24576, (.recurrence 32 (.basic false true)), (.splitRaw (mkRat 1 2))⟩)⟩,
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
  ⟨9223372036854775808, (.numeric ⟨24576, (.recurrence 16 (.basic false true)), (.splitRaw (mkRat 1 4))⟩)⟩,
  ⟨10376293541461622784, (.numeric ⟨24576, .moment, (.splitRaw (mkRat 1 4))⟩)⟩,
  ⟨11529215046068469760, (.numeric ⟨24576, .moment, (.splitRaw (mkRat 1 4))⟩)⟩,
  ⟨12682136550675316736, (.numeric ⟨24576, (.recurrence 16 (.basic false true)), (.splitRaw (mkRat 1 4))⟩)⟩,
  ⟨13258597302978740224, (.numeric ⟨24576, .moment, (.splitRaw (mkRat 1 4))⟩)⟩,
  ⟨13835058055282163712, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), (.splitRaw (mkRat 1 4))⟩)⟩,
  ⟨14411518807585587200, (.numeric ⟨24576, (.recurrence 8 (.basic true true)), (.convexRiemann 4294950912)⟩)⟩,
  ⟨14699749183737298944, (.numeric ⟨24576, (.recurrence 8 (.basic true true)), (.splitRaw (mkRat 1 4))⟩)⟩,
  ⟨14987979559889010688, (.numeric ⟨24576, .moment, .geometric⟩)⟩,
  ⟨16140901064495857664, (.numeric ⟨24576, (.recurrence 8 (.basic true true)), .geometric⟩)⟩,
  ⟨18446744073709551616, (.numeric ⟨24576, (.recurrence 8 (.basic true false)), .geometric⟩)⟩
]

end Schmeisser.Certificates.Finite.Generated.M238_244

import Schmeisser.Certificates.BlockSoundness
import Schmeisser.Certificates.CommonCauchyEndpoint

namespace Schmeisser.Certificates.Finite.Generated.M226_231

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

def data : Data where
  lo := 226
  hi := 231
  cutoff := 775761267359350784
  upper := [0, 0, 0, 28191066691978197, 4038690776328740, 638831799397144, 109892515367118, 20329111597736, 4009777146522, 837628774476, 184314348225]
  panels := [
    ((mkRat 0 1), (mkRat 1 2304)),
    ((mkRat 1 2304), (mkRat 1 576)),
    ((mkRat 1 576), (mkRat 1 256)),
    ((mkRat 1 256), (mkRat 1 144)),
    ((mkRat 1 144), (mkRat 25 2304)),
    ((mkRat 25 2304), (mkRat 1 64)),
    ((mkRat 1 64), (mkRat 49 2304)),
    ((mkRat 49 2304), (mkRat 1 36)),
    ((mkRat 1 36), (mkRat 9 256)),
    ((mkRat 9 256), (mkRat 25 576)),
    ((mkRat 25 576), (mkRat 121 2304)),
    ((mkRat 121 2304), (mkRat 1 16)),
    ((mkRat 1 16), (mkRat 169 2304)),
    ((mkRat 169 2304), (mkRat 49 576)),
    ((mkRat 49 576), (mkRat 25 256)),
    ((mkRat 25 256), (mkRat 1 9)),
    ((mkRat 1 9), (mkRat 289 2304)),
    ((mkRat 289 2304), (mkRat 9 64)),
    ((mkRat 9 64), (mkRat 361 2304)),
    ((mkRat 361 2304), (mkRat 25 144)),
    ((mkRat 25 144), (mkRat 49 256)),
    ((mkRat 49 256), (mkRat 121 576)),
    ((mkRat 121 576), (mkRat 529 2304)),
    ((mkRat 529 2304), (mkRat 1 4)),
    ((mkRat 1 4), (mkRat 625 2304)),
    ((mkRat 625 2304), (mkRat 169 576)),
    ((mkRat 169 576), (mkRat 81 256)),
    ((mkRat 81 256), (mkRat 49 144)),
    ((mkRat 49 144), (mkRat 841 2304)),
    ((mkRat 841 2304), (mkRat 25 64)),
    ((mkRat 25 64), (mkRat 961 2304)),
    ((mkRat 961 2304), (mkRat 4 9)),
    ((mkRat 4 9), (mkRat 121 256)),
    ((mkRat 121 256), (mkRat 289 576)),
    ((mkRat 289 576), (mkRat 1225 2304)),
    ((mkRat 1225 2304), (mkRat 9 16)),
    ((mkRat 9 16), (mkRat 1369 2304)),
    ((mkRat 1369 2304), (mkRat 361 576)),
    ((mkRat 361 576), (mkRat 169 256)),
    ((mkRat 169 256), (mkRat 25 36)),
    ((mkRat 25 36), (mkRat 1681 2304)),
    ((mkRat 1681 2304), (mkRat 49 64)),
    ((mkRat 49 64), (mkRat 1849 2304)),
    ((mkRat 1849 2304), (mkRat 121 144)),
    ((mkRat 121 144), (mkRat 225 256)),
    ((mkRat 225 256), (mkRat 529 576)),
    ((mkRat 529 576), (mkRat 2209 2304)),
    ((mkRat 2209 2304), (mkRat 1 1))
  ]

theorem data_checked : data.check = true := by
  decide +kernel

theorem common_coefficients_checked : checkCommonCauchy 226 231 scaleNat data.upper = true := by
  exact checkCommonCauchy_of_endpoint 226 231 scaleNat data.upper (by decide) (by decide +kernel)

def segments0 : List Segment := [
  ⟨576460752303423488, .threshold⟩,
  ⟨864691128455135232, (.numeric ⟨24576, (.recurrence 16 (.basic false true)), (.convexRiemann 281472829227008)⟩)⟩,
  ⟨936748722493063168, (.numeric ⟨24576, (.recurrence 16 (.basic false true)), (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨1008806316530991104, (.numeric ⟨24576, (.recurrence 16 (.basic false true)), (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨1152921504606846976, (.numeric ⟨24576, (.recurrence 16 (.basic false true)), (.splitRaw (mkRat 1 2))⟩)⟩,
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
  ⟨14411518807585587200, (.numeric ⟨24576, (.recurrence 8 (.basic true true)), (.splitRaw (mkRat 1 4))⟩)⟩,
  ⟨14987979559889010688, (.numeric ⟨24576, (.recurrence 16 (.basic true true)), (.convexRiemann 281474974613504)⟩)⟩,
  ⟨16140901064495857664, (.numeric ⟨24576, (.recurrence 8 (.basic true true)), .geometric⟩)⟩,
  ⟨18446744073709551616, (.numeric ⟨24576, (.recurrence 8 (.basic true false)), .geometric⟩)⟩
]

end Schmeisser.Certificates.Finite.Generated.M226_231

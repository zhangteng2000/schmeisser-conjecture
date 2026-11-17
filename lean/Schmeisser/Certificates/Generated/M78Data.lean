import Schmeisser.Certificates.BlockSoundness
import Schmeisser.Certificates.Generated.M78Coefficients

namespace Schmeisser.Certificates.Finite.Generated.M78

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

def data : Data where
  lo := 78
  hi := 78
  cutoff := 1829998325409513472
  upper := coefficients.upper
  panels := [
    ((mkRat 0 1), (mkRat 1 144)),
    ((mkRat 1 144), (mkRat 1 36)),
    ((mkRat 1 36), (mkRat 1 16)),
    ((mkRat 1 16), (mkRat 1 9)),
    ((mkRat 1 9), (mkRat 25 144)),
    ((mkRat 25 144), (mkRat 1 4)),
    ((mkRat 1 4), (mkRat 49 144)),
    ((mkRat 49 144), (mkRat 4 9)),
    ((mkRat 4 9), (mkRat 9 16)),
    ((mkRat 9 16), (mkRat 25 36)),
    ((mkRat 25 36), (mkRat 121 144)),
    ((mkRat 121 144), (mkRat 1 1))
  ]

theorem data_checked : data.check = true := by
  decide +kernel

def segments0 : List Segment := [
  ⟨1729382256910270464, .threshold⟩,
  ⟨2017612633061982208, (.numeric ⟨24576, (.recurrence 16 (.basic false true)), (.convexRiemann 3840)⟩)⟩,
  ⟨2161727821137838080, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), (.convexRiemann 3840)⟩)⟩,
  ⟨2305843009213693952, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), (.convexRiemann 3840)⟩)⟩,
  ⟨2594073385365405696, (.numeric ⟨24576, (.recurrence 16 (.basic false true)), (.convexRiemann 3840)⟩)⟩,
  ⟨2882303761517117440, (.numeric ⟨24576, (.recurrence 16 (.basic false true)), (.convexRiemann 3968)⟩)⟩,
  ⟨3170534137668829184, (.numeric ⟨24576, (.recurrence 16 (.basic false true)), (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨3458764513820540928, (.numeric ⟨24576, (.recurrence 16 (.basic false true)), (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨4035225266123964416, (.numeric ⟨24576, (.recurrence 16 (.basic false true)), (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨4611686018427387904, (.numeric ⟨24576, (.recurrence 16 (.basic false true)), (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨5188146770730811392, (.numeric ⟨24576, (.recurrence 16 (.basic false true)), (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨5764607523034234880, (.numeric ⟨24576, (.recurrence 16 (.basic false true)), (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨6917529027641081856, (.numeric ⟨24576, (.recurrence 16 (.basic false true)), (.convexRiemann 4032)⟩)⟩,
  ⟨8070450532247928832, (.numeric ⟨24576, (.recurrence 16 (.basic false true)), (.convexRiemann 4032)⟩)⟩,
  ⟨9223372036854775808, (.numeric ⟨24576, (.recurrence 16 (.basic false true)), (.splitRaw (mkRat 1 4))⟩)⟩,
  ⟨10376293541461622784, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), (.splitRaw (mkRat 1 4))⟩)⟩,
  ⟨11529215046068469760, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), (.splitRaw (mkRat 1 4))⟩)⟩,
  ⟨12682136550675316736, (.numeric ⟨24576, (.recurrence 16 (.basic false true)), (.splitRaw (mkRat 1 4))⟩)⟩,
  ⟨13258597302978740224, (.numeric ⟨24576, (.recurrence 16 (.basic false true)), (.splitRaw (mkRat 1 4))⟩)⟩,
  ⟨13835058055282163712, (.numeric ⟨24576, (.recurrence 16 (.basic false true)), (.splitRaw (mkRat 1 4))⟩)⟩,
  ⟨14411518807585587200, (.numeric ⟨24576, (.recurrence 8 (.basic true true)), (.splitRaw (mkRat 1 4))⟩)⟩,
  ⟨16140901064495857664, (.numeric ⟨24576, (.recurrence 8 (.basic true true)), .geometric⟩)⟩,
  ⟨18446744073709551616, (.numeric ⟨24576, (.recurrence 8 (.basic true false)), .geometric⟩)⟩
]

end Schmeisser.Certificates.Finite.Generated.M78

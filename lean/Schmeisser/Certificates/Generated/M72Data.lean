import Schmeisser.Certificates.BlockSoundness
import Schmeisser.Certificates.Generated.M72Coefficients

namespace Schmeisser.Certificates.Finite.Generated.M72

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

def data : Data where
  lo := 72
  hi := 72
  cutoff := 1946244762853113856
  upper := coefficients.upper
  panels := [
    ((mkRat 0 1), (mkRat 1 256)),
    ((mkRat 1 256), (mkRat 1 64)),
    ((mkRat 1 64), (mkRat 9 256)),
    ((mkRat 9 256), (mkRat 1 16)),
    ((mkRat 1 16), (mkRat 25 256)),
    ((mkRat 25 256), (mkRat 9 64)),
    ((mkRat 9 64), (mkRat 49 256)),
    ((mkRat 49 256), (mkRat 1 4)),
    ((mkRat 1 4), (mkRat 81 256)),
    ((mkRat 81 256), (mkRat 25 64)),
    ((mkRat 25 64), (mkRat 121 256)),
    ((mkRat 121 256), (mkRat 9 16)),
    ((mkRat 9 16), (mkRat 169 256)),
    ((mkRat 169 256), (mkRat 49 64)),
    ((mkRat 49 64), (mkRat 225 256)),
    ((mkRat 225 256), (mkRat 1 1))
  ]

theorem data_checked : data.check = true := by
  decide +kernel

def segments0 : List Segment := [
  ⟨1729382256910270464, .threshold⟩,
  ⟨2017612633061982208, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), (.convexRiemann 63488)⟩)⟩,
  ⟨2161727821137838080, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), (.convexRiemann 63488)⟩)⟩,
  ⟨2305843009213693952, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), (.convexRiemann 63488)⟩)⟩,
  ⟨2594073385365405696, (.numeric ⟨24576, (.recurrence 16 (.basic false true)), (.convexRiemann 64512)⟩)⟩,
  ⟨2882303761517117440, (.numeric ⟨24576, (.recurrence 16 (.basic false true)), (.convexRiemann 64512)⟩)⟩,
  ⟨3170534137668829184, (.numeric ⟨24576, (.recurrence 16 (.basic false true)), (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨3458764513820540928, (.numeric ⟨24576, (.recurrence 16 (.basic false true)), (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨4035225266123964416, (.numeric ⟨24576, (.recurrence 32 (.basic false true)), (.convexRiemann 64512)⟩)⟩,
  ⟨4611686018427387904, (.numeric ⟨24576, (.recurrence 16 (.basic false true)), (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨5188146770730811392, (.numeric ⟨24576, (.recurrence 16 (.basic false true)), (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨5764607523034234880, (.numeric ⟨24576, (.recurrence 16 (.basic false true)), (.splitRaw (mkRat 1 2))⟩)⟩,
  ⟨6917529027641081856, (.numeric ⟨24576, (.recurrence 16 (.basic false true)), (.convexRiemann 65024)⟩)⟩,
  ⟨8070450532247928832, (.numeric ⟨24576, (.recurrence 16 (.basic false true)), (.convexRiemann 65280)⟩)⟩,
  ⟨9223372036854775808, (.numeric ⟨24576, (.recurrence 16 (.basic false true)), (.convexRiemann 65280)⟩)⟩,
  ⟨10376293541461622784, (.numeric ⟨24576, (.recurrence 16 (.basic false true)), (.splitRaw (mkRat 1 4))⟩)⟩,
  ⟨11529215046068469760, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), (.splitRaw (mkRat 1 4))⟩)⟩,
  ⟨12682136550675316736, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), (.splitRaw (mkRat 1 4))⟩)⟩,
  ⟨13258597302978740224, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), (.splitRaw (mkRat 1 4))⟩)⟩,
  ⟨13835058055282163712, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), (.splitRaw (mkRat 1 4))⟩)⟩,
  ⟨14411518807585587200, (.numeric ⟨24576, (.recurrence 8 (.basic true true)), .geometric⟩)⟩,
  ⟨16140901064495857664, (.numeric ⟨24576, (.recurrence 8 (.basic true true)), .geometric⟩)⟩,
  ⟨18446744073709551616, (.numeric ⟨24576, (.recurrence 8 (.basic true false)), .geometric⟩)⟩
]

end Schmeisser.Certificates.Finite.Generated.M72

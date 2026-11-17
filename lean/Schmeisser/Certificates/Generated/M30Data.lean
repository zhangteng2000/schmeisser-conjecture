import Schmeisser.Certificates.BlockSoundness
import Schmeisser.Certificates.Generated.M30Coefficients

namespace Schmeisser.Certificates.Finite.Generated.M30

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

def data : Data where
  lo := 30
  hi := 30
  cutoff := 3745150881162330112
  upper := coefficients.upper
  panels := [
    ((mkRat 0 1), (mkRat 1 64)),
    ((mkRat 1 64), (mkRat 1 16)),
    ((mkRat 1 16), (mkRat 9 64)),
    ((mkRat 9 64), (mkRat 1 4)),
    ((mkRat 1 4), (mkRat 25 64)),
    ((mkRat 25 64), (mkRat 9 16)),
    ((mkRat 9 16), (mkRat 49 64)),
    ((mkRat 49 64), (mkRat 1 1))
  ]

theorem data_checked : data.check = true := by
  decide +kernel

def segments0 : List Segment := [
  ⟨3458764513820540928, .threshold⟩,
  ⟨3891110078048108544, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), (.convexRiemann 192)⟩)⟩,
  ⟨4035225266123964416, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), (.convexRiemann 192)⟩)⟩,
  ⟨4179340454199820288, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), (.convexRiemann 192)⟩)⟩,
  ⟨4323455642275676160, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), (.convexRiemann 192)⟩)⟩,
  ⟨4611686018427387904, (.numeric ⟨24576, (.recurrence 14 .exactTwo), (.convexRiemann 192)⟩)⟩,
  ⟨4899916394579099648, (.numeric ⟨24576, (.recurrence 14 .exactTwo), (.convexRiemann 192)⟩)⟩,
  ⟨5188146770730811392, (.numeric ⟨24576, (.recurrence 14 .exactTwo), (.convexRiemann 224)⟩)⟩,
  ⟨5476377146882523136, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), (.convexRiemann 224)⟩)⟩,
  ⟨5764607523034234880, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), (.convexRiemann 224)⟩)⟩,
  ⟨6052837899185946624, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), (.convexRiemann 224)⟩)⟩,
  ⟨6341068275337658368, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), (.convexRiemann 224)⟩)⟩,
  ⟨6629298651489370112, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), (.convexRiemann 224)⟩)⟩,
  ⟨6917529027641081856, (.numeric ⟨24576, (.recurrence 14 .exactTwo), .finite⟩)⟩,
  ⟨7493989779944505344, (.numeric ⟨24576, (.recurrence 14 .exactTwo), (.convexRiemann 224)⟩)⟩,
  ⟨8070450532247928832, (.numeric ⟨24576, (.recurrence 14 .exactTwo), (.convexRiemann 224)⟩)⟩,
  ⟨8646911284551352320, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), .finite⟩)⟩,
  ⟨9223372036854775808, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), .finite⟩)⟩,
  ⟨9799832789158199296, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), .finite⟩)⟩,
  ⟨10376293541461622784, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), .finite⟩)⟩,
  ⟨11529215046068469760, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), .finite⟩)⟩,
  ⟨12682136550675316736, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), .finite⟩)⟩,
  ⟨13835058055282163712, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), .finite⟩)⟩,
  ⟨14987979559889010688, (.numeric ⟨24576, (.recurrence 8 (.basic true true)), .geometric⟩)⟩,
  ⟨16140901064495857664, (.numeric ⟨24576, (.recurrence 8 (.basic true true)), .geometric⟩)⟩,
  ⟨17293822569102704640, (.numeric ⟨24576, (.recurrence 8 (.basic true true)), .geometric⟩)⟩,
  ⟨18446744073709551616, (.numeric ⟨24576, (.recurrence 8 (.basic true false)), .geometric⟩)⟩
]

end Schmeisser.Certificates.Finite.Generated.M30

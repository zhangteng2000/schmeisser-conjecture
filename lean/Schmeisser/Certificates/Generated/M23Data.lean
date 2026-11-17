import Schmeisser.Certificates.BlockSoundness
import Schmeisser.Certificates.Generated.M23Coefficients

namespace Schmeisser.Certificates.Finite.Generated.M23

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

def data : Data where
  lo := 23
  hi := 23
  cutoff := 4530778523741782016
  upper := coefficients.upper
  panels := [
    ((mkRat 0 1), (mkRat 1 12)),
    ((mkRat 1 12), (mkRat 1 6)),
    ((mkRat 1 6), (mkRat 1 4)),
    ((mkRat 1 4), (mkRat 1 3)),
    ((mkRat 1 3), (mkRat 5 12)),
    ((mkRat 5 12), (mkRat 1 2)),
    ((mkRat 1 2), (mkRat 7 12)),
    ((mkRat 7 12), (mkRat 2 3)),
    ((mkRat 2 3), (mkRat 3 4)),
    ((mkRat 3 4), (mkRat 5 6)),
    ((mkRat 5 6), (mkRat 11 12)),
    ((mkRat 11 12), (mkRat 1 1))
  ]

theorem data_checked : data.check = true := by
  decide +kernel

def segments0 : List Segment := [
  ⟨4755801206503243776, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), (.convexRiemann 3968)⟩)⟩,
  ⟨5044031582654955520, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), (.convexRiemann 4032)⟩)⟩,
  ⟨5332261958806667264, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), (.convexRiemann 4032)⟩)⟩,
  ⟨5620492334958379008, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), (.convexRiemann 4032)⟩)⟩,
  ⟨5764607523034234880, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), (.convexRiemann 4032)⟩)⟩,
  ⟨6052837899185946624, (.numeric ⟨24576, (.recurrence 10 .trapezoidThree), (.convexRiemann 4032)⟩)⟩,
  ⟨6341068275337658368, (.numeric ⟨24576, (.recurrence 10 .trapezoidThree), (.convexRiemann 4032)⟩)⟩,
  ⟨6629298651489370112, (.numeric ⟨24576, (.recurrence 10 .trapezoidThree), (.convexRiemann 4032)⟩)⟩,
  ⟨6917529027641081856, (.numeric ⟨24576, (.recurrence 10 .trapezoidThree), (.convexRiemann 4032)⟩)⟩,
  ⟨7205759403792793600, (.numeric ⟨24576, (.recurrence 10 .trapezoidThree), (.convexRiemann 4032)⟩)⟩,
  ⟨7493989779944505344, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), (.convexRiemann 4032)⟩)⟩,
  ⟨7782220156096217088, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), (.convexRiemann 4064)⟩)⟩,
  ⟨8070450532247928832, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), (.convexRiemann 4064)⟩)⟩,
  ⟨8358680908399640576, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), (.convexRiemann 4064)⟩)⟩,
  ⟨8646911284551352320, (.numeric ⟨24576, (.recurrence 7 (.basic false true)), (.convexRiemann 4064)⟩)⟩,
  ⟨8935141660703064064, (.numeric ⟨24576, (.recurrence 7 (.basic false true)), (.convexRiemann 4064)⟩)⟩
]

def segments1 : List Segment := [
  ⟨9223372036854775808, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), .finite⟩)⟩,
  ⟨9511602413006487552, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), .finite⟩)⟩,
  ⟨9799832789158199296, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), .finite⟩)⟩,
  ⟨10376293541461622784, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), .finite⟩)⟩,
  ⟨10952754293765046272, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), .finite⟩)⟩,
  ⟨11529215046068469760, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), .finite⟩)⟩,
  ⟨12105675798371893248, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), .finite⟩)⟩,
  ⟨12682136550675316736, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), .finite⟩)⟩,
  ⟨13835058055282163712, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), .finite⟩)⟩,
  ⟨14987979559889010688, (.numeric ⟨24576, (.recurrence 8 (.basic true true)), .geometric⟩)⟩,
  ⟨16140901064495857664, (.numeric ⟨24576, (.recurrence 8 (.basic true true)), .geometric⟩)⟩,
  ⟨17293822569102704640, (.numeric ⟨24576, (.recurrence 8 (.basic true true)), .geometric⟩)⟩,
  ⟨18446744073709551616, (.numeric ⟨24576, (.recurrence 8 (.basic true false)), .geometric⟩)⟩
]

end Schmeisser.Certificates.Finite.Generated.M23

import Schmeisser.Certificates.BlockSoundness
import Schmeisser.Certificates.Generated.M17Coefficients

namespace Schmeisser.Certificates.Finite.Generated.M17

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

def data : Data where
  lo := 17
  hi := 17
  cutoff := 5593896142522744832
  upper := coefficients.upper
  panels := [
    ((mkRat 0 1), (mkRat 1 16)),
    ((mkRat 1 16), (mkRat 1 8)),
    ((mkRat 1 8), (mkRat 3 16)),
    ((mkRat 3 16), (mkRat 1 4)),
    ((mkRat 1 4), (mkRat 5 16)),
    ((mkRat 5 16), (mkRat 3 8)),
    ((mkRat 3 8), (mkRat 7 16)),
    ((mkRat 7 16), (mkRat 1 2)),
    ((mkRat 1 2), (mkRat 9 16)),
    ((mkRat 9 16), (mkRat 5 8)),
    ((mkRat 5 8), (mkRat 11 16)),
    ((mkRat 11 16), (mkRat 3 4)),
    ((mkRat 3 4), (mkRat 13 16)),
    ((mkRat 13 16), (mkRat 7 8)),
    ((mkRat 7 8), (mkRat 15 16)),
    ((mkRat 15 16), (mkRat 1 1))
  ]

theorem data_checked : data.check = true := by
  decide +kernel

def segments0 : List Segment := [
  ⟨4611686018427387904, .threshold⟩,
  ⟨5764607523034234880, (.numeric ⟨24576, (.recurrence 7 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨5908722711110090752, (.numeric ⟨24576, (.recurrence 7 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨6052837899185946624, (.numeric ⟨24576, (.recurrence 7 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨6341068275337658368, (.numeric ⟨24576, (.recurrence 7 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨6629298651489370112, (.numeric ⟨25232, (.recurrence 7 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨6917529027641081856, (.numeric ⟨25024, (.recurrence 7 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨7205759403792793600, (.numeric ⟨24576, (.recurrence 7 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨7493989779944505344, (.numeric ⟨24576, (.recurrence 7 .trapezoidThree), (.convexRiemann 65280)⟩)⟩,
  ⟨7782220156096217088, (.numeric ⟨24576, (.recurrence 7 .trapezoidThree), (.convexRiemann 65280)⟩)⟩,
  ⟨8070450532247928832, (.numeric ⟨24576, (.recurrence 7 .trapezoidThree), (.convexRiemann 65280)⟩)⟩,
  ⟨8358680908399640576, (.numeric ⟨24576, (.recurrence 7 .trapezoidThree), (.convexRiemann 65280)⟩)⟩,
  ⟨8646911284551352320, (.numeric ⟨24576, (.recurrence 7 .trapezoidThree), (.convexRiemann 65280)⟩)⟩,
  ⟨8935141660703064064, (.numeric ⟨24576, (.recurrence 7 .trapezoidThree), (.convexRiemann 65280)⟩)⟩,
  ⟨9223372036854775808, (.numeric ⟨24576, (.recurrence 7 .trapezoidThree), (.convexRiemann 65280)⟩)⟩,
  ⟨9511602413006487552, (.numeric ⟨24576, (.recurrence 7 .trapezoidThree), (.convexRiemann 65280)⟩)⟩
]

def segments1 : List Segment := [
  ⟨9799832789158199296, (.numeric ⟨24576, (.recurrence 7 .trapezoidThree), (.convexRiemann 65280)⟩)⟩,
  ⟨10088063165309911040, (.numeric ⟨24576, (.recurrence 7 .trapezoidThree), (.convexRiemann 65280)⟩)⟩,
  ⟨10376293541461622784, (.numeric ⟨24576, (.recurrence 7 .trapezoidThree), (.convexRiemann 65280)⟩)⟩,
  ⟨10664523917613334528, (.numeric ⟨24576, (.recurrence 7 .trapezoidThree), (.convexRiemann 65280)⟩)⟩,
  ⟨10952754293765046272, (.numeric ⟨24576, (.recurrence 7 .trapezoidThree), (.convexRiemann 65280)⟩)⟩,
  ⟨11240984669916758016, (.numeric ⟨24576, (.recurrence 6 (.basic false true)), (.convexRiemann 65280)⟩)⟩,
  ⟨11529215046068469760, (.numeric ⟨24576, (.recurrence 7 .trapezoidThree), .finite⟩)⟩,
  ⟨11817445422220181504, (.numeric ⟨24576, (.recurrence 7 .trapezoidThree), .finite⟩)⟩,
  ⟨12105675798371893248, (.numeric ⟨24576, (.recurrence 7 .trapezoidThree), .finite⟩)⟩,
  ⟨12393906174523604992, (.numeric ⟨24576, (.recurrence 7 .trapezoidThree), .finite⟩)⟩,
  ⟨12682136550675316736, (.numeric ⟨24576, (.recurrence 7 .trapezoidThree), .finite⟩)⟩,
  ⟨13258597302978740224, (.numeric ⟨24576, (.recurrence 7 .trapezoidThree), .finite⟩)⟩,
  ⟨13835058055282163712, (.numeric ⟨24576, (.recurrence 7 .trapezoidThree), .finite⟩)⟩,
  ⟨14411518807585587200, (.numeric ⟨24576, (.recurrence 7 .trapezoidThree), .geometric⟩)⟩,
  ⟨14987979559889010688, (.numeric ⟨24576, (.recurrence 7 .trapezoidThree), .geometric⟩)⟩,
  ⟨16140901064495857664, (.numeric ⟨24576, (.recurrence 7 .trapezoidThree), .geometric⟩)⟩
]

def segments2 : List Segment := [
  ⟨17293822569102704640, (.numeric ⟨24576, (.recurrence 7 .trapezoidThree), .geometric⟩)⟩,
  ⟨18446744073709551616, (.numeric ⟨24576, (.recurrence 7 .trapezoidThree), .geometric⟩)⟩
]

end Schmeisser.Certificates.Finite.Generated.M17

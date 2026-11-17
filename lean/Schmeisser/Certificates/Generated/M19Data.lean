import Schmeisser.Certificates.BlockSoundness
import Schmeisser.Certificates.Generated.M19Coefficients

namespace Schmeisser.Certificates.Finite.Generated.M19

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

def data : Data where
  lo := 19
  hi := 19
  cutoff := 5180514431347458048
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
  ⟨4611686018427387904, .threshold⟩,
  ⟨5476377146882523136, (.numeric ⟨24576, (.recurrence 8 .trapezoidThree), (.convexRiemann 61440)⟩)⟩,
  ⟨5764607523034234880, (.numeric ⟨25588, (.recurrence 8 .trapezoidThree), (.convexRiemann 61440)⟩)⟩,
  ⟨6052837899185946624, (.numeric ⟨24576, (.recurrence 8 .trapezoidThree), (.convexRiemann 61440)⟩)⟩,
  ⟨6341068275337658368, (.numeric ⟨24576, (.recurrence 8 .trapezoidThree), (.convexRiemann 61440)⟩)⟩,
  ⟨6629298651489370112, (.numeric ⟨24576, (.recurrence 8 .trapezoidThree), (.convexRiemann 61440)⟩)⟩,
  ⟨6917529027641081856, (.numeric ⟨24576, (.recurrence 8 .trapezoidThree), (.convexRiemann 63488)⟩)⟩,
  ⟨7205759403792793600, (.numeric ⟨24576, (.recurrence 8 .trapezoidThree), (.convexRiemann 63488)⟩)⟩,
  ⟨7493989779944505344, (.numeric ⟨24576, (.recurrence 8 .trapezoidThree), (.convexRiemann 63488)⟩)⟩,
  ⟨7782220156096217088, (.numeric ⟨24576, (.recurrence 8 .trapezoidThree), (.convexRiemann 63488)⟩)⟩,
  ⟨8070450532247928832, (.numeric ⟨24576, (.recurrence 8 .trapezoidThree), (.convexRiemann 63488)⟩)⟩,
  ⟨8358680908399640576, (.numeric ⟨24576, (.recurrence 8 .trapezoidThree), (.convexRiemann 63488)⟩)⟩,
  ⟨8646911284551352320, (.numeric ⟨24576, (.recurrence 8 .trapezoidThree), (.convexRiemann 63488)⟩)⟩,
  ⟨8935141660703064064, (.numeric ⟨24576, (.recurrence 8 .trapezoidThree), (.convexRiemann 63488)⟩)⟩,
  ⟨9223372036854775808, (.numeric ⟨24576, (.recurrence 8 .trapezoidThree), (.convexRiemann 63488)⟩)⟩,
  ⟨9511602413006487552, (.numeric ⟨24576, (.recurrence 8 .trapezoidThree), (.convexRiemann 63488)⟩)⟩
]

def segments1 : List Segment := [
  ⟨9799832789158199296, (.numeric ⟨24576, (.recurrence 8 .trapezoidThree), (.convexRiemann 63488)⟩)⟩,
  ⟨10088063165309911040, (.numeric ⟨24576, (.recurrence 8 .trapezoidThree), (.convexRiemann 63488)⟩)⟩,
  ⟨10376293541461622784, (.numeric ⟨24576, (.recurrence 8 .trapezoidThree), .finite⟩)⟩,
  ⟨10952754293765046272, (.numeric ⟨24576, (.recurrence 8 .trapezoidThree), (.convexRiemann 63488)⟩)⟩,
  ⟨11529215046068469760, (.numeric ⟨24576, (.recurrence 8 .trapezoidThree), (.convexRiemann 63488)⟩)⟩,
  ⟨12105675798371893248, (.numeric ⟨24576, (.recurrence 8 .trapezoidThree), .finite⟩)⟩,
  ⟨12682136550675316736, (.numeric ⟨24576, (.recurrence 8 .trapezoidThree), .finite⟩)⟩,
  ⟨13258597302978740224, (.numeric ⟨24576, (.recurrence 8 .trapezoidThree), .finite⟩)⟩,
  ⟨13835058055282163712, (.numeric ⟨24576, (.recurrence 8 .trapezoidThree), .finite⟩)⟩,
  ⟨14987979559889010688, (.numeric ⟨24576, (.recurrence 8 .trapezoidThree), .finite⟩)⟩,
  ⟨16140901064495857664, (.numeric ⟨24576, (.recurrence 8 .trapezoidThree), .geometric⟩)⟩,
  ⟨17293822569102704640, (.numeric ⟨24576, (.recurrence 8 .trapezoidThree), .geometric⟩)⟩,
  ⟨18446744073709551616, (.numeric ⟨24576, (.recurrence 8 .trapezoidThree), .geometric⟩)⟩
]

end Schmeisser.Certificates.Finite.Generated.M19

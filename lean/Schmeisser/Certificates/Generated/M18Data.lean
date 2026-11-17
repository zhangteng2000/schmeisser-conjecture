import Schmeisser.Certificates.BlockSoundness
import Schmeisser.Certificates.Generated.M18Coefficients

namespace Schmeisser.Certificates.Finite.Generated.M18

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

def data : Data where
  lo := 18
  hi := 18
  cutoff := 5378142055305183232
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
  ⟨5188146770730811392, .threshold⟩,
  ⟨5620492334958379008, (.numeric ⟨24576, (.recurrence 8 .exactTwo), (.convexRiemann 3584)⟩)⟩,
  ⟨5764607523034234880, (.numeric ⟨24576, (.recurrence 8 .exactTwo), (.convexRiemann 3584)⟩)⟩,
  ⟨6052837899185946624, (.numeric ⟨25506, (.recurrence 8 .exactTwo), (.convexRiemann 3584)⟩)⟩,
  ⟨6341068275337658368, (.numeric ⟨25286, (.recurrence 8 .exactTwo), (.convexRiemann 3584)⟩)⟩,
  ⟨6629298651489370112, (.numeric ⟨24576, (.recurrence 8 .exactTwo), (.convexRiemann 3584)⟩)⟩,
  ⟨6917529027641081856, (.numeric ⟨24576, (.recurrence 8 .exactTwo), (.convexRiemann 3584)⟩)⟩,
  ⟨7205759403792793600, (.numeric ⟨24576, (.recurrence 8 .exactTwo), (.convexRiemann 3584)⟩)⟩,
  ⟨7493989779944505344, (.numeric ⟨24576, (.recurrence 8 .exactTwo), (.convexRiemann 3584)⟩)⟩,
  ⟨7782220156096217088, (.numeric ⟨24576, (.recurrence 8 .exactTwo), (.convexRiemann 3584)⟩)⟩,
  ⟨8070450532247928832, (.numeric ⟨24576, (.recurrence 8 .exactTwo), (.convexRiemann 3840)⟩)⟩,
  ⟨8358680908399640576, (.numeric ⟨24576, (.recurrence 8 .exactTwo), (.convexRiemann 3840)⟩)⟩,
  ⟨8646911284551352320, (.numeric ⟨24576, (.recurrence 8 .exactTwo), (.convexRiemann 3840)⟩)⟩,
  ⟨8935141660703064064, (.numeric ⟨24576, (.recurrence 8 .exactTwo), (.convexRiemann 3840)⟩)⟩,
  ⟨9223372036854775808, (.numeric ⟨24576, (.recurrence 8 .exactTwo), (.convexRiemann 3840)⟩)⟩,
  ⟨9511602413006487552, (.numeric ⟨24576, (.recurrence 8 .exactTwo), (.convexRiemann 3840)⟩)⟩,
  ⟨9799832789158199296, (.numeric ⟨24576, (.recurrence 8 .exactTwo), (.convexRiemann 3840)⟩)⟩,
  ⟨10088063165309911040, (.numeric ⟨24576, (.recurrence 8 .exactTwo), (.convexRiemann 3840)⟩)⟩,
  ⟨10376293541461622784, (.numeric ⟨24576, (.recurrence 8 .exactTwo), (.convexRiemann 3840)⟩)⟩,
  ⟨10664523917613334528, (.numeric ⟨24576, (.recurrence 6 (.basic false true)), (.convexRiemann 3840)⟩)⟩,
  ⟨10952754293765046272, (.numeric ⟨24576, (.recurrence 8 .exactTwo), .finite⟩)⟩,
  ⟨11240984669916758016, (.numeric ⟨24576, (.recurrence 8 .exactTwo), .finite⟩)⟩,
  ⟨11529215046068469760, (.numeric ⟨24576, (.recurrence 8 .exactTwo), .finite⟩)⟩,
  ⟨11817445422220181504, (.numeric ⟨24576, (.recurrence 8 .exactTwo), .finite⟩)⟩,
  ⟨12105675798371893248, (.numeric ⟨24576, (.recurrence 8 .exactTwo), .finite⟩)⟩,
  ⟨12682136550675316736, (.numeric ⟨24576, (.recurrence 8 .exactTwo), .finite⟩)⟩,
  ⟨13258597302978740224, (.numeric ⟨24576, (.recurrence 8 .exactTwo), .finite⟩)⟩,
  ⟨13835058055282163712, (.numeric ⟨24576, (.recurrence 8 .exactTwo), .finite⟩)⟩,
  ⟨14411518807585587200, (.numeric ⟨24576, (.recurrence 8 .exactTwo), .geometric⟩)⟩,
  ⟨14987979559889010688, (.numeric ⟨24576, (.recurrence 8 .exactTwo), .geometric⟩)⟩,
  ⟨16140901064495857664, (.numeric ⟨24576, (.recurrence 8 .exactTwo), .geometric⟩)⟩,
  ⟨17293822569102704640, (.numeric ⟨24576, (.recurrence 8 .exactTwo), .geometric⟩)⟩,
  ⟨18446744073709551616, (.numeric ⟨24576, (.recurrence 8 .exactTwo), .geometric⟩)⟩
]

end Schmeisser.Certificates.Finite.Generated.M18

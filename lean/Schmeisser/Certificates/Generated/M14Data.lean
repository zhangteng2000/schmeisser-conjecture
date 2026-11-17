import Schmeisser.Certificates.BlockSoundness
import Schmeisser.Certificates.Generated.M14Coefficients

namespace Schmeisser.Certificates.Finite.Generated.M14

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

def data : Data where
  lo := 14
  hi := 14
  cutoff := 6380732328535785472
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
  ⟨6341068275337658368, .threshold⟩,
  ⟨6485183463413514240, (.numeric ⟨24576, (.recurrence 6 .exactTwo), (.convexRiemann 64512)⟩)⟩,
  ⟨6629298651489370112, (.numeric ⟨24576, (.recurrence 6 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨6773413839565225984, (.numeric ⟨24576, (.recurrence 6 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨6917529027641081856, (.numeric ⟨24576, (.recurrence 6 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨7061644215716937728, (.numeric ⟨24576, (.recurrence 6 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨7205759403792793600, (.numeric ⟨24576, (.recurrence 6 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨7349874591868649472, (.numeric ⟨24576, (.recurrence 6 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨7493989779944505344, (.numeric ⟨24576, (.recurrence 6 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨7638104968020361216, (.numeric ⟨24576, (.recurrence 6 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨7782220156096217088, (.numeric ⟨24576, (.recurrence 6 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨7926335344172072960, (.numeric ⟨24576, (.recurrence 6 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨8070450532247928832, (.numeric ⟨24576, (.recurrence 6 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨8214565720323784704, (.numeric ⟨24576, (.recurrence 6 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨8358680908399640576, (.numeric ⟨24576, (.recurrence 6 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨8502796096475496448, (.numeric ⟨24576, (.recurrence 6 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨8646911284551352320, (.numeric ⟨24576, (.recurrence 6 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨8791026472627208192, (.numeric ⟨24576, (.recurrence 6 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨8935141660703064064, (.numeric ⟨24576, (.recurrence 6 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨9079256848778919936, (.numeric ⟨24576, (.recurrence 6 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨9223372036854775808, (.numeric ⟨24576, (.recurrence 6 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨9367487224930631680, (.numeric ⟨24576, (.recurrence 6 .exactTwo), (.convexRiemann 65280)⟩)⟩,
  ⟨9511602413006487552, (.numeric ⟨24576, (.recurrence 6 .exactTwo), (.convexRiemann 65280)⟩)⟩,
  ⟨9655717601082343424, (.numeric ⟨24576, (.recurrence 6 .exactTwo), (.convexRiemann 65280)⟩)⟩,
  ⟨9799832789158199296, (.numeric ⟨24576, (.recurrence 6 .exactTwo), (.convexRiemann 65280)⟩)⟩,
  ⟨9943947977234055168, (.numeric ⟨24576, (.recurrence 6 .exactTwo), (.convexRiemann 65280)⟩)⟩,
  ⟨10088063165309911040, (.numeric ⟨24576, (.recurrence 6 .exactTwo), (.convexRiemann 65280)⟩)⟩,
  ⟨10232178353385766912, (.numeric ⟨24576, (.recurrence 6 .exactTwo), (.convexRiemann 65280)⟩)⟩,
  ⟨10376293541461622784, (.numeric ⟨24576, (.recurrence 6 .exactTwo), (.convexRiemann 65280)⟩)⟩,
  ⟨10520408729537478656, (.numeric ⟨24576, (.recurrence 6 .exactTwo), (.convexRiemann 65280)⟩)⟩,
  ⟨10664523917613334528, (.numeric ⟨24576, (.recurrence 6 .exactTwo), (.convexRiemann 65280)⟩)⟩,
  ⟨10808639105689190400, (.numeric ⟨24576, (.recurrence 6 .exactTwo), (.convexRiemann 65280)⟩)⟩,
  ⟨10952754293765046272, (.numeric ⟨24576, (.recurrence 6 .exactTwo), (.convexRiemann 65280)⟩)⟩
]

def segments1 : List Segment := [
  ⟨11096869481840902144, (.numeric ⟨24576, (.recurrence 6 .exactTwo), (.convexRiemann 65280)⟩)⟩,
  ⟨11240984669916758016, (.numeric ⟨24576, (.recurrence 6 .exactTwo), (.convexRiemann 65280)⟩)⟩,
  ⟨11385099857992613888, (.numeric ⟨24576, (.recurrence 6 .exactTwo), (.convexRiemann 65280)⟩)⟩,
  ⟨11529215046068469760, (.numeric ⟨24576, (.recurrence 6 .exactTwo), (.convexRiemann 65280)⟩)⟩,
  ⟨11673330234144325632, (.numeric ⟨24576, (.recurrence 6 .exactTwo), (.convexRiemann 65280)⟩)⟩,
  ⟨11817445422220181504, (.numeric ⟨24576, (.recurrence 6 .exactTwo), (.convexRiemann 65280)⟩)⟩,
  ⟨11961560610296037376, (.numeric ⟨24576, (.recurrence 6 .exactTwo), (.convexRiemann 65280)⟩)⟩,
  ⟨12105675798371893248, (.numeric ⟨24576, (.recurrence 5 (.basic false true)), (.convexRiemann 65280)⟩)⟩,
  ⟨12249790986447749120, (.numeric ⟨24576, (.recurrence 5 (.basic false true)), (.convexRiemann 65280)⟩)⟩,
  ⟨12393906174523604992, (.numeric ⟨24576, (.recurrence 6 .exactTwo), .finite⟩)⟩,
  ⟨12538021362599460864, (.numeric ⟨24576, (.recurrence 6 .exactTwo), .finite⟩)⟩,
  ⟨12682136550675316736, (.numeric ⟨24576, (.recurrence 6 .exactTwo), .finite⟩)⟩,
  ⟨12826251738751172608, (.numeric ⟨24576, (.recurrence 6 .exactTwo), .finite⟩)⟩,
  ⟨12970366926827028480, (.numeric ⟨24576, (.recurrence 6 .exactTwo), .finite⟩)⟩,
  ⟨13258597302978740224, (.numeric ⟨24576, (.recurrence 6 .exactTwo), .finite⟩)⟩,
  ⟨13546827679130451968, (.numeric ⟨24576, (.recurrence 6 .exactTwo), .finite⟩)⟩,
  ⟨13835058055282163712, (.numeric ⟨24576, (.recurrence 6 .exactTwo), .finite⟩)⟩,
  ⟨14411518807585587200, (.numeric ⟨24576, (.recurrence 6 .exactTwo), .finite⟩)⟩,
  ⟨14987979559889010688, (.numeric ⟨24576, (.recurrence 6 .exactTwo), .geometric⟩)⟩,
  ⟨15564440312192434176, (.numeric ⟨24576, (.recurrence 6 .exactTwo), .geometric⟩)⟩,
  ⟨16140901064495857664, (.numeric ⟨24576, (.recurrence 6 .exactTwo), .geometric⟩)⟩,
  ⟨17293822569102704640, (.numeric ⟨24576, (.recurrence 6 .exactTwo), .geometric⟩)⟩,
  ⟨18446744073709551616, (.numeric ⟨24576, (.recurrence 6 .exactTwo), .geometric⟩)⟩
]

end Schmeisser.Certificates.Finite.Generated.M14

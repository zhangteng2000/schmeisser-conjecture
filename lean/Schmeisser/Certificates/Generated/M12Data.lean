import Schmeisser.Certificates.BlockSoundness
import Schmeisser.Certificates.Generated.M12Coefficients

namespace Schmeisser.Certificates.Finite.Generated.M12

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

def data : Data where
  lo := 12
  hi := 12
  cutoff := 7066718071413997568
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
  ⟨6917529027641081856, .threshold⟩,
  ⟨7205759403792793600, (.numeric ⟨28271, (.recurrence 5 .exactTwo), (.convexRiemann 64512)⟩)⟩,
  ⟨7349874591868649472, (.numeric ⟨28100, (.recurrence 5 .exactTwo), (.convexRiemann 64512)⟩)⟩,
  ⟨7493989779944505344, (.numeric ⟨28010, (.recurrence 5 .exactTwo), (.convexRiemann 64512)⟩)⟩,
  ⟨7638104968020361216, (.numeric ⟨27923, (.recurrence 5 .exactTwo), (.convexRiemann 64512)⟩)⟩,
  ⟨7782220156096217088, (.numeric ⟨27838, (.recurrence 5 .exactTwo), (.convexRiemann 64512)⟩)⟩,
  ⟨7926335344172072960, (.numeric ⟨27756, (.recurrence 5 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨8070450532247928832, (.numeric ⟨27675, (.recurrence 5 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨8214565720323784704, (.numeric ⟨27596, (.recurrence 5 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨8358680908399640576, (.numeric ⟨27518, (.recurrence 5 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨8502796096475496448, (.numeric ⟨27441, (.recurrence 5 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨8646911284551352320, (.numeric ⟨27364, (.recurrence 5 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨8791026472627208192, (.numeric ⟨27286, (.recurrence 5 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨8935141660703064064, (.numeric ⟨27209, (.recurrence 5 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨9079256848778919936, (.numeric ⟨27130, (.recurrence 5 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨9223372036854775808, (.numeric ⟨27049, (.recurrence 5 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨9367487224930631680, (.numeric ⟨26967, (.recurrence 5 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨9511602413006487552, (.numeric ⟨26881, (.recurrence 5 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨9655717601082343424, (.numeric ⟨26793, (.recurrence 5 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨9799832789158199296, (.numeric ⟨26701, (.recurrence 5 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨9943947977234055168, (.numeric ⟨26605, (.recurrence 5 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨10088063165309911040, (.numeric ⟨26504, (.recurrence 5 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨10232178353385766912, (.numeric ⟨26397, (.recurrence 5 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨10376293541461622784, (.numeric ⟨26283, (.recurrence 5 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨10520408729537478656, (.numeric ⟨26162, (.recurrence 5 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨10664523917613334528, (.numeric ⟨26033, (.recurrence 5 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨10808639105689190400, (.numeric ⟨25894, (.recurrence 5 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨10952754293765046272, (.numeric ⟨25744, (.recurrence 5 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨11024811887802974208, (.numeric ⟨27612, (.recurrence 5 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨11096869481840902144, (.numeric ⟨27572, (.recurrence 5 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨11168927075878830080, (.numeric ⟨27531, (.recurrence 5 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨11240984669916758016, (.numeric ⟨27488, (.recurrence 5 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨11313042263954685952, (.numeric ⟨27444, (.recurrence 5 .exactTwo), (.convexRiemann 65024)⟩)⟩
]

def segments1 : List Segment := [
  ⟨11385099857992613888, (.numeric ⟨27398, (.recurrence 5 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨11457157452030541824, (.numeric ⟨27350, (.recurrence 5 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨11529215046068469760, (.numeric ⟨27301, (.recurrence 5 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨11601272640106397696, (.numeric ⟨27249, (.recurrence 5 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨11673330234144325632, (.numeric ⟨27196, (.recurrence 5 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨11745387828182253568, (.numeric ⟨27140, (.recurrence 5 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨11817445422220181504, (.numeric ⟨27082, (.recurrence 5 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨11889503016258109440, (.numeric ⟨27021, (.recurrence 5 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨11961560610296037376, (.numeric ⟨26957, (.recurrence 5 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨12033618204333965312, (.numeric ⟨26891, (.recurrence 4 (.basic false true)), (.convexRiemann 65024)⟩)⟩,
  ⟨12105675798371893248, (.numeric ⟨26821, (.recurrence 4 (.basic false true)), (.convexRiemann 65024)⟩)⟩,
  ⟨12177733392409821184, (.numeric ⟨26748, (.recurrence 4 (.basic false true)), (.convexRiemann 65024)⟩)⟩,
  ⟨12249790986447749120, (.numeric ⟨26672, (.recurrence 4 (.basic false true)), (.convexRiemann 65024)⟩)⟩,
  ⟨12321848580485677056, (.numeric ⟨26591, (.recurrence 4 (.basic false true)), (.convexRiemann 65024)⟩)⟩,
  ⟨12393906174523604992, (.numeric ⟨26507, (.recurrence 4 (.basic false true)), (.convexRiemann 65024)⟩)⟩,
  ⟨12465963768561532928, (.numeric ⟨26418, (.recurrence 4 (.basic false true)), (.convexRiemann 65024)⟩)⟩,
  ⟨12538021362599460864, (.numeric ⟨26324, (.recurrence 5 .exactTwo), .finite⟩)⟩,
  ⟨12610078956637388800, (.numeric ⟨26225, (.recurrence 5 .exactTwo), .finite⟩)⟩,
  ⟨12682136550675316736, (.numeric ⟨26121, (.recurrence 5 .exactTwo), .finite⟩)⟩,
  ⟨12754194144713244672, (.numeric ⟨26010, (.recurrence 5 .exactTwo), .finite⟩)⟩,
  ⟨12826251738751172608, (.numeric ⟨25893, (.recurrence 5 .exactTwo), .finite⟩)⟩,
  ⟨12898309332789100544, (.numeric ⟨25769, (.recurrence 5 .exactTwo), .finite⟩)⟩,
  ⟨12970366926827028480, (.numeric ⟨25638, (.recurrence 5 .exactTwo), .finite⟩)⟩,
  ⟨13006395723845992448, (.numeric ⟨24576, (.recurrence 5 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨13042424520864956416, (.numeric ⟨24576, (.recurrence 5 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨13078453317883920384, (.numeric ⟨24576, (.recurrence 5 .exactTwo), (.convexRiemann 65024)⟩)⟩,
  ⟨13114482114902884352, (.numeric ⟨24576, (.recurrence 5 .exactTwo), .finite⟩)⟩,
  ⟨13150510911921848320, (.numeric ⟨24576, (.recurrence 5 .exactTwo), .finite⟩)⟩,
  ⟨13186539708940812288, (.numeric ⟨24576, (.recurrence 5 .exactTwo), .finite⟩)⟩,
  ⟨13222568505959776256, (.numeric ⟨24576, (.recurrence 5 .exactTwo), .finite⟩)⟩,
  ⟨13258597302978740224, (.numeric ⟨24576, (.recurrence 5 .exactTwo), .finite⟩)⟩,
  ⟨13330654897016668160, (.numeric ⟨24576, (.recurrence 5 .exactTwo), .finite⟩)⟩,
  ⟨13402712491054596096, (.numeric ⟨24576, (.recurrence 5 .exactTwo), .finite⟩)⟩,
  ⟨13474770085092524032, (.numeric ⟨24576, (.recurrence 5 .exactTwo), .finite⟩)⟩,
  ⟨13546827679130451968, (.numeric ⟨24576, (.recurrence 5 .exactTwo), .finite⟩)⟩,
  ⟨13690942867206307840, (.numeric ⟨24576, (.recurrence 5 .exactTwo), .finite⟩)⟩,
  ⟨13835058055282163712, (.numeric ⟨24576, (.recurrence 5 .exactTwo), .finite⟩)⟩,
  ⟨13979173243358019584, (.numeric ⟨24576, (.recurrence 5 .exactTwo), .finite⟩)⟩,
  ⟨14123288431433875456, (.numeric ⟨24576, (.recurrence 5 .exactTwo), .finite⟩)⟩,
  ⟨14411518807585587200, (.numeric ⟨24576, (.recurrence 5 .exactTwo), .finite⟩)⟩,
  ⟨14699749183737298944, (.numeric ⟨24576, (.recurrence 5 .exactTwo), .geometric⟩)⟩,
  ⟨14987979559889010688, (.numeric ⟨24576, (.recurrence 5 .exactTwo), .geometric⟩)⟩,
  ⟨15564440312192434176, (.numeric ⟨24576, (.recurrence 5 .exactTwo), .geometric⟩)⟩,
  ⟨16140901064495857664, (.numeric ⟨24576, (.recurrence 5 .exactTwo), .geometric⟩)⟩,
  ⟨17293822569102704640, (.numeric ⟨24576, (.recurrence 5 .exactTwo), .geometric⟩)⟩,
  ⟨18446744073709551616, (.numeric ⟨24576, (.recurrence 5 .exactTwo), .geometric⟩)⟩
]

end Schmeisser.Certificates.Finite.Generated.M12

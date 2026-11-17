import Schmeisser.Certificates.BlockSoundness
import Schmeisser.Certificates.Generated.M13Coefficients

namespace Schmeisser.Certificates.Finite.Generated.M13

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

def data : Data where
  lo := 13
  hi := 13
  cutoff := 6703634826000596992
  upper := coefficients.upper
  panels := [
    ((mkRat 0 1), (mkRat 1 24)),
    ((mkRat 1 24), (mkRat 1 12)),
    ((mkRat 1 12), (mkRat 1 8)),
    ((mkRat 1 8), (mkRat 1 6)),
    ((mkRat 1 6), (mkRat 5 24)),
    ((mkRat 5 24), (mkRat 1 4)),
    ((mkRat 1 4), (mkRat 7 24)),
    ((mkRat 7 24), (mkRat 1 3)),
    ((mkRat 1 3), (mkRat 3 8)),
    ((mkRat 3 8), (mkRat 5 12)),
    ((mkRat 5 12), (mkRat 11 24)),
    ((mkRat 11 24), (mkRat 1 2)),
    ((mkRat 1 2), (mkRat 13 24)),
    ((mkRat 13 24), (mkRat 7 12)),
    ((mkRat 7 12), (mkRat 5 8)),
    ((mkRat 5 8), (mkRat 2 3)),
    ((mkRat 2 3), (mkRat 17 24)),
    ((mkRat 17 24), (mkRat 3 4)),
    ((mkRat 3 4), (mkRat 19 24)),
    ((mkRat 19 24), (mkRat 5 6)),
    ((mkRat 5 6), (mkRat 7 8)),
    ((mkRat 7 8), (mkRat 11 12)),
    ((mkRat 11 12), (mkRat 23 24)),
    ((mkRat 23 24), (mkRat 1 1))
  ]

theorem data_checked : data.check = true := by
  decide +kernel

def segments0 : List Segment := [
  ⟨4611686018427387904, .threshold⟩,
  ⟨6917529027641081856, (.numeric ⟨27003, (.recurrence 5 .trapezoidThree), (.convexRiemann 16760832)⟩)⟩,
  ⟨7061644215716937728, (.numeric ⟨27947, (.recurrence 5 .trapezoidThree), (.convexRiemann 16760832)⟩)⟩,
  ⟨7205759403792793600, (.numeric ⟨27852, (.recurrence 5 .trapezoidThree), (.convexRiemann 16760832)⟩)⟩,
  ⟨7349874591868649472, (.numeric ⟨27760, (.recurrence 5 .trapezoidThree), (.convexRiemann 16760832)⟩)⟩,
  ⟨7493989779944505344, (.numeric ⟨27671, (.recurrence 5 .trapezoidThree), (.convexRiemann 16760832)⟩)⟩,
  ⟨7638104968020361216, (.numeric ⟨27584, (.recurrence 5 .trapezoidThree), (.convexRiemann 16760832)⟩)⟩,
  ⟨7782220156096217088, (.numeric ⟨27500, (.recurrence 5 .trapezoidThree), (.convexRiemann 16760832)⟩)⟩,
  ⟨7926335344172072960, (.numeric ⟨27418, (.recurrence 5 .trapezoidThree), (.convexRiemann 16760832)⟩)⟩,
  ⟨8070450532247928832, (.numeric ⟨27338, (.recurrence 5 .trapezoidThree), (.convexRiemann 16760832)⟩)⟩,
  ⟨8214565720323784704, (.numeric ⟨27258, (.recurrence 5 .trapezoidThree), (.convexRiemann 16760832)⟩)⟩,
  ⟨8358680908399640576, (.numeric ⟨27180, (.recurrence 5 .trapezoidThree), (.convexRiemann 16760832)⟩)⟩,
  ⟨8502796096475496448, (.numeric ⟨27102, (.recurrence 5 .trapezoidThree), (.convexRiemann 16769024)⟩)⟩,
  ⟨8646911284551352320, (.numeric ⟨27024, (.recurrence 5 .trapezoidThree), (.convexRiemann 16769024)⟩)⟩,
  ⟨8791026472627208192, (.numeric ⟨26945, (.recurrence 5 .trapezoidThree), (.convexRiemann 16769024)⟩)⟩,
  ⟨8935141660703064064, (.numeric ⟨26866, (.recurrence 5 .trapezoidThree), (.convexRiemann 16769024)⟩)⟩
]

def segments1 : List Segment := [
  ⟨9079256848778919936, (.numeric ⟨26785, (.recurrence 5 .trapezoidThree), (.convexRiemann 16769024)⟩)⟩,
  ⟨9223372036854775808, (.numeric ⟨26703, (.recurrence 5 .trapezoidThree), (.convexRiemann 16769024)⟩)⟩,
  ⟨9367487224930631680, (.numeric ⟨26619, (.recurrence 5 .trapezoidThree), (.convexRiemann 16769024)⟩)⟩,
  ⟨9511602413006487552, (.numeric ⟨26532, (.recurrence 5 .trapezoidThree), (.convexRiemann 16769024)⟩)⟩,
  ⟨9655717601082343424, (.numeric ⟨26441, (.recurrence 5 .trapezoidThree), (.convexRiemann 16769024)⟩)⟩,
  ⟨9799832789158199296, (.numeric ⟨26347, (.recurrence 5 .trapezoidThree), (.convexRiemann 16769024)⟩)⟩,
  ⟨9943947977234055168, (.numeric ⟨26249, (.recurrence 5 .trapezoidThree), (.convexRiemann 16769024)⟩)⟩,
  ⟨10088063165309911040, (.numeric ⟨26146, (.recurrence 5 .trapezoidThree), (.convexRiemann 16769024)⟩)⟩,
  ⟨10232178353385766912, (.numeric ⟨26036, (.recurrence 5 .trapezoidThree), (.convexRiemann 16769024)⟩)⟩,
  ⟨10376293541461622784, (.numeric ⟨25920, (.recurrence 5 .trapezoidThree), (.convexRiemann 16769024)⟩)⟩,
  ⟨10520408729537478656, (.numeric ⟨25797, (.recurrence 5 .trapezoidThree), (.convexRiemann 16769024)⟩)⟩,
  ⟨10664523917613334528, (.numeric ⟨25665, (.recurrence 5 .trapezoidThree), (.convexRiemann 16769024)⟩)⟩,
  ⟨10808639105689190400, (.numeric ⟨25524, (.recurrence 5 .trapezoidThree), (.convexRiemann 16769024)⟩)⟩,
  ⟨10952754293765046272, (.numeric ⟨25371, (.recurrence 5 .trapezoidThree), (.convexRiemann 16769024)⟩)⟩,
  ⟨11096869481840902144, (.numeric ⟨24576, (.recurrence 5 .trapezoidThree), (.convexRiemann 16769024)⟩)⟩,
  ⟨11240984669916758016, (.numeric ⟨24576, (.recurrence 5 .trapezoidThree), (.convexRiemann 16769024)⟩)⟩
]

def segments2 : List Segment := [
  ⟨11385099857992613888, (.numeric ⟨24576, (.recurrence 5 .trapezoidThree), (.convexRiemann 16769024)⟩)⟩,
  ⟨11529215046068469760, (.numeric ⟨24576, (.recurrence 5 .trapezoidThree), (.convexRiemann 16769024)⟩)⟩,
  ⟨11673330234144325632, (.numeric ⟨24576, (.recurrence 5 .trapezoidThree), (.convexRiemann 16769024)⟩)⟩,
  ⟨11817445422220181504, (.numeric ⟨24576, (.recurrence 5 .trapezoidThree), (.convexRiemann 16769024)⟩)⟩,
  ⟨11961560610296037376, (.numeric ⟨24576, (.recurrence 5 .trapezoidThree), (.convexRiemann 16769024)⟩)⟩,
  ⟨12105675798371893248, (.numeric ⟨24576, (.recurrence 5 .trapezoidThree), (.convexRiemann 16769024)⟩)⟩,
  ⟨12249790986447749120, (.numeric ⟨24576, (.recurrence 5 .trapezoidThree), (.convexRiemann 16769024)⟩)⟩,
  ⟨12393906174523604992, (.numeric ⟨24576, (.recurrence 5 .trapezoidThree), (.convexRiemann 16769024)⟩)⟩,
  ⟨12538021362599460864, (.numeric ⟨24576, (.recurrence 5 .trapezoidThree), (.convexRiemann 16769024)⟩)⟩,
  ⟨12682136550675316736, (.numeric ⟨24576, (.recurrence 5 .trapezoidThree), (.convexRiemann 16769024)⟩)⟩,
  ⟨12826251738751172608, (.numeric ⟨24576, (.recurrence 5 .trapezoidThree), (.convexRiemann 16769024)⟩)⟩,
  ⟨12970366926827028480, (.numeric ⟨24576, (.recurrence 5 .trapezoidThree), .finite⟩)⟩,
  ⟨13114482114902884352, (.numeric ⟨24576, (.recurrence 5 .trapezoidThree), .finite⟩)⟩,
  ⟨13258597302978740224, (.numeric ⟨24576, (.recurrence 5 .trapezoidThree), .finite⟩)⟩,
  ⟨13402712491054596096, (.numeric ⟨24576, (.recurrence 5 .trapezoidThree), .finite⟩)⟩,
  ⟨13546827679130451968, (.numeric ⟨24576, (.recurrence 5 .trapezoidThree), .finite⟩)⟩
]

def segments3 : List Segment := [
  ⟨13835058055282163712, (.numeric ⟨24576, (.recurrence 5 .trapezoidThree), .finite⟩)⟩,
  ⟨14123288431433875456, (.numeric ⟨24576, (.recurrence 5 .trapezoidThree), .finite⟩)⟩,
  ⟨14411518807585587200, (.numeric ⟨24576, (.recurrence 5 .trapezoidThree), .geometric⟩)⟩,
  ⟨14987979559889010688, (.numeric ⟨24576, (.recurrence 5 .trapezoidThree), .geometric⟩)⟩,
  ⟨15564440312192434176, (.numeric ⟨24576, (.recurrence 5 .trapezoidThree), .geometric⟩)⟩,
  ⟨16140901064495857664, (.numeric ⟨24576, (.recurrence 5 .trapezoidThree), .geometric⟩)⟩,
  ⟨17293822569102704640, (.numeric ⟨24576, (.recurrence 5 .trapezoidThree), .geometric⟩)⟩,
  ⟨18446744073709551616, (.numeric ⟨24576, (.recurrence 5 .trapezoidThree), .geometric⟩)⟩
]

end Schmeisser.Certificates.Finite.Generated.M13

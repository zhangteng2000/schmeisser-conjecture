import Schmeisser.Certificates.BlockSoundness
import Schmeisser.Certificates.Generated.M11Coefficients

namespace Schmeisser.Certificates.Finite.Generated.M11

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

def data : Data where
  lo := 11
  hi := 11
  cutoff := 7478458047598428160
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
  ⟨7493989779944505344, (.numeric ⟨24576, (.recurrence 4 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨7638104968020361216, (.numeric ⟨28325, (.recurrence 4 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨7782220156096217088, (.numeric ⟨28240, (.recurrence 4 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨7926335344172072960, (.numeric ⟨28157, (.recurrence 4 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨8070450532247928832, (.numeric ⟨28077, (.recurrence 4 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨8214565720323784704, (.numeric ⟨27998, (.recurrence 4 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨8358680908399640576, (.numeric ⟨27921, (.recurrence 4 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨8502796096475496448, (.numeric ⟨27845, (.recurrence 4 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨8646911284551352320, (.numeric ⟨27769, (.recurrence 4 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨8791026472627208192, (.numeric ⟨27693, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨8935141660703064064, (.numeric ⟨27617, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨9079256848778919936, (.numeric ⟨27540, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨9223372036854775808, (.numeric ⟨27462, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨9367487224930631680, (.numeric ⟨27382, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨9511602413006487552, (.numeric ⟨27299, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩
]

def segments1 : List Segment := [
  ⟨9655717601082343424, (.numeric ⟨27214, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨9799832789158199296, (.numeric ⟨27124, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨9871890383196127232, (.numeric ⟨28562, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨9943947977234055168, (.numeric ⟨28536, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨10016005571271983104, (.numeric ⟨28509, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨10088063165309911040, (.numeric ⟨28482, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨10160120759347838976, (.numeric ⟨28454, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨10232178353385766912, (.numeric ⟨28426, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨10304235947423694848, (.numeric ⟨28398, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨10376293541461622784, (.numeric ⟨28369, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨10448351135499550720, (.numeric ⟨28339, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨10520408729537478656, (.numeric ⟨28308, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨10592466323575406592, (.numeric ⟨28277, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨10664523917613334528, (.numeric ⟨28245, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨10736581511651262464, (.numeric ⟨28212, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨10808639105689190400, (.numeric ⟨28178, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩
]

def segments2 : List Segment := [
  ⟨10880696699727118336, (.numeric ⟨28144, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨10952754293765046272, (.numeric ⟨28108, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨11024811887802974208, (.numeric ⟨28070, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨11096869481840902144, (.numeric ⟨28032, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨11168927075878830080, (.numeric ⟨27992, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨11240984669916758016, (.numeric ⟨27951, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨11313042263954685952, (.numeric ⟨27908, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨11385099857992613888, (.numeric ⟨27864, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨11457157452030541824, (.numeric ⟨27818, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨11529215046068469760, (.numeric ⟨27770, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨11601272640106397696, (.numeric ⟨27720, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨11673330234144325632, (.numeric ⟨27668, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨11745387828182253568, (.numeric ⟨27613, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨11817445422220181504, (.numeric ⟨27556, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨11889503016258109440, (.numeric ⟨27497, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨11961560610296037376, (.numeric ⟨27435, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩
]

def segments3 : List Segment := [
  ⟨12033618204333965312, (.numeric ⟨27370, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨12105675798371893248, (.numeric ⟨27302, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨12177733392409821184, (.numeric ⟨27230, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨12249790986447749120, (.numeric ⟨27155, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨12321848580485677056, (.numeric ⟨27076, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨12393906174523604992, (.numeric ⟨26993, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨12465963768561532928, (.numeric ⟨26906, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨12538021362599460864, (.numeric ⟨26814, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨12610078956637388800, (.numeric ⟨26716, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨12682136550675316736, (.numeric ⟨26613, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨12754194144713244672, (.numeric ⟨26505, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨12826251738751172608, (.numeric ⟨26389, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨12898309332789100544, (.numeric ⟨26267, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨12970366926827028480, (.numeric ⟨26137, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨13042424520864956416, (.numeric ⟨25999, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨13114482114902884352, (.numeric ⟨25852, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩
]

def segments4 : List Segment := [
  ⟨13186539708940812288, (.numeric ⟨25695, (.recurrence 4 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨13222568505959776256, (.numeric ⟨27892, (.recurrence 4 .trapezoidThree), .finite⟩)⟩,
  ⟨13258597302978740224, (.numeric ⟨27855, (.recurrence 4 .trapezoidThree), .finite⟩)⟩,
  ⟨13294626099997704192, (.numeric ⟨27817, (.recurrence 4 .trapezoidThree), .finite⟩)⟩,
  ⟨13330654897016668160, (.numeric ⟨27778, (.recurrence 4 .trapezoidThree), .finite⟩)⟩,
  ⟨13366683694035632128, (.numeric ⟨27738, (.recurrence 4 .trapezoidThree), .finite⟩)⟩,
  ⟨13402712491054596096, (.numeric ⟨27697, (.recurrence 4 .trapezoidThree), .finite⟩)⟩,
  ⟨13438741288073560064, (.numeric ⟨27654, (.recurrence 4 .trapezoidThree), .finite⟩)⟩,
  ⟨13474770085092524032, (.numeric ⟨27610, (.recurrence 4 .trapezoidThree), .finite⟩)⟩,
  ⟨13510798882111488000, (.numeric ⟨27564, (.recurrence 4 .trapezoidThree), .finite⟩)⟩,
  ⟨13546827679130451968, (.numeric ⟨27276, (.recurrence 4 .trapezoidThree), .finite⟩)⟩,
  ⟨13582856476149415936, (.numeric ⟨27276, (.recurrence 4 .trapezoidThree), .finite⟩)⟩,
  ⟨13618885273168379904, (.numeric ⟨27277, (.recurrence 4 .trapezoidThree), .finite⟩)⟩,
  ⟨13654914070187343872, (.numeric ⟨27277, (.recurrence 4 .trapezoidThree), .finite⟩)⟩,
  ⟨13690942867206307840, (.numeric ⟨27278, (.recurrence 4 .trapezoidThree), .finite⟩)⟩,
  ⟨13744986062734753792, (.numeric ⟨25251, (.recurrence 4 .trapezoidThree), .finite⟩)⟩
]

def segments5 : List Segment := [
  ⟨13763000461244235776, (.numeric ⟨24576, (.recurrence 4 .trapezoidThree), .finite⟩)⟩,
  ⟨13781014859753717760, (.numeric ⟨24576, (.recurrence 4 .trapezoidThree), .finite⟩)⟩,
  ⟨13799029258263199744, (.numeric ⟨24576, (.recurrence 4 .trapezoidThree), .finite⟩)⟩,
  ⟨13835058055282163712, (.numeric ⟨24576, (.recurrence 4 .trapezoidThree), .finite⟩)⟩,
  ⟨13871086852301127680, (.numeric ⟨24576, (.recurrence 4 .trapezoidThree), .finite⟩)⟩,
  ⟨13907115649320091648, (.numeric ⟨24576, (.recurrence 4 .trapezoidThree), .finite⟩)⟩,
  ⟨13979173243358019584, (.numeric ⟨24576, (.recurrence 4 .trapezoidThree), .finite⟩)⟩,
  ⟨14051230837395947520, (.numeric ⟨24576, (.recurrence 4 .trapezoidThree), .finite⟩)⟩,
  ⟨14123288431433875456, (.numeric ⟨24576, (.recurrence 4 .trapezoidThree), .finite⟩)⟩,
  ⟨14195346025471803392, (.numeric ⟨24576, (.recurrence 4 .trapezoidThree), .finite⟩)⟩,
  ⟨14267403619509731328, (.numeric ⟨24576, (.recurrence 4 .trapezoidThree), .finite⟩)⟩,
  ⟨14411518807585587200, (.numeric ⟨24576, (.recurrence 4 .trapezoidThree), .finite⟩)⟩,
  ⟨14555633995661443072, (.numeric ⟨24576, (.recurrence 4 .trapezoidThree), .finite⟩)⟩,
  ⟨14699749183737298944, (.numeric ⟨24576, (.recurrence 4 .trapezoidThree), .geometric⟩)⟩,
  ⟨14987979559889010688, (.numeric ⟨24576, (.recurrence 4 .trapezoidThree), .finite⟩)⟩,
  ⟨15276209936040722432, (.numeric ⟨24576, (.recurrence 4 .trapezoidThree), .geometric⟩)⟩
]

def segments6 : List Segment := [
  ⟨15564440312192434176, (.numeric ⟨24576, (.recurrence 4 .trapezoidThree), .geometric⟩)⟩,
  ⟨16140901064495857664, (.numeric ⟨24576, (.recurrence 4 .trapezoidThree), .geometric⟩)⟩,
  ⟨16717361816799281152, (.numeric ⟨24576, (.recurrence 4 .trapezoidThree), .geometric⟩)⟩,
  ⟨17293822569102704640, (.numeric ⟨24576, (.recurrence 4 .trapezoidThree), .geometric⟩)⟩,
  ⟨18446744073709551616, (.numeric ⟨24576, (.recurrence 4 .trapezoidThree), .geometric⟩)⟩
]

end Schmeisser.Certificates.Finite.Generated.M11

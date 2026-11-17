import Schmeisser.Certificates.BlockSoundness
import Schmeisser.Certificates.Generated.M9Coefficients

namespace Schmeisser.Certificates.Finite.Generated.M9

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

def data : Data where
  lo := 9
  hi := 9
  cutoff := 8496182317389381632
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
  ⟨8358680908399640576, .threshold⟩,
  ⟨8502796096475496448, (.numeric ⟨31356, (.recurrence 3 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨8574853690513424384, (.numeric ⟨30169, (.recurrence 3 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨8646911284551352320, (.numeric ⟨30142, (.recurrence 3 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨8718968878589280256, (.numeric ⟨30116, (.recurrence 3 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨8791026472627208192, (.numeric ⟨30090, (.recurrence 3 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨8863084066665136128, (.numeric ⟨30065, (.recurrence 3 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨8935141660703064064, (.numeric ⟨30040, (.recurrence 3 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨9007199254740992000, (.numeric ⟨30016, (.recurrence 3 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨9079256848778919936, (.numeric ⟨29992, (.recurrence 3 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨9151314442816847872, (.numeric ⟨29969, (.recurrence 3 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨9223372036854775808, (.numeric ⟨29946, (.recurrence 3 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨9295429630892703744, (.numeric ⟨29924, (.recurrence 3 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨9367487224930631680, (.numeric ⟨29902, (.recurrence 3 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨9439544818968559616, (.numeric ⟨29880, (.recurrence 3 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨9511602413006487552, (.numeric ⟨29858, (.recurrence 3 .trapezoidThree), (.convexRiemann 64512)⟩)⟩
]

def segments1 : List Segment := [
  ⟨9583660007044415488, (.numeric ⟨29836, (.recurrence 3 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨9655717601082343424, (.numeric ⟨29814, (.recurrence 3 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨9727775195120271360, (.numeric ⟨29793, (.recurrence 3 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨9799832789158199296, (.numeric ⟨29771, (.recurrence 3 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨9871890383196127232, (.numeric ⟨29749, (.recurrence 3 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨9943947977234055168, (.numeric ⟨29727, (.recurrence 3 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨10016005571271983104, (.numeric ⟨29705, (.recurrence 3 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨10088063165309911040, (.numeric ⟨29682, (.recurrence 3 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨10160120759347838976, (.numeric ⟨29660, (.recurrence 3 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨10232178353385766912, (.numeric ⟨29636, (.recurrence 3 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨10304235947423694848, (.numeric ⟨29613, (.recurrence 3 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨10376293541461622784, (.numeric ⟨29588, (.recurrence 3 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨10448351135499550720, (.numeric ⟨29563, (.recurrence 3 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨10520408729537478656, (.numeric ⟨29538, (.recurrence 3 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨10592466323575406592, (.numeric ⟨29512, (.recurrence 3 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨10664523917613334528, (.numeric ⟨29485, (.recurrence 3 .trapezoidThree), (.convexRiemann 64512)⟩)⟩
]

def segments2 : List Segment := [
  ⟨10736581511651262464, (.numeric ⟨29457, (.recurrence 3 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨10808639105689190400, (.numeric ⟨29428, (.recurrence 3 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨10880696699727118336, (.numeric ⟨29398, (.recurrence 3 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨10952754293765046272, (.numeric ⟨29367, (.recurrence 3 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨11024811887802974208, (.numeric ⟨29335, (.recurrence 3 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨11096869481840902144, (.numeric ⟨29302, (.recurrence 3 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨11168927075878830080, (.numeric ⟨29267, (.recurrence 3 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨11240984669916758016, (.numeric ⟨29231, (.recurrence 3 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨11313042263954685952, (.numeric ⟨29194, (.recurrence 3 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨11385099857992613888, (.numeric ⟨29154, (.recurrence 3 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨11457157452030541824, (.numeric ⟨29113, (.recurrence 3 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨11529215046068469760, (.numeric ⟨29070, (.recurrence 3 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨11601272640106397696, (.numeric ⟨29026, (.recurrence 3 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨11673330234144325632, (.numeric ⟨28979, (.recurrence 3 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨11745387828182253568, (.numeric ⟨28929, (.recurrence 3 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨11817445422220181504, (.numeric ⟨28878, (.recurrence 3 .trapezoidThree), (.convexRiemann 65024)⟩)⟩
]

def segments3 : List Segment := [
  ⟨11889503016258109440, (.numeric ⟨28823, (.recurrence 3 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨11961560610296037376, (.numeric ⟨28766, (.recurrence 3 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨12033618204333965312, (.numeric ⟨28706, (.recurrence 3 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨12105675798371893248, (.numeric ⟨28643, (.recurrence 3 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨12177733392409821184, (.numeric ⟨28577, (.recurrence 3 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨12249790986447749120, (.numeric ⟨28507, (.recurrence 3 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨12321848580485677056, (.numeric ⟨28433, (.recurrence 3 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨12357877377504641024, (.numeric ⟨29895, (.recurrence 3 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨12393906174523604992, (.numeric ⟨29878, (.recurrence 3 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨12429934971542568960, (.numeric ⟨29861, (.recurrence 3 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨12465963768561532928, (.numeric ⟨29842, (.recurrence 3 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨12501992565580496896, (.numeric ⟨29824, (.recurrence 3 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨12538021362599460864, (.numeric ⟨29805, (.recurrence 3 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨12574050159618424832, (.numeric ⟨29785, (.recurrence 3 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨12610078956637388800, (.numeric ⟨29765, (.recurrence 3 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨12646107753656352768, (.numeric ⟨29744, (.recurrence 3 .trapezoidThree), (.convexRiemann 65024)⟩)⟩
]

def segments4 : List Segment := [
  ⟨12682136550675316736, (.numeric ⟨29722, (.recurrence 3 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨12718165347694280704, (.numeric ⟨29700, (.recurrence 3 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨12754194144713244672, (.numeric ⟨29677, (.recurrence 3 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨12790222941732208640, (.numeric ⟨29654, (.recurrence 3 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨12826251738751172608, (.numeric ⟨29630, (.recurrence 3 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨12862280535770136576, (.numeric ⟨29605, (.recurrence 3 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨12898309332789100544, (.numeric ⟨29580, (.recurrence 3 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨12934338129808064512, (.numeric ⟨29553, (.recurrence 3 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨12970366926827028480, (.numeric ⟨29526, (.recurrence 3 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨13006395723845992448, (.numeric ⟨29498, (.recurrence 3 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨13042424520864956416, (.numeric ⟨29469, (.recurrence 3 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨13078453317883920384, (.numeric ⟨29440, (.recurrence 3 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨13114482114902884352, (.numeric ⟨29409, (.recurrence 3 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨13150510911921848320, (.numeric ⟨29378, (.recurrence 3 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨13186539708940812288, (.numeric ⟨29345, (.recurrence 3 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨13222568505959776256, (.numeric ⟨29311, (.recurrence 3 .trapezoidThree), (.convexRiemann 65024)⟩)⟩
]

def segments5 : List Segment := [
  ⟨13258597302978740224, (.numeric ⟨29277, (.recurrence 3 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨13294626099997704192, (.numeric ⟨29241, (.recurrence 3 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨13330654897016668160, (.numeric ⟨29204, (.recurrence 3 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨13366683694035632128, (.numeric ⟨29166, (.recurrence 3 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨13402712491054596096, (.numeric ⟨29126, (.recurrence 3 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨13438741288073560064, (.numeric ⟨29086, (.recurrence 3 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨13474770085092524032, (.numeric ⟨29044, (.recurrence 3 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨13510798882111488000, (.numeric ⟨29000, (.recurrence 3 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨13546827679130451968, (.numeric ⟨28955, (.recurrence 3 .trapezoidThree), (.convexRiemann 65024)⟩)⟩,
  ⟨13582856476149415936, (.numeric ⟨28909, (.recurrence 3 .trapezoidThree), .finite⟩)⟩,
  ⟨13618885273168379904, (.numeric ⟨28861, (.recurrence 3 .trapezoidThree), .finite⟩)⟩,
  ⟨13654914070187343872, (.numeric ⟨28811, (.recurrence 3 .trapezoidThree), .finite⟩)⟩,
  ⟨13690942867206307840, (.numeric ⟨28760, (.recurrence 3 .trapezoidThree), .finite⟩)⟩,
  ⟨13726971664225271808, (.numeric ⟨28706, (.recurrence 3 .trapezoidThree), .finite⟩)⟩,
  ⟨13763000461244235776, (.numeric ⟨28651, (.recurrence 3 .trapezoidThree), .finite⟩)⟩,
  ⟨13799029258263199744, (.numeric ⟨28594, (.recurrence 3 .trapezoidThree), .finite⟩)⟩
]

def segments6 : List Segment := [
  ⟨13835058055282163712, (.numeric ⟨28534, (.recurrence 3 .trapezoidThree), .finite⟩)⟩,
  ⟨13871086852301127680, (.numeric ⟨28473, (.recurrence 3 .trapezoidThree), .finite⟩)⟩,
  ⟨13907115649320091648, (.numeric ⟨28409, (.recurrence 3 .trapezoidThree), .finite⟩)⟩,
  ⟨13943144446339055616, (.numeric ⟨28343, (.recurrence 3 .trapezoidThree), .finite⟩)⟩,
  ⟨13979173243358019584, (.numeric ⟨28274, (.recurrence 3 .trapezoidThree), .finite⟩)⟩,
  ⟨14015202040376983552, (.numeric ⟨28203, (.recurrence 3 .trapezoidThree), .finite⟩)⟩,
  ⟨14051230837395947520, (.numeric ⟨28129, (.recurrence 3 .trapezoidThree), .finite⟩)⟩,
  ⟨14087259634414911488, (.numeric ⟨28052, (.recurrence 3 .trapezoidThree), .finite⟩)⟩,
  ⟨14123288431433875456, (.numeric ⟨27971, (.recurrence 3 .trapezoidThree), .finite⟩)⟩,
  ⟨14159317228452839424, (.numeric ⟨27888, (.recurrence 3 .trapezoidThree), .finite⟩)⟩,
  ⟨14195346025471803392, (.numeric ⟨27801, (.recurrence 3 .trapezoidThree), .finite⟩)⟩,
  ⟨14231374822490767360, (.numeric ⟨27711, (.recurrence 3 .trapezoidThree), .finite⟩)⟩,
  ⟨14267403619509731328, (.numeric ⟨27616, (.recurrence 3 .trapezoidThree), .finite⟩)⟩,
  ⟨14303432416528695296, (.numeric ⟨27518, (.recurrence 3 .trapezoidThree), .finite⟩)⟩,
  ⟨14339461213547659264, (.numeric ⟨27415, (.recurrence 3 .trapezoidThree), .finite⟩)⟩,
  ⟨14375490010566623232, (.numeric ⟨27308, (.recurrence 3 .trapezoidThree), .finite⟩)⟩
]

def segments7 : List Segment := [
  ⟨14411518807585587200, (.numeric ⟨27196, (.recurrence 3 .trapezoidThree), .finite⟩)⟩,
  ⟨14447547604604551168, (.numeric ⟨27078, (.recurrence 3 .trapezoidThree), .finite⟩)⟩,
  ⟨14483576401623515136, (.numeric ⟨26956, (.recurrence 3 .trapezoidThree), .finite⟩)⟩,
  ⟨14519605198642479104, (.numeric ⟨26827, (.recurrence 3 .trapezoidThree), .finite⟩)⟩,
  ⟨14555633995661443072, (.numeric ⟨26692, (.recurrence 3 .trapezoidThree), .finite⟩)⟩,
  ⟨14591662792680407040, (.numeric ⟨26550, (.recurrence 3 .trapezoidThree), .finite⟩)⟩,
  ⟨14627691589699371008, (.numeric ⟨26401, (.recurrence 3 .trapezoidThree), .finite⟩)⟩,
  ⟨14663720386718334976, (.numeric ⟨26244, (.recurrence 3 .trapezoidThree), .finite⟩)⟩,
  ⟨14699749183737298944, (.numeric ⟨26079, (.recurrence 3 .trapezoidThree), .finite⟩)⟩,
  ⟨14735777980756262912, (.numeric ⟨25905, (.recurrence 3 .trapezoidThree), .finite⟩)⟩,
  ⟨14771806777775226880, (.numeric ⟨25721, (.recurrence 3 .trapezoidThree), .finite⟩)⟩,
  ⟨14789821176284708864, (.numeric ⟨25526, (.recurrence 3 .trapezoidThree), .finite⟩)⟩,
  ⟨14807835574794190848, (.numeric ⟨25526, (.recurrence 3 .trapezoidThree), .finite⟩)⟩,
  ⟨14825849973303672832, (.numeric ⟨28040, (.recurrence 3 .trapezoidThree), .geometric⟩)⟩,
  ⟨14843864371813154816, (.numeric ⟨28040, (.recurrence 3 .trapezoidThree), .geometric⟩)⟩,
  ⟨14861878770322636800, (.numeric ⟨28041, (.recurrence 3 .trapezoidThree), .geometric⟩)⟩
]

def segments8 : List Segment := [
  ⟨14879893168832118784, (.numeric ⟨28041, (.recurrence 3 .trapezoidThree), .geometric⟩)⟩,
  ⟨14897907567341600768, (.numeric ⟨28042, (.recurrence 3 .trapezoidThree), .geometric⟩)⟩,
  ⟨14915921965851082752, (.numeric ⟨28042, (.recurrence 3 .trapezoidThree), .geometric⟩)⟩,
  ⟨14933936364360564736, (.numeric ⟨28486, (.recurrence 3 .trapezoidThree), .geometric⟩)⟩,
  ⟨14951950762870046720, (.numeric ⟨28043, (.recurrence 3 .trapezoidThree), .geometric⟩)⟩,
  ⟨14969965161379528704, (.numeric ⟨28043, (.recurrence 3 .trapezoidThree), .geometric⟩)⟩,
  ⟨14987979559889010688, (.numeric ⟨28044, (.recurrence 3 .trapezoidThree), .geometric⟩)⟩,
  ⟨15005993958398492672, (.numeric ⟨28044, (.recurrence 3 .trapezoidThree), .geometric⟩)⟩,
  ⟨15024008356907974656, (.numeric ⟨28045, (.recurrence 3 .trapezoidThree), .geometric⟩)⟩,
  ⟨15042022755417456640, (.numeric ⟨28045, (.recurrence 3 .trapezoidThree), .geometric⟩)⟩,
  ⟨15060037153926938624, (.numeric ⟨28046, (.recurrence 3 .trapezoidThree), .geometric⟩)⟩,
  ⟨15078051552436420608, (.numeric ⟨28046, (.recurrence 3 .trapezoidThree), .geometric⟩)⟩,
  ⟨15087058751691161600, (.numeric ⟨28046, (.recurrence 3 .trapezoidThree), .geometric⟩)⟩,
  ⟨15096065950945902592, (.numeric ⟨28047, (.recurrence 3 .trapezoidThree), .geometric⟩)⟩,
  ⟨15105073150200643584, (.numeric ⟨28047, (.recurrence 3 .trapezoidThree), .geometric⟩)⟩,
  ⟨15114080349455384576, (.numeric ⟨28047, (.recurrence 3 .trapezoidThree), .geometric⟩)⟩
]

def segments9 : List Segment := [
  ⟨15123087548710125568, (.numeric ⟨28047, (.recurrence 3 .trapezoidThree), .geometric⟩)⟩,
  ⟨15132094747964866560, (.numeric ⟨28048, (.recurrence 3 .trapezoidThree), .geometric⟩)⟩,
  ⟨15141101947219607552, (.numeric ⟨28048, (.recurrence 3 .trapezoidThree), .geometric⟩)⟩,
  ⟨15150109146474348544, (.numeric ⟨24576, (.recurrence 3 .trapezoidThree), .finite⟩)⟩,
  ⟨15159116345729089536, (.numeric ⟨24576, (.recurrence 3 .trapezoidThree), .finite⟩)⟩,
  ⟨15168123544983830528, (.numeric ⟨24576, (.recurrence 3 .trapezoidThree), .finite⟩)⟩,
  ⟨15186137943493312512, (.numeric ⟨24576, (.recurrence 3 .trapezoidThree), .finite⟩)⟩,
  ⟨15204152342002794496, (.numeric ⟨24576, (.recurrence 3 .trapezoidThree), .finite⟩)⟩,
  ⟨15222166740512276480, (.numeric ⟨24576, (.recurrence 3 .trapezoidThree), .finite⟩)⟩,
  ⟨15240181139021758464, (.numeric ⟨24576, (.recurrence 3 .trapezoidThree), .finite⟩)⟩,
  ⟨15276209936040722432, (.numeric ⟨24576, (.recurrence 3 .trapezoidThree), .finite⟩)⟩,
  ⟨15312238733059686400, (.numeric ⟨24576, (.recurrence 3 .trapezoidThree), .finite⟩)⟩,
  ⟨15348267530078650368, (.numeric ⟨24576, (.recurrence 3 .trapezoidThree), .finite⟩)⟩,
  ⟨15420325124116578304, (.numeric ⟨24576, (.recurrence 3 .trapezoidThree), .finite⟩)⟩,
  ⟨15492382718154506240, (.numeric ⟨24576, (.recurrence 3 .trapezoidThree), .finite⟩)⟩,
  ⟨15564440312192434176, (.numeric ⟨24576, (.recurrence 3 .trapezoidThree), .geometric⟩)⟩
]

def segments10 : List Segment := [
  ⟨15708555500268290048, (.numeric ⟨24576, (.recurrence 3 .trapezoidThree), .finite⟩)⟩,
  ⟨15852670688344145920, (.numeric ⟨24576, (.recurrence 3 .trapezoidThree), .geometric⟩)⟩,
  ⟨16140901064495857664, (.numeric ⟨24576, (.recurrence 3 .trapezoidThree), .geometric⟩)⟩,
  ⟨16429131440647569408, (.numeric ⟨24576, (.recurrence 3 .trapezoidThree), .geometric⟩)⟩,
  ⟨16717361816799281152, (.numeric ⟨24576, (.recurrence 3 .trapezoidThree), .geometric⟩)⟩,
  ⟨17293822569102704640, (.numeric ⟨24576, (.recurrence 3 .trapezoidThree), .geometric⟩)⟩,
  ⟨17870283321406128128, (.numeric ⟨24576, (.recurrence 3 .trapezoidThree), .geometric⟩)⟩,
  ⟨18446744073709551616, (.numeric ⟨24576, (.recurrence 3 .trapezoidThree), .geometric⟩)⟩
]

end Schmeisser.Certificates.Finite.Generated.M9

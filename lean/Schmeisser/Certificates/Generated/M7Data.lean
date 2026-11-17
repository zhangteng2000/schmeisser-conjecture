import Schmeisser.Certificates.BlockSoundness
import Schmeisser.Certificates.Generated.M7Coefficients

namespace Schmeisser.Certificates.Finite.Generated.M7

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

def data : Data where
  lo := 7
  hi := 7
  cutoff := 9903177987962437632
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
  ⟨9799832789158199296, .threshold⟩,
  ⟨9943947977234055168, (.numeric ⟨32338, (.recurrence 2 .trapezoidThree), (.convexRiemann 63488)⟩)⟩,
  ⟨10016005571271983104, (.numeric ⟨31638, (.recurrence 2 .trapezoidThree), (.convexRiemann 63488)⟩)⟩,
  ⟨10088063165309911040, (.numeric ⟨31626, (.recurrence 2 .trapezoidThree), (.convexRiemann 63488)⟩)⟩,
  ⟨10160120759347838976, (.numeric ⟨31613, (.recurrence 2 .trapezoidThree), (.convexRiemann 63488)⟩)⟩,
  ⟨10232178353385766912, (.numeric ⟨31601, (.recurrence 2 .trapezoidThree), (.convexRiemann 63488)⟩)⟩,
  ⟨10304235947423694848, (.numeric ⟨31588, (.recurrence 2 .trapezoidThree), (.convexRiemann 63488)⟩)⟩,
  ⟨10376293541461622784, (.numeric ⟨31575, (.recurrence 2 .trapezoidThree), (.convexRiemann 63488)⟩)⟩,
  ⟨10448351135499550720, (.numeric ⟨31562, (.recurrence 2 .trapezoidThree), (.convexRiemann 63488)⟩)⟩,
  ⟨10520408729537478656, (.numeric ⟨31548, (.recurrence 2 .trapezoidThree), (.convexRiemann 63488)⟩)⟩,
  ⟨10592466323575406592, (.numeric ⟨31534, (.recurrence 2 .trapezoidThree), (.convexRiemann 63488)⟩)⟩,
  ⟨10664523917613334528, (.numeric ⟨31519, (.recurrence 2 .trapezoidThree), (.convexRiemann 63488)⟩)⟩,
  ⟨10736581511651262464, (.numeric ⟨31503, (.recurrence 2 .trapezoidThree), (.convexRiemann 63488)⟩)⟩,
  ⟨10808639105689190400, (.numeric ⟨31487, (.recurrence 2 .trapezoidThree), (.convexRiemann 63488)⟩)⟩,
  ⟨10880696699727118336, (.numeric ⟨31469, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨10952754293765046272, (.numeric ⟨31451, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩
]

def segments1 : List Segment := [
  ⟨11024811887802974208, (.numeric ⟨31431, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨11096869481840902144, (.numeric ⟨31410, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨11168927075878830080, (.numeric ⟨31388, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨11204955872897794048, (.numeric ⟨32413, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨11240984669916758016, (.numeric ⟨32411, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨11277013466935721984, (.numeric ⟨32409, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨11313042263954685952, (.numeric ⟨32406, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨11349071060973649920, (.numeric ⟨32404, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨11385099857992613888, (.numeric ⟨32402, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨11421128655011577856, (.numeric ⟨32399, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨11457157452030541824, (.numeric ⟨32396, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨11493186249049505792, (.numeric ⟨32393, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨11529215046068469760, (.numeric ⟨32390, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨11565243843087433728, (.numeric ⟨32386, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨11601272640106397696, (.numeric ⟨32382, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨11637301437125361664, (.numeric ⟨32378, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩
]

def segments2 : List Segment := [
  ⟨11673330234144325632, (.numeric ⟨32374, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨11709359031163289600, (.numeric ⟨32370, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨11745387828182253568, (.numeric ⟨32365, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨11781416625201217536, (.numeric ⟨32360, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨11817445422220181504, (.numeric ⟨32355, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨11853474219239145472, (.numeric ⟨32349, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨11889503016258109440, (.numeric ⟨32343, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨11925531813277073408, (.numeric ⟨32337, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨11961560610296037376, (.numeric ⟨32330, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨11997589407315001344, (.numeric ⟨32323, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨12033618204333965312, (.numeric ⟨32316, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨12069647001352929280, (.numeric ⟨32308, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨12105675798371893248, (.numeric ⟨32300, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨12141704595390857216, (.numeric ⟨32292, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨12177733392409821184, (.numeric ⟨32283, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨12213762189428785152, (.numeric ⟨32274, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩
]

def segments3 : List Segment := [
  ⟨12249790986447749120, (.numeric ⟨32264, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨12285819783466713088, (.numeric ⟨32254, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨12321848580485677056, (.numeric ⟨32244, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨12357877377504641024, (.numeric ⟨32233, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨12393906174523604992, (.numeric ⟨32221, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨12429934971542568960, (.numeric ⟨32209, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨12465963768561532928, (.numeric ⟨32197, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨12501992565580496896, (.numeric ⟨32183, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨12538021362599460864, (.numeric ⟨32170, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨12574050159618424832, (.numeric ⟨32156, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨12610078956637388800, (.numeric ⟨32141, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨12646107753656352768, (.numeric ⟨32126, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨12682136550675316736, (.numeric ⟨32110, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨12718165347694280704, (.numeric ⟨32093, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨12754194144713244672, (.numeric ⟨32076, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨12790222941732208640, (.numeric ⟨32058, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩
]

def segments4 : List Segment := [
  ⟨12826251738751172608, (.numeric ⟨32039, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨12862280535770136576, (.numeric ⟨32019, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨12898309332789100544, (.numeric ⟨31999, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨12934338129808064512, (.numeric ⟨31978, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨12970366926827028480, (.numeric ⟨31956, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨13006395723845992448, (.numeric ⟨31933, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨13042424520864956416, (.numeric ⟨31910, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨13078453317883920384, (.numeric ⟨31885, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨13114482114902884352, (.numeric ⟨31860, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨13150510911921848320, (.numeric ⟨31833, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨13186539708940812288, (.numeric ⟨31806, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨13222568505959776256, (.numeric ⟨31778, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨13258597302978740224, (.numeric ⟨31748, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨13294626099997704192, (.numeric ⟨31717, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨13330654897016668160, (.numeric ⟨31685, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨13366683694035632128, (.numeric ⟨31652, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩
]

def segments5 : List Segment := [
  ⟨13402712491054596096, (.numeric ⟨31618, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨13438741288073560064, (.numeric ⟨31582, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨13474770085092524032, (.numeric ⟨31545, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨13510798882111488000, (.numeric ⟨31507, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨13546827679130451968, (.numeric ⟨31467, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨13582856476149415936, (.numeric ⟨31425, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨13618885273168379904, (.numeric ⟨31382, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨13654914070187343872, (.numeric ⟨31337, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨13690942867206307840, (.numeric ⟨31291, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨13726971664225271808, (.numeric ⟨31243, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨13763000461244235776, (.numeric ⟨31192, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨13799029258263199744, (.numeric ⟨31140, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨13835058055282163712, (.numeric ⟨31086, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨13871086852301127680, (.numeric ⟨31030, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨13907115649320091648, (.numeric ⟨30971, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨13943144446339055616, (.numeric ⟨30910, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩
]

def segments6 : List Segment := [
  ⟨13979173243358019584, (.numeric ⟨30846, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨14015202040376983552, (.numeric ⟨30780, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨14051230837395947520, (.numeric ⟨30711, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨14087259634414911488, (.numeric ⟨30640, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨14123288431433875456, (.numeric ⟨30565, (.recurrence 2 .trapezoidThree), (.convexRiemann 64512)⟩)⟩,
  ⟨14141302829943357440, (.numeric ⟨31687, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨14159317228452839424, (.numeric ⟨31689, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨14177331626962321408, (.numeric ⟨31692, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨14195346025471803392, (.numeric ⟨31694, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨14213360423981285376, (.numeric ⟨31696, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨14231374822490767360, (.numeric ⟨31698, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨14249389221000249344, (.numeric ⟨31701, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨14267403619509731328, (.numeric ⟨31703, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨14285418018019213312, (.numeric ⟨31705, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨14303432416528695296, (.numeric ⟨31707, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨14321446815038177280, (.numeric ⟨31710, (.recurrence 2 .trapezoidThree), .finite⟩)⟩
]

def segments7 : List Segment := [
  ⟨14339461213547659264, (.numeric ⟨31712, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨14357475612057141248, (.numeric ⟨31713, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨14375490010566623232, (.numeric ⟨31716, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨14393504409076105216, (.numeric ⟨31718, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨14411518807585587200, (.numeric ⟨31720, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨14429533206095069184, (.numeric ⟨31722, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨14447547604604551168, (.numeric ⟨31725, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨14465562003114033152, (.numeric ⟨31727, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨14483576401623515136, (.numeric ⟨31728, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨14501590800132997120, (.numeric ⟨31731, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨14519605198642479104, (.numeric ⟨31733, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨14537619597151961088, (.numeric ⟨31735, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨14555633995661443072, (.numeric ⟨31737, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨14573648394170925056, (.numeric ⟨31739, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨14591662792680407040, (.numeric ⟨31741, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨14609677191189889024, (.numeric ⟨31796, (.recurrence 2 .trapezoidThree), .finite⟩)⟩
]

def segments8 : List Segment := [
  ⟨14627691589699371008, (.numeric ⟨31767, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨14645705988208852992, (.numeric ⟨31738, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨14663720386718334976, (.numeric ⟨31708, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨14681734785227816960, (.numeric ⟨31677, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨14699749183737298944, (.numeric ⟨31646, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨14717763582246780928, (.numeric ⟨31614, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨14735777980756262912, (.numeric ⟨31581, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨14753792379265744896, (.numeric ⟨31547, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨14771806777775226880, (.numeric ⟨31513, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨14789821176284708864, (.numeric ⟨31477, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨14807835574794190848, (.numeric ⟨31441, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨14825849973303672832, (.numeric ⟨31404, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨14843864371813154816, (.numeric ⟨31367, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨14861878770322636800, (.numeric ⟨31328, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨14879893168832118784, (.numeric ⟨31288, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨14897907567341600768, (.numeric ⟨31248, (.recurrence 2 .trapezoidThree), .finite⟩)⟩
]

def segments9 : List Segment := [
  ⟨14915921965851082752, (.numeric ⟨31206, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨14933936364360564736, (.numeric ⟨31163, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨14951950762870046720, (.numeric ⟨31120, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨14969965161379528704, (.numeric ⟨31075, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨14987979559889010688, (.numeric ⟨31029, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨15005993958398492672, (.numeric ⟨30982, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨15024008356907974656, (.numeric ⟨30933, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨15042022755417456640, (.numeric ⟨30884, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨15060037153926938624, (.numeric ⟨30833, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨15078051552436420608, (.numeric ⟨30780, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨15096065950945902592, (.numeric ⟨30727, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨15114080349455384576, (.numeric ⟨30672, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨15132094747964866560, (.numeric ⟨30615, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨15150109146474348544, (.numeric ⟨30557, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨15168123544983830528, (.numeric ⟨30498, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨15186137943493312512, (.numeric ⟨30437, (.recurrence 2 .trapezoidThree), .finite⟩)⟩
]

def segments10 : List Segment := [
  ⟨15204152342002794496, (.numeric ⟨30374, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨15222166740512276480, (.numeric ⟨30309, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨15240181139021758464, (.numeric ⟨30243, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨15258195537531240448, (.numeric ⟨30174, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨15276209936040722432, (.numeric ⟨30104, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨15294224334550204416, (.numeric ⟨30031, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨15312238733059686400, (.numeric ⟨29957, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨15330253131569168384, (.numeric ⟨29880, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨15348267530078650368, (.numeric ⟨29801, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨15366281928588132352, (.numeric ⟨29720, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨15384296327097614336, (.numeric ⟨29636, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨15402310725607096320, (.numeric ⟨29549, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨15420325124116578304, (.numeric ⟨29460, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨15438339522626060288, (.numeric ⟨29368, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨15456353921135542272, (.numeric ⟨29273, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨15474368319645024256, (.numeric ⟨29175, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩
]

def segments11 : List Segment := [
  ⟨15492382718154506240, (.numeric ⟨29074, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨15510397116663988224, (.numeric ⟨28969, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨15528411515173470208, (.numeric ⟨28861, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨15546425913682952192, (.numeric ⟨28749, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨15564440312192434176, (.numeric ⟨28633, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨15582454710701916160, (.numeric ⟨28512, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨15600469109211398144, (.numeric ⟨28388, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨15618483507720880128, (.numeric ⟨28259, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨15636497906230362112, (.numeric ⟨28125, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨15654512304739844096, (.numeric ⟨27986, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨15672526703249326080, (.numeric ⟨27841, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨15690541101758808064, (.numeric ⟨27690, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨15708555500268290048, (.numeric ⟨27534, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨15726569898777772032, (.numeric ⟨27371, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨15744584297287254016, (.numeric ⟨27200, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨15762598695796736000, (.numeric ⟨27022, (.recurrence 2 .trapezoidThree), .finite⟩)⟩
]

def segments12 : List Segment := [
  ⟨15780613094306217984, (.numeric ⟨26836, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨15789620293560958976, (.numeric ⟨26641, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨15798627492815699968, (.numeric ⟨26641, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨15807634692070440960, (.numeric ⟨29429, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨15816641891325181952, (.numeric ⟨29429, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨15825649090579922944, (.numeric ⟨29430, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨15834656289834663936, (.numeric ⟨29430, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨15843663489089404928, (.numeric ⟨29431, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨15852670688344145920, (.numeric ⟨29431, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨15861677887598886912, (.numeric ⟨30671, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨15870685086853627904, (.numeric ⟨30632, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨15879692286108368896, (.numeric ⟨30592, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨15888699485363109888, (.numeric ⟨30551, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨15897706684617850880, (.numeric ⟨30509, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨15906713883872591872, (.numeric ⟨30467, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨15915721083127332864, (.numeric ⟨30424, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩
]

def segments13 : List Segment := [
  ⟨15924728282382073856, (.numeric ⟨30380, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨15933735481636814848, (.numeric ⟨30336, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨15942742680891555840, (.numeric ⟨30290, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨15951749880146296832, (.numeric ⟨30244, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨15960757079401037824, (.numeric ⟨30197, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨15969764278655778816, (.numeric ⟨30149, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨15978771477910519808, (.numeric ⟨30100, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨15987778677165260800, (.numeric ⟨30051, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨15996785876420001792, (.numeric ⟨30000, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16005793075674742784, (.numeric ⟨29949, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16014800274929483776, (.numeric ⟨29896, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16023807474184224768, (.numeric ⟨29842, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16032814673438965760, (.numeric ⟨29788, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16041821872693706752, (.numeric ⟨29732, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16050829071948447744, (.numeric ⟨29675, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16059836271203188736, (.numeric ⟨29617, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩
]

def segments14 : List Segment := [
  ⟨16068843470457929728, (.numeric ⟨29558, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16077850669712670720, (.numeric ⟨29498, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16086857868967411712, (.numeric ⟨29437, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16095865068222152704, (.numeric ⟨29374, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16104872267476893696, (.numeric ⟨29310, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16113879466731634688, (.numeric ⟨29245, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16122886665986375680, (.numeric ⟨29178, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16131893865241116672, (.numeric ⟨29110, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16140901064495857664, (.numeric ⟨29040, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16149908263750598656, (.numeric ⟨28969, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16158915463005339648, (.numeric ⟨28896, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16167922662260080640, (.numeric ⟨28822, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16176929861514821632, (.numeric ⟨28746, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16185937060769562624, (.numeric ⟨28668, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16194944260024303616, (.numeric ⟨28589, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16203951459279044608, (.numeric ⟨28508, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩
]

def segments15 : List Segment := [
  ⟨16212958658533785600, (.numeric ⟨28424, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16221965857788526592, (.numeric ⟨28339, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16230973057043267584, (.numeric ⟨28252, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16239980256298008576, (.numeric ⟨28163, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16248987455552749568, (.numeric ⟨28071, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16257994654807490560, (.numeric ⟨27977, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16267001854062231552, (.numeric ⟨27881, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16276009053316972544, (.numeric ⟨27782, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16285016252571713536, (.numeric ⟨27681, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16294023451826454528, (.numeric ⟨27577, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16303030651081195520, (.numeric ⟨27470, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16312037850335936512, (.numeric ⟨27361, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16321045049590677504, (.numeric ⟨27248, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16330052248845418496, (.numeric ⟨27132, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16339059448100159488, (.numeric ⟨27012, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16348066647354900480, (.numeric ⟨26890, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩
]

def segments16 : List Segment := [
  ⟨16352570246982270976, (.numeric ⟨29453, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16357073846609641472, (.numeric ⟨29453, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16361577446237011968, (.numeric ⟨29453, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16366081045864382464, (.numeric ⟨29453, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16370584645491752960, (.numeric ⟨29453, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16375088245119123456, (.numeric ⟨29454, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16379591844746493952, (.numeric ⟨29454, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16384095444373864448, (.numeric ⟨29454, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16388599044001234944, (.numeric ⟨29454, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16393102643628605440, (.numeric ⟨29454, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16397606243255975936, (.numeric ⟨29454, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16402109842883346432, (.numeric ⟨29455, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16406613442510716928, (.numeric ⟨29455, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16411117042138087424, (.numeric ⟨29455, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16415620641765457920, (.numeric ⟨29455, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16420124241392828416, (.numeric ⟨29455, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩
]

def segments17 : List Segment := [
  ⟨16424627841020198912, (.numeric ⟨29455, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16429131440647569408, (.numeric ⟨29456, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16433635040274939904, (.numeric ⟨29456, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16438138639902310400, (.numeric ⟨29456, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16442642239529680896, (.numeric ⟨29456, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16447145839157051392, (.numeric ⟨29456, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16451649438784421888, (.numeric ⟨29456, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16456153038411792384, (.numeric ⟨29457, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16460656638039162880, (.numeric ⟨29457, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16465160237666533376, (.numeric ⟨29457, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16469663837293903872, (.numeric ⟨29457, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16474167436921274368, (.numeric ⟨29457, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16478671036548644864, (.numeric ⟨29457, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16483174636176015360, (.numeric ⟨29458, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16487678235803385856, (.numeric ⟨29458, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16492181835430756352, (.numeric ⟨29458, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩
]

def segments18 : List Segment := [
  ⟨16496685435058126848, (.numeric ⟨29458, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16501189034685497344, (.numeric ⟨29458, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16505692634312867840, (.numeric ⟨29458, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16510196233940238336, (.numeric ⟨29458, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16514699833567608832, (.numeric ⟨29459, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16519203433194979328, (.numeric ⟨29459, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16523707032822349824, (.numeric ⟨29459, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16528210632449720320, (.numeric ⟨29459, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16532714232077090816, (.numeric ⟨24576, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨16537217831704461312, (.numeric ⟨24576, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨16546225030959202304, (.numeric ⟨24576, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨16555232230213943296, (.numeric ⟨24576, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨16564239429468684288, (.numeric ⟨24576, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨16573246628723425280, (.numeric ⟨24576, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨16591261027232907264, (.numeric ⟨24576, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨16609275425742389248, (.numeric ⟨24576, (.recurrence 2 .trapezoidThree), .finite⟩)⟩
]

def segments19 : List Segment := [
  ⟨16645304222761353216, (.numeric ⟨24576, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨16681333019780317184, (.numeric ⟨24576, (.recurrence 2 .trapezoidThree), .finite⟩)⟩,
  ⟨16717361816799281152, (.numeric ⟨24576, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16789419410837209088, (.numeric ⟨24576, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨16861477004875137024, (.numeric ⟨24576, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨17005592192950992896, (.numeric ⟨24576, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨17149707381026848768, (.numeric ⟨24576, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨17293822569102704640, (.numeric ⟨24576, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨17582052945254416384, (.numeric ⟨24576, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨17870283321406128128, (.numeric ⟨24576, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩,
  ⟨18446744073709551616, (.numeric ⟨24576, (.recurrence 2 .trapezoidThree), .geometric⟩)⟩
]

end Schmeisser.Certificates.Finite.Generated.M7

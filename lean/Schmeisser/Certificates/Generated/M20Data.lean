import Schmeisser.Certificates.BlockSoundness
import Schmeisser.Certificates.Generated.M20Coefficients

namespace Schmeisser.Certificates.Finite.Generated.M20

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option Elab.async false

def data : Data where
  lo := 20
  hi := 20
  cutoff := 4998728504461819904
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
  ⟨4611686018427387904, .threshold⟩,
  ⟨5188146770730811392, (.numeric ⟨24576, (.recurrence 9 .exactTwo), (.convexRiemann 3968)⟩)⟩,
  ⟨5476377146882523136, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), (.convexRiemann 3968)⟩)⟩,
  ⟨5620492334958379008, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), (.convexRiemann 3968)⟩)⟩,
  ⟨5908722711110090752, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), (.convexRiemann 4032)⟩)⟩,
  ⟨6196953087261802496, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), (.convexRiemann 4032)⟩)⟩,
  ⟨6485183463413514240, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), (.convexRiemann 4032)⟩)⟩,
  ⟨6773413839565225984, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), (.convexRiemann 4032)⟩)⟩,
  ⟨7061644215716937728, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), (.convexRiemann 4032)⟩)⟩,
  ⟨7349874591868649472, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), (.convexRiemann 4032)⟩)⟩,
  ⟨7638104968020361216, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), (.convexRiemann 4032)⟩)⟩,
  ⟨7782220156096217088, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), (.convexRiemann 4032)⟩)⟩,
  ⟨8070450532247928832, (.numeric ⟨24576, (.recurrence 9 .exactTwo), (.convexRiemann 4032)⟩)⟩,
  ⟨8358680908399640576, (.numeric ⟨24576, (.recurrence 9 .exactTwo), (.convexRiemann 4032)⟩)⟩,
  ⟨8646911284551352320, (.numeric ⟨24576, (.recurrence 9 .exactTwo), (.convexRiemann 4032)⟩)⟩,
  ⟨8935141660703064064, (.numeric ⟨24576, (.recurrence 9 .exactTwo), (.convexRiemann 4032)⟩)⟩,
  ⟨9223372036854775808, (.numeric ⟨24576, (.recurrence 9 .exactTwo), (.convexRiemann 4032)⟩)⟩,
  ⟨9511602413006487552, (.numeric ⟨24576, (.recurrence 9 .exactTwo), (.convexRiemann 4032)⟩)⟩,
  ⟨9799832789158199296, (.numeric ⟨24576, (.recurrence 9 .exactTwo), (.convexRiemann 4064)⟩)⟩,
  ⟨10088063165309911040, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), .finite⟩)⟩,
  ⟨10376293541461622784, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), .finite⟩)⟩,
  ⟨10664523917613334528, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), .finite⟩)⟩,
  ⟨10952754293765046272, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), .finite⟩)⟩,
  ⟨11529215046068469760, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), .finite⟩)⟩,
  ⟨12105675798371893248, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), .finite⟩)⟩,
  ⟨12682136550675316736, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), .finite⟩)⟩,
  ⟨13258597302978740224, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), .finite⟩)⟩,
  ⟨13835058055282163712, (.numeric ⟨24576, (.recurrence 8 (.basic false true)), .finite⟩)⟩,
  ⟨14987979559889010688, (.numeric ⟨24576, (.recurrence 8 (.basic true true)), .finite⟩)⟩,
  ⟨16140901064495857664, (.numeric ⟨24576, (.recurrence 8 (.basic true true)), .geometric⟩)⟩,
  ⟨17293822569102704640, (.numeric ⟨24576, (.recurrence 8 (.basic true true)), .geometric⟩)⟩,
  ⟨18446744073709551616, (.numeric ⟨24576, (.recurrence 8 (.basic true false)), .geometric⟩)⟩
]

end Schmeisser.Certificates.Finite.Generated.M20

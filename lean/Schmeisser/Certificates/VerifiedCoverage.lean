import Schmeisser.Certificates.VerifiedBlock

namespace Schmeisser.Certificates.Finite

def VerifiedBlock.degreeBlock (block : VerifiedBlock) : DegreeBlock VerifiedBlock :=
  ⟨block.data.lo, block.data.hi, block⟩

def checkCoverage (blocks : List VerifiedBlock) : Bool :=
  DegreeBlock.checkRanges (fun _ => true) 3 6000 (blocks.map VerifiedBlock.degreeBlock)

theorem checkCoverage_sound (blocks : List VerifiedBlock)
    (hcheck : checkCoverage blocks = true) (m : Nat) (hm3 : 3 ≤ m) (hm6000 : m < 6000) :
    ∃ block ∈ blocks, block.data.lo ≤ m ∧ m ≤ block.data.hi := by
  obtain ⟨block, hmem, hlo, hhi, _⟩ :=
    DegreeBlock.checkRanges_covers (fun _ => true) (blocks.map VerifiedBlock.degreeBlock)
      3 6000 hcheck m hm3 hm6000
  obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hmem
  exact ⟨original, horiginal, hlo, hhi⟩

def checkCoverageFrom (first : Nat) (blocks : List VerifiedBlock) : Bool :=
  DegreeBlock.checkRanges (fun _ => true) first 6000 (blocks.map VerifiedBlock.degreeBlock)

theorem checkCoverageFrom_sound (first : Nat) (blocks : List VerifiedBlock)
    (hcheck : checkCoverageFrom first blocks = true)
    (m : Nat) (hmfirst : first ≤ m) (hm6000 : m < 6000) :
    ∃ block ∈ blocks, block.data.lo ≤ m ∧ m ≤ block.data.hi := by
  obtain ⟨block, hmem, hlo, hhi, _⟩ :=
    DegreeBlock.checkRanges_covers (fun _ => true) (blocks.map VerifiedBlock.degreeBlock)
      first 6000 hcheck m hmfirst hm6000
  obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hmem
  exact ⟨original, horiginal, hlo, hhi⟩

end Schmeisser.Certificates.Finite

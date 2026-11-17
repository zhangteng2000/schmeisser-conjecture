import Schmeisser.Certificates.Interval

namespace Schmeisser.Certificates

/-- Certificate subdivisions have closed children, both containing the split. -/
inductive SplitTree (α : Type) where
  | leaf (data : α)
  | split (cut : Int) (left right : SplitTree α)
  deriving Repr

namespace SplitTree

def check (test : Interval → α → Bool) (box : Interval) : SplitTree α → Bool
  | .leaf data => test box data
  | .split cut left right =>
      decide (box.lo < cut ∧ cut < box.hi) &&
      check test ⟨box.lo, cut⟩ left && check test ⟨cut, box.hi⟩ right

theorem check_sound {α : Type} (test : Interval → α → Bool)
    (s : Int) (p : ℝ → Prop)
    (leaf_sound : ∀ box data, test box data = true →
      ∀ x, box.Contains s x → p x)
    (tree : SplitTree α) (box : Interval) (hcheck : tree.check test box = true) :
    ∀ x, box.Contains s x → p x := by
  induction tree generalizing box with
  | leaf data => exact leaf_sound box data hcheck
  | split cut left right ihl ihr =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hcheck
    obtain ⟨⟨_, hl⟩, hr⟩ := hcheck
    intro x hx
    rcases le_total x ((cut : ℝ) / s) with hleft | hright
    · exact ihl ⟨box.lo, cut⟩ hl x ⟨hx.1, hleft⟩
    · exact ihr ⟨cut, box.hi⟩ hr x ⟨hright, hx.2⟩

end SplitTree

/-- A closed range of critical-point counts, with an attached certificate. -/
structure DegreeBlock (α : Type) where
  lo : Nat
  hi : Nat
  data : α
  deriving Repr

namespace DegreeBlock

def checkRanges (test : DegreeBlock α → Bool) (next stop : Nat) :
    List (DegreeBlock α) → Bool
  | [] => decide (next = stop)
  | block :: rest =>
      decide (block.lo = next ∧ block.lo ≤ block.hi ∧ block.hi < stop) &&
      test block && checkRanges test (block.hi + 1) stop rest

theorem checkRanges_covers {α : Type} (test : DegreeBlock α → Bool)
    (blocks : List (DegreeBlock α)) (next stop : Nat)
    (hcheck : checkRanges test next stop blocks = true)
    (m : Nat) (hmlo : next ≤ m) (hmhi : m < stop) :
    ∃ block ∈ blocks, block.lo ≤ m ∧ m ≤ block.hi ∧ test block = true := by
  induction blocks generalizing next with
  | nil =>
    simp only [checkRanges, decide_eq_true_eq] at hcheck
    omega
  | cons block rest ih =>
    simp only [checkRanges, Bool.and_eq_true, decide_eq_true_eq] at hcheck
    obtain ⟨⟨⟨hlo, hvalid, hlast⟩, htest⟩, hrest⟩ := hcheck
    by_cases hm : m ≤ block.hi
    · exact ⟨block, List.mem_cons_self, by omega, hm, htest⟩
    · obtain ⟨found, hfound, hbounds⟩ := ih (block.hi + 1) hrest (by omega)
      exact ⟨found, List.mem_cons_of_mem block hfound, hbounds⟩

theorem checkRanges_sound {α : Type} (test : DegreeBlock α → Bool)
    (p : Nat → Prop)
    (block_sound : ∀ block, test block = true →
      ∀ m, block.lo ≤ m → m ≤ block.hi → p m)
    (blocks : List (DegreeBlock α)) (next stop : Nat)
    (hcheck : checkRanges test next stop blocks = true) :
    ∀ m, next ≤ m → m < stop → p m := by
  intro m hmlo hmhi
  obtain ⟨block, _, hlo, hhi, htest⟩ :=
    checkRanges_covers test blocks next stop hcheck m hmlo hmhi
  exact block_sound block htest m hlo hhi

end DegreeBlock
end Schmeisser.Certificates

import Mathlib.Data.Rat.Cast.Order
import Lean.Elab.Tactic.Omega

namespace Schmeisser.Certificates

/-- A consecutive list of nondegenerate panels from the first endpoint to
the final endpoint. This structure can be used directly for summing
interval integrals. -/
inductive PanelPartition {α : Type} [LT α] (finish : α) : α → List (α × α) → Prop
  | nil : PanelPartition finish finish []
  | cons {a b : α} {rest : List (α × α)} (hab : a < b)
      (tail : PanelPartition finish b rest) :
      PanelPartition finish a ((a, b) :: rest)

namespace PanelPartition

theorem map {α β : Type} [LT α] [LT β] (f : α → β)
    (hf : ∀ a b, a < b → f a < f b) {a b : α} {panels : List (α × α)}
    (h : PanelPartition b a panels) :
    PanelPartition (f b) (f a) (panels.map fun ab => (f ab.1, f ab.2)) := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (hf _ _ hab) ih

end PanelPartition

def checkPanels (start finish : Rat) : List (Rat × Rat) → Bool
  | [] => decide (start = finish)
  | (a, b) :: rest => decide (a = start ∧ a < b) && checkPanels b finish rest

theorem checkPanels_sound (start finish : Rat) (panels : List (Rat × Rat))
    (h : checkPanels start finish panels = true) : PanelPartition finish start panels := by
  induction panels generalizing start with
  | nil =>
    simp only [checkPanels, decide_eq_true_eq] at h
    subst start
    exact .nil
  | cons ab rest ih =>
    rcases ab with ⟨a, b⟩
    simp only [checkPanels, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨rfl, hab⟩, hrest⟩ := h
    exact .cons hab (ih b hrest)

end Schmeisser.Certificates

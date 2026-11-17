import Schmeisser.Certificates.Expression

namespace Schmeisser.Certificates.Expr

def checkLe (s : Int) (env : Nat → Interval) (left right : Expr) : Bool :=
  match left.eval s env, right.eval s env with
  | some li, some ri => decide (li.hi ≤ ri.lo)
  | _, _ => false

theorem checkLe_sound {s : Int} (hs : 0 < s)
    {env : Nat → Interval} {realEnv : Nat → ℝ}
    (henv : ∀ index, (env index).Contains s (realEnv index))
    (left right : Expr) (hcheck : checkLe s env left right = true) :
    left.value realEnv ≤ right.value realEnv := by
  cases hl : left.eval s env with
  | none => simp [checkLe, hl] at hcheck
  | some li =>
    cases hr : right.eval s env with
    | none => simp [checkLe, hl, hr] at hcheck
    | some ri =>
      simp only [checkLe, hl, hr, decide_eq_true_eq] at hcheck
      apply (eval_sound hs henv left hl).2.trans
      apply le_trans _ (eval_sound hs henv right hr).1
      apply (div_le_div_iff_of_pos_right (show (0 : ℝ) < s by exact_mod_cast hs)).2
      exact_mod_cast hcheck

end Schmeisser.Certificates.Expr

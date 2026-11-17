import Schmeisser.Certificates.IntervalHalf

/-! A checked real-expression evaluator.  Its input data and arithmetic
results are computational, while its soundness is a theorem about real
numbers.  No external evaluator is trusted. -/

namespace Schmeisser.Certificates

inductive Expr where
  | var (index : Nat)
  | int (value : Int)
  | rat (numerator denominator : Int)
  | add (left right : Expr)
  | neg (arg : Expr)
  | mul (left right : Expr)
  | div (left right : Expr)
  | pow (arg : Expr) (exponent : Nat)
  | sqrt (arg : Expr)
  | halfRange (arg exponent : Expr) (lo hi : Nat)
  | minimum (left right : Expr)
  | maximum (left right : Expr)
  deriving Repr

namespace Expr

noncomputable def value (env : Nat → ℝ) : Expr → ℝ
  | .var index => env index
  | .int z => z
  | .rat a b => (a : ℝ) / b
  | .add a b => a.value env + b.value env
  | .neg a => -a.value env
  | .mul a b => a.value env * b.value env
  | .div a b => a.value env / b.value env
  | .pow a n => a.value env ^ n
  | .sqrt a => Real.sqrt (a.value env)
  | .halfRange a b _ _ => (a.value env) ^ (b.value env / 2)
  | .minimum a b => min (a.value env) (b.value env)
  | .maximum a b => max (a.value env) (b.value env)

def eval (s : Int) (env : Nat → Interval) : Expr → Option Interval
  | .var index => some (env index)
  | .int z => some (Interval.point s z)
  | .rat a b => if 0 < b then some (Interval.rational s a b) else none
  | .add a b => do return (← a.eval s env).add (← b.eval s env)
  | .neg a => do return (← a.eval s env).neg
  | .mul a b => do return (← a.eval s env).mul s (← b.eval s env)
  | .div a b => do
      let ai ← a.eval s env
      let bi ← b.eval s env
      if 0 < bi.lo ∨ bi.hi < 0 then some (ai.div s bi) else none
  | .pow a n => do return (← a.eval s env).pow s n
  | .sqrt a => do
      let ai ← a.eval s env
      if 0 ≤ ai.lo then some (ai.sqrt s) else none
  | .halfRange a b lo hi => do
      let ai ← a.eval s env
      let bi ← b.eval s env
      if 0 ≤ ai.lo ∧ ai.hi ≤ s ∧ (lo : Int) * s ≤ bi.lo ∧ bi.hi ≤ (hi : Int) * s
      then some (ai.halfRange s lo hi) else none
  | .minimum a b => do return (← a.eval s env).cap (← b.eval s env)
  | .maximum a b => do return (← a.eval s env).floor (← b.eval s env)

theorem eval_sound {s : Int} (hs : 0 < s)
    {env : Nat → Interval} {realEnv : Nat → ℝ}
    (henv : ∀ index, (env index).Contains s (realEnv index))
    (e : Expr) {out : Interval} (hout : e.eval s env = some out) :
    out.Contains s (e.value realEnv) := by
  induction e generalizing out with
  | var index =>
    simp [eval, Option.some.injEq] at hout
    subst out
    exact henv index
  | int z =>
    simp [eval, Option.some.injEq] at hout
    subst out
    exact Interval.contains_point hs z
  | rat a b =>
    by_cases hb : 0 < b
    · simp [eval, hb] at hout
      subst out
      exact Interval.contains_rational hs hb a
    · simp [eval, hb] at hout
  | add a b iha ihb =>
    cases ha : a.eval s env with
    | none => simp [eval, ha] at hout
    | some ai =>
      cases hb : b.eval s env with
      | none => simp [eval, ha, hb] at hout
      | some bi =>
        simp [eval, ha, hb, Option.bind_some, Option.some.injEq] at hout
        subst out
        exact Interval.contains_add (iha ha) (ihb hb)
  | neg a ih =>
    cases ha : a.eval s env with
    | none => simp [eval, ha] at hout
    | some ai =>
      simp [eval, ha, Option.bind_some, Option.some.injEq] at hout
      subst out
      exact Interval.contains_neg (ih ha)
  | mul a b iha ihb =>
    cases ha : a.eval s env with
    | none => simp [eval, ha] at hout
    | some ai =>
      cases hb : b.eval s env with
      | none => simp [eval, ha, hb] at hout
      | some bi =>
        simp [eval, ha, hb, Option.bind_some, Option.some.injEq] at hout
        subst out
        exact Interval.contains_mul hs (iha ha) (ihb hb)
  | div a b iha ihb =>
    cases ha : a.eval s env with
    | none => simp [eval, ha] at hout
    | some ai =>
      cases hb : b.eval s env with
      | none => simp [eval, ha, hb] at hout
      | some bi =>
        by_cases hbi : 0 < bi.lo ∨ bi.hi < 0
        · simp [eval, ha, hb, Option.bind_some, hbi, ↓reduceIte,
            Option.some.injEq] at hout
          subst out
          exact Interval.contains_div hs (iha ha) (ihb hb) hbi
        · simp [eval, ha, hb, hbi] at hout
  | pow a n ih =>
    cases ha : a.eval s env with
    | none => simp [eval, ha] at hout
    | some ai =>
      simp [eval, ha, Option.bind_some, Option.some.injEq] at hout
      subst out
      exact Interval.contains_pow hs (ih ha) n
  | sqrt a ih =>
    cases ha : a.eval s env with
    | none => simp [eval, ha] at hout
    | some ai =>
      by_cases hai : 0 ≤ ai.lo
      · simp [eval, ha, Option.bind_some, hai, ↓reduceIte,
          Option.some.injEq] at hout
        subst out
        exact Interval.contains_sqrt hs (ih ha) hai
      · simp [eval, ha, hai] at hout
  | minimum a b iha ihb =>
    cases ha : a.eval s env with
    | none => simp [eval, ha] at hout
    | some ai =>
      cases hb : b.eval s env with
      | none => simp [eval, ha, hb] at hout
      | some bi =>
        simp [eval, ha, hb, Option.bind_some, Option.some.injEq] at hout
        subst out
        exact Interval.contains_cap hs (iha ha) (ihb hb)
  | halfRange a b lo hi iha ihb =>
    cases ha : a.eval s env with
    | none => simp [eval, ha] at hout
    | some ai =>
      cases hb : b.eval s env with
      | none => simp [eval, ha, hb] at hout
      | some bi =>
        by_cases hd : 0 ≤ ai.lo ∧ ai.hi ≤ s ∧ (lo : Int) * s ≤ bi.lo ∧
            bi.hi ≤ (hi : Int) * s
        · simp [eval, ha, hb, hd] at hout
          subst out
          exact Interval.contains_halfRange hs (iha ha) (ihb hb) lo hi
            hd.1 hd.2.1 hd.2.2.1 hd.2.2.2
        · simp [eval, ha, hb, hd] at hout
  | maximum a b iha ihb =>
    cases ha : a.eval s env with
    | none => simp [eval, ha] at hout
    | some ai =>
      cases hb : b.eval s env with
      | none => simp [eval, ha, hb] at hout
      | some bi =>
        simp [eval, ha, hb, Option.bind_some, Option.some.injEq] at hout
        subst out
        exact Interval.contains_floor hs (iha ha) (ihb hb)

def checkGreater (s : Int) (env : Nat → Interval) (left right : Expr) : Bool :=
  match left.eval s env, right.eval s env with
  | some li, some ri => decide (ri.hi < li.lo)
  | _, _ => false

theorem checkGreater_sound {s : Int} (hs : 0 < s)
    {env : Nat → Interval} {realEnv : Nat → ℝ}
    (henv : ∀ index, (env index).Contains s (realEnv index))
    (left right : Expr) (hcheck : checkGreater s env left right = true) :
    right.value realEnv < left.value realEnv := by
  cases hl : left.eval s env with
  | none => simp [checkGreater, hl] at hcheck
  | some li =>
    cases hr : right.eval s env with
    | none => simp [checkGreater, hl, hr] at hcheck
    | some ri =>
      simp only [checkGreater, hl, hr, decide_eq_true_eq] at hcheck
      exact Interval.strict_of_bounds hs (eval_sound hs henv left hl).1
        (eval_sound hs henv right hr).2 hcheck

end Expr
end Schmeisser.Certificates


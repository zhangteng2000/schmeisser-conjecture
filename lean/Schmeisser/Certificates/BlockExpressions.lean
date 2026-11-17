import Schmeisser.Certificates.ExpressionValues

/-! Expressions with a real degree variable.  Evaluation encloses every
integer degree in a specified block; the analytic theorems still use the
actual integer degree. -/

namespace Schmeisser.Certificates.Block

def u : Expr := .var 0
def degree : Expr := .var 1
def kap : Expr := .var 2
def index (offset : Nat) : Expr := degree - .int offset
def eps : Expr := .minimum 1 (.maximum 0 (1 - u))
def h : Expr := kap * eps / u
def d : Expr := u + h
def b : Expr := u + h / 2
def mt : Expr := .minimum (.maximum 0 (1 - kap ^ 2 * eps / (4 * u ^ 2 * d))) 1
def mass : Expr := eps * mt
def te : Expr := kap / (2 * u * d)
def correction : Expr := kap ^ 2 * eps / (4 * u ^ 3 * d)
def ac (offset : Nat) : Expr := 1 + 1 / (index offset - 1)
def epsHalf (lo hi offset : Nat) : Expr :=
  .halfRange eps (index offset) (lo - offset) (hi - offset)

def basic (offset : Nat) (quarter invEps : Bool) : Expr :=
  let initial := 1 / u - index offset
  let initial := if invEps then .maximum initial (-(1 / (u * eps))) else initial
  if quarter then .maximum initial (1 / u - 3) else initial

def baseTwo : Expr := 1 / u - 2 + kap / (2 * u)

def quadratic (t : Expr) : Expr :=
  .maximum 0 (1 - 2 * u * t + u * t ^ 2 - h * t * (1 - t))

def trapezoidPhi (j : Nat) : Expr :=
  let t : Expr := .rat j 16
  eps * (t * (2 - t) - kap / u * t * (1 - t)) /
    ((quadratic t).sqrt + 1 - t)

def trapezoidCorrection : Expr :=
  (eps.sqrt + 2 * Expr.sum ((List.range 15).map fun j => trapezoidPhi (j + 1))) / 16

def baseThree : Expr :=
  1 / u + te * (1 - eps.half 3) - (3 / 2) * mt * (1 + trapezoidCorrection)

inductive BaseKind where
  | basic (quarter invEps : Bool)
  | exactTwo
  | trapezoidThree
  deriving Repr

def base (offset : Nat) : BaseKind → Expr
  | .basic quarter invEps => basic offset quarter invEps
  | .exactTwo => baseTwo
  | .trapezoidThree => baseThree

def recurrence (lo hi offset steps : Nat) (kind : BaseKind) : Expr :=
  match steps with
  | 0 => base offset kind
  | k + 1 =>
      -(1 / ((index offset - 1) * u)) + ac offset * correction +
        te * (1 - epsHalf lo hi offset) +
        ac offset * mass * recurrence lo hi (offset + 2) k kind
termination_by steps

def moment (lo hi : Nat) : Expr :=
  kap / (2 * u ^ 2 * b) - (11 / 10) * mt * d / (.int lo * b ^ 3) -
    .int (hi + 1) * te * eps.half lo

/-- This test is used only when the degree block is a singleton. -/
def polar (m : Nat) : Expr :=
  2 * ((1 + h * u).half (m + 2) - (1 - h).half (m + 2)) /
    (.int (m + 2) * h * (1 + u))

noncomputable def env (x : ℝ) (m : Nat) (κ : ℝ) : Nat → ℝ :=
  fun i => if i = 0 then x else if i = 1 then m else κ

end Schmeisser.Certificates.Block

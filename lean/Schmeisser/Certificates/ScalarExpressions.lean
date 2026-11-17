import Schmeisser.Certificates.Expression

/-!
Executable expressions for the scalar certificate inequalities. The error
series uses the exact second coefficient and Cauchy's estimates; it does
not use Schoenberg's inequality.
-/

namespace Schmeisser.Certificates

namespace Expr

instance : OfNat Expr n := ⟨.int n⟩
instance : Add Expr := ⟨.add⟩
instance : Neg Expr := ⟨.neg⟩
instance : Sub Expr := ⟨fun a b => .add a (.neg b)⟩
instance : Mul Expr := ⟨.mul⟩
instance : Div Expr := ⟨.div⟩
instance : Pow Expr Nat := ⟨.pow⟩

def ofRat (q : Rat) : Expr := .rat q.num q.den

def half (a : Expr) (n : Nat) : Expr :=
  a ^ (n / 2) * if n % 2 = 0 then 1 else a.sqrt

def sum (expressions : List Expr) : Expr := expressions.foldl (· + ·) 0

end Expr

namespace Scalar

def u : Expr := .var 0
def eps : Expr := .maximum 0 (1 - u)
def kap (m : Nat) : Expr := 6 / .int m
def h (m : Nat) : Expr := kap m * eps / u
def d (m : Nat) : Expr := u + h m
def b (m : Nat) : Expr := u + h m / 2
def mt (m : Nat) : Expr :=
  .minimum (.maximum 0 (1 - kap m ^ 2 * eps / (4 * u ^ 2 * d m))) 1
def mass (m : Nat) : Expr := eps * mt m
def te (m : Nat) : Expr := kap m / (2 * u * d m)
def correction (m : Nat) : Expr := kap m ^ 2 * eps / (4 * u ^ 3 * d m)

def base (index : Nat) (quarter invEps : Bool) : Expr :=
  let initial := 1 / u - .int index
  let initial := if invEps then .maximum initial (-(1 / (u * eps))) else initial
  if quarter then .maximum initial (1 / u - 3) else initial

/-- The first parameter fixes kappa. The second is the current recurrence index. -/
def recurrence (m index : Nat) (quarter invEps : Bool) (steps : Nat) : Expr :=
  match steps with
  | 0 => base index quarter invEps
  | k + 1 =>
      let ac : Expr := Expr.int index / Expr.int (index - 1)
      (-(1 / (Expr.int (index - 1) * u)) + ac * correction m +
        te m * (1 - eps.half index) +
        ac * mass m * recurrence m (index - 2) quarter invEps k)
termination_by steps

def beta (a : Expr) : Expr := .maximum 0 (1 - u * a * (2 - a))
def da (a : Expr) : Expr := .maximum 0 (1 - u * a)

def front (m : Nat) (a : Expr) : Expr :=
  .int (40 * m) / (.int (3 * (m - 1) * (m + 3)) * (2 - a) ^ 3 * u ^ 2)

def splitOld (m : Nat) (a : Expr) : Expr :=
  front m a + (5 / 6) * (1 - a) * u * .int (m * (m + 1)) *
    (beta a).half (m - 3)

def splitRaw (m : Nat) (a : Expr) : Expr :=
  front m a + (1 - a) * .int (m + 1) *
    ((beta a).half m + da a ^ m) / eps

def cauchyCoefficient (m k : Nat) : Expr :=
  ((Expr.rat (m ^ m) (k ^ k * (m - k) ^ (m - k))).sqrt) /
    Expr.int (Nat.fast_choose m k)

/-- This expression is used only for m >= 11 and (1-u)/u < 1. -/
def geometricCauchy (m : Nat) : Expr :=
  let z := eps / u
  let terms := Expr.sum ((List.range 8).map fun j =>
    cauchyCoefficient m (j + 3) * z.half (j + 1))
  (1 / .int (m - 1) + terms + z.half 9 / (1 - z.sqrt)) / u ^ 2

def panel (m : Nat) (a b : Expr) : Expr :=
  let old := (5 / 6) * u * b ^ 2 / (1 - u * b) *
    .int (m * (m + 1)) * (beta a).half (m - 1)
  let raw := .int (m + 1) * ((beta a).half m + da a ^ m) / eps
  (b - a) * .minimum old raw

def riemann (m : Nat) (panels : List (Rat × Rat)) : Expr :=
  Expr.sum (panels.map fun ab => panel m (.ofRat ab.1) (.ofRat ab.2))

inductive ErrorBound where
  | splitOld (a : Rat)
  | splitRaw (a : Rat)
  | geometricCauchy
  | riemann
  deriving Repr

def error (m : Nat) (panels : List (Rat × Rat)) : ErrorBound → Expr
  | .splitOld a => splitOld m (.ofRat a)
  | .splitRaw a => splitRaw m (.ofRat a)
  | .geometricCauchy => geometricCauchy m
  | .riemann => riemann m panels

def target (m : Nat) (panels : List (Rat × Rat)) (bound : ErrorBound) : Expr :=
  error m panels bound + eps ^ m / u

end Scalar
end Schmeisser.Certificates

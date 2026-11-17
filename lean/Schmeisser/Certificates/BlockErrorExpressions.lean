import Schmeisser.Certificates.BlockExpressions

namespace Schmeisser.Certificates.Block

def beta (a : Expr) : Expr := .maximum 0 (1 - u * a * (2 - a))
def da (a : Expr) : Expr := .maximum 0 (1 - u * a)

def front (lo : Nat) (a : Expr) : Expr :=
  .int (40 * lo) / (.int (3 * (lo - 1) * (lo + 3)) * (2 - a) ^ 3 * u ^ 2)

def quadraticFactor (lo hi : Nat) : Expr :=
  let aa := lo * (lo + 1)
  let bb := hi * (hi + 1)
  1 + .rat (((bb : Int) - aa) ^ 2) (4 * aa * bb)

def linearFactor (lo hi : Nat) : Expr :=
  1 + .rat (((hi : Int) - lo) ^ 2) (4 * (lo + 1) * (hi + 1))

def rawDegreeEnvelope (lo hi : Nat) (a : Expr) : Expr :=
  linearFactor lo hi * .maximum
    (.int (lo + 1) * ((beta a).half lo + da a ^ lo))
    (.int (hi + 1) * ((beta a).half hi + da a ^ hi))

def splitRaw (lo hi : Nat) (a : Expr) : Expr :=
  front lo a + (1 - a) * rawDegreeEnvelope lo hi a / eps

def panel (lo hi : Nat) (a b : Expr) : Expr :=
  let old := (5 / 6) * u * b ^ 2 / (1 - u * b) * quadraticFactor lo hi *
    .maximum (.int (lo * (lo + 1)) * (beta a).half (lo - 1))
      (.int (hi * (hi + 1)) * (beta a).half (hi - 1))
  let raw := rawDegreeEnvelope lo hi a / eps
  (b - a) * .minimum old raw

def riemann (lo hi : Nat) (panels : List (Rat × Rat)) : Expr :=
  Expr.sum (panels.map fun ab => panel lo hi (.ofRat ab.1) (.ofRat ab.2))

/-- Coefficients are supplied as certified upper numerators at scale `s`. -/
def coefficient (s : Nat) (upper : List Int) (k : Nat) : Expr :=
  .rat (upper[k]?.getD 0) s

def polynomial (coefficients : List Nat) (x : Expr) : Expr :=
  coefficients.foldr (fun a v => .int a + x * v) 0

def finiteError (m s : Nat) (upper : List Int) : Expr :=
  Expr.sum ((List.range (m - 1)).map fun j =>
    let k := j + 2
    coefficient s upper k * u.half k * eps.half (k - 2) *
      polynomial ((List.range (m - k + 1)).map fun j => Nat.fast_choose (k + j) k) eps)

/-- In a degree block, the supplied coefficient constants bound all degrees. -/
def geometricError (lo hi s : Nat) (upper : List Int) : Expr :=
  let kmax := min 10 lo
  let z := eps / u
  let terms := Expr.sum ((List.range (kmax - 2)).map fun j =>
    coefficient s upper (j + 3) * z.half (j + 1))
  let tail := if kmax < hi then z.half (kmax - 1) / (1 - z.sqrt) else 0
  (1 / .int (lo - 1) + terms + tail) / u ^ 2

def convexPanelA (t : Expr) : Expr := u * t ^ 2 / (1 - u * t)

def convexPanelB (lo hi : Nat) (t : Expr) : Expr :=
  if lo = hi then
    (.rat 5 6) * (.int (lo * (lo + 1)) * (beta t).half (lo - 1))
  else
    (.rat 5 6) * quadraticFactor lo hi *
      .maximum (.int (lo * (lo + 1)) * (beta t).half (lo - 1))
        (.int (hi * (hi + 1)) * (beta t).half (hi - 1))

def convexPanelRaw (lo hi : Nat) (t : Expr) : Expr :=
  if lo = hi then
    .int (lo + 1) * ((beta t).half lo + da t ^ lo) / eps
  else
    rawDegreeEnvelope lo hi t / eps

def convexPanel (lo hi : Nat) (a b : Expr) : Expr :=
  .minimum
    ((b - a) / 4 * (convexPanelA a + convexPanelA b) *
      (convexPanelB lo hi a + convexPanelB lo hi b))
    ((b - a) / 2 * (convexPanelRaw lo hi a + convexPanelRaw lo hi b))

def convexRiemann (lo hi : Nat) (panels : List (Rat × Rat)) : Expr :=
  Expr.sum (panels.map fun ab => convexPanel lo hi (.ofRat ab.1) (.ofRat ab.2))

def convexPanelSelected (raw : Bool) (lo hi : Nat) (a b : Expr) : Expr :=
  if raw then
    (b - a) / 2 * (convexPanelRaw lo hi a + convexPanelRaw lo hi b)
  else
    (b - a) / 4 * (convexPanelA a + convexPanelA b) *
      (convexPanelB lo hi a + convexPanelB lo hi b)

def convexRiemannSelected (lo hi : Nat) (panels : List (Rat × Rat)) (mask : Nat) : Expr :=
  Expr.sum (panels.mapIdx fun j ab =>
    convexPanelSelected (mask.testBit j) lo hi (.ofRat ab.1) (.ofRat ab.2))

inductive ErrorKind where
  | finite
  | geometric
  | splitRaw (a : Rat)
  | riemann
  | convexRiemann (mask : Nat)
  deriving Repr

def error (lo hi s : Nat) (upper : List Int) (panels : List (Rat × Rat)) :
    ErrorKind → Expr
  | .finite => finiteError lo s upper
  | .geometric => geometricError lo hi s upper
  | .splitRaw a => splitRaw lo hi (.ofRat a)
  | .riemann => riemann lo hi panels
  | .convexRiemann mask => convexRiemannSelected lo hi panels mask

def target (lo hi s : Nat) (upper : List Int) (panels : List (Rat × Rat))
    (kind : ErrorKind) : Expr :=
  error lo hi s upper panels kind + eps ^ lo / u

end Schmeisser.Certificates.Block

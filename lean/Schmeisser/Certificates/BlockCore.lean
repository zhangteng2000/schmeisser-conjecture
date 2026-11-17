import Schmeisser.Certificates.BlockErrorExpressions
import Schmeisser.Certificates.ExpressionComparisons
import Schmeisser.Certificates.PanelCoverage
import Schmeisser.Certificates.Coverage

namespace Schmeisser.Certificates.Finite

def precision : Nat := 64
def scaleNat : Nat := 2 ^ precision
def scale : Int := scaleNat

theorem scale_pos : 0 < scale := by norm_num [scale, scaleNat, precision]

structure Data where
  lo : Nat
  hi : Nat
  cutoff : Int
  upper : List Int
  panels : List (Rat × Rat)
  deriving Repr

inductive LowerKind where
  | recurrence (steps : Nat) (base : Block.BaseKind)
  | moment
  deriving Repr

structure NumericRule where
  num : Nat
  lower : LowerKind
  error : Block.ErrorKind
  deriving Repr

inductive Rule where
  | threshold
  | quartic
  | numeric (rule : NumericRule)
  deriving Repr

def Data.cutoffExpr (data : Data) : Expr := .rat data.cutoff scale

def Data.thresholdLeft (data : Data) : Expr := .int (data.hi + 2) ^ 2
def Data.thresholdRight (data : Data) : Expr := 4 * (1 + data.cutoffExpr) ^ data.hi

def Data.check (data : Data) : Bool :=
  decide (3 ≤ data.lo ∧ data.lo ≤ data.hi ∧ data.hi ≤ 5999 ∧
    0 < data.cutoff ∧ data.cutoff < scale) &&
  checkPanels 0 1 data.panels &&
  Expr.checkGreater scale (fun _ => Interval.point scale 0)
    data.thresholdLeft data.thresholdRight

def Data.clip (data : Data) (box : Interval) : Interval :=
  ⟨max box.lo data.cutoff, box.hi⟩

def NumericRule.kapExpr (data : Data) (rule : NumericRule) : Expr :=
  .rat rule.num (4096 * data.hi)

noncomputable def NumericRule.kappa (data : Data) (rule : NumericRule) : ℝ :=
  (rule.num : ℝ) / (4096 * data.hi)

def NumericRule.intervalEnv (data : Data) (rule : NumericRule) (box : Interval) : Nat → Interval :=
  fun i => if i = 0 then data.clip box else
    if i = 1 then ⟨data.lo * scale, data.hi * scale⟩ else
      Interval.rational scale rule.num (4096 * data.hi)

def NumericRule.lowerExpr (data : Data) (rule : NumericRule) : Expr :=
  match rule.lower with
  | .recurrence steps kind => Block.recurrence data.lo data.hi 0 steps kind
  | .moment => Block.moment data.lo data.hi

def NumericRule.upperExpr (data : Data) (rule : NumericRule) : Expr :=
  Block.target data.lo data.hi scaleNat data.upper data.panels rule.error

def LowerKind.domain (data : Data) (box : Interval) : LowerKind → Prop
  | .moment => True
  | .recurrence steps (.basic quarter invEps) =>
      2 * steps + 2 ≤ data.lo ∧
      (quarter = true → 3 * scale ≤ 4 * box.lo) ∧
      (invEps = true → box.hi < scale)
  | .recurrence steps .exactTwo => data.lo = data.hi ∧ data.lo = 2 * steps + 2
  | .recurrence steps .trapezoidThree => data.lo = data.hi ∧ data.lo = 2 * steps + 3

instance (data : Data) (box : Interval) (kind : LowerKind) :
    Decidable (kind.domain data box) := by
  cases kind with
  | moment => unfold LowerKind.domain; infer_instance
  | recurrence steps base => cases base <;> unfold LowerKind.domain <;> infer_instance

def errorDomain (data : Data) (box : Interval) : Block.ErrorKind → Prop
  | .finite => data.lo = data.hi
  | .geometric => scale < 2 * box.lo
  | .splitRaw a => 0 ≤ a ∧ a < 1 ∧ box.hi < scale
  | .riemann => box.hi < scale
  | .convexRiemann _ => box.hi < scale

instance (data : Data) (box : Interval) (kind : Block.ErrorKind) :
    Decidable (errorDomain data box kind) := by
  cases kind <;> unfold errorDomain <;> infer_instance

def NumericRule.domain (data : Data) (rule : NumericRule) (raw : Interval) : Prop :=
  let box := data.clip raw
  24576 ≤ rule.num ∧ 0 < box.lo ∧ box.lo ≤ box.hi ∧ box.hi ≤ scale ∧
    rule.lower.domain data box ∧ errorDomain data box rule.error

instance (data : Data) (rule : NumericRule) (raw : Interval) :
    Decidable (rule.domain data raw) := by
  unfold NumericRule.domain
  infer_instance

def NumericRule.checkPolar (data : Data) (rule : NumericRule) (box : Interval) : Bool :=
  let env := rule.intervalEnv data box
  Expr.checkLe scale env (Block.kap / Block.u) 4 &&
    if rule.num = 24576 then true else
      decide (data.lo = data.hi) && Expr.checkLe scale env Block.h 1 &&
      Expr.checkGreater scale env 1 (Block.polar data.lo)

def NumericRule.checkLowerDomain (data : Data) (rule : NumericRule) (box : Interval) : Bool :=
  match rule.lower with
  | .recurrence _ _ => true
  | .moment => Expr.checkLe scale (rule.intervalEnv data box) 90
      (.int data.lo * Block.b ^ 2 / Block.d)

def NumericRule.check (data : Data) (rule : NumericRule) (box : Interval) : Bool :=
  decide (rule.domain data box) && rule.checkPolar data box &&
    rule.checkLowerDomain data box &&
    Expr.checkGreater scale (rule.intervalEnv data box) (rule.lowerExpr data) (rule.upperExpr data)

def Rule.check (data : Data) (box : Interval) : Rule → Bool
  | .threshold => decide (box.hi ≤ data.cutoff)
  | .quartic => decide (data.lo = 3 ∧ data.hi = 3 ∧ 99 * scale ≤ 100 * box.lo)
  | .numeric rule => rule.check data box

structure Segment where
  finish : Int
  rule : Rule
  deriving Repr

def checkSegments (data : Data) (start finish : Int) : List Segment → Bool
  | [] => decide (start = finish)
  | seg :: rest => decide (start < seg.finish) &&
      seg.rule.check data ⟨start, seg.finish⟩ && checkSegments data seg.finish finish rest

end Schmeisser.Certificates.Finite

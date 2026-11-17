import Schmeisser.Certificates.ScalarExpressions

namespace Schmeisser.Certificates.Expr

@[simp] theorem value_add (env : Nat → ℝ) (a b : Expr) :
    (a + b).value env = a.value env + b.value env := rfl

@[simp] theorem value_neg (env : Nat → ℝ) (a : Expr) :
    (-a).value env = -a.value env := rfl

@[simp] theorem value_sub (env : Nat → ℝ) (a b : Expr) :
    (a - b).value env = a.value env - b.value env := rfl

@[simp] theorem value_mul (env : Nat → ℝ) (a b : Expr) :
    (a * b).value env = a.value env * b.value env := rfl

@[simp] theorem value_div (env : Nat → ℝ) (a b : Expr) :
    (a / b).value env = a.value env / b.value env := rfl

@[simp] theorem value_pow (env : Nat → ℝ) (a : Expr) (n : Nat) :
    (a ^ n).value env = a.value env ^ n := rfl

@[simp] theorem value_ofNat (env : Nat → ℝ) (n : Nat) :
    (ofNat(n) : Expr).value env = (n : ℝ) := by
  simp only [value, Int.cast_natCast]

@[simp] theorem value_ofRat (env : Nat → ℝ) (q : Rat) :
    (ofRat q).value env = (q : ℝ) := by
  simp only [ofRat, value, Rat.cast_def, Int.cast_natCast]

theorem value_half (env : Nat → ℝ) (a : Expr) (n : Nat) :
    (a.half n).value env = a.value env ^ (n / 2) *
      (if n % 2 = 0 then 1 else Real.sqrt (a.value env)) := by
  unfold half
  split <;> simp [value_pow, value]

end Schmeisser.Certificates.Expr

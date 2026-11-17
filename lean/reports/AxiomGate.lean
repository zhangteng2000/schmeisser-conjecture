import Schmeisser.Main
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command

/-- Fail compilation if a theorem transitively uses any additional axiom. -/
elab "assert_standard_axioms " n:ident : command => do
  let name ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  let axioms ← Lean.collectAxioms name
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let rejected := axioms.filter fun a => !allowed.contains a
  unless rejected.isEmpty do
    throwError "{name} depends on forbidden axioms: {rejected}"
  logInfo m!"{name}: axiom gate passed; dependencies = {axioms}"

assert_standard_axioms Schmeisser.sharpness
assert_standard_axioms Schmeisser.main
assert_standard_axioms Schmeisser.universal_bound_iff
assert_standard_axioms Schmeisser.finite_degree_scalar_exclusion
assert_standard_axioms Schmeisser.large_degree_scalar_exclusion
assert_standard_axioms Schmeisser.quartic_endpoint_scalar_exclusion
assert_standard_axioms Schmeisser.quartic_scalar_exclusion
assert_standard_axioms Schmeisser.quintic_scalar_exclusion
assert_standard_axioms Schmeisser.sextic_scalar_exclusion
assert_standard_axioms Schmeisser.septic_scalar_exclusion

example (p : Polynomial ℂ) (hn : 2 ≤ p.natDegree)
    (hroots : ∀ z : ℂ, p.eval z = 0 → ‖z‖ ≤ 1)
    (ξ : ℂ) (hξ : ξ ∈ convexHull ℝ {z : ℂ | p.eval z = 0}) :
    ∃ ζ : ℂ, p.derivative.eval ζ = 0 ∧ ‖ξ - ζ‖ ≤ 1 :=
  Schmeisser.main p hn hroots ξ hξ

example (n : ℕ) (hn : 2 ≤ n) (r : ℝ) (hr : r < 1) :
    ∃ p : Polynomial ℂ, p.natDegree = n ∧
      (∀ z : ℂ, p.eval z = 0 → ‖z‖ ≤ 1) ∧
      ∃ ξ : ℂ, ξ ∈ convexHull ℝ {z : ℂ | p.eval z = 0} ∧
        ¬ ∃ ζ : ℂ, p.derivative.eval ζ = 0 ∧ ‖ξ - ζ‖ ≤ r :=
  Schmeisser.sharpness n hn r hr

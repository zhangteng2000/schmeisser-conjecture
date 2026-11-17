import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

open scoped BigOperators

namespace Schmeisser

theorem finite_geometric_tail_bound (k m l : ℕ) (hl : l ≤ k)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) :
    (∑ j ∈ Finset.Ico k (m + 1), z ^ (j - l)) ≤ z ^ (k - l) / (1 - z) := by
  rw [Finset.sum_Ico_eq_sum_range]
  have he (j : ℕ) : k + j - l = (k - l) + j := by omega
  simp_rw [he, pow_add]
  rw [← Finset.mul_sum]
  have hs := sum_le_hasSum (Finset.range (m + 1 - k))
    (fun j _ => pow_nonneg hz j) (hasSum_geometric_of_lt_one hz hz1)
  simpa only [div_eq_mul_inv] using
    mul_le_mul_of_nonneg_left hs (pow_nonneg hz (k - l))

end Schmeisser

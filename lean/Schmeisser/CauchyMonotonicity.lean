import Schmeisser.GeometricErrorIntegrals

/-! The normalized Cauchy coefficient bound decreases with the degree.
The proof uses only powers, the adjacent binomial-coefficient identity,
and the elementary inequality `j * (j + 2) ≤ (j + 1)^2`. -/

namespace Schmeisser

noncomputable def cauchyDegreeRatio (j : ℕ) : ℝ :=
  ((j : ℝ) + 1) ^ (j - 1) / (j : ℝ) ^ j

theorem cauchyDegreeRatio_pos {j : ℕ} (hj : 1 ≤ j) : 0 < cauchyDegreeRatio j := by
  have hjR : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  unfold cauchyDegreeRatio
  positivity

theorem cauchyDegreeRatio_succ (j : ℕ) (hj : 1 ≤ j) :
    cauchyDegreeRatio (j + 1) = cauchyDegreeRatio j *
      ((j : ℝ) * ((j : ℝ) + 2) / ((j : ℝ) + 1) ^ 2) ^ j := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show j ≠ 0 by omega)
  simp only [cauchyDegreeRatio, Nat.succ_eq_add_one, Nat.add_sub_cancel,
    Nat.cast_add, Nat.cast_one]
  rw [div_pow, mul_pow, ← pow_mul, Nat.mul_comm 2 (i + 1), pow_mul]
  simp only [pow_succ]
  have hi1 : (i : ℝ) + 1 ≠ 0 := by positivity
  have hi2 : (i : ℝ) + 1 + 1 ≠ 0 := by positivity
  field_simp
  ring

theorem cauchyDegreeRatio_succ_le (j : ℕ) (hj : 1 ≤ j) :
    cauchyDegreeRatio (j + 1) ≤ cauchyDegreeRatio j := by
  rw [cauchyDegreeRatio_succ j hj]
  have hjR : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hden : 0 < ((j : ℝ) + 1) ^ 2 := by positivity
  have hq0 : 0 ≤ (j : ℝ) * ((j : ℝ) + 2) / ((j : ℝ) + 1) ^ 2 := by positivity
  have hq1 : (j : ℝ) * ((j : ℝ) + 2) / ((j : ℝ) + 1) ^ 2 ≤ 1 :=
    (div_le_one hden).2 (by nlinarith)
  exact mul_le_of_le_one_right (cauchyDegreeRatio_pos hj).le (pow_le_one₀ hq0 hq1)

theorem cauchyDegreeRatio_antitone {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) :
    cauchyDegreeRatio j ≤ cauchyDegreeRatio i :=
  (antitoneOn_nat_Ici_of_succ_le cauchyDegreeRatio_succ_le) hi (hi.trans hij) hij

theorem normalizedCauchyCoefficient_nonneg (m k : ℕ) :
    0 ≤ normalizedCauchyCoefficient m k := by
  unfold normalizedCauchyCoefficient
  positivity

theorem normalizedCauchyCoefficient_sq (m k : ℕ) :
    normalizedCauchyCoefficient m k ^ 2 = (m : ℝ) ^ m /
      ((m.choose k : ℝ) ^ 2 * (k : ℝ) ^ k * ((m - k : ℕ) : ℝ) ^ (m - k)) := by
  rw [normalizedCauchyCoefficient, div_pow, Real.sq_sqrt (by positivity), div_div]
  congr 1
  ring

theorem normalizedCauchyCoefficient_succ_sq_identity (m k : ℕ)
    (hk : 1 ≤ k) (hkm : k < m) :
    normalizedCauchyCoefficient (m + 1) k ^ 2 * cauchyDegreeRatio (m - k) =
      normalizedCauchyCoefficient m k ^ 2 * cauchyDegreeRatio m := by
  have hm : 1 ≤ m := by omega
  have hd : 1 ≤ m - k := by omega
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hd0 : ((m - k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show m - k ≠ 0 by omega)
  have hc0 : (m.choose k : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hkm.le).ne'
  have hm10 : (m : ℝ) + 1 ≠ 0 := by positivity
  have hd10 : ((m - k : ℕ) : ℝ) + 1 ≠ 0 := by positivity
  have hsub : m + 1 - k = (m - k) + 1 := by omega
  have hchoose : ((m + 1).choose k : ℝ) =
      (m.choose k : ℝ) * ((m : ℝ) + 1) / (((m - k : ℕ) : ℝ) + 1) := by
    apply (eq_div_iff hd10).2
    have h := Nat.choose_mul_succ_eq m k
    rw [hsub] at h
    exact_mod_cast h.symm
  have hmpow : ((m : ℝ) + 1) ^ (m + 1) =
      ((m : ℝ) + 1) ^ (m - 1) * ((m : ℝ) + 1) ^ 2 := by
    rw [← pow_add]
    congr 1
    omega
  have hdpow : (((m - k : ℕ) : ℝ) + 1) ^ (m - k + 1) =
      (((m - k : ℕ) : ℝ) + 1) ^ (m - k - 1) * (((m - k : ℕ) : ℝ) + 1) ^ 2 := by
    rw [← pow_add]
    congr 1
    omega
  rw [normalizedCauchyCoefficient_sq, normalizedCauchyCoefficient_sq]
  simp only [cauchyDegreeRatio, hsub, Nat.cast_add, Nat.cast_one]
  rw [hchoose, hmpow, hdpow]
  field_simp

theorem normalizedCauchyCoefficient_succ_le (m k : ℕ) (hk : 1 ≤ k) (hkm : k < m) :
    normalizedCauchyCoefficient (m + 1) k ≤ normalizedCauchyCoefficient m k := by
  have hd : 1 ≤ m - k := by omega
  have hratio := cauchyDegreeRatio_antitone hd (Nat.sub_le m k)
  have h := mul_le_mul_of_nonneg_left hratio (sq_nonneg (normalizedCauchyCoefficient m k))
  rw [← normalizedCauchyCoefficient_succ_sq_identity m k hk hkm] at h
  have hsq := (mul_le_mul_iff_left₀ (cauchyDegreeRatio_pos hd)).1 h
  exact (sq_le_sq₀ (normalizedCauchyCoefficient_nonneg _ _) (normalizedCauchyCoefficient_nonneg _ _)).1 hsq

theorem normalizedCauchyCoefficient_antitone {lo m k : ℕ} (hk : 1 ≤ k)
    (hklo : k < lo) (hlom : lo ≤ m) :
    normalizedCauchyCoefficient m k ≤ normalizedCauchyCoefficient lo k := by
  have hanti : AntitoneOn (fun n => normalizedCauchyCoefficient n k) {n | k + 1 ≤ n} :=
    antitoneOn_nat_Ici_of_succ_le (fun n hn => normalizedCauchyCoefficient_succ_le n k hk (by omega))
  exact hanti (show k + 1 ≤ lo by omega) (show k + 1 ≤ m by omega) hlom

theorem normalizedCauchyCoefficient_le_iff_sq {m k : ℕ} (hk : 1 ≤ k) (hkm : k < m)
    {a s : ℝ} (ha : 0 ≤ a) (hs : 0 < s) :
    normalizedCauchyCoefficient m k ≤ a / s ↔
      (m : ℝ) ^ m * s ^ 2 ≤ a ^ 2 * (m.choose k : ℝ) ^ 2 *
        (k : ℝ) ^ k * ((m - k : ℕ) : ℝ) ^ (m - k) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hdpos : (0 : ℝ) < ((m - k : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hkm
  have hcpos : (0 : ℝ) < m.choose k := by exact_mod_cast Nat.choose_pos hkm.le
  have hden : 0 < (m.choose k : ℝ) ^ 2 * (k : ℝ) ^ k * ((m - k : ℕ) : ℝ) ^ (m - k) := by
    positivity
  rw [← sq_le_sq₀ (normalizedCauchyCoefficient_nonneg m k) (div_nonneg ha hs.le),
    normalizedCauchyCoefficient_sq, div_pow, div_le_div_iff₀ hden (sq_pos_of_pos hs)]
  constructor <;> intro h <;> nlinarith only [h]

end Schmeisser

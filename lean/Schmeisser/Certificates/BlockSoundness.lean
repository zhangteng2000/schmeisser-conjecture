import Schmeisser.Certificates.BlockCore

namespace Schmeisser.Certificates.Finite

theorem Data.check_sound (data : Data) (h : data.check = true) :
    3 ≤ data.lo ∧ data.lo ≤ data.hi ∧ data.hi ≤ 5999 ∧
    0 < data.cutoff ∧ data.cutoff < scale ∧
    PanelPartition (1 : Rat) 0 data.panels ∧
    4 * (1 + (data.cutoff : ℝ) / scale) ^ data.hi < ((data.hi : ℝ) + 2) ^ 2 := by
  simp only [Data.check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hb, hp⟩, ht⟩ := h
  have he := Expr.checkGreater_sound scale_pos
    (fun _ => Interval.contains_point scale_pos 0)
    data.thresholdLeft data.thresholdRight ht
  refine ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2,
    checkPanels_sound 0 1 data.panels hp, ?_⟩
  simpa [Data.thresholdLeft, Data.thresholdRight, Data.cutoffExpr, Expr.value,
    Nat.cast_add, Nat.cast_ofNat] using he

theorem Data.clip_contains (data : Data) {box : Interval} {x : ℝ}
    (hx : box.Contains scale x) (hcut : (data.cutoff : ℝ) / scale ≤ x) :
    (data.clip box).Contains scale x := by
  have hs : (0 : ℝ) < scale := by exact_mod_cast scale_pos
  obtain ⟨hxlo, hxhi⟩ := (Interval.contains_iff_scaled scale_pos box x).1 hx
  have hc : (data.cutoff : ℝ) ≤ x * scale := (div_le_iff₀ hs).1 hcut
  rw [Interval.contains_iff_scaled scale_pos]
  simpa only [Data.clip, Int.cast_max] using And.intro (max_le hxlo hc) hxhi

theorem NumericRule.intervalEnv_contains (data : Data) (rule : NumericRule)
    (hhi : 0 < data.hi) {box : Interval} {x : ℝ} {m : Nat}
    (hx : box.Contains scale x) (hcut : (data.cutoff : ℝ) / scale ≤ x)
    (hlo : data.lo ≤ m) (hup : m ≤ data.hi) :
    ∀ i, (rule.intervalEnv data box i).Contains scale
      (Block.env x m (rule.kappa data) i) := by
  intro i
  by_cases hi0 : i = 0
  · simp only [NumericRule.intervalEnv, Block.env, hi0, ↓reduceIte]
    exact data.clip_contains hx hcut
  by_cases hi1 : i = 1
  · simp only [NumericRule.intervalEnv, Block.env, hi1, show ¬ (1 : Nat) = 0 by decide,
      ↓reduceIte]
    rw [Interval.contains_iff_scaled scale_pos]
    have hs : (0 : ℝ) ≤ scale := by exact_mod_cast scale_pos.le
    constructor
    · simpa only [Int.cast_mul, Int.cast_natCast] using
        mul_le_mul_of_nonneg_right (show (data.lo : ℝ) ≤ m by exact_mod_cast hlo) hs
    · simpa only [Int.cast_mul, Int.cast_natCast] using
        mul_le_mul_of_nonneg_right (show (m : ℝ) ≤ data.hi by exact_mod_cast hup) hs
  · simp only [NumericRule.intervalEnv, Block.env, hi0, hi1, ↓reduceIte]
    have hden : (0 : Int) < 4096 * data.hi := by omega
    simpa [NumericRule.kappa] using Interval.contains_rational scale_pos hden (rule.num : Int)

def NumericRule.Checked (data : Data) (rule : NumericRule) (box : Interval)
    (m : Nat) (x : ℝ) : Prop :=
  let env := Block.env x m (rule.kappa data)
  rule.domain data box ∧
    (rule.upperExpr data).value env < (rule.lowerExpr data).value env ∧
    (Block.kap / Block.u : Expr).value env ≤ 4 ∧
    (rule.num = 24576 ∨ data.lo = data.hi ∧ Block.h.value env ≤ 1 ∧
      (Block.polar data.lo).value env < 1) ∧
    match rule.lower with
    | .recurrence _ _ => True
    | .moment => 90 ≤ (.int data.lo * Block.b ^ 2 / Block.d : Expr).value env

theorem NumericRule.check_sound (data : Data) (rule : NumericRule)
    (hhi : 0 < data.hi) {box : Interval} {x : ℝ} {m : Nat}
    (hx : box.Contains scale x) (hcut : (data.cutoff : ℝ) / scale ≤ x)
    (hlo : data.lo ≤ m) (hup : m ≤ data.hi)
    (hcheck : rule.check data box = true) : rule.Checked data box m x := by
  have henv := rule.intervalEnv_contains data hhi hx hcut hlo hup
  simp only [NumericRule.check, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  obtain ⟨⟨⟨hdomain, hpolar⟩, hlower⟩, hstrict⟩ := hcheck
  have hstrictR := Expr.checkGreater_sound scale_pos henv _ _ hstrict
  simp only [NumericRule.checkPolar, Bool.and_eq_true] at hpolar
  have hkap := Expr.checkLe_sound scale_pos henv _ _ hpolar.1
  refine ⟨hdomain, hstrictR, ?_, ?_, ?_⟩
  · simpa only [Expr.value_ofNat, Nat.cast_ofNat] using hkap
  · by_cases hn : rule.num = 24576
    · exact Or.inl hn
    · have hp := hpolar.2
      simp only [hn, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hp
      refine Or.inr ⟨hp.1.1, ?_, ?_⟩
      · simpa only [Expr.value_ofNat, Nat.cast_one] using
          Expr.checkLe_sound scale_pos henv _ _ hp.1.2
      · simpa only [Expr.value_ofNat, Nat.cast_one] using
          Expr.checkGreater_sound scale_pos henv _ _ hp.2
  · cases hl : rule.lower with
    | recurrence steps base => trivial
    | moment =>
      simp only [NumericRule.checkLowerDomain, hl] at hlower
      simpa only [Expr.value_ofNat, Nat.cast_ofNat] using
        Expr.checkLe_sound scale_pos henv _ _ hlower

theorem checkSegments_append (data : Data) (first rest : List Segment)
    (start middle finish : Int)
    (hfirst : checkSegments data start middle first = true)
    (hrest : checkSegments data middle finish rest = true) :
    checkSegments data start finish (first ++ rest) = true := by
  induction first generalizing start with
  | nil =>
    simp only [checkSegments, decide_eq_true_eq] at hfirst
    simpa only [List.nil_append, hfirst] using hrest
  | cons seg tail ih =>
    simp only [checkSegments, Bool.and_eq_true, decide_eq_true_eq] at hfirst
    simp only [List.cons_append, checkSegments, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hfirst.1, ih seg.finish hfirst.2⟩

theorem checkSegments_covers (data : Data) (segments : List Segment) (start finish : Int)
    (hcheck : checkSegments data start finish segments = true)
    {x : ℝ} (hxlo : (start : ℝ) / scale < x) (hxhi : x ≤ (finish : ℝ) / scale) :
    ∃ (box : Interval) (rule : Rule), box.Contains scale x ∧ rule.check data box = true := by
  induction segments generalizing start with
  | nil =>
    simp only [checkSegments, decide_eq_true_eq] at hcheck
    subst start
    exact False.elim (not_lt_of_ge hxhi hxlo)
  | cons seg tail ih =>
    simp only [checkSegments, Bool.and_eq_true, decide_eq_true_eq] at hcheck
    by_cases hx : x ≤ (seg.finish : ℝ) / scale
    · exact ⟨⟨start, seg.finish⟩, seg.rule, ⟨hxlo.le, hx⟩, hcheck.1.2⟩
    · exact ih seg.finish hcheck.2 (lt_of_not_ge hx)

end Schmeisser.Certificates.Finite

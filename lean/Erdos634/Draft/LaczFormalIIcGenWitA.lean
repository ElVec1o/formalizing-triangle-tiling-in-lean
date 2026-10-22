-- Draft/LaczFormalIIcGenWitA.lean -- WITNESS of the GENERIC Case IIc block (alpha != beta), step A: exact arithmetic in Z[sqrt 2] (pairs of integers), sign test, soundness against the reals.
-- Laczkovich (DCG 48 (2012)), Thm 2.1 (v), construction l.236-290: octagon of 204 tiles, gamma = pi/4.  NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012)), Beeson, Beeson-Zhang.
import Erdos634.CertCoord
import Erdos634.CertGeom

namespace Erdos634.Draft.LaczFormal.GenWit

/-- `a + b * sqrt 2` with integer `a, b`. -/
structure Z2 where
  a : Int
  b : Int
deriving DecidableEq

namespace Z2

noncomputable def val (z : Z2) : ℝ := (z.a : ℝ) + (z.b : ℝ) * Real.sqrt 2

def add (x y : Z2) : Z2 := ⟨x.a + y.a, x.b + y.b⟩
def sub (x y : Z2) : Z2 := ⟨x.a - y.a, x.b - y.b⟩
def neg (x : Z2) : Z2 := ⟨-x.a, -x.b⟩
def mul (x y : Z2) : Z2 := ⟨x.a * y.a + 2 * (x.b * y.b), x.a * y.b + x.b * y.a⟩
def zero : Z2 := ⟨0, 0⟩

theorem hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
theorem hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)

theorem val_add (x y : Z2) : (add x y).val = x.val + y.val := by unfold val add; push_cast; ring
theorem val_sub (x y : Z2) : (sub x y).val = x.val - y.val := by unfold val sub; push_cast; ring
theorem val_neg (x : Z2) : (neg x).val = - x.val := by unfold val neg; push_cast; ring
theorem val_zero : zero.val = 0 := by unfold val zero; simp
theorem val_mul (x y : Z2) : (mul x y).val = x.val * y.val := by
  unfold val mul; push_cast
  linear_combination (-(x.b : ℝ) * y.b) * hs

/-- sign test: `0 < a + b sqrt 2`. -/
def posB (z : Z2) : Bool :=
  if 0 < z.a then (if 0 ≤ z.b then true else decide (2 * (z.b * z.b) < z.a * z.a))
  else if z.a = 0 then decide (0 < z.b)
  else (if 0 < z.b then decide (z.a * z.a < 2 * (z.b * z.b)) else false)

theorem posB_iff (z : Z2) : posB z = true ↔ 0 < z.val := by
  have h2 := hs
  have h0 := hspos
  unfold posB val
  rcases lt_trichotomy z.a 0 with ha | ha | ha
  · have ha' : ¬ (0 < z.a) := by omega
    have ha'' : z.a ≠ 0 := by omega
    have haR : (z.a : ℝ) < 0 := by exact_mod_cast ha
    simp only [ha', ha'', if_false]
    by_cases hb : 0 < z.b
    · have hbR : (0 : ℝ) < z.b := by exact_mod_cast hb
      simp only [hb, if_true, decide_eq_true_eq]
      have e : (z.a * z.a : Int) < 2 * (z.b * z.b) ↔ (z.a : ℝ) * z.a < 2 * ((z.b : ℝ) * z.b) := by
        constructor <;> intro h <;> [exact_mod_cast h; exact_mod_cast h]
      rw [e]
      constructor
      · intro h
        by_contra hneg
        push_neg at hneg
        nlinarith [mul_pos hbR h0]
      · intro h
        nlinarith [mul_pos hbR h0]
    · have hbR : (z.b : ℝ) ≤ 0 := by exact_mod_cast (not_lt.mp hb)
      simp only [hb, if_false]
      constructor
      · intro h; exact absurd h (by simp)
      · intro h; nlinarith [mul_nonneg (neg_nonneg.mpr hbR) h0.le]
  · simp only [ha, lt_irrefl, if_false, if_true, decide_eq_true_eq]
    simp only [Int.cast_zero, zero_add]
    constructor
    · intro h
      have hbR : (0 : ℝ) < z.b := by exact_mod_cast h
      nlinarith [mul_pos hbR h0]
    · intro h
      have : (0 : ℝ) < z.b := by
        by_contra hneg; push_neg at hneg; nlinarith [mul_nonneg (neg_nonneg.mpr hneg) h0.le]
      exact_mod_cast this
  · have haR : (0 : ℝ) < z.a := by exact_mod_cast ha
    simp only [ha, if_true]
    by_cases hb : 0 ≤ z.b
    · have hbR : (0 : ℝ) ≤ z.b := by exact_mod_cast hb
      simp only [hb, if_true, true_iff]
      nlinarith [mul_nonneg hbR h0.le]
    · have hbR : (z.b : ℝ) < 0 := by exact_mod_cast (not_le.mp hb)
      simp only [hb, if_false, decide_eq_true_eq]
      have e : (2 * (z.b * z.b) : Int) < z.a * z.a ↔ 2 * ((z.b : ℝ) * z.b) < (z.a : ℝ) * z.a := by
        constructor <;> intro h <;> [exact_mod_cast h; exact_mod_cast h]
      rw [e]
      constructor
      · intro h
        by_contra hneg; push_neg at hneg
        nlinarith [mul_pos (neg_pos.mpr hbR) h0]
      · intro h
        nlinarith [mul_pos (neg_pos.mpr hbR) h0]

theorem val_eq_zero_iff (z : Z2) : z.val = 0 ↔ z = zero := by
  constructor
  · intro h
    have hb : z.b = 0 := by
      by_contra hb
      have hbR : (z.b : ℝ) ≠ 0 := by exact_mod_cast hb
      apply irrational_sqrt_two
      refine ⟨-(z.a : ℚ) / z.b, ?_⟩
      unfold val at h
      push_cast
      field_simp
      linarith
    have ha : z.a = 0 := by
      unfold val at h; rw [hb] at h; simp at h; exact_mod_cast h
    cases z; simp_all [zero]
  · rintro rfl; exact val_zero

theorem val_inj {x y : Z2} (h : x.val = y.val) : x = y := by
  have : (sub x y).val = 0 := by rw [val_sub, h]; ring
  have h2 := (val_eq_zero_iff _).mp this
  cases x; cases y; simp [sub, zero] at h2
  obtain ⟨h1, h2⟩ := h2
  simp only [Z2.mk.injEq]; omega

/-- `0 ≤ a + b sqrt 2`. -/
def geB (z : Z2) : Bool := posB z || decide (z = zero)

theorem geB_iff (z : Z2) : geB z = true ↔ 0 ≤ z.val := by
  unfold geB
  simp only [Bool.or_eq_true, decide_eq_true_eq, posB_iff]
  constructor
  · rintro (h | h)
    · exact h.le
    · rw [h, val_zero]
  · intro h
    rcases h.lt_or_eq with h | h
    · exact Or.inl h
    · exact Or.inr ((val_eq_zero_iff z).mp h.symm)

/-- `a + b sqrt 2 ≤ 0`. -/
def leB (z : Z2) : Bool := geB (neg z)

theorem leB_iff (z : Z2) : leB z = true ↔ z.val ≤ 0 := by
  unfold leB
  rw [geB_iff, val_neg]
  constructor <;> intro h <;> linarith

end Z2

end Erdos634.Draft.LaczFormal.GenWit

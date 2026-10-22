import Mathlib.Tactic

/-!
# Beeson (arXiv 1206.2229v4) Lemma 52: the dichotomy for a rational tile with `3 alpha + 2 beta = pi`

Tile `(a,b,c)`, `b = c - a^2/c`, i.e. `a^2 = c (c - b)`, `0 < b < c` natural numbers.  The printed
identity is `b (a^2+b^2) - a^2 c = -(c^3 - 2 b c^2 + b^2 c - b^3)` (the signs are lost in the text
extraction; verified here by `ring`), and for rational `b/c` neither side vanishes (rational root
test: `x^3 = (1-x)^2` has no rational root in `(0,1)`).  Hence exactly one of (i)
`c + b^2/c < a^2/b + b` and (ii) `a^2 c < b (a^2+b^2)` holds.  Credit Beeson (arXiv 1206.2229),
Laczkovich.  UNAUDITED.
-/

namespace Erdos634.BeesonLemma52

theorem identity52 (a b c : ℝ) (h : a ^ 2 = c * (c - b)) :
    b * (a ^ 2 + b ^ 2) - a ^ 2 * c = -(c ^ 3 - 2 * b * c ^ 2 + b ^ 2 * c - b ^ 3) := by
  rw [h]; ring

/-- no rational root: `c (c-b)^2 = b^3` is impossible for `0 < b < c`. -/
theorem no_rational_root (b c : ℕ) (hb : 0 < b) (hbc : b < c) : c * (c - b) ^ 2 ≠ b ^ 3 := by
  intro h
  obtain ⟨d, hd⟩ : ∃ d, c = b + d := ⟨c - b, by omega⟩
  have hd0 : 0 < d := by omega
  subst hd
  rw [Nat.add_sub_cancel_left] at h
  obtain ⟨b', d', hcop, hb', hd'⟩ := Nat.exists_coprime b d
  have hg : 0 < Nat.gcd b d := Nat.gcd_pos_of_pos_left d hb
  set g := Nat.gcd b d with hgdef
  rw [hb', hd'] at h
  have h2 : (b' + d') * d' ^ 2 * g ^ 3 = b' ^ 3 * g ^ 3 := by nlinarith [h]
  have h3 : (b' + d') * d' ^ 2 = b' ^ 3 :=
    Nat.eq_of_mul_eq_mul_right (pow_pos hg 3) h2
  have h4 : d' ^ 2 ∣ b' ^ 3 := ⟨b' + d', by rw [← h3]; ring⟩
  have h5 : d' ^ 2 = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow 2 3 hcop.symm) h4
  have hd1 : d' = 1 := by
    have : d' ^ 2 = 1 ^ 2 := by simpa using h5
    exact (Nat.pow_left_injective (by norm_num : 2 ≠ 0)) this
  subst hd1
  have hb'0 : 0 < b' := by
    rcases Nat.eq_zero_or_pos b' with h0 | h0
    · rw [h0] at hb'; omega
    · exact h0
  rcases Nat.lt_or_ge b' 2 with h6 | h6
  · have : b' = 1 := by omega
    subst this; norm_num at h3
  · nlinarith [h3, Nat.mul_le_mul h6 h6, Nat.mul_le_mul (Nat.mul_le_mul h6 h6) h6]

/-- **Lemma 52 (dichotomy).**  For a tile `(a,b,c)` of naturals with `a^2 = c (c-b)`, `0 < b < c`:
exactly one of (i) `c + b^2/c < a^2/b + b`, (ii) `a^2 c < b (a^2 + b^2)` holds. -/
theorem lemma52 (a b c : ℕ) (hb : 0 < b) (hbc : b < c) (ha : a * a = c * (c - b)) :
    ((c : ℝ) + (b : ℝ) ^ 2 / c < (a : ℝ) ^ 2 / b + b ∧ ¬ ((a : ℝ) ^ 2 * c < b * ((a : ℝ) ^ 2 + (b : ℝ) ^ 2))) ∨
    ((a : ℝ) ^ 2 * c < b * ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) ∧ ¬ ((c : ℝ) + (b : ℝ) ^ 2 / c < (a : ℝ) ^ 2 / b + b)) := by
  have hbR : (0 : ℝ) < b := Nat.cast_pos.mpr hb
  have hcR : (0 : ℝ) < c := Nat.cast_pos.mpr (by omega)
  have haR : (a : ℝ) ^ 2 = c * (c - b) := by
    have : ((a * a : ℕ) : ℝ) = ((c * (c - b) : ℕ) : ℝ) := by rw [ha]
    push_cast [Nat.cast_sub hbc.le] at this
    nlinarith [this]
  have hne := no_rational_root b c hb hbc
  have hneR : (c : ℝ) * (c - b) ^ 2 ≠ (b : ℝ) ^ 3 := by
    intro h
    apply hne
    have : ((c * (c - b) ^ 2 : ℕ) : ℝ) = ((b ^ 3 : ℕ) : ℝ) := by
      push_cast [Nat.cast_sub hbc.le]; exact h
    exact_mod_cast this
  have key : (c : ℝ) + (b : ℝ) ^ 2 / c < (a : ℝ) ^ 2 / b + b ↔ (b : ℝ) ^ 3 < c * (c - b) ^ 2 := by
    rw [haR]
    constructor
    · intro h
      have := h
      rw [← sub_pos] at this
      have e : (c * (c - b) / b + b - (c + b ^ 2 / c) : ℝ) =
          (c * (c - b) ^ 2 - b ^ 3) / (b * c) := by field_simp; ring
      rw [e] at this
      have := (div_pos_iff_of_pos_right (by positivity)).mp this
      linarith
    · intro h
      rw [← sub_pos]
      have e : (c * (c - b) / b + b - (c + b ^ 2 / c) : ℝ) =
          (c * (c - b) ^ 2 - b ^ 3) / (b * c) := by field_simp; ring
      rw [e]; apply div_pos <;> [linarith; positivity]
  have key2 : (a : ℝ) ^ 2 * c < b * ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) ↔ c * (c - b) ^ 2 < (b : ℝ) ^ 3 := by
    rw [haR]; constructor <;> intro h <;> nlinarith [h]
  rcases lt_or_gt_of_ne hneR with h | h
  · right
    refine ⟨key2.mpr h, ?_⟩
    rw [key]; intro h'; linarith
  · left
    refine ⟨key.mpr h, ?_⟩
    rw [key2]; intro h'; linarith

/- Witness `(12,7,16)` (Beeson's example, `s = 3/4`): hypotheses `144 = 16*9`, `0<7<16` hold, so
exactly one of (i), (ii) holds (here (i): `16 + 49/16 < 144/7 + 7`). -/
example := lemma52 12 7 16 (by norm_num) (by norm_num) (by norm_num)

end Erdos634.BeesonLemma52

-- Draft/FDCEqSpec.lean -- FDC item 11: `prop:eqspec` (division form, q as in the paper) and
-- `prop:eqspecint` (tiling form, integers s, t, q), stated as in main erdos-634.tex:1791-1822.
--
-- The existing `EqSpecAlgebra` is in cleared-denominator form (s, t, N supplied as `s*X = 3S`,
-- ...; `q` never defined as `2S(a+b)/(ab)`).  Part A derives the paper's division form from
-- positivity + the 120-degree relation (X, Y, ab are nonzero; nothing else is assumed).  Part B
-- assembles `prop:eqspecint` from `Row5.theoremE_twoPiThree` (FluxCRow5; positivity, parity,
-- `s X = 3S`, `t Y = 3S`, `S^2 = N a b`, `s t = 3 N`: ALREADY in Lean, the PAPER_MAP row for
-- `prop:eqspecint` is stale on this) plus the one new step "q is an integer".
--
-- STATEMENT MATCH recorded in (private working notes, not included)  UNAUDITED; promotes no label.
-- Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).  No sorry, no native_decide.
import Erdos634.EqSpecAlgebra
import Erdos634.Draft.FluxCRow5
import Erdos634.Draft.FluxPaperCorIntAnchored
import Erdos634.Draft.G3CEqui135Control

namespace Erdos634.Draft.FDCEqSpec
open Erdos634.Geometry Erdos634.EqSpecAlgebra

/-! ## Part A: `prop:eqspec` in the paper's division form -/

/-- For a `2pi/3` triple, `c + a - b > 0` and `c + b - a > 0`. -/
theorem X_Y_pos {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : c ^ 2 = a ^ 2 + a * b + b ^ 2) : 0 < c + a - b ∧ 0 < c + b - a := by
  have hab := mul_pos ha hb
  have h1 : b < c := by
    by_contra hh
    push Not at hh
    nlinarith [mul_self_le_mul_self hc.le hh]
  have h2 : a < c := by
    by_contra hh
    push Not at hh
    nlinarith [mul_self_le_mul_self hc.le hh]
  constructor <;> linarith

/-- **`prop:eqspec` as written** (erdos-634.tex:1791).  `(a,b,c)` a `2pi/3` tile (`c^2 = a^2+ab+b^2`,
sides positive), `S > 0`, `X = c+a-b`, `Y = c+b-a`, `s = 3S/X`, `t = 3S/Y`, `N = S^2/(ab)`,
`q = 2S(a+b)/(ab)` (real division, as in the paper).  Then `XY = 3ab`, `st = 3N`,
`(t-s)^2 + 16N = q^2`. -/
theorem eqspec_division_form {a b c S X Y s t N q : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hS : 0 < S)
    (h : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (hX : X = c + a - b) (hY : Y = c + b - a)
    (hs : s = 3 * S / X) (ht : t = 3 * S / Y)
    (hN : N = S ^ 2 / (a * b)) (hq : q = 2 * S * (a + b) / (a * b)) :
    X * Y = 3 * a * b ∧ s * t = 3 * N ∧ (t - s) ^ 2 + 16 * N = q ^ 2 := by
  obtain ⟨hXp, hYp⟩ := X_Y_pos ha hb hc h
  have hab : a * b ≠ 0 := (mul_pos ha hb).ne'
  have hXne : X ≠ 0 := by rw [hX]; exact hXp.ne'
  have hYne : Y ≠ 0 := by rw [hY]; exact hYp.ne'
  have hXY : X * Y = 3 * a * b := by
    rw [hX, hY]; linear_combination h
  refine ⟨hXY, ?_, ?_⟩
  · rw [hs, ht, hN, div_mul_div_comm, hXY]
    field_simp
  · have hsX : s * X = 3 * S := by rw [hs]; field_simp
    have htY : t * Y = 3 * S := by rw [ht]; field_simp
    have hNab : N * (a * b) = S ^ 2 := by rw [hN]; field_simp
    have hsv : s * (a * b) = S * (c + b - a) := by
      rw [← hY]
      apply mul_right_cancel₀ hXne
      linear_combination (a * b) * hsX - S * hXY
    have htv : t * (a * b) = S * (c + a - b) := by
      rw [← hX]
      apply mul_right_cancel₀ hYne
      linear_combination (a * b) * htY - S * hXY
    have hd := disc_eq (a := a) (b := b) (c := c) (S := S) s t N hab
      (by rw [← hX]; exact hsX) (by rw [← hY]; exact htY) h hNab hsv htv
    rw [hq, div_pow, eq_div_iff (pow_ne_zero 2 hab)]
    exact hd

/-- **The converse clause of `prop:eqspec`.**  If `s, t > 0`, `st = 3N` and `q^2 = (t-s)^2 + 16N`
with `q > 0`, then the triple `lam*(q+(t-s), q-(t-s), 2(s+t))` has positive entries and satisfies the
`2pi/3` relation `C^2 = A^2 + AB + B^2` (for every `lam`; positivity for `lam > 0`). -/
theorem eqspec_converse {s t N q : ℝ} (hs : 0 < s) (ht : 0 < t) (hN : s * t = 3 * N)
    (hq : (t - s) ^ 2 + 16 * N = q ^ 2) (hq0 : 0 < q) (lam : ℝ) :
    (lam * (2 * (s + t))) ^ 2 =
        (lam * (q + (t - s))) ^ 2 + (lam * (q + (t - s))) * (lam * (q - (t - s)))
          + (lam * (q - (t - s))) ^ 2
      ∧ (0 < lam → 0 < lam * (q + (t - s)) ∧ 0 < lam * (q - (t - s)) ∧ 0 < lam * (2 * (s + t))) := by
  have hN0 : 0 < N := by nlinarith [mul_pos hs ht]
  have hcore := converse_triple s t q (by rw [← hq]; nlinarith [hN])
  refine ⟨by nlinarith [hcore], fun hl => ?_⟩
  have hqt : |t - s| < q := by
    have : (t - s) ^ 2 < q ^ 2 := by nlinarith
    exact abs_lt_of_sq_lt_sq this hq0.le
  have h1 := (abs_lt.mp hqt)
  refine ⟨mul_pos hl (by linarith [h1.1]), mul_pos hl (by linarith [h1.2]), mul_pos hl (by linarith)⟩

/-- **The forward proportionality** (the sentence after the proof of `prop:eqspecint`: "Then `a-b`,
`a+b` and `c` give the displayed proportions"): `(a,b,c) = (S/4N) * (q+(t-s), q-(t-s), 2(s+t))`. -/
theorem eqspec_proportional {a b c S X Y s t N q : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hS : 0 < S)
    (h : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (hX : X = c + a - b) (hY : Y = c + b - a)
    (hs : s = 3 * S / X) (ht : t = 3 * S / Y)
    (hN : N = S ^ 2 / (a * b)) (hq : q = 2 * S * (a + b) / (a * b)) :
    a = S / (4 * N) * (q + (t - s)) ∧ b = S / (4 * N) * (q - (t - s)) ∧
      c = S / (4 * N) * (2 * (s + t)) := by
  obtain ⟨hXp, hYp⟩ := X_Y_pos ha hb hc h
  have hab : a * b ≠ 0 := (mul_pos ha hb).ne'
  have hXne : X ≠ 0 := by rw [hX]; exact hXp.ne'
  have hYne : Y ≠ 0 := by rw [hY]; exact hYp.ne'
  have hXY : X * Y = 3 * a * b := by
    rw [hX, hY]; linear_combination h
  have hsX : s * X = 3 * S := by rw [hs]; field_simp
  have htY : t * Y = 3 * S := by rw [ht]; field_simp
  have hNab : N * (a * b) = S ^ 2 := by rw [hN]; field_simp
  have hN0 : 0 < N := by
    rw [hN]; exact div_pos (pow_pos hS 2) (mul_pos ha hb)
  have hsv : s * (a * b) = S * Y := by
    apply mul_right_cancel₀ hXne
    linear_combination (a * b) * hsX - S * hXY
  have htv : t * (a * b) = S * X := by
    apply mul_right_cancel₀ hYne
    linear_combination (a * b) * htY - S * hXY
  have hqab : q * (a * b) = 2 * S * (a + b) := by rw [hq]; field_simp
  have hts : (t - s) * (a * b) = 2 * S * (a - b) := by
    have : (t - s) * (a * b) = S * (X - Y) := by rw [sub_mul, htv, hsv]; ring
    rw [this, hX, hY]; ring
  have hst : (s + t) * (a * b) = 2 * S * c := by
    have : (s + t) * (a * b) = S * (X + Y) := by rw [add_mul, htv, hsv]; ring
    rw [this, hX, hY]; ring
  have hfin : ∀ u v : ℝ, u * (4 * N) = S * v → u = S / (4 * N) * v := by
    intro u v h1
    rw [div_mul_eq_mul_div, eq_div_iff (mul_pos four_pos hN0).ne']
    linarith
  refine ⟨hfin a _ ?_, hfin b _ ?_, hfin c _ ?_⟩
  · apply mul_right_cancel₀ hab
    linear_combination (4 * a) * hNab - S * (hqab + hts)
  · apply mul_right_cancel₀ hab
    linear_combination (4 * b) * hNab - S * (hqab - hts)
  · apply mul_right_cancel₀ hab
    linear_combination (4 * c) * hNab - S * (2 * hst)

/-! ## Part B: `prop:eqspecint` -/

/-- A rational whose square is an integer is an integer (positive root). -/
theorem exists_int_of_sq_int {r : ℝ} (hr : 0 < r) (hq : ∃ x : ℚ, (x : ℝ) = r) (M : ℤ)
    (hM : r ^ 2 = M) : ∃ z : ℤ, 0 < z ∧ (z : ℝ) = r := by
  obtain ⟨x, rfl⟩ := hq
  have hx2 : x ^ 2 = (M : ℚ) := by
    have : ((x ^ 2 : ℚ) : ℝ) = ((M : ℚ) : ℝ) := by push_cast; exact hM
    exact_mod_cast this
  have hsq : IsSquare (M : ℚ) := ⟨x, by rw [← hx2]; ring⟩
  obtain ⟨z, hz⟩ := Rat.isSquare_intCast_iff.mp hsq
  have hzx : (z : ℚ) ^ 2 = x ^ 2 := by rw [hx2, hz]; push_cast; ring
  have hxpos : 0 < x := by exact_mod_cast hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hzx with h | h
  · refine ⟨z, ?_, by rw [← h]; norm_cast⟩
    have : (0 : ℚ) < z := h ▸ hxpos
    exact_mod_cast this
  · have hx' : x = ((-z : ℤ) : ℚ) := by push_cast; linarith
    refine ⟨-z, ?_, by rw [hx']; norm_cast⟩
    have : (0 : ℚ) < -z := by linarith
    exact_mod_cast this

/-- **`prop:eqspecint` as written** (erdos-634.tex:1801), for the paper's integer-sided tile.
`D` an `N`-tiling of a target all of whose angles are `pi/3` (equilateral, side `S`) by the
`2pi/3` tile of sides `(a,b,c)` (integers, as the paper normalizes; `alpha` not in `Q pi` as
for `cor:int`).  Then there are integers `s, t, q` with `s = 3S/(c+a-b)`, `t = 3S/(c+b-a)`,
`q = 2S(a+b)/(ab)`, `s, t, q >= 1`, `s = t = N (mod 2)`, and the identities `st = 3N`,
`(t-s)^2 + 16N = q^2`.  (The final clause "primitivity then pins the scale, hence S" is not a
statement about a fixed tiling and is not formalized here.) -/
theorem eqspecint_paper {N : ℕ} (D : CongruentDissection N) {α a b c S : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoPiThreeData α a b c)
    (hint : ∃ a' b' c' : ℤ, (a' : ℝ) = a ∧ (b' : ℝ) = b ∧ (c' : ℝ) = c)
    (hP : ∀ k, D.target.angleAt k = Real.pi / 3)
    (hS : ∀ k, D.target.oppLen k = S) :
    ∃ s t q : ℤ, 1 ≤ s ∧ 1 ≤ t ∧ 1 ≤ q ∧ (2 : ℤ) ∣ s - N ∧ (2 : ℤ) ∣ t - N ∧
      (s : ℝ) = 3 * S / (c + a - b) ∧ (t : ℝ) = 3 * S / (c + b - a) ∧
      (q : ℝ) = 2 * S * (a + b) / (a * b) ∧
      S ^ 2 = N * a * b ∧ s * t = 3 * N ∧ (t - s) ^ 2 + 16 * (N : ℤ) = q ^ 2 := by
  obtain ⟨s, t, hs2, ht2, hs1, -, ht1, -, hsX, htY, harea, hst, -⟩ :=
    Row5.theoremE_twoPiThree D hα h hP
  have hS0 := hS 0
  rw [hS0] at hsX htY harea
  obtain ⟨σ, -, oa, -, ob, hγ, oc⟩ := h
  have ha0 : 0 < a := oa ▸ D.model.oppLen_pos (σ 0)
  have hb0 : 0 < b := ob ▸ D.model.oppLen_pos (σ 1)
  have hc0 : 0 < c := oc ▸ D.model.oppLen_pos (σ 2)
  have hSpos : 0 < S := hS0 ▸ D.target.oppLen_pos 0
  have hcos : c ^ 2 = a ^ 2 + a * b + b ^ 2 := by
    have hl := D.model.lawCos_perm σ
    rw [oa, ob, oc, hγ, show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
      Real.cos_pi_div_three] at hl
    linear_combination hl
  obtain ⟨hXp, hYp⟩ := X_Y_pos ha0 hb0 hc0 hcos
  have hsd : (s : ℝ) = 3 * S / (c + a - b) := by
    rw [eq_div_iff hXp.ne']; exact hsX
  have htd : (t : ℝ) = 3 * S / (c + b - a) := by
    rw [eq_div_iff hYp.ne']; exact htY
  have hNr : (N : ℝ) = S ^ 2 / (a * b) := by
    rw [eq_div_iff (mul_pos ha0 hb0).ne']; linear_combination -harea
  obtain ⟨-, -, hconic⟩ := eqspec_division_form (X := c + a - b) (Y := c + b - a) (s := (s : ℝ))
    (t := (t : ℝ)) (N := (N : ℝ)) (q := 2 * S * (a + b) / (a * b)) ha0 hb0 hc0 hSpos hcos
    rfl rfl hsd htd hNr rfl
  -- q is rational: S = s (c+a-b)/3 with integer data
  obtain ⟨a', b', c', ea, eb, ec⟩ := hint
  have hqrat : ∃ x : ℚ, (x : ℝ) = 2 * S * (a + b) / (a * b) := by
    refine ⟨2 * (((s : ℚ) * ((c' : ℚ) + a' - b')) / 3) * ((a' : ℚ) + b') / ((a' : ℚ) * b'), ?_⟩
    have hSv : S = (s : ℝ) * (c + a - b) / 3 := by linarith
    rw [hSv, ← ea, ← eb, ← ec]
    push_cast
    try ring
  have hqpos : 0 < 2 * S * (a + b) / (a * b) := by positivity
  obtain ⟨q, hq1, hqe⟩ := exists_int_of_sq_int hqpos hqrat ((t - s) ^ 2 + 16 * (N : ℤ))
    (by push_cast; linarith [hconic])
  refine ⟨s, t, q, hs1, ht1, by omega, hs2, ht2, hsd, htd, hqe, harea, hst, ?_⟩
  have : (((t - s) ^ 2 + 16 * (N : ℤ) : ℤ) : ℝ) = ((q ^ 2 : ℤ) : ℝ) := by
    push_cast
    rw [hqe]
    linarith [hconic]
  exact_mod_cast this

/-! ## Non-vacuity: `eqspecint_paper` applied to the certified `N = 1215` tiling

The real Zhang/Herdt tiling of the equilateral triangle of side `1890*135` by the `2pi/3` tile
`1890*(3,5,7)` (`G3CEqui135Control`; `alpha` irrational, integer sides, all target angles `pi/3`).
Every hypothesis of `eqspecint_paper` is discharged by existing Lean on a real dissection, and the
integers it produces are pinned: `s = 81`, `t = 45`, `q = 144`
(`45*81 = 3*1215`; `36^2 + 16*1215 = 144^2`; all of `s, t, 1215` odd). -/

open Erdos634.Draft.G3CEqui135Control in
theorem eqspecint_values_1215 : ∃ s t q : ℤ, s = 81 ∧ t = 45 ∧ q = 144 := by
  have hS : ∀ k, D.target.oppLen k = 1890 * 135 := by
    intro k
    fin_cases k
    · exact t_opp0
    · exact t_opp1
    · exact t_opp2
  obtain ⟨s, t, q, -, -, -, -, -, hsd, htd, hqd, -⟩ := eqspecint_paper D α_irr data
    ⟨5670, 9450, 13230, by norm_num, by norm_num, by norm_num⟩ t_angle hS
  have e1 : (s : ℝ) = 81 := by rw [hsd]; norm_num
  have e2 : (t : ℝ) = 45 := by rw [htd]; norm_num
  have e3 : (q : ℝ) = 144 := by rw [hqd]; norm_num
  exact ⟨s, t, q, by exact_mod_cast e1, by exact_mod_cast e2, by exact_mod_cast e3⟩

end Erdos634.Draft.FDCEqSpec

#print axioms Erdos634.Draft.FDCEqSpec.eqspec_division_form
#print axioms Erdos634.Draft.FDCEqSpec.eqspec_converse
#print axioms Erdos634.Draft.FDCEqSpec.eqspec_proportional
#print axioms Erdos634.Draft.FDCEqSpec.eqspecint_paper
#print axioms Erdos634.Draft.FDCEqSpec.eqspecint_values_1215

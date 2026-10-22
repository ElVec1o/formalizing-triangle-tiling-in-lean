-- Draft/ThmIso.lean — Partial formalization toward `thmIso : ThmIsoStatement` (C10, thm:iso).
-- This file proves three sub-lemmas (det formula for the model, det formula for the base-α target,
-- and the area identity N·b = μ²·(a+2b)) using ZERO sorry, ZERO native_decide.
-- Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04). Formalization debt; NOT /goal progress.
--
-- REMAINING GAP to complete `thmIso`:
--   The area identity N·b = μ²·(a+2b) is proved here. To complete the proof one still needs:
--   (1) Apply cor_int_at → Mα, Mβ ∈ ℤ; connect to lemmaCF_alpha/beta to get
--       μ·(c-a-b) = ±Mα·b (integer) and μ·(c+a+b) = ±Mβ·b (integer).
--   (2) Apply tile_rational (with the area identity as the "N·b²" input) to get a/b, c/b ∈ ℚ.
--   (3) Construct integer triple (a₀,b₀,c₀) from the rational outputs q_a = a/b, q_c = c/b
--       by setting b₀ = q_a.den * q_c.den, a₀ = q_a.num * q_c.den, c₀ = q_c.num * q_a.den.
--   (4) Show the integer triple satisfies all hypotheses of iso_arith_core and invoke it.
--   The integer-triple construction (step 3) is the hard part; it requires working with
--   Rat.num / Rat.den and showing the resulting integers satisfy c₀²=a₀²+a₀b₀+b₀², IsCoprime a₀ c₀,
--   IsCoprime b₀ (a₀+2b₀), and N·b₀ = k²·(a₀+2b₀), all in ℤ.
import Erdos634.Draft.FluxE2Pi3Row9
import Erdos634.Draft.FluxCRow5
import Erdos634.Draft.FluxCRow2

open scoped Classical

namespace Erdos634.Draft.ThmIso

open Erdos634.Geometry Erdos634.AreaDet

/-! ## Auxiliary: law-of-cosines derivation of c² = a²+ab+b² -/

/-- For a 2π/3 tile, the law of cosines at the 2π/3 vertex gives c² = a²+ab+b². -/
private lemma twoPiThree_c_sq {α a b c : ℝ} (T : Tri) (h : T.TwoPiThreeData α a b c) :
    c ^ 2 = a ^ 2 + a * b + b ^ 2 := by
  obtain ⟨σ, -, ha, -, hb, hγ, hc⟩ := h
  have hlc := T.lawCos_perm σ
  rw [ha, hb, hc, hγ,
      show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three] at hlc
  linarith

/-! ## Lemma 1: det formula for the 2π/3 model -/

/-- `4 · det(model)² = 3 · a² · b²` for a `TwoPiThreeData` triangle. -/
theorem model_four_det_sq {α a b c : ℝ} (T : Tri) (h : T.TwoPiThreeData α a b c) :
    4 * Erdos634.AreaDet.detTri T ^ 2 = 3 * a ^ 2 * b ^ 2 := by
  have hc2 := twoPiThree_c_sq T h
  obtain ⟨σ, -, ha, -, hb, -, hc⟩ := h
  have hM := T.four_detTri_sq_sym
  rw [T.sum_perm 2 σ, T.sum_perm 4 σ, ha, hb, hc] at hM
  -- hM : 4*det² = (a²+b²+c²)² - 2*(a⁴+b⁴+c⁴)
  -- Identity: (a²+b²+c²)² - 2(a⁴+b⁴+c⁴) - 3a²b² = (a²-ab+b²-c²)*(c²-a²-ab-b²)
  linear_combination hM + (a ^ 2 - a * b + b ^ 2 - c ^ 2) * hc2

/-! ## Lemma 2: det formula for the base-α target -/

/-- `4 · det(target)² = 3 · μ⁴ · a² · (a+2b)²` for a `BaseAlphaData` triangle,
given `c² = a²+ab+b²`. -/
theorem target_four_det_sq {α a b c μ : ℝ} (T : Tri) (h : T.BaseAlphaData α a b c μ)
    (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    4 * Erdos634.AreaDet.detTri T ^ 2 = 3 * μ ^ 4 * a ^ 2 * (a + 2 * b) ^ 2 := by
  obtain ⟨-, hgrid⟩ := h
  obtain ⟨σ, -, o0, -, o1, -, o2⟩ := hgrid
  have hM := T.four_detTri_sq_sym
  rw [T.sum_perm 2 σ, T.sum_perm 4 σ, o0, o1, o2] at hM
  -- hM : 4*det² = ((μc)²+(μc)²+(μ(a+2b))²)² - 2*((μc)⁴+(μc)⁴+(μ(a+2b))⁴)
  -- Identity: big_expr - 3μ⁴a²(a+2b)² = 4μ⁴(a+2b)²·(c²-a²-ab-b²)
  linear_combination hM + 4 * μ ^ 4 * (a + 2 * b) ^ 2 * hc2

/-! ## Lemma 3: area identity N·b = μ²·(a+2b) -/

/-- **Area identity for the base-α case**: `N · b = μ² · (a + 2b)`.
Proof: combine abs_detTri_target with the two det formulas. -/
theorem base_alpha_area_identity {N : ℕ} (D : CongruentDissection N) {α a b c μ : ℝ}
    (hm : D.model.TwoPiThreeData α a b c)
    (ht : D.target.BaseAlphaData α a b c μ)
    (ha : 0 < a) (hb : 0 < b) (hμ : 0 < μ) :
    (N : ℝ) * b = μ ^ 2 * (a + 2 * b) := by
  have hc2 := twoPiThree_c_sq D.model hm
  have hdet := D.abs_detTri_target
  -- det-square identity: det(target)² = N² · det(model)²
  have hdet_sq : Erdos634.AreaDet.detTri D.target ^ 2
      = (N : ℝ) ^ 2 * Erdos634.AreaDet.detTri D.model ^ 2 := by
    have h := congrArg (fun x : ℝ => x ^ 2) hdet
    simp only [mul_pow, sq_abs] at h
    exact h
  have hmod_det := model_four_det_sq D.model hm
  have htgt_det := target_four_det_sq D.target ht hc2
  -- Algebraic combination via linear_combination: 3·μ⁴·a²·(a+2b)² = 3·N²·a²·b²
  have key : 3 * μ ^ 4 * a ^ 2 * (a + 2 * b) ^ 2 = 3 * (N : ℝ) ^ 2 * a ^ 2 * b ^ 2 := by
    linear_combination -htgt_det + (N : ℝ) ^ 2 * hmod_det + 4 * hdet_sq
  -- Cancel 3·a² to get μ⁴·(a+2b)² = N²·b²
  have hμ4_eq : μ ^ 4 * (a + 2 * b) ^ 2 = (N : ℝ) ^ 2 * b ^ 2 :=
    mul_left_cancel₀ (by positivity : (3 : ℝ) * a ^ 2 ≠ 0) (by linear_combination key)
  -- (μ²·(a+2b))² = (N·b)²
  have h_sq_eq : (μ ^ 2 * (a + 2 * b)) ^ 2 = ((N : ℝ) * b) ^ 2 := by
    have : (μ ^ 2 * (a + 2 * b)) ^ 2 = μ ^ 4 * (a + 2 * b) ^ 2 := by ring
    rw [this, hμ4_eq]; ring
  -- Conclude μ²·(a+2b) = N·b by sq_inj, then symm
  have hLpos : (0 : ℝ) ≤ μ ^ 2 * (a + 2 * b) := by positivity
  have hRpos : (0 : ℝ) ≤ (N : ℝ) * b := mul_nonneg (Nat.cast_nonneg N) hb.le
  exact ((pow_left_inj₀ hLpos hRpos two_ne_zero).mp h_sq_eq).symm

/-! ## What remains for `thmIso` (see file header) -/
-- No `theorem thmIso` in this file; the integer-bridge construction (step 3 above) is the blocker.
-- Filed as formalization debt. The three lemmas above are the new Lean contribution.

end Erdos634.Draft.ThmIso

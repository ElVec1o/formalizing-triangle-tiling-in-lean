-- Draft/FluxPaperCorIntAnchored.lean — `cor:int` (paper/erdos-634.tex, label `cor:int`) in the
-- paper's own ANCHORED form, closing the two discrepancies D1, D2 of the statement-match audit
-- (private working notes, not included)  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
--
-- * D1 (frame).  The paper fixes the direction grid `G = {θ₀ + jπ/3 + kα}` with the reference `θ₀`
--   along an edge of one tile, and `f_α = (−1)^j`, `f_β = (−1)^{j+k}` on it.  `fAlpha`/`fBeta`
--   (FluxPaper.lean) hard-code anchor `0`.  Here `fAlphaAt α hα θ₀`, `fBetaAt α hα θ₀` take the
--   anchor as an argument (`GridChar.rankn` already does); on `G` they ARE the paper's `f_α`, `f_β`
--   (`fAlphaAt_weight_on_grid`, `fBetaAt_weight_on_grid`).  `cor_int_at` holds for EVERY anchor;
--   `Paper.cor_int_anchored` specialises it to `θ₀` = the direction of edge `k` of tile `i`
--   (traversed with the tile on the left), i.e. the paper's choice, for any `i`, `k`.
--   No sign-transport lemma is needed: the proof runs directly in the anchored frame.
-- * D2 (quotient).  `c + a − b > 0`, `c + b − a > 0` (`TwoPiThreeData.pos_caMb/pos_cbMa`, strict
--   triangle inequality), and the statement is `M_α = Φ_{f_α}/(c+a−b)` with `M_α ∈ ℤ`.
--
-- Reuses FluxPaper.lean / FluxValue.lean (`target_flux_signs`, `rankn_mem`, `rankn_chi`,
-- `rankn_sq`, `val_of_mem_anchor`) and FluxRow2.lean (`Tri.strict_triangle'`).  The two lemmas
-- `data_angles_mem_at` and `data_tileValue_at` are the anchor-general restatements of
-- `Tri.data_angles_mem` / `data_tileValue` (whose statements fix anchor `0`); proofs are the same.
--
-- Formalization debt; not progress on the three /goal outcomes.
import Erdos634.Draft.FluxPaper
import Erdos634.Draft.FluxRow2
import Erdos634.Draft.FluxPaperWitness

open scoped Classical

namespace Erdos634.Geometry

/-! ## The paper's anchored `f_α`, `f_β` -/

/-- **The paper's `f_α` in the frame with reference `θ₀`**: `(−1)^j` on `θ₀ + jπ/3 + kα`. -/
noncomputable def fAlphaAt (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (θ₀ : Real.Angle) :
    GridChar ℝ :=
  GridChar.rankn 3 (by norm_num) (by decide) α hα 0 θ₀

/-- **The paper's `f_β` in the frame with reference `θ₀`**: `(−1)^(j+k)` on `θ₀ + jπ/3 + kα`. -/
noncomputable def fBetaAt (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (θ₀ : Real.Angle) :
    GridChar ℝ :=
  GridChar.rankn 3 (by norm_num) (by decide) α hα 1 θ₀

theorem fAlphaAt_zero (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) :
    fAlphaAt α hα 0 = fAlpha α hα := rfl

theorem fBetaAt_zero (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) :
    fBetaAt α hα 0 = fBeta α hα := rfl

/-- **On the anchored grid, `fAlphaAt θ₀` is the paper's `f_α = (−1)^j`.** -/
theorem fAlphaAt_weight_on_grid (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (θ₀ : Real.Angle) (d : Dir) (j k : ℤ)
    (hd : d.angle = θ₀ + (((j : ℝ) * (Real.pi / 3) + (k : ℝ) * α : ℝ) : Real.Angle)) :
    (fAlphaAt α hα θ₀).weight d = if (j : ZMod 2) = 0 then 1 else -1 := by
  unfold GridChar.weight
  have hmem := GridChar.rankn_mem 3 (by norm_num) (by decide) α hα 0 θ₀ j k
  rw [← grid_form] at hmem
  have hsub : d.angle - (fAlphaAt α hα θ₀).anchor
      = (((j : ℝ) * (Real.pi / 3) + (k : ℝ) * α : ℝ) : Real.Angle) := by
    rw [hd]; show θ₀ + _ - θ₀ = _; abel
  rw [GridChar.val_of_mem_anchor _ (by rw [hsub]; exact hmem), hsub, grid_form]
  unfold fAlphaAt
  rw [GridChar.rankn_chi]
  simp

/-- **On the anchored grid, `fBetaAt θ₀` is the paper's `f_β = (−1)^(j+k)`.** -/
theorem fBetaAt_weight_on_grid (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (θ₀ : Real.Angle) (d : Dir) (j k : ℤ)
    (hd : d.angle = θ₀ + (((j : ℝ) * (Real.pi / 3) + (k : ℝ) * α : ℝ) : Real.Angle)) :
    (fBetaAt α hα θ₀).weight d = if (j : ZMod 2) + (k : ZMod 2) = 0 then 1 else -1 := by
  unfold GridChar.weight
  have hmem := GridChar.rankn_mem 3 (by norm_num) (by decide) α hα 1 θ₀ j k
  rw [← grid_form] at hmem
  have hsub : d.angle - (fBetaAt α hα θ₀).anchor
      = (((j : ℝ) * (Real.pi / 3) + (k : ℝ) * α : ℝ) : Real.Angle) := by
    rw [hd]; show θ₀ + _ - θ₀ = _; abel
  rw [GridChar.val_of_mem_anchor _ (by rw [hsub]; exact hmem), hsub, grid_form]
  unfold fBetaAt
  rw [GridChar.rankn_chi]
  simp

/-! ## Anchor-general tile data -/

theorem Tri.data_angles_mem_at {T : Tri} {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : T.TwoPiThreeData α a b c) (b' : ZMod 2) (θ₀ : Real.Angle) :
    ∀ j, ((T.angleAt j : ℝ) : Real.Angle)
      ∈ (GridChar.rankn 3 (by norm_num) (by decide) α hα b' θ₀).L := by
  obtain ⟨σ, h0, -, h1, -, h2, -⟩ := h
  intro j
  obtain ⟨k, rfl⟩ := σ.surjective j
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
  rcases hk with rfl | rfl | rfl
  · rw [h0, show ((α : ℝ) : Real.Angle)
        = ((((0 : ℤ) : ℝ) * (Real.pi / ((3 : ℕ) : ℝ)) + ((1 : ℤ) : ℝ) * α : ℝ) : Real.Angle) by
          congr 1; push_cast; ring]
    exact GridChar.rankn_mem _ _ _ _ _ _ _ _ _
  · rw [h1, show ((Real.pi / 3 - α : ℝ) : Real.Angle)
        = ((((1 : ℤ) : ℝ) * (Real.pi / ((3 : ℕ) : ℝ)) + ((-1 : ℤ) : ℝ) * α : ℝ) : Real.Angle) by
          congr 1; push_cast; ring]
    exact GridChar.rankn_mem _ _ _ _ _ _ _ _ _
  · rw [h2, show ((2 * Real.pi / 3 : ℝ) : Real.Angle)
        = ((((2 : ℤ) : ℝ) * (Real.pi / ((3 : ℕ) : ℝ)) + ((0 : ℤ) : ℝ) * α : ℝ) : Real.Angle) by
          congr 1; push_cast; ring]
    exact GridChar.rankn_mem _ _ _ _ _ _ _ _ _

theorem data_tileValue_at (T : Tri) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : T.TwoPiThreeData α a b c) (b' : ZMod 2) (θ₀ : Real.Angle) :
    (GridChar.rankn 3 (by norm_num) (by decide) α hα b' θ₀).tileValue T
      = (if ((3 : ℤ) : ZMod 2) + b' * ((-1 : ℤ) : ZMod 2) = 0 then 1 else -1) * a
        + (if ((2 : ℤ) : ZMod 2) + b' * ((1 : ℤ) : ZMod 2) = 0 then 1 else -1) * b
        + (if ((1 : ℤ) : ZMod 2) + b' * ((0 : ℤ) : ZMod 2) = 0 then 1 else -1) * c := by
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  unfold GridChar.tileValue
  rw [← Equiv.sum_comp σ (fun j => (GridChar.rankn 3 (by norm_num) (by decide) α hα b' θ₀).chi
    ((Real.pi - T.angleAt j : ℝ) : Real.Angle) * T.oppLen j), Fin.sum_univ_three]
  rw [h0, o0, h1, o1, h2, o2,
    show Real.pi - α = ((3 : ℤ) : ℝ) * (Real.pi / ((3 : ℕ) : ℝ)) + ((-1 : ℤ) : ℝ) * α by
      push_cast; ring,
    show Real.pi - (Real.pi / 3 - α) = ((2 : ℤ) : ℝ) * (Real.pi / ((3 : ℕ) : ℝ)) + ((1 : ℤ) : ℝ) * α by
      push_cast; ring,
    show Real.pi - 2 * Real.pi / 3 = ((1 : ℤ) : ℝ) * (Real.pi / ((3 : ℕ) : ℝ)) + ((0 : ℤ) : ℝ) * α by
      push_cast; ring,
    GridChar.rankn_chi, GridChar.rankn_chi, GridChar.rankn_chi]

theorem data_tileValue_alpha_at (T : Tri) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : T.TwoPiThreeData α a b c) (θ₀ : Real.Angle) :
    (fAlphaAt α hα θ₀).tileValue T = -(c + a - b) := by
  unfold fAlphaAt
  rw [data_tileValue_at T hα h 0 θ₀, if_neg (by decide), if_pos (by decide), if_neg (by decide)]
  ring

theorem data_tileValue_beta_at (T : Tri) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : T.TwoPiThreeData α a b c) (θ₀ : Real.Angle) :
    (fBetaAt α hα θ₀).tileValue T = -(c + b - a) := by
  unfold fBetaAt
  rw [data_tileValue_at T hα h 1 θ₀, if_pos (by decide), if_neg (by decide), if_neg (by decide)]
  ring

/-! ## D2: the denominators are positive -/

/-- Strict triangle inequality in `oppLen` form: each side is shorter than the other two. -/
theorem Tri.oppLen_lt_sum (T : Tri) (j : Fin 3) :
    T.oppLen j < T.oppLen (j + 1) + T.oppLen (j + 2) := by
  have h0 := T.strict_triangle' 0
  have h1 := T.strict_triangle' 1
  have h2 := T.strict_triangle' 2
  have c01 := dist_comm (T.pts 0) (T.pts 1)
  have c02 := dist_comm (T.pts 0) (T.pts 2)
  have c12 := dist_comm (T.pts 1) (T.pts 2)
  unfold Tri.oppLen
  fin_cases j <;> simp at h0 h1 h2 ⊢ <;> linarith

/-- The three `oppLen`s of a `TwoPiThreeData` placement are `a, b, c` at distinct indices; each is
less than the sum of the other two. -/
theorem Tri.TwoPiThreeData.tri_ineq {T : Tri} {α a b c : ℝ} (h : T.TwoPiThreeData α a b c) :
    a < b + c ∧ b < a + c ∧ c < a + b := by
  obtain ⟨σ, -, o0, -, o1, -, o2⟩ := h
  have H : ∀ j, T.oppLen j < T.oppLen (j + 1) + T.oppLen (j + 2) := T.oppLen_lt_sum
  have i01 : σ 0 ≠ σ 1 := fun e => absurd (σ.injective e) (by decide)
  have i02 : σ 0 ≠ σ 2 := fun e => absurd (σ.injective e) (by decide)
  have i12 : σ 1 ≠ σ 2 := fun e => absurd (σ.injective e) (by decide)
  subst o0 o1 o2
  generalize σ 0 = x at *
  generalize σ 1 = y at *
  generalize σ 2 = z at *
  have H0 := H 0; have H1 := H 1; have H2 := H 2
  simp only [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl,
    show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl,
    show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl] at H0 H1 H2
  refine ⟨?_, ?_, ?_⟩ <;>
    fin_cases x <;> fin_cases y <;> fin_cases z <;> simp at i01 i02 i12 ⊢ <;> linarith

theorem Tri.TwoPiThreeData.pos_caMb {T : Tri} {α a b c : ℝ} (h : T.TwoPiThreeData α a b c) :
    0 < c + a - b := by linarith [h.tri_ineq.2.1]

theorem Tri.TwoPiThreeData.pos_cbMa {T : Tri} {α a b c : ℝ} (h : T.TwoPiThreeData α a b c) :
    0 < c + b - a := by linarith [h.tri_ineq.1]

/-! ## `cor:int`, anchored, quotient form -/

/-- **`cor:int` for any reference `θ₀`, in the paper's quotient form.**  `c+a−b > 0`,
`c+b−a > 0`, and `M_α = Φ_{f_α}/(c+a−b)`, `M_β = Φ_{f_β}/(c+b−a)` are integers with
`M_α ≡ M_β ≡ N (mod 2)`, where `f_α, f_β` are taken in the frame of reference `θ₀`. -/
theorem Paper.cor_int_at {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoPiThreeData α a b c)
    (θ₀ : Real.Angle) :
    0 < c + a - b ∧ 0 < c + b - a ∧
    ∃ Mα Mβ : ℤ,
      (Mα : ℝ) = D.target.flux (fAlphaAt α hα θ₀).weight / (c + a - b) ∧
      (Mβ : ℝ) = D.target.flux (fBetaAt α hα θ₀).weight / (c + b - a) ∧
      (2 : ℤ) ∣ Mα - N ∧ (2 : ℤ) ∣ Mβ - N ∧ (2 : ℤ) ∣ Mα - Mβ := by
  have hA := h.pos_caMb
  have hB := h.pos_cbMa
  obtain ⟨S, hS2, -, hSf⟩ := D.target_flux_signs (fAlphaAt α hα θ₀)
    (GridChar.rankn_sq _ _ _ _ _ _ _) (D.model.data_angles_mem_at hα h 0 θ₀)
  obtain ⟨S', hS2', -, hSf'⟩ := D.target_flux_signs (fBetaAt α hα θ₀)
    (GridChar.rankn_sq _ _ _ _ _ _ _) (D.model.data_angles_mem_at hα h 1 θ₀)
  have p1 : (2 : ℤ) ∣ -S - N := by
    rw [show -S - (N : ℤ) = -(S - N) - 2 * N by ring]
    exact dvd_sub (dvd_neg.mpr hS2) (dvd_mul_right 2 _)
  have p2 : (2 : ℤ) ∣ -S' - N := by
    rw [show -S' - (N : ℤ) = -(S' - N) - 2 * N by ring]
    exact dvd_sub (dvd_neg.mpr hS2') (dvd_mul_right 2 _)
  refine ⟨hA, hB, -S, -S', ?_, ?_, p1, p2, ?_⟩
  · rw [hSf, data_tileValue_alpha_at D.model hα h θ₀, eq_div_iff hA.ne']; push_cast; ring
  · rw [hSf', data_tileValue_beta_at D.model hα h θ₀, eq_div_iff hB.ne']; push_cast; ring
  · rw [show -S - -S' = (-S - N) - (-S' - N) by ring]; exact dvd_sub p1 p2

/-- **`cor:int` AS WRITTEN (paper, erdos-634.tex, label `cor:int`).**  The reference of the
direction grid is fixed along an edge of one tile: `θ₀` is the direction of edge `k` of tile `i`
(any `i`, `k`).  Then `c + a − b ≠ 0`, `c + b − a ≠ 0`, and `M_α = Φ_{f_α}(∂ABC)/(c+a−b)`,
`M_β = Φ_{f_β}(∂ABC)/(c+b−a)` are integers with `M_α ≡ M_β ≡ N (mod 2)`. -/
theorem Paper.cor_int_anchored {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoPiThreeData α a b c)
    (i : Fin N) (k : Fin 3) :
    c + a - b ≠ 0 ∧ c + b - a ≠ 0 ∧
    ∃ Mα Mβ : ℤ,
      (Mα : ℝ) = D.target.flux (fAlphaAt α hα ((D.tile i).leftUnit k).angle).weight / (c + a - b) ∧
      (Mβ : ℝ) = D.target.flux (fBetaAt α hα ((D.tile i).leftUnit k).angle).weight / (c + b - a) ∧
      (2 : ℤ) ∣ Mα - N ∧ (2 : ℤ) ∣ Mβ - N ∧ (2 : ℤ) ∣ Mα - Mβ := by
  obtain ⟨hA, hB, rest⟩ := Paper.cor_int_at D hα h ((D.tile i).leftUnit k).angle
  exact ⟨hA.ne', hB.ne', rest⟩

/-- In the anchored frame the reference edge itself has weight `1` (`j = k = 0`), so the weight
is the paper's normalisation, not merely `±` it. -/
theorem fAlphaAt_reference (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (d : Dir) :
    (fAlphaAt α hα d.angle).weight d = 1 := by
  rw [fAlphaAt_weight_on_grid α hα d.angle d 0 0 (by push_cast; simp)]
  simp

end Erdos634.Geometry

/-! ## Non-vacuity witness on `D357` -/

namespace Erdos634.Draft.FluxPaperWitness

open Erdos634.Geometry

/-- **`cor:int` as written, instantiated on the real `CongruentDissection 4` `D357`**, reference
along edge `0` of tile `0`: every hypothesis is realised. -/
theorem cor_int_anchored_357 :
    (7 : ℝ) + 3 - 5 ≠ 0 ∧ (7 : ℝ) + 5 - 3 ≠ 0 ∧
    ∃ Mα Mβ : ℤ,
      (Mα : ℝ) = D357.target.flux
        (fAlphaAt α357 α357_irr ((D357.tile 0).leftUnit 0).angle).weight / (7 + 3 - 5) ∧
      (Mβ : ℝ) = D357.target.flux
        (fBetaAt α357 α357_irr ((D357.tile 0).leftUnit 0).angle).weight / (7 + 5 - 3) ∧
      (2 : ℤ) ∣ Mα - ((2 * 2 : ℕ) : ℤ) ∧ (2 : ℤ) ∣ Mβ - ((2 * 2 : ℕ) : ℤ) ∧ (2 : ℤ) ∣ Mα - Mβ :=
  Paper.cor_int_anchored D357 α357_irr data357 0 0

end Erdos634.Draft.FluxPaperWitness

#print axioms Erdos634.Geometry.Paper.cor_int_at
#print axioms Erdos634.Geometry.Paper.cor_int_anchored
#print axioms Erdos634.Geometry.fAlphaAt_weight_on_grid
#print axioms Erdos634.Geometry.fBetaAt_weight_on_grid
#print axioms Erdos634.Geometry.Tri.TwoPiThreeData.tri_ineq
#print axioms Erdos634.Draft.FluxPaperWitness.cor_int_anchored_357

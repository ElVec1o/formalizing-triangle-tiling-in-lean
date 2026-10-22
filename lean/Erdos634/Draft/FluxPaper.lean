-- Draft/FluxPaper.lean — layer 2, part 5: the paper's own grid `G = {jπ/3 + kα}` and the paper's
-- statements `lem:value` and `cor:int` (erdos-634.tex:1096, 1123) for a `2π/3` tile, as instances
-- of the general-grid theorems of Draft/FluxValue.lean.  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
-- Design: (private working notes, not included) §3.6 (`FluxGrids.lean`, `rank2 3 α`), §4.2 row "Paper".
--
-- Statement-match notes (for a later VERIFIED audit — NOT claimed here):
-- * The paper's `f_α(jπ/3 + kα) = (−1)^j` is defined on the grid only.  `fAlpha` is the
--   coset-representative extension with anchor `0`; on the grid it IS the paper's `f_α`
--   (`fAlpha_weight_on_grid`, `fBeta_weight_on_grid`).  Off the grid the paper's `C_f` is undefined;
--   here every placement, in any coset, still has `C = ±(c+a−b)`.
-- * The paper's `cor:int` says `M_α = Φ/(c+a−b) ∈ ℤ`, `M_α ≡ N (mod 2)`; stated here as
--   `Φ = M_α·(c+a−b)` with `M_α ≡ N`, equivalent since `c + a − b > 0` for a triangle.
-- * "Placement of T" is a `Tri` carrying the tile's angle/side data under some vertex order
--   (`Tri.TwoPiThreeData`); reflections are included (either orientation).
--
-- Formalization debt; not progress on the three /goal outcomes.
import Erdos634.Draft.FluxGrids
import Erdos634.Draft.FluxValue

open scoped Classical

namespace Erdos634.Geometry

/-! ## The grid `ℤ·(π/n) + ℤ·θ`, `n` odd -/

/-- `(j, k) ↦ j·(π/n) + k·θ`. -/
noncomputable def rankMap (n : ℕ) (θ : ℝ) : ℤ × ℤ →+ Real.Angle where
  toFun p := p.1 • ((Real.pi / n : ℝ) : Real.Angle) + p.2 • ((θ : ℝ) : Real.Angle)
  map_zero' := by simp
  map_add' := by
    intro p q
    simp only [Prod.fst_add, Prod.snd_add, add_zsmul]
    abel

theorem rankMap_apply (n : ℕ) (θ : ℝ) (j k : ℤ) :
    rankMap n θ (j, k) = (((j : ℝ) * (Real.pi / n) + (k : ℝ) * θ : ℝ) : Real.Angle) := by
  show j • ((Real.pi / n : ℝ) : Real.Angle) + k • ((θ : ℝ) : Real.Angle) = _
  rw [Real.Angle.coe_add, ← Real.Angle.coe_zsmul, ← Real.Angle.coe_zsmul, zsmul_eq_mul,
    zsmul_eq_mul]

/-- The kernel condition: `j·(π/n) + kθ ∈ 2πℤ` with `θ ∉ ℚπ` forces `k = 0`, `2n ∣ j`. -/
theorem rankn_ker (n : ℕ) (hn : 0 < n) (θ : ℝ) (hθ : ¬ ∃ r : ℚ, θ = (r : ℝ) * Real.pi)
    (b : ZMod 2) (p : ℤ × ℤ) (hp : rankMap n θ p = 0) : rank2Par b p = 0 := by
  obtain ⟨j, k⟩ := p
  rw [rankMap_apply, Real.Angle.coe_eq_zero_iff] at hp
  obtain ⟨m, hm⟩ := hp
  rw [zsmul_eq_mul] at hm
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have e : (j : ℝ) * (Real.pi / n) * n = j * Real.pi := by field_simp
  by_cases hk : k = 0
  · have hk0 : (k : ℝ) = 0 := by exact_mod_cast hk
    have h2 : ((j : ℝ) - 2 * m * n) * Real.pi = 0 := by
      linear_combination (-(n : ℝ)) * hm - e - (θ * n) * hk0
    have h3 : (j : ℝ) - 2 * m * n = 0 := (mul_eq_zero.mp h2).resolve_right Real.pi_ne_zero
    have hj : j = 2 * (m * n) := by
      have h4 : (j : ℝ) = ((2 * (m * n) : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast h4
    show (j : ZMod 2) + b * (k : ZMod 2) = 0
    rw [hj, hk]
    push_cast
    have h20 : (2 : ZMod 2) = 0 := by decide
    rw [h20]
    ring
  · exfalso
    apply hθ
    have hk' : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
    have h1 : (k : ℝ) * n * θ = (2 * m * n - j) * Real.pi := by
      linear_combination (-(n : ℝ)) * hm - e
    refine ⟨((2 * m * n - j : ℤ) : ℚ) / ((n * k : ℤ) : ℚ), ?_⟩
    push_cast
    rw [div_mul_eq_mul_div, eq_div_iff (mul_ne_zero hn' hk')]
    linear_combination h1

/-- **The grid character on `ℤ·(π/n) + ℤ·θ`**, `ψ(j·π/n + kθ) = (−1)^(j + b k)`, `n` odd. -/
noncomputable def GridChar.rankn (n : ℕ) (hn : 0 < n) (hodd : (n : ZMod 2) = 1) (θ : ℝ)
    (hθ : ¬ ∃ r : ℚ, θ = (r : ℝ) * Real.pi) (b : ZMod 2) (anchor : Real.Angle) : GridChar ℝ :=
  GridChar.ofHom (rankMap n θ) (rank2Par b) (rankn_ker n hn θ hθ b) ((n : ℤ), 0)
    (by
      rw [rankMap_apply]
      congr 1
      have hn' : (n : ℝ) ≠ 0 := by positivity
      push_cast
      field_simp
      ring)
    (by
      show (((n : ℤ)) : ZMod 2) + b * ((0 : ℤ) : ZMod 2) = 1
      push_cast
      rw [hodd]
      ring)
    anchor

theorem GridChar.rankn_mem (n : ℕ) (hn : 0 < n) (hodd : (n : ZMod 2) = 1) (θ : ℝ)
    (hθ : ¬ ∃ r : ℚ, θ = (r : ℝ) * Real.pi) (b : ZMod 2) (anchor : Real.Angle) (j k : ℤ) :
    (((j : ℝ) * (Real.pi / n) + (k : ℝ) * θ : ℝ) : Real.Angle)
      ∈ (GridChar.rankn n hn hodd θ hθ b anchor).L := by
  rw [← rankMap_apply]
  exact AddMonoidHom.mem_range.mpr ⟨(j, k), rfl⟩

theorem GridChar.rankn_chi (n : ℕ) (hn : 0 < n) (hodd : (n : ZMod 2) = 1) (θ : ℝ)
    (hθ : ¬ ∃ r : ℚ, θ = (r : ℝ) * Real.pi) (b : ZMod 2) (anchor : Real.Angle) (j k : ℤ) :
    (GridChar.rankn n hn hodd θ hθ b anchor).chi
        (((j : ℝ) * (Real.pi / n) + (k : ℝ) * θ : ℝ) : Real.Angle)
      = if (j : ZMod 2) + b * (k : ZMod 2) = 0 then 1 else -1 := by
  rw [← rankMap_apply]
  exact GridChar.ofHom_chi _ _ _ _ _ _ _ (j, k)

theorem GridChar.rankn_sq (n : ℕ) (hn : 0 < n) (hodd : (n : ZMod 2) = 1) (θ : ℝ)
    (hθ : ¬ ∃ r : ℚ, θ = (r : ℝ) * Real.pi) (b : ZMod 2) (anchor : Real.Angle) :
    ∀ l ∈ (GridChar.rankn n hn hodd θ hθ b anchor).L,
      (GridChar.rankn n hn hodd θ hθ b anchor).chi l
        * (GridChar.rankn n hn hodd θ hθ b anchor).chi l = 1 :=
  GridChar.ofHom_sq _ _ _ _ _ _ _

/-- On the anchor's coset the weight is the character itself. -/
theorem GridChar.val_of_mem_anchor {R : Type*} [CommRing R] (G : GridChar R) {θ : Real.Angle}
    (h : θ - G.anchor ∈ G.L) : G.val θ = G.chi (θ - G.anchor) := by
  unfold GridChar.val GridChar.rep
  rw [if_pos h]

/-! ## The paper's `f_α`, `f_β` -/

/-- **The paper's `f_α`**: `(−1)^j` on `jπ/3 + kα`, extended off the grid by coset representatives
(anchor `0`). -/
noncomputable def fAlpha (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) : GridChar ℝ :=
  GridChar.rankn 3 (by norm_num) (by decide) α hα 0 0

/-- **The paper's `f_β`**: `(−1)^(j+k)` on `jπ/3 + kα` (`= (−1)^{j'}` for `j'π/3 + k'β`,
`β = π/3 − α`). -/
noncomputable def fBeta (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) : GridChar ℝ :=
  GridChar.rankn 3 (by norm_num) (by decide) α hα 1 0

theorem grid_form (α : ℝ) (j k : ℤ) :
    ((j : ℝ) * (Real.pi / 3) + (k : ℝ) * α) = ((j : ℝ) * (Real.pi / ((3 : ℕ) : ℝ)) + (k : ℝ) * α) := by
  push_cast; ring

/-- **On the grid, `fAlpha` is the paper's `f_α = (−1)^j`.** -/
theorem fAlpha_weight_on_grid (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (d : Dir) (j k : ℤ)
    (hd : d.angle = (((j : ℝ) * (Real.pi / 3) + (k : ℝ) * α : ℝ) : Real.Angle)) :
    (fAlpha α hα).weight d = if (j : ZMod 2) = 0 then 1 else -1 := by
  unfold GridChar.weight
  rw [hd, grid_form]
  have hmem := GridChar.rankn_mem 3 (by norm_num) (by decide) α hα 0 0 j k
  rw [GridChar.val_of_mem_anchor _ (by show _ - (0 : Real.Angle) ∈ _; rw [sub_zero]; exact hmem)]
  show (fAlpha α hα).chi (_ - (0 : Real.Angle)) = _
  rw [sub_zero]
  unfold fAlpha
  rw [GridChar.rankn_chi]
  simp

/-- **On the grid, `fBeta` is the paper's `f_β = (−1)^(j+k)`.** -/
theorem fBeta_weight_on_grid (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (d : Dir) (j k : ℤ)
    (hd : d.angle = (((j : ℝ) * (Real.pi / 3) + (k : ℝ) * α : ℝ) : Real.Angle)) :
    (fBeta α hα).weight d = if (j : ZMod 2) + (k : ZMod 2) = 0 then 1 else -1 := by
  unfold GridChar.weight
  rw [hd, grid_form]
  have hmem := GridChar.rankn_mem 3 (by norm_num) (by decide) α hα 1 0 j k
  rw [GridChar.val_of_mem_anchor _ (by show _ - (0 : Real.Angle) ∈ _; rw [sub_zero]; exact hmem)]
  show (fBeta α hα).chi (_ - (0 : Real.Angle)) = _
  rw [sub_zero]
  unfold fBeta
  rw [GridChar.rankn_chi]
  simp

/-! ## A placement of the `2π/3` tile -/

/-- **A placement of the paper's tile**: under some vertex order, angles `(α, π/3 − α, 2π/3)`
with opposite sides `(a, b, c)`. -/
def Tri.TwoPiThreeData (T : Tri) (α a b c : ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3),
    T.angleAt (σ 0) = α ∧ T.oppLen (σ 0) = a ∧
    T.angleAt (σ 1) = Real.pi / 3 - α ∧ T.oppLen (σ 1) = b ∧
    T.angleAt (σ 2) = 2 * Real.pi / 3 ∧ T.oppLen (σ 2) = c

theorem Tri.data_angles_mem {T : Tri} {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : T.TwoPiThreeData α a b c) (b' : ZMod 2) :
    ∀ j, ((T.angleAt j : ℝ) : Real.Angle)
      ∈ (GridChar.rankn 3 (by norm_num) (by decide) α hα b' 0).L := by
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

/-- The three exterior angles on the grid: `π − α = 3·π/3 − α`, `π − (π/3 − α) = 2·π/3 + α`,
`π − 2π/3 = 1·π/3`. -/
theorem data_tileValue (T : Tri) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : T.TwoPiThreeData α a b c) (b' : ZMod 2) :
    (GridChar.rankn 3 (by norm_num) (by decide) α hα b' 0).tileValue T
      = (if ((3 : ℤ) : ZMod 2) + b' * ((-1 : ℤ) : ZMod 2) = 0 then 1 else -1) * a
        + (if ((2 : ℤ) : ZMod 2) + b' * ((1 : ℤ) : ZMod 2) = 0 then 1 else -1) * b
        + (if ((1 : ℤ) : ZMod 2) + b' * ((0 : ℤ) : ZMod 2) = 0 then 1 else -1) * c := by
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  unfold GridChar.tileValue
  rw [← Equiv.sum_comp σ (fun j => (GridChar.rankn 3 (by norm_num) (by decide) α hα b' 0).chi
    ((Real.pi - T.angleAt j : ℝ) : Real.Angle) * T.oppLen j), Fin.sum_univ_three]
  rw [h0, o0, h1, o1, h2, o2,
    show Real.pi - α = ((3 : ℤ) : ℝ) * (Real.pi / ((3 : ℕ) : ℝ)) + ((-1 : ℤ) : ℝ) * α by
      push_cast; ring,
    show Real.pi - (Real.pi / 3 - α) = ((2 : ℤ) : ℝ) * (Real.pi / ((3 : ℕ) : ℝ)) + ((1 : ℤ) : ℝ) * α by
      push_cast; ring,
    show Real.pi - 2 * Real.pi / 3 = ((1 : ℤ) : ℝ) * (Real.pi / ((3 : ℕ) : ℝ)) + ((0 : ℤ) : ℝ) * α by
      push_cast; ring,
    GridChar.rankn_chi, GridChar.rankn_chi, GridChar.rankn_chi]

theorem data_tileValue_alpha (T : Tri) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : T.TwoPiThreeData α a b c) : (fAlpha α hα).tileValue T = -(c + a - b) := by
  unfold fAlpha
  rw [data_tileValue T hα h 0, if_neg (by decide), if_pos (by decide), if_neg (by decide)]
  ring

theorem data_tileValue_beta (T : Tri) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : T.TwoPiThreeData α a b c) : (fBeta α hα).tileValue T = -(c + b - a) := by
  unfold fBeta
  rw [data_tileValue T hα h 1, if_pos (by decide), if_neg (by decide), if_neg (by decide)]
  ring

/-- **`lem:value` (paper, erdos-634.tex:1096), `f_α` half.**  Every placement of a `2π/3` tile
with `α ∉ ℚπ` — either orientation — has `C_{f_α} = ±(c + a − b)`. -/
theorem Paper.lem_value_alpha (T : Tri) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : T.TwoPiThreeData α a b c) :
    T.flux (fAlpha α hα).weight = c + a - b ∨ T.flux (fAlpha α hα).weight = -(c + a - b) := by
  rcases T.flux_grid_pm (fAlpha α hα) (GridChar.rankn_sq _ _ _ _ _ _ _) (T.data_angles_mem hα h 0)
    with h1 | h1
  · right; rw [h1, data_tileValue_alpha T hα h]
  · left; rw [h1, data_tileValue_alpha T hα h, neg_neg]

/-- **`lem:value`, `f_β` half: `C_{f_β} = ±(c + b − a)`.** -/
theorem Paper.lem_value_beta (T : Tri) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : T.TwoPiThreeData α a b c) :
    T.flux (fBeta α hα).weight = c + b - a ∨ T.flux (fBeta α hα).weight = -(c + b - a) := by
  rcases T.flux_grid_pm (fBeta α hα) (GridChar.rankn_sq _ _ _ _ _ _ _) (T.data_angles_mem hα h 1)
    with h1 | h1
  · right; rw [h1, data_tileValue_beta T hα h]
  · left; rw [h1, data_tileValue_beta T hα h, neg_neg]

/-- **`cor:int` (paper, erdos-634.tex:1123).**  For an `N`-tiling by a `2π/3` tile with
`α ∉ ℚπ`: `Φ_{f_α}(∂ABC) = M_α (c+a−b)`, `Φ_{f_β}(∂ABC) = M_β (c+b−a)` with integers
`M_α ≡ M_β ≡ N (mod 2)`. -/
theorem Paper.cor_int {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoPiThreeData α a b c) :
    ∃ Mα Mβ : ℤ, (2 : ℤ) ∣ Mα - N ∧ (2 : ℤ) ∣ Mβ - N ∧
      D.target.flux (fAlpha α hα).weight = (Mα : ℝ) * (c + a - b) ∧
      D.target.flux (fBeta α hα).weight = (Mβ : ℝ) * (c + b - a) := by
  obtain ⟨S, hS2, -, hSf⟩ := D.target_flux_signs (fAlpha α hα)
    (GridChar.rankn_sq _ _ _ _ _ _ _) (D.model.data_angles_mem hα h 0)
  obtain ⟨S', hS2', -, hSf'⟩ := D.target_flux_signs (fBeta α hα)
    (GridChar.rankn_sq _ _ _ _ _ _ _) (D.model.data_angles_mem hα h 1)
  refine ⟨-S, -S', ?_, ?_, ?_, ?_⟩
  · rw [show -S - (N : ℤ) = -(S - N) - 2 * N by ring]
    exact dvd_sub (dvd_neg.mpr hS2) (dvd_mul_right 2 _)
  · rw [show -S' - (N : ℤ) = -(S' - N) - 2 * N by ring]
    exact dvd_sub (dvd_neg.mpr hS2') (dvd_mul_right 2 _)
  · rw [hSf, data_tileValue_alpha D.model hα h]; push_cast; ring
  · rw [hSf', data_tileValue_beta D.model hα h]; push_cast; ring

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Paper.lem_value_alpha
#print axioms Erdos634.Geometry.Paper.lem_value_beta
#print axioms Erdos634.Geometry.Paper.cor_int
#print axioms Erdos634.Geometry.fAlpha_weight_on_grid

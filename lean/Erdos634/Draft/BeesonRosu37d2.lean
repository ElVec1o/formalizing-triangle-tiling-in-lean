import Mathlib
import Erdos634.Draft.BeesonRosu37d1

/-!
# Beeson-Rosu Theorem 37, gap (1): the corner tile counted on both sides (matching of the two end tiles)

NOTE, UNAUDITED.  Credit: Michael Beeson and Rosu (arXiv 2607.23453 v2, Theorem 37, last paragraph), Beeson, Laczkovich.
Formalization debt, not progress on the /goal outcomes.

`tile_swap`: two `SideTiling`s of the two sides `[Pb, A]`, `[Pl, A]` of the target through a vertex `A` (so `A` is the END of both lists) whose last tiles are
the SAME tile `t`, both showing the opposite side `sL = b` (angle `beta` at `A`): the `a` letter occurs in one of the two last types
(`1 <= cA t1 + cA t2`).  Pure combinatorics of the labels of one triangle: the other two vertices of `t` are the points on the two sides, matched by `seg_inter`.

`thm37_j1_of_corner`: base (swapped orientation, `A` at the right end) + leg + `hNoM` + the NAMED hypothesis `hCorner` (the two last tiles are one tile
with `sL = b`) give `False`.  `hCorner` is the one thing NOT proved (see the end of the file): it is the printed "the tile at `A` has `beta` at `A`".
-/

open scoped Classical
set_option linter.unusedVariables false

namespace Erdos634.BeesonRosu37d2

open Erdos634.Geometry Erdos634.Draft.FDBBaseBetaE1 Erdos634.Draft.SideRunG Erdos634.Draft.SideRunGA
  Erdos634.Draft.SideRun Erdos634.Draft.W2E1 Erdos634.BaseBetaTargetCoord Erdos634.TilePlacement Erdos634.Geometry.Dissection
  Erdos634.BeesonRosu37b1 Erdos634.BeesonRosu37c2 Erdos634.BeesonRosu37d1

variable {N : ℕ}

theorem fin3_a : ∀ k₁ k₂ j₂ m : Fin 3, k₂ ≠ j₂ → k₂ ≠ m → j₂ ≠ m → k₁ ≠ m → k₁ ≠ k₂ → k₁ = j₂ := by decide
theorem fin3_b : ∀ k₁ j₁ k₂ j₂ m : Fin 3, k₁ ≠ m → j₁ ≠ m → k₁ ≠ j₁ → k₂ ≠ j₂ → k₂ ≠ m → j₂ ≠ m → k₁ ≠ k₂ → k₁ = j₂ →
    j₁ = k₂ := by decide

/-- the distance between two points on the side at parameters `x`, `x + l` -/
theorem dist_on_side (P B : Plane) {x l : ℝ} (hl : 0 < l) (hd : 0 < dist P B) :
    dist (AffineMap.lineMap P B (x / dist P B)) (AffineMap.lineMap P B ((x + l) / dist P B)) = l := by
  rw [dist_lineMap_lineMap, Real.dist_eq]
  have : x / dist P B - (x + l) / dist P B = -(l / dist P B) := by field_simp; ring
  rw [this, abs_neg, abs_of_pos (div_pos hl hd)]
  field_simp

/-- the last tile of a `SideTiling` ending at `B`: two of its vertices are `B` and a point `Q ≠ B` of the side -/
theorem last_tile {D₀ : CongruentDissection N} {e f : ℝ} (he : 0 < e) (hef : e < f) {P B : Plane} (hd : 0 < dist P B) {c : ℕ} {X : ℕ → ℝ}
    {tile : ℕ → Fin N} {ty : ℕ → Ty} (h : SideTiling D₀ e f P B c X tile ty) :
    ∃ k m j : Fin 3, k ≠ m ∧ k ≠ j ∧ m ≠ j ∧
      (D₀.tile (tile (c - 1))).pts k = AffineMap.lineMap P B (X (c - 1) / dist P B) ∧ X (c - 1) < dist P B ∧
      (D₀.tile (tile (c - 1))).pts m = B ∧
      dist ((D₀.tile (tile (c - 1))).pts j) ((D₀.tile (tile (c - 1))).pts k) = (ty (c - 1)).sLG e f ∧
      dist ((D₀.tile (tile (c - 1))).pts j) ((D₀.tile (tile (c - 1))).pts m) = (ty (c - 1)).sRG e f ∧
      dist ((D₀.tile (tile (c - 1))).pts k) ((D₀.tile (tile (c - 1))).pts m) = (ty (c - 1)).lenG e f := by
  obtain ⟨hc, -, hXc, hstep, hlay⟩ := h
  have hs := hstep (c - 1) (by omega)
  rw [Nat.sub_add_cancel hc] at hs
  have hlen := Ty.lenG_pos he hef (ty (c - 1))
  obtain ⟨k, m, j, hkm, hkj, hmj, hk, hm, hjk, hjm⟩ := hlay (c - 1) (by omega)
  have hxl : (X (c - 1) + (ty (c - 1)).lenG e f) / dist P B = 1 := by
    rw [← hs, hXc]; exact div_self hd.ne'
  rw [hxl, AffineMap.lineMap_apply_one] at hm
  refine ⟨k, m, j, hkm, hkj, hmj, hk, by linarith, hm, hjk, hjm, ?_⟩
  rw [hk, hm]
  have := dist_on_side P B (x := X (c - 1)) hlen hd
  rw [hxl, AffineMap.lineMap_apply_one] at this
  exact this

/-- **the swap**: the two last tiles are the same tile `t`, both with `sL = b`: one of the two last types is `A1` or `A2` -/
theorem tile_swap {D₀ : CongruentDissection N} {e f : ℝ} (T : TileOK e f) (i l j : Fin 3) (hij : i ≠ j) (hlj : l ≠ j) (hil : i ≠ l)
    {c₁ c₂ : ℕ} {X₁ X₂ : ℕ → ℝ} {tile₁ tile₂ : ℕ → Fin N} {ty₁ ty₂ : ℕ → Ty}
    (h₁ : SideTiling D₀ e f (D₀.target.pts i) (D₀.target.pts j) c₁ X₁ tile₁ ty₁)
    (h₂ : SideTiling D₀ e f (D₀.target.pts l) (D₀.target.pts j) c₂ X₂ tile₂ ty₂)
    (hsame : tile₁ (c₁ - 1) = tile₂ (c₂ - 1))
    (hS₁ : (ty₁ (c₁ - 1)).sLG e f = f ^ 2 - e ^ 2) (hS₂ : (ty₂ (c₂ - 1)).sLG e f = f ^ 2 - e ^ 2) :
    1 ≤ (ty₁ (c₁ - 1)).cA + (ty₂ (c₂ - 1)).cA := by
  have hd₁ : 0 < dist (D₀.target.pts i) (D₀.target.pts j) := dist_pos.mpr (fun h => hij (D₀.target.indep.injective h))
  have hd₂ : 0 < dist (D₀.target.pts l) (D₀.target.pts j) := dist_pos.mpr (fun h => hlj (D₀.target.indep.injective h))
  obtain ⟨k₁, m₁, j₁, hkm₁, hkj₁, hmj₁, hk₁, hX₁, hm₁, hjk₁, hjm₁, hkm₁'⟩ := last_tile T.he T.hef hd₁ h₁
  obtain ⟨k₂, m₂, j₂, hkm₂, hkj₂, hmj₂, hk₂, hX₂, hm₂, hjk₂, hjm₂, hkm₂'⟩ := last_tile T.he T.hef hd₂ h₂
  rw [hsame] at hk₁ hm₁ hjk₁ hjm₁ hkm₁'
  have hmm : m₁ = m₂ := (D₀.tile (tile₂ (c₂ - 1))).indep.injective (hm₁.trans hm₂.symm)
  subst hmm
  have hkk : k₁ ≠ k₂ := by
    intro hkk
    subst hkk
    have := Erdos634.BeesonRosu37c4a.seg_inter D₀.target hij hlj hil (hk₁.symm.trans hk₂)
    have hdiv : X₁ (c₁ - 1) / dist (D₀.target.pts i) (D₀.target.pts j) = 1 := this
    rw [div_eq_one_iff_eq hd₁.ne'] at hdiv
    linarith
  have e1 : k₁ = j₂ := fin3_a _ _ _ _ hkj₂ hkm₂ hmj₂.symm hkm₁ hkk
  have e2 : j₁ = k₂ := fin3_b _ _ _ _ _ hkm₁ hmj₁.symm hkj₁ hkj₂ hkm₂ hmj₂.symm hkk e1
  subst e1 e2
  have hab := T.hab
  have h3 : (ty₂ (c₂ - 1)).lenG e f = (ty₁ (c₁ - 1)).sRG e f := by rw [← hjm₁, ← hkm₂']
  have h4 : (ty₁ (c₁ - 1)).lenG e f = (ty₂ (c₂ - 1)).sRG e f := by rw [← hjm₂, ← hkm₁']
  exact Erdos634.BeesonRosu37c3.swap_has_A T hS₁ hS₂ h3 h4


/-- **Theorem 37, `j = 1` (the triangle `T_1(m,k)`, sides `k^3, k^3, m(3k^2-m^2)`, tile `(km, k^2-m^2, k^2)`), from the two NAMED hypotheses**:
* `hNoM`: no mirror beside the first tile of the leg (printed hypothesis of Lemma 34, NOT derived);
* `hCorner`: the corner-tile claim, for any tile lists of the two sides ending at `A = τ 0`: their last tiles are one tile and show `beta` at `A`
  (`sL = b`).  NOT proved: it needs the unique tile at a `beta` corner (`corner_counts`), the passage `localAngle = beta` => `sL = b`, and the identification of the
  frame-independent `LaysBaseOn` data across the two normal forms.
Conclusion `False`: the base tile list (via `base_tiling`, swapped orientation `[τ 1, τ 0]`, no `a` edge, Lemma 30(D)) and the leg tile list (via `leg_tiling`,
no `a` edge) are both `a`-free, but `tile_swap` puts an `a` letter in one of the two last tiles. -/
theorem thm37_j1_of_corner (k m : ℕ) (hm : 1 ≤ m) (hmk : m < k) (hco : Nat.Coprime m k) (D₀ : CongruentDissection N)
    (τ : Equiv.Perm (Fin 3))
    (h1 : dist (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) = (k : ℝ) ^ 3)
    (h2 : dist (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) = (k : ℝ) ^ 3)
    (h3 : dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) = (m : ℝ) * (3 * (k : ℝ) ^ 2 - (m : ℝ) ^ 2))
    (hMod : HasSides D₀.model ((m : ℝ) * k) ((k : ℝ) ^ 2 - (m : ℝ) ^ 2) ((k : ℝ) ^ 2))
    (hNoM : ∀ i₀ T : Fin N, LaysBaseOn D₀ (m : ℝ) (k : ℝ) (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) i₀ Ty.C1 0 →
      ¬ MirrorBeside D₀ (m : ℝ) (k : ℝ) (D₀.target.pts (τ 2)) i₀ T)
    (hCorner : ∀ (c₁ c₂ : ℕ) (X₁ X₂ : ℕ → ℝ) (tile₁ tile₂ : ℕ → Fin N) (ty₁ ty₂ : ℕ → Ty),
      SideTiling D₀ (m : ℝ) (k : ℝ) (D₀.target.pts (τ 1)) (D₀.target.pts (τ 0)) c₁ X₁ tile₁ ty₁ →
      SideTiling D₀ (m : ℝ) (k : ℝ) (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) c₂ X₂ tile₂ ty₂ →
      tile₁ (c₁ - 1) = tile₂ (c₂ - 1) ∧ (ty₁ (c₁ - 1)).sLG (m : ℝ) (k : ℝ) = (k : ℝ) ^ 2 - (m : ℝ) ^ 2 ∧
        (ty₂ (c₂ - 1)).sLG (m : ℝ) (k : ℝ) = (k : ℝ) ^ 2 - (m : ℝ) ^ 2) : False := by
  obtain ⟨c₁, X₁, tile₁, ty₁, hb, hbc⟩ := base_tiling k m hm hmk hco D₀ ((Equiv.swap (0 : Fin 3) 1).trans τ)
    (by rw [dist_comm]; exact h2) (by rw [dist_comm]; exact h1) (by rw [dist_comm]; exact h3) hMod
  obtain ⟨c₂, X₂, tile₂, ty₂, hl, hlA, -⟩ := leg_tiling k m hm hmk hco D₀ τ h1 h2 h3 hMod hNoM
  have e0 : ((Equiv.swap (0 : Fin 3) 1).trans τ) 0 = τ 1 := by simp [Equiv.swap_apply_left]
  have e1 : ((Equiv.swap (0 : Fin 3) 1).trans τ) 1 = τ 0 := by simp [Equiv.swap_apply_right]
  rw [e0, e1] at hb
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hkR : (m : ℝ) < k := by exact_mod_cast hmk
  have T : TileOK (m : ℝ) (k : ℝ) := tileOK_of_nat hm hmk hco
  obtain ⟨hsame, hS1, hS2⟩ := hCorner c₁ c₂ X₁ X₂ tile₁ tile₂ ty₁ ty₂ hb hl
  have key := tile_swap (D₀ := D₀) T (τ 1) (τ 2) (τ 0) (fun h => absurd (τ.injective h) (by decide))
    (fun h => absurd (τ.injective h) (by decide)) (fun h => absurd (τ.injective h) (by decide)) hb hl hsame hS1 hS2
  have hc1 : 0 < c₁ := hb.1
  have hc2 : 0 < c₂ := hl.1
  have z1 := Erdos634.BeesonRosu37c4a.no_A_of_sum_zero (c := c₁) (τ := ty₁)
    (by have := congrArg Prod.fst hbc; simpa [edgeCounts] using this) (k := c₁ - 1) (by omega)
  have z2 := Erdos634.BeesonRosu37c4a.no_A_of_sum_zero (c := c₂) (τ := ty₂) (by simpa [edgeCounts] using hlA) (k := c₂ - 1) (by omega)
  omega

end Erdos634.BeesonRosu37d2

#print axioms Erdos634.BeesonRosu37d2.tile_swap
#print axioms Erdos634.BeesonRosu37d2.thm37_j1_of_corner

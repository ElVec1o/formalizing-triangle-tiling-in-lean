import Erdos634.Draft.BeesonIso4d
import Erdos634.Draft.BeesonIso3j

/-!
# Beeson, "Tilings of an isosceles triangle" (arXiv 1206.1974 v7), Lemma 11.10 (first half) for the isosceles triangle, and the witnesses on the 1125-tiling

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.1974 v7, Lemmas 11.8, 11.10; arXiv 1206.2229), Laczkovich (DCG 48 (2012), Sect. 4), Beeson-Zhang, Herdt, Zhang (the 1125-tiling).
Formalization debt, not progress on the /goal outcomes.

`beeson_l11_10_ge3`: isosceles `ABC` (base angles `alpha` at target corners `0`, `1`) `N`-tiled by a tile `(alpha, beta, 2 alpha)`, H1.  In the counterclockwise convex-polygon form `P` of the target there is
a side `j` joining the corners `0` and `1` (the base `AC`), and every walk of tiles along it has at least three steps: at least three tiles are supported by `AC`.
(`a < c` follows from `c^2 = a^2 + ab`, Lemma 11.1.)
PRINTED GAP (L11.10, second half, "at least FOUR"): the case `X = a + c` (the leg supports exactly an `a`-edge tile and a `c`-edge tile) is dismissed in the print by "the tiles at A and C both have their alpha
angles at A or C, hence their a edges do not lie on AC"; this is a statement about the BASE AC, not about the leg AB, and the tile at `B` with `beta` at `B` has an `a` edge on `AB`.  The configuration is consistent
with all the length and angle-count facts used (leg `a+c`, base `a+b+c`, `N = (k+m)/(m-k)`, e.g. `k = 3, m = 4`, `N = 7`).  So the `>= 4` half is NOT proved here.
-/

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

theorem beeson_l11_10_ge3 (D : CongruentDissection N) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : D.model.TwoAlphaData α a b c) (hA : D.target.angleAt 0 = α) (hB : D.target.angleAt 1 = α) :
    ∃ (P : ConvPoly 3) (j : Fin 3), P.carrier = D.target.carrier ∧
      (P.v j = D.target.pts 0 ∧ P.v (j + 1) = D.target.pts 1 ∨ P.v j = D.target.pts 1 ∧ P.v (j + 1) = D.target.pts 0) ∧
      ∀ L : List (Fin N × Plane × Plane), WalkT D.toRegion.toRegionDissection (toV2 (P.e j)) (P.v j) (P.v (j + 1)) L → 3 ≤ L.length := by
  have hrel0 := (Erdos634.Draft.BeesonIsoL11Geo.l11_1_4 D hα h hA hB).1
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  set C := relabel D.toRegion σ with hC
  have hAC : C.model.angleAt 0 = α := (relabel_angleAt D.toRegion σ 0).trans h0
  have hβ : C.model.angleAt 1 = Real.pi - 3 * C.model.angleAt 0 := by
    rw [hAC]; exact (relabel_angleAt D.toRegion σ 1).trans h1
  have hγ : C.model.angleAt 2 = 2 * C.model.angleAt 0 := by
    rw [hAC]; exact (relabel_angleAt D.toRegion σ 2).trans h2
  have hirr : ¬ ∃ r : ℚ, C.model.angleAt 0 = (r : ℝ) * Real.pi := by rw [hAC]; exact hα
  obtain ⟨P, hPc, τ, hPa, hPv⟩ := exists_convpoly_of_tri' D.target
  have hreg : C.region = P.carrier := hPc.symm
  haveI : HasFansC C.toRegionDissection := hasFansC_poly _ P hreg
  obtain ⟨idx, hidx, hidxA⟩ := exists_idx_both C
  have ea : slen C 0 = a := (relabel_slen D.toRegion σ 0).trans o0
  have eb : slen C 1 = b := (relabel_slen D.toRegion σ 1).trans o1
  have ec : slen C 2 = c := (relabel_slen D.toRegion σ 2).trans o2
  have hac : slen C 0 < slen C 2 := by
    have ha : 0 < a := ea ▸ slen_pos C 0
    have hb : 0 < b := eb ▸ slen_pos C 1
    have hc : 0 < c := ec ▸ slen_pos C 2
    rw [ea, ec]
    nlinarith
  -- the base side of the polygon
  have key : ∀ j : Fin 3, P.v j = D.target.pts 0 ∨ P.v j = D.target.pts 1 → P.v (j + 1) = D.target.pts 1 ∨ P.v (j + 1) = D.target.pts 0 →
      P.angle j = α → P.angle (j + 1) = α →
      ∀ L : List (Fin N × Plane × Plane), WalkT D.toRegion.toRegionDissection (toV2 (P.e j)) (P.v j) (P.v (j + 1)) L → 3 ≤ L.length := by
    intro j _ _ hj0 hj1 L W
    obtain ⟨k, rfl⟩ : ∃ k, k + 1 = j := ⟨j - 1, sub_add_cancel j 1⟩
    exact base_ge_three C P hreg idx hidx hidxA hβ hγ hirr hac k (by rw [hj0, hAC]) (by rw [hj1, hAC]) W
  have hu : τ.symm 0 ≠ τ.symm 1 := fun e => by have := τ.symm.injective e; simp at this
  have hPu : P.v (τ.symm 0) = D.target.pts 0 := by rw [hPv]; simp
  have hPw : P.v (τ.symm 1) = D.target.pts 1 := by rw [hPv]; simp
  have hAu : P.angle (τ.symm 0) = α := by rw [hPa]; simp; exact hA
  have hAw : P.angle (τ.symm 1) = α := by rw [hPa]; simp; exact hB
  have hcase : τ.symm 1 = τ.symm 0 + 1 ∨ τ.symm 0 = τ.symm 1 + 1 := by
    have h3 : ∀ x y : Fin 3, x ≠ y → y = x + 1 ∨ x = y + 1 := by
      intro x y; fin_cases x <;> fin_cases y <;> simp
    exact h3 _ _ hu
  rcases hcase with hc | hc
  · have hPw' : P.v (τ.symm 0 + 1) = D.target.pts 1 := by rw [← hc]; exact hPw
    have hAw' : P.angle (τ.symm 0 + 1) = α := by rw [← hc]; exact hAw
    exact ⟨P, τ.symm 0, hPc, Or.inl ⟨hPu, hPw'⟩, key (τ.symm 0) (Or.inl hPu) (Or.inl hPw') hAu hAw'⟩
  · have hPu' : P.v (τ.symm 1 + 1) = D.target.pts 0 := by rw [← hc]; exact hPu
    have hAu' : P.angle (τ.symm 1 + 1) = α := by rw [← hc]; exact hAu
    exact ⟨P, τ.symm 1, hPc, Or.inr ⟨hPw, hPu'⟩, key (τ.symm 1) (Or.inr hPw) (Or.inr hPu') hAw hAu'⟩

open Erdos634.Draft.G3GControl in
/-- Witness (hypotheses not vacuous): the certified 1125-tiling satisfies every hypothesis of `beeson_l11_8`, `chord_no_tile_open` (via `beeson_l11_8`) and `beeson_l11_10_ge3`:
a `CongruentDissection` of an isosceles target with base angles `alpha` (corners 0, 1) by a `TwoAlphaData` tile, H1. -/
theorem wit_1125_hyps : ∃ (N : ℕ) (D : CongruentDissection N) (α a b c : ℝ), (¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) ∧
    D.model.TwoAlphaData α a b c ∧ D.target.angleAt 0 = α ∧ D.target.angleAt 1 = α :=
  ⟨_, D, _, _, _, _, α_irr, data, t_ang0, t_ang1⟩

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.beeson_l11_10_ge3
#print axioms Erdos634.Draft.LaczFormal.RG.wit_1125_hyps

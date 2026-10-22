-- Draft/LaczFormalIVcRatWit1.lean -- cells for the RATIONAL hexagon witness of `ivc_rat_final` (Laczkovich DCG 48 (2012), Sect. 2 (vi), 8.3, Concl9):
-- the tile (1, 2, sqrt 3) (a = 1, b = 2, c = sqrt 3, gamma = pi/3, alpha = pi/6, beta = pi/2), model `rT.C.model` (= `pT0 2 (1/2) iT`);
-- `cellE g u w` = parallelogram `Par g u w` (|u|^2 = 4, |w|^2 = 1, u.w = 1) cut into two point-reflected copies of the model; `cellE_regular`.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIVcHexWit

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

/-- the tile (1, 2, sqrt 3) carried by a 2-triangle parallelogram. -/
noncomputable def rT : PolyTiling 2 4 := pTiling 2 (1 / 2) iT (by norm_num) iT_pos

/-- Any triangle `ct g u w` with `|u|^2 = 4`, `|w|^2 = 1`, `u.w = 1` is isometric to the model vertex for vertex. -/
theorem ct_isoE {g0 g1 u0 u1 w0 w1 : ℝ} (hD : u0 * w1 - u1 * w0 ≠ 0)
    (hu : u0 ^ 2 + u1 ^ 2 = 4) (hw : w0 ^ 2 + w1 ^ 2 = 1) (huw : u0 * w0 + u1 * w1 = 1) :
    ∃ f : Plane ≃ᵢ Plane, ∀ k, f ((ct g0 g1 u0 u1 w0 w1 hD).pts k) = rT.C.model.pts k := by
  have hh := iT_sq
  refine iso_of_dist3 ?_ ?_ ?_
  · show dist (mkPt (g0 + u0) (g1 + u1)) (mkPt (g0 + w0) (g1 + w1)) = dist (mkPt 2 0) (mkPt (1 / 2) iT)
    refine Erdos634.SssCongruent.dist_of_sq ?_
    rw [sqd_mk, sqd_mk]; nlinarith
  · show dist (mkPt (g0 + w0) (g1 + w1)) (mkPt g0 g1) = dist (mkPt (1 / 2) iT) (mkPt 0 0)
    refine Erdos634.SssCongruent.dist_of_sq ?_
    rw [sqd_mk, sqd_mk]; nlinarith
  · show dist (mkPt g0 g1) (mkPt (g0 + u0) (g1 + u1)) = dist (mkPt 0 0) (mkPt 2 0)
    refine Erdos634.SssCongruent.dist_of_sq ?_
    rw [sqd_mk, sqd_mk]; nlinarith


/-- **A cell**: the parallelogram `Par g u w` cut into two congruent triangles (point reflections of each other), both congruent to the model `rT.C.model`. -/
noncomputable def cellE (g0 g1 u0 u1 w0 w1 : ℝ) (hD : u0 * w1 - u1 * w0 ≠ 0)
    (hu : u0 ^ 2 + u1 ^ 2 = 4) (hw : w0 ^ 2 + w1 ^ 2 = 1) (huw : u0 * w0 + u1 * w1 = 1) : CongruentRegionDissection 2 where
  region := Par g0 g1 u0 u1 w0 w1
  tile := ![ct g0 g1 u0 u1 w0 w1 hD, ct (g0 + u0 + w0) (g1 + u1 + w1) (-u0) (-u1) (-w0) (-w1) (hD2 hD)]
  covers := by
    rw [← cell_cover hD]
    ext x
    simp only [Set.mem_iUnion, Fin.exists_fin_two, Set.mem_union]
    rfl
  interiors_disjoint := by
    intro i j hij
    obtain ⟨f, c, hf, h1, h2⟩ := cell_sep (g0 := g0) (g1 := g1) hD
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact Erdos634.CertGeom.interiors_disjoint_of_separating f hf c h1 h2
    · exact (Erdos634.CertGeom.interiors_disjoint_of_separating f hf c h1 h2).symm
    · exact absurd rfl hij
  model := rT.C.model
  tiles_congruent := by
    intro i
    fin_cases i
    · obtain ⟨f, hf⟩ := ct_isoE (g0 := g0) (g1 := g1) hD hu hw huw
      exact ⟨f, Equiv.refl _, hf⟩
    · have hu' : (-u0) ^ 2 + (-u1) ^ 2 = 4 := by nlinarith
      have hw' : (-w0) ^ 2 + (-w1) ^ 2 = 1 := by nlinarith
      have huw' : (-u0) * (-w0) + (-u1) * (-w1) = 1 := by nlinarith
      obtain ⟨f, hf⟩ := ct_isoE (g0 := g0 + u0 + w0) (g1 := g1 + u1 + w1) (hD2 hD) hu' hw' huw'
      exact ⟨f, Equiv.refl _, hf⟩

theorem cell_swapE0 {g0 g1 u0 u1 w0 w1 : ℝ} (hD : u0 * w1 - u1 * w0 ≠ 0)
    (hu : u0 ^ 2 + u1 ^ 2 = 4) (hw : w0 ^ 2 + w1 ^ 2 = 1) (huw : u0 * w0 + u1 * w1 = 1) (i : Fin 2) :
    ((cellE g0 g1 u0 u1 w0 w1 hD hu hw huw).tile (i + 1)).pts 1 = ((cellE g0 g1 u0 u1 w0 w1 hD hu hw huw).tile i).pts 0 := by
  fin_cases i
  · exact mkPt_congr (by ring) (by ring)
  · exact mkPt_congr (by ring) (by ring)

theorem cell_swapE1 {g0 g1 u0 u1 w0 w1 : ℝ} (hD : u0 * w1 - u1 * w0 ≠ 0)
    (hu : u0 ^ 2 + u1 ^ 2 = 4) (hw : w0 ^ 2 + w1 ^ 2 = 1) (huw : u0 * w0 + u1 * w1 = 1) (i : Fin 2) :
    ((cellE g0 g1 u0 u1 w0 w1 hD hu hw huw).tile (i + 1)).pts 0 = ((cellE g0 g1 u0 u1 w0 w1 hD hu hw huw).tile i).pts 1 := by
  fin_cases i
  · exact mkPt_congr (by ring) (by ring)
  · exact mkPt_congr (by ring) (by ring)

theorem cellE_regular {g0 g1 u0 u1 w0 w1 : ℝ} (hD : u0 * w1 - u1 * w0 ≠ 0)
    (hu : u0 ^ 2 + u1 ^ 2 = 4) (hw : w0 ^ 2 + w1 ^ 2 = 1) (huw : u0 * w0 + u1 * w1 = 1) :
    RegularPQ (cellE g0 g1 u0 u1 w0 w1 hD hu hw huw) := by
  refine ⟨fun _ => 1, fun i v => ?_, fun X => ?_⟩
  · fin_cases i
    · obtain ⟨f, hf⟩ := ct_isoE (g0 := g0) (g1 := g1) hD hu hw huw
      exact angleAt_of_iso' f hf v
    · have hu' : (-u0) ^ 2 + (-u1) ^ 2 = 4 := by nlinarith
      have hw' : (-w0) ^ 2 + (-w1) ^ 2 = 1 := by nlinarith
      have huw' : (-u0) * (-w0) + (-u1) * (-w1) = 1 := by nlinarith
      obtain ⟨f, hf⟩ := ct_isoE (g0 := g0 + u0 + w0) (g1 := g1 + u1 + w1) (hD2 hD) hu' hw' huw'
      exact angleAt_of_iso' f hf v
  · unfold cntR
    refine Finset.card_nbij' (fun x => (x.1 + 1, (1 : Fin 3))) (fun x => (x.1 + 1, (0 : Fin 3))) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, Equiv.Perm.coe_one, id_eq] at hx ⊢
      obtain ⟨h1, h2⟩ := hx
      rw [h2] at h1
      exact ⟨by rw [cell_swapE0 hD hu hw huw]; exact h1, trivial⟩
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, Equiv.Perm.coe_one, id_eq] at hx ⊢
      obtain ⟨h1, h2⟩ := hx
      rw [h2] at h1
      exact ⟨by rw [cell_swapE1 hD hu hw huw]; exact h1, trivial⟩
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, Equiv.Perm.coe_one, id_eq] at hx
      obtain ⟨i, k⟩ := x
      simp only at hx ⊢
      obtain ⟨h1, h2⟩ := hx
      subst h2
      ext
      · simp only; fin_cases i <;> rfl
      · rfl
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, Equiv.Perm.coe_one, id_eq] at hx
      obtain ⟨i, k⟩ := x
      simp only at hx ⊢
      obtain ⟨h1, h2⟩ := hx
      subst h2
      ext
      · simp only; fin_cases i <;> rfl
      · rfl



end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.cellE_regular

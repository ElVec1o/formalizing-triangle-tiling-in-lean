-- Draft/LaczFormalIIcL8n.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.3, L8 `gexc_disjoint`, step 7 (B): `cross_exc`.
-- A point `V` that is an INNER point of two edges `X1 -> Y1`, `X2 -> Y2` of Gamma_except on non-parallel lines (and is not a vertex of the polygon) is an exceptional vertex of the tiling.
-- Route: `gexc_inner_split` for both edges; an inner-side element on any of the four divisions contradicts the other edge (`no_inner_cross`, (B1)); so `V` is the head of a `gamma`-headed element of each of
-- the four divisions, i.e. the four `gamma` sectors of `exc_of_two_lines`.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcL8k
import Erdos634.Draft.LaczFormalIIcL8l
import Erdos634.Draft.LaczFormalIIcL8m

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

theorem crs_ne_of_par {w1 w2 d1 d2 : V2} (h1 : Par w1 d1) (h2 : Par w2 d2) (h : crs w1 w2 ≠ 0) : crs d1 d2 ≠ 0 := by
  obtain ⟨c1, hc1, e1⟩ := h1.smul
  obtain ⟨c2, hc2, e2⟩ := h2.smul
  intro hd
  apply h
  rw [e1, e2]; unfold crs at hd ⊢; simp only; linear_combination (c1 * c2) * hd

/-- **(B)** a crossing point of two edges is an exceptional vertex. -/
theorem cross_exc [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (h1 : D.model.angleAt 2 < Real.pi / 2)
    {X1 Y1 X2 Y2 V : Plane} (e1 : GExc D idx X1 Y1) (e2 : GExc D idx X2 Y2) (hV1 : V ∈ openSegment ℝ X1 Y1) (hV2 : V ∈ openSegment ℝ X2 Y2)
    (hnp : crs (toV2 (Y1 - X1)) (toV2 (Y2 - X2)) ≠ 0) (hnc : ∀ k : Fin M, V ≠ P.v (k + 1)) : V ∈ excVerts2 D idx P := by
  obtain ⟨d1, hd1, nb1, par1, ⟨Z1, L1, T1, v1, W1, hT1, hv1, hv10, hv1T⟩, EL1, ER1, -, -⟩ := gexc_inner_split D idx e1 hV1
  obtain ⟨d2, hd2, nb2, par2, ⟨Z2, L2, T2, v2, W2, hT2, hv2, hv20, hv2T⟩, EL2, ER2, -, -⟩ := gexc_inner_split D idx e2 hV2
  have hnp12 : crs d1 d2 ≠ 0 := crs_ne_of_par par1 par2 hnp
  have hnp21 : crs d2 d1 ≠ 0 := by
    intro h; apply hnp12; unfold crs at h ⊢; linarith
  have hnn1 : crs (neg2 d1) d2 ≠ 0 := by
    intro h; apply hnp12; unfold crs neg2 at h; unfold crs; simp only at h; linarith
  have hnn2 : crs (neg2 d2) d1 ≠ 0 := by
    intro h; apply hnp21; unfold crs neg2 at h; unfold crs; simp only at h; linarith
  -- head type on the four divisions
  obtain ⟨iL1, A1, B1, hS1, hL1⟩ := EL1
  obtain ⟨iR1, A1', B1', hS1', hR1⟩ := ER1
  obtain ⟨iL2, A2, B2, hS2, hL2⟩ := EL2
  obtain ⟨iR2, A2', B2', hS2', hR2⟩ := ER2
  have hL1h : V = B1 ∧ ∃ k, (D.tile iL1).pts k = V ∧ idx iL1 k = 2 := by
    rcases hL1 with h | ⟨hin, -⟩
    · exact h
    · exact (no_inner_cross D.toRegionDissection hS1 hin hd2 W2 hT2 hv2 hv20 hv2T hnp12).elim
  have hR1h : V = B1' ∧ ∃ k, (D.tile iR1).pts k = V ∧ idx iR1 k = 2 := by
    rcases hR1 with h | ⟨hin, -⟩
    · exact h
    · exact (no_inner_cross D.toRegionDissection hS1' (by rw [openSegment_symm]; exact hin) hd2 W2 hT2 hv2 hv20 hv2T hnn1).elim
  have hL2h : V = B2 ∧ ∃ k, (D.tile iL2).pts k = V ∧ idx iL2 k = 2 := by
    rcases hL2 with h | ⟨hin, -⟩
    · exact h
    · exact (no_inner_cross D.toRegionDissection hS2 hin hd1 W1 hT1 hv1 hv10 hv1T hnp21).elim
  have hR2h : V = B2' ∧ ∃ k, (D.tile iR2).pts k = V ∧ idx iR2 k = 2 := by
    rcases hR2 with h | ⟨hin, -⟩
    · exact h
    · exact (no_inner_cross D.toRegionDissection hS2' (by rw [openSegment_symm]; exact hin) hd1 W1 hT1 hv1 hv10 hv1T hnn2).elim
  obtain ⟨hVB1, k1, hk1, hk12⟩ := hL1h
  have hvert : ∃ j k, (D.tile j).pts k = V := ⟨iL1, k1, hk1⟩
  obtain ⟨κ, _, ⟨F⟩⟩ := HasFansC.fans (D := D.toRegionDissection) V hvert
  obtain ⟨hVB1', k1', hk1', hk12'⟩ := hR1h
  obtain ⟨hVB2, k2, hk2, hk22⟩ := hL2h
  obtain ⟨hVB2', k2', hk2', hk22'⟩ := hR2h
  rw [← hVB1] at hS1
  rw [← hVB1'] at hS1'
  rw [← hVB2] at hS2
  rw [← hVB2'] at hS2'
  obtain ⟨x1, hx1i, hx1q⟩ := sec_end F hS1
  obtain ⟨y1, hy1i, hy1p⟩ := sec_start F hS1'
  obtain ⟨x2, hx2i, hx2q⟩ := sec_end F hS2
  obtain ⟨y2, hy2i, hy2p⟩ := sec_start F hS2'
  have hlt := exc_of_two_lines D P hreg idx hC h1 hvert hnc F hnp12 (aL1 := x1) (aR1 := y1) (aL2 := x2) (aR2 := y2) hx1q hy1p
    ⟨k1, by rw [hx1i]; exact hk1, by rw [hx1i]; exact hk12⟩ ⟨k1', by rw [hy1i]; exact hk1', by rw [hy1i]; exact hk12'⟩
    hx2q hy2p ⟨k2, by rw [hx2i]; exact hk2, by rw [hx2i]; exact hk22⟩ ⟨k2', by rw [hy2i]; exact hk2', by rw [hy2i]; exact hk22'⟩
  unfold excVerts2
  simp only [Finset.mem_filter, Finset.mem_sdiff]
  exact ⟨⟨mem_vtxSet.mpr hvert, fun h => by obtain ⟨k, hk⟩ := mem_polyVerts.mp h; exact hnc k hk⟩, hlt⟩

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.cross_exc

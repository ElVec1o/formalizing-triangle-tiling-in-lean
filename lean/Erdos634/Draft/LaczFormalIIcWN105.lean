-- Draft/LaczFormalIIcWN105.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3, p. 360), Lemma 6.2, R3: "The segments V_i W_i are pairwise disjoint, since an intersection of two of them would be an exceptional point."
-- `spokes_disjoint_C`: the closed chords `P.v i -> W_i`, `P.v j -> W_j` (ends `W` vertices of the cycle) from distinct corners of `A` are disjoint.
-- Endpoint cases: corners of `A` are not interior points while the open chords and the cycle vertices are; a cycle vertex is never an inner point of an edge of Gamma_except; equal ends mean equal starts
-- (at most one edge arrives, `gexc_arrive_kite_unique`).  Inner/inner: non-parallel is an exceptional point (`cross_exc`) against `ExcInside` (the winding number vanishes on the chord); parallel is excluded by `seg_overlap_eq`.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN104
import Erdos634.Draft.LaczFormalIIcWN97

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG
open Erdos634.Draft.LaczFormal.WN (edgeSet wind extAng OrientOK sideFn)

local notation "tc" => Erdos634.Draft.LaczFormal.WN.toC

variable {N M : ℕ}

set_option maxHeartbeats 6400000 in
theorem spokes_disjoint_C [NeZero N] [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (G : AngGen (fun l => D.model.angleAt l))
    {m : ℕ} [NeZero m] (C : Fin m → Plane) (hCy : ∀ k : Fin m, GKite D idx (C k) (C (k + 1)))
    (hExc : ∀ E ∈ excVerts2 D idx P, tc E ∉ edgeSet (cyc C) ∧ wind (cyc C) (tc E) ≠ 0)
    {i j : Fin M} (hij : i ≠ j) {ki kj : Fin m}
    (hWi : GExc D idx (P.v i) (C ki)) (hWj : GExc D idx (P.v j) (C kj))
    (hwind : ∀ s : ℝ, 0 < s → s < 1 → wind (cyc C) (tc (P.v i + s • (C ki - P.v i))) = 0) :
    ∀ V, V ∈ segment ℝ (P.v i) (C ki) → V ∈ segment ℝ (P.v j) (C kj) → False := by
  classical
  intro V hV1 hV2
  have no_inner : ∀ {X Y : Plane}, GExc D idx X Y → ∀ a : Fin m, C a ∉ openSegment ℝ X Y := fun hE a h =>
    gexc_interior_not_kite D P hreg idx hC hab hac h1 h3 G hE h (Or.inr ⟨C (a + 1), hCy a⟩)
  have hint : ∀ a : Fin m, C a ∈ interior P.carrier := by
    intro a
    have hXY : GKite D idx (C (a - 1)) (C a) := by simpa using hCy (a - 1)
    have := (gkite_vertex_type D P hreg idx hC.hidxA hC.hregc h1 h3 hXY).1.1
    rw [hreg] at this; exact this
  have vtx_cases : ∀ {a b Z : Plane}, Z ∈ segment ℝ a b → (Z = a ∨ Z = b ∨ Z ∈ openSegment ℝ a b) := by
    intro a b Z hZ
    by_cases hZa : Z = a
    · exact Or.inl hZa
    by_cases hZb : Z = b
    · exact Or.inr (Or.inl hZb)
    exact Or.inr (Or.inr (mem_openSegment_of_ne_left_right (Ne.symm hZa) (Ne.symm hZb) hZ))
  have open_int : ∀ (a : Fin M) (b : Fin m), openSegment ℝ (P.v a) (C b) ⊆ interior P.carrier := fun a b Z hZ =>
    openSegment_interior_of P (hint b) (vtx_mem' P a) (by rw [openSegment_symm] at hZ; exact hZ)
  have corner_ni : ∀ a : Fin M, P.v a ∉ interior P.carrier := fun a => vertex_not_interior P a
  rcases vtx_cases hV1 with rfl | rfl | hV1o
  · rcases vtx_cases hV2 with h | h | h
    · exact hij (vtx_inj' P h)
    · exact corner_ni i (h ▸ hint kj)
    · exact corner_ni i (open_int j kj h)
  · rcases vtx_cases hV2 with h | h | h
    · exact corner_ni j (h ▸ hint ki)
    · exact hij (vtx_inj' P (gexc_arrive_kite_unique D P hreg idx hC h1 h3 G (hCy ki) hWi (h ▸ hWj)))
    · exact no_inner hWj ki h
  · rcases vtx_cases hV2 with h | h | hV2o
    · exact corner_ni j (h ▸ open_int i ki hV1o)
    · exact no_inner hWi kj (by rw [h] at hV1o; exact hV1o)
    · by_cases hpar : crs (toV2 (C ki - P.v i)) (toV2 (C kj - P.v j)) = 0
      · rcases seg_overlap_eq hV1o hV2o hpar (fun h => corner_ni i (open_int j kj h)) (no_inner hWj ki)
          (fun h => corner_ni j (open_int i ki h)) (no_inner hWi kj) with ⟨h, -⟩ | ⟨h, -⟩
        · exact hij (vtx_inj' P h)
        · exact corner_ni i (h ▸ hint kj)
      · have hVint : V ∈ interior P.carrier := open_int i ki hV1o
        have hexc := cross_exc D P hreg idx hC h1 hWi hWj hV1o hV2o hpar (fun a ha => vertex_not_interior P (a + 1) (ha ▸ hVint))
        obtain ⟨s, hs0, hs1, hVs⟩ := openSegment_param hV1o
        apply (hExc V hexc).2
        rw [hVs]; exact hwind s hs0 hs1

#print axioms spokes_disjoint_C

end Erdos634.Draft.LaczFormal.RG

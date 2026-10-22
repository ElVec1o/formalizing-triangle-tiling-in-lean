-- Draft/LaczFormalIIcWN97.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3, p. 359), Lemma 6.2, R2: "These segments VW are pairwise disjoint, since any intersection would be an exceptional point."
-- `chords_disjoint`: the closed chords `C k -> C j`, `C k' -> C j'` of two distinct concave vertices (ends convex) are disjoint.
-- Endpoint cases: a vertex of the cycle is never an inner point of an edge of Gamma_except (`gexc_interior_not_kite`); equal starts mean `k = k'`; equal ends mean `k = k'` (at most one edge arrives, `gexc_arrive_kite_unique`);
-- a start equal to an end is impossible (concave vs convex).  Inner/inner: non-parallel is an exceptional point (`cross_exc`), contradicting `ExcInside` since the winding number vanishes on the open chord;
-- parallel is excluded by `seg_overlap_eq` (WN96).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN96
import Erdos634.Draft.LaczFormalIIcWN95
import Erdos634.Draft.LaczFormalIIcL8t
import Erdos634.Draft.LaczFormalIIcL8n

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG
open Erdos634.Draft.LaczFormal.WN (edgeSet wind extAng OrientOK)

local notation "tc" => Erdos634.Draft.LaczFormal.WN.toC

variable {N M : ℕ}

set_option maxHeartbeats 6400000 in
theorem chords_disjoint [NeZero N] [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (G : AngGen (fun l => D.model.angleAt l))
    {m : ℕ} [NeZero m] (C : Fin m → Plane) (hCy : ∀ k : Fin m, GKite D idx (C k) (C (k + 1))) (hinj : Function.Injective C)
    (hExc : ∀ E ∈ excVerts2 D idx P, tc E ∉ edgeSet (cyc C) ∧ wind (cyc C) (tc E) ≠ 0)
    {σ : ℝ} {k k' j j' : Fin m} (hkk' : k ≠ k')
    (hconc : σ * extAng (cyc C) k < 0) (hconc' : σ * extAng (cyc C) k' < 0) (hconv : 0 < σ * extAng (cyc C) j) (hconv' : 0 < σ * extAng (cyc C) j')
    (hW : GExc D idx (C k) (C j)) (hW' : GExc D idx (C k') (C j'))
    (hwind : ∀ s : ℝ, 0 < s → s < 1 → wind (cyc C) (tc (C k + s • (C j - C k))) = 0) :
    ∀ V, V ∈ segment ℝ (C k) (C j) → V ∈ segment ℝ (C k') (C j') → False := by
  classical
  intro V hV1 hV2
  have no_inner : ∀ {X Y : Plane}, GExc D idx X Y → ∀ i : Fin m, C i ∉ openSegment ℝ X Y := fun hE i h =>
    gexc_interior_not_kite D P hreg idx hC hab hac h1 h3 G hE h (Or.inr ⟨C (i + 1), hCy i⟩)
  have ext_ne : ∀ {a b : Fin m}, σ * extAng (cyc C) a < 0 → 0 < σ * extAng (cyc C) b → a ≠ b := by
    intro a b ha hb hab'; subst hab'; linarith
  have hint : ∀ i : Fin m, C i ∈ interior P.carrier := by
    intro i
    have hXY : GKite D idx (C (i - 1)) (C i) := by simpa using hCy (i - 1)
    have := (gkite_vertex_type D P hreg idx hC.hidxA hC.hregc h1 h3 hXY).1.1
    rw [hreg] at this; exact this
  have vtx_cases : ∀ {a b Z : Plane}, Z ∈ segment ℝ a b → (Z = a ∨ Z = b ∨ Z ∈ openSegment ℝ a b) := by
    intro a b Z hZ
    by_cases hZa : Z = a
    · exact Or.inl hZa
    by_cases hZb : Z = b
    · exact Or.inr (Or.inl hZb)
    exact Or.inr (Or.inr (mem_openSegment_of_ne_left_right (Ne.symm hZa) (Ne.symm hZb) hZ))
  rcases vtx_cases hV1 with rfl | rfl | hV1o
  · -- V = C k
    rcases vtx_cases hV2 with h | h | h
    · exact hkk' (hinj h)
    · exact ext_ne hconc hconv' (hinj h)
    · exact no_inner hW' k h
  · -- V = C j
    rcases vtx_cases hV2 with h | h | h
    · have : j = k' := hinj h
      subst this; linarith
    · obtain rfl : j = j' := hinj h
      exact hkk' (hinj (gexc_arrive_kite_unique D P hreg idx hC h1 h3 G (hCy j) hW hW'))
    · exact no_inner hW' j h
  · rcases vtx_cases hV2 with h | h | hV2o
    · exact no_inner hW k' (by rw [h] at hV1o; exact hV1o)
    · exact no_inner hW j' (by rw [h] at hV1o; exact hV1o)
    · by_cases hpar : crs (toV2 (C j - C k)) (toV2 (C j' - C k')) = 0
      · rcases seg_overlap_eq hV1o hV2o hpar (no_inner hW' k) (no_inner hW' j) (no_inner hW k') (no_inner hW j') with ⟨h, -⟩ | ⟨h, -⟩
        · exact hkk' (hinj h)
        · exact ext_ne hconc hconv' (hinj h)
      · have hVint : V ∈ interior P.carrier :=
          openSegment_interior_of P (hint j) (interior_subset (hint k)) (by rw [openSegment_symm] at hV1o; exact hV1o)
        have hexc := cross_exc D P hreg idx hC h1 hW hW' hV1o hV2o hpar (fun i hi => vertex_not_interior P (i + 1) (hi ▸ hVint))
        obtain ⟨s, hs0, hs1, hVs⟩ := openSegment_param hV1o
        apply (hExc V hexc).2
        rw [hVs]; exact hwind s hs0 hs1

#print axioms chords_disjoint

end Erdos634.Draft.LaczFormal.RG

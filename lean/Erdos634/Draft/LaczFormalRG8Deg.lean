-- Draft/LaczFormalRG8Deg.lean -- degree facts of `Gamma_c` used in Lemma 4.6: every tail of an edge is also a head (balance), the edge out of a vertex is unique, unpacking of an edge into
-- side-uniform walk data.  UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 4), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG8Walk
import Erdos634.Draft.LaczFormalRG8Arith

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

theorem stepU_vertex {D : RegionDissection N} {b : Bool} {d : V2} {e : Fin N × Plane × Plane} (h : StepU D b d e) :
    (∃ j k, (D.tile j).pts k = e.2.1) ∧ (∃ j k, (D.tile j).pts k = e.2.2) := by
  cases b
  · simp only [StepU, Bool.false_eq_true, if_false] at h
    obtain ⟨kk, f, g, hk, hf, -⟩ := h
    exact ⟨⟨e.1, f, hf⟩, ⟨e.1, kk, hk⟩⟩
  · simp only [StepU, if_true] at h
    obtain ⟨kk, f, g, hk, hf, -⟩ := h
    exact ⟨⟨e.1, kk, hk⟩, ⟨e.1, f, hf⟩⟩

theorem gc_indegree (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseC D idx)
    {X X' H : Plane} (h1 : GcEdge D X H) (h2 : GcEdge D X' H) : X = X' := by
  have hG := h.caseG
  haveI : HasFansC (relabelC D).toRegionDissection := (inferInstance : HasFansC D.toRegionDissection)
  rw [gcEdge_iff] at h1 h2
  exact ga_indegree (relabelC D) (relabelCIdx idx) hG.hidx hG.hnc h1 h2

theorem gc_in_of_out (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseC D idx) {X H : Plane} (hE : GcEdge D X H) : ∃ Z, GcEdge D Z X := by
  classical
  haveI : HasFansC (relabelC D).toRegionDissection := (inferInstance : HasFansC D.toRegionDissection)
  have hbal := gc_balance D P hreg idx h
  obtain ⟨hX, hH⟩ := ga_edge_endpoints D.toRegionDissection (slen D 2) hE
  have hXv : X ∈ vtxSet (relabelC D).toRegionDissection := mem_vtxSet.mpr hX
  have hHv : H ∈ vtxSet (relabelC D).toRegionDissection := mem_vtxSet.mpr hH
  have hpos : 0 < ((GAset (relabelC D)).filter fun e => e.1 = ⟨X, hXv⟩).card := by
    apply Finset.card_pos.mpr
    refine ⟨(⟨X, hXv⟩, ⟨H, hHv⟩), ?_⟩
    simp only [GAset, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
    exact (gcEdge_iff D X H).mp hE
  have h2 := hbal ⟨X, hXv⟩
  rw [h2] at hpos
  obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
  simp only [GAset, Finset.mem_filter, Finset.mem_univ, true_and] at he
  refine ⟨e.1.1, (gcEdge_iff D e.1.1 X).mpr ?_⟩
  have := he.1
  rw [he.2] at this
  exact this

theorem gc_out_unique (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseC D idx) {X W V : Plane} (h1 : GcEdge D X W) (h2 : GcEdge D X V) : W = V := by
  classical
  by_contra hne
  haveI : HasFansC (relabelC D).toRegionDissection := (inferInstance : HasFansC D.toRegionDissection)
  have hbal := gc_balance D P hreg idx h
  obtain ⟨hX, hW⟩ := ga_edge_endpoints D.toRegionDissection (slen D 2) h1
  obtain ⟨-, hV⟩ := ga_edge_endpoints D.toRegionDissection (slen D 2) h2
  have hXv : X ∈ vtxSet (relabelC D).toRegionDissection := mem_vtxSet.mpr hX
  have hWv : W ∈ vtxSet (relabelC D).toRegionDissection := mem_vtxSet.mpr hW
  have hVv : V ∈ vtxSet (relabelC D).toRegionDissection := mem_vtxSet.mpr hV
  have hge : 2 ≤ ((GAset (relabelC D)).filter fun e => e.1 = ⟨X, hXv⟩).card := by
    have hsub : ({(⟨X, hXv⟩, ⟨W, hWv⟩), (⟨X, hXv⟩, ⟨V, hVv⟩)} : Finset _) ⊆ (GAset (relabelC D)).filter fun e => e.1 = ⟨X, hXv⟩ := by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      simp only [GAset, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hp with rfl | rfl
      · exact ⟨(gcEdge_iff D X W).mp h1, rfl⟩
      · exact ⟨(gcEdge_iff D X V).mp h2, rfl⟩
    have hneq : ((⟨X, hXv⟩, ⟨W, hWv⟩) : ↥(vtxSet (relabelC D).toRegionDissection) × ↥(vtxSet (relabelC D).toRegionDissection)) ≠ (⟨X, hXv⟩, ⟨V, hVv⟩) := by
      intro e
      exact hne (congrArg (fun p => p.2.1) e)
    have := Finset.card_le_card hsub
    rwa [Finset.card_pair hneq] at this
  rw [hbal ⟨X, hXv⟩] at hge
  have hle : ((GAset (relabelC D)).filter fun e => e.2 = ⟨X, hXv⟩).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro e1 he1 e2 he2
    simp only [GAset, Finset.mem_filter, Finset.mem_univ, true_and] at he1 he2
    have hs : e1.1.1 = e2.1.1 := by
      apply gc_indegree D idx h
      · exact (gcEdge_iff D e1.1.1 X).mpr (by have := he1.1; rw [he1.2] at this; exact this)
      · exact (gcEdge_iff D e2.1.1 X).mpr (by have := he2.1; rw [he2.2] at this; exact this)
    exact Prod.ext (Subtype.ext hs) (he1.2.trans he2.2.symm)
  omega

/-- **Unpacking of an edge**: side-uniform walks, `LA` the division whose first side is `c` (run side). -/
theorem gcEdge_unpack (D : CongruentRegionDissection N) {X H : Plane} (h : GcEdge D X H) :
    ∃ (d : V2) (Y : Plane) (bA : Bool) (LA LB : List (Fin N × Plane × Plane)), d ≠ 0 ∧ NoBack D.toRegionDissection d X ∧
      WalkU D.toRegionDissection bA d X Y LA ∧ WalkU D.toRegionDissection (!bA) d X Y LB ∧ LA ≠ [] ∧ LB ≠ [] ∧
      (∀ i U', ¬ TriStep (D.tile i) d Y U') ∧ (∀ i U', ¬ TriStep (D.tile i) (neg2 d) U' Y) ∧
      RunEnd (slen D 2) LA H ∧ (∀ e ∈ LB.head?, dist e.2.1 e.2.2 ≠ slen D 2) := by
  obtain ⟨d, Y, L1, L2, hd, hnb, W1, W2, hL1, hL2, hn1, hn2, hcase⟩ := h
  rcases hcase with ⟨hR, hf⟩ | ⟨hR, hf⟩
  · exact ⟨d, Y, true, L1, L2, hd, hnb, walkU_of_T W1, by simpa using walkU_of_R W2, hL1, hL2, hn1, hn2, hR, hf⟩
  · exact ⟨d, Y, false, L2, L1, hd, hnb, walkU_of_R W2, by simpa using walkU_of_T W1, hL2, hL1, hn1, hn2, hR, hf⟩

end Erdos634.Draft.LaczFormal.RG

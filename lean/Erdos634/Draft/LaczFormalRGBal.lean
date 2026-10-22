-- Draft/LaczFormalRGBal.lean -- S4 of PLAN_THM21: Laczkovich Lemma 9.1 (i), (ii) for a congruent dissection of a REGION with `gamma = pi/2`:
-- (i) at every vertex the out-degree of `Gamma_a` equals its in-degree; (ii) no edge of `Gamma_a` starts at a vertex that is not an interior point of the region.
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Lemma 9.1 (i), (ii)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRGHead2
import Erdos634.Draft.LaczFormalRegArith

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

theorem ga_edge_endpoints (D : RegionDissection N) (a : ℝ) {X H : Plane} (h : GaEdge D a X H) :
    (∃ i k, (D.tile i).pts k = X) ∧ (∃ i k, (D.tile i).pts k = H) := by
  refine ⟨?_, ga_edge_vertex D a h⟩
  obtain ⟨d, Y, L1, L2, hd, hnb, W1, W2, hL1, hL2, -⟩ := h
  cases W1 with
  | nil => exact absurd rfl hL1
  | cons hS _ =>
    obtain ⟨kk, f, g, hk, -⟩ := hS
    exact ⟨_, kk, hk⟩

/-- All vertices of the tiling as a finite set of points. -/
theorem mem_vtxSet' {D : RegionDissection N} {P : Plane} : P ∈ vtxSet D ↔ ∃ i k, (D.tile i).pts k = P := mem_vtxSet

/-- The edge set of `Γ_a` on the finite vertex set. -/
noncomputable def GAset (D : CongruentRegionDissection N) : Finset (↥(vtxSet D.toRegionDissection) × ↥(vtxSet D.toRegionDissection)) :=
  Finset.univ.filter (fun e => GaEdge D.toRegionDissection (slen D 0) e.1.1 e.2.1)

/-- The head of a `Γ_a` edge is an interior point of the region. -/
theorem ga_head_interior (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) {X H : Plane} (hE : GaEdge D.toRegionDissection (slen D 0) X H) :
    H ∈ interior D.region := by
  classical
  obtain ⟨κ, _, ⟨F⟩⟩ := HasFansC.fans (D := D.toRegionDissection) H (ga_edge_vertex _ _ hE)
  obtain ⟨d, hd, nb, hc⟩ := ga_edge_data D idx hidx hnc hE F
  rcases hc with ⟨P, W, hP, a, b, s, h1, h2, h3, h4, h5, h6, h7, h8⟩ | ⟨P, W, hP, a, b, s, h1, h2, h3, h4, h5, h6, h7, h8⟩
  · exact (F.head_cyc a b s h1 h2 h3 h4 h5 h6).2.1
  · obtain ⟨c1, c2, c3, c4, c5, c6, -⟩ := HeadCfg.of_right D F a b s h1 h2 h3 h4 h5 h6 h7 h8
    exact (F.head_cyc b a s c1 c2 c3 c4 c5 c6).2.1

/-- **Lemma 9.1 (i)** (`γ = π/2`): in `Γ_a`, out-degree = in-degree at every vertex. -/
theorem lemma91_i (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2)
    (hhp : HalfPar D idx) :
    ∀ v : ↥(vtxSet D.toRegionDissection), ((GAset D).filter fun e => e.1 = v).card = ((GAset D).filter fun e => e.2 = v).card := by
  classical
  apply digraph_balance
  · intro v
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [GAset, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    have hb1 : GaEdge D.toRegionDissection (slen D 0) b.1.1 a.2.1 := by rw [show a.2 = b.2 from ha.2.trans hb.2.symm]; exact hb.1
    have := ga_indegree D idx hidx hnc ha.1 hb1
    exact Prod.ext (Subtype.ext this) (ha.2.trans hb.2.symm)
  · intro v hv
    obtain ⟨e, he⟩ := Finset.card_pos.mp hv
    simp only [GAset, Finset.mem_filter, Finset.mem_univ, true_and] at he
    obtain ⟨hE, hev⟩ := he
    have hvv : v.1 = e.2.1 := by rw [hev]
    have hout : ∃ H', GaEdge D.toRegionDissection (slen D 0) v.1 H' := by
      rw [hvv]
      exact ga_head_out_half D idx hidx hidxA hnc hab hac hhp hE
    obtain ⟨H', hH'⟩ := hout
    apply Finset.card_pos.mpr
    have hv' : H' ∈ vtxSet D.toRegionDissection := mem_vtxSet.mpr (ga_edge_endpoints _ _ hH').2
    exact ⟨(v, ⟨H', hv'⟩), by simp [GAset, hH']⟩

/-- **Lemma 9.1 (ii)**: no edge of `Γ_a` starts at a point that is not an interior point of the region. -/
theorem lemma91_ii (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2)
    (hhp : HalfPar D idx)
    {X H : Plane} (hX : X ∉ interior D.region) : ¬ GaEdge D.toRegionDissection (slen D 0) X H := by
  classical
  intro hE
  have hXv : X ∈ vtxSet D.toRegionDissection := mem_vtxSet.mpr (ga_edge_endpoints _ _ hE).1
  have hHv : H ∈ vtxSet D.toRegionDissection := mem_vtxSet.mpr (ga_edge_endpoints _ _ hE).2
  have hbal := lemma91_i D idx hidx hidxA hnc hab hac hhp ⟨X, hXv⟩
  have hout : 0 < ((GAset D).filter fun e => e.1 = (⟨X, hXv⟩ : ↥(vtxSet D.toRegionDissection))).card :=
    Finset.card_pos.mpr ⟨(⟨X, hXv⟩, ⟨H, hHv⟩), by simp [GAset, hE]⟩
  rw [hbal] at hout
  obtain ⟨e, he⟩ := Finset.card_pos.mp hout
  simp only [GAset, Finset.mem_filter, Finset.mem_univ, true_and] at he
  obtain ⟨hE', hev⟩ := he
  have hvv : e.2.1 = X := by rw [hev]
  apply hX
  rw [← hvv]
  exact ga_head_interior D idx hidx hnc hE'

end Erdos634.Draft.LaczFormal.RG

-- Draft/LaczFormalBZL7h9.lean -- Beeson (arXiv 1206.1974v7) Lemmas 10.5/10.6 (G5): `g5_of_steps`: a left walk along a side with a c step and a non-c step gives a boundary vertex with an outgoing Gamma_c edge.
-- NOTE, UNAUDITED.  Credit: Beeson (arXiv 1206.1974v7, Lemmas 10.5, 10.6), Laczkovich (DCG 48 (2012), Sect. 4), Beeson-Zhang.
import Erdos634.Draft.LaczFormalBZL7h8

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

theorem g5_of_steps (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hβ : D.model.angleAt 1 = Real.pi - 3 * D.model.angleAt 0) (hγ : D.model.angleAt 2 = 2 * D.model.angleAt 0)
    (hα : ¬ ∃ r : ℚ, D.model.angleAt 0 = (r : ℝ) * Real.pi)
    (hnc : NotComb (slen D 2) (slen D 0) (slen D 1))
    (i : Fin M) {L : List (Fin N × Plane × Plane)} (W : WalkT D.toRegionDissection (toV2 (P.e i)) (P.v i) (P.v (i + 1)) L)
    (hc : ∃ e ∈ L, dist e.2.1 e.2.2 = slen D 2) (hn : ∃ e ∈ L, dist e.2.1 e.2.2 ≠ slen D 2) :
    ∃ Q, Q ∉ interior D.region ∧ ∃ H, GaEdge D.toRegionDissection (slen D 2) Q H := by
  classical
  obtain ⟨L1, x, y, L2, hdec, hd⟩ := list_adjacent_diff (fun e : Fin N × Plane × Plane => dist e.2.1 e.2.2 = slen D 2) L hc hn
  obtain ⟨hxy, hxS, hyS⟩ := walkT_adjacent W hdec
  obtain ⟨t, ht0, ht1, hQ⟩ := walkT_open_side D.toRegionDissection P i W hdec
  have hQnot : y.2.1 ∉ interior D.region := by
    rw [hreg, hQ]; exact not_interior_of_c_zero P (c_on_edge P i t)
  refine ⟨y.2.1, hQnot, ?_⟩
  have hvertQ : ∃ j k, (D.tile j).pts k = y.2.1 := by
    obtain ⟨kk, f, g, hk, -⟩ := hyS
    exact ⟨y.1, kk, hk⟩
  have hAsum : Asum D idx y.2.1 = Real.pi := by
    rcases vertex_A D P hreg idx hidxA hvertQ with ⟨hint, -⟩ | ⟨-, h1 | ⟨k, hk, -⟩⟩
    · exact absurd hint hQnot
    · exact h1
    · exact absurd (hQ.symm.trans hk) (openSide_ne_vertex P ht0 ht1 (k + 1))
  obtain ⟨hc1, hc3⟩ := head_classify D idx hβ hγ hα hAsum
  haveI : HasFansC (relabelC D).toRegionDissection := (inferInstance : HasFansC D.toRegionDissection)
  have hidx' := relabel_hidx D idx (Equiv.swap 0 2) hidx
  have hnc' : NotComb (slen (relabelC D) 0) (slen (relabelC D) 1) (slen (relabelC D) 2) := by
    unfold relabelC
    rw [relabel_slen, relabel_slen, relabel_slen, swap02_0, swap02_1, swap02_2]
    exact notComb_swap hnc
  have hev : (cnt (relabelC D) (relabelCIdx idx) y.2.1 1 + cnt (relabelC D) (relabelCIdx idx) y.2.1 2) % 2 = 0 := by
    have e1 := relabel_cnt D idx (Equiv.swap 0 2) y.2.1 1
    have e2 := relabel_cnt D idx (Equiv.swap 0 2) y.2.1 2
    rw [swap02_1] at e1
    rw [swap02_2] at e2
    show (cnt (relabel D (Equiv.swap 0 2)) (relabelIdx idx (Equiv.swap 0 2)) y.2.1 1 + cnt (relabel D (Equiv.swap 0 2)) (relabelIdx idx (Equiv.swap 0 2)) y.2.1 2) % 2 = 0
    rw [e1, e2]
    omega
  have hxS' : TriStep ((relabelC D).tile x.1) (toV2 (P.e i)) x.2.1 y.2.1 := by rw [← hxy]; exact hxS
  have hd' : (dist x.2.1 x.2.2 = slen D 2) ↔ ¬ (dist y.2.1 y.2.2 = slen D 2) := hd
  have hx' : dist x.2.1 y.2.1 = dist x.2.1 x.2.2 := by rw [hxy]
  have hdiff : ¬ (dist y.2.1 y.2.2 = slen (relabelC D) 0 ↔ dist x.2.1 y.2.1 = slen (relabelC D) 0) := by
    rw [relabelC_slen0, hx']
    intro h
    by_cases hp : dist y.2.1 y.2.2 = slen D 2
    · exact (hd'.mp (h.mp hp)) hp
    · exact hp (h.mpr (hd'.mpr hp))
  have hyS' : TriStep ((relabelC D).tile y.1) (toV2 (P.e i)) y.2.1 y.2.2 := hyS
  have := junction_edge (relabelC D) (relabelCIdx idx) hidx' hnc' P hreg i ht0 ht1 hQ hxS' hyS' hdiff hev
  obtain ⟨H', hH'⟩ := this
  refine ⟨H', ?_⟩
  rw [relabelC_slen0] at hH'
  exact hH'

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.g5_of_steps

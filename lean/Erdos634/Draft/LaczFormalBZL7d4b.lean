-- Draft/LaczFormalBZL7d4b.lean -- Beeson-Zhang (arXiv 2604.01314v1) Lemma 3.4, the core, formal for a polygon with POSSIBLY NON-REGULAR corners:
--   `caseG_of_pi`  : the hypotheses `CaseG (relabelC D) ...` of the Gamma_c theory built WITHOUT the `CaseC` field "#alpha = #beta at every point" (false at a corner such as 2 alpha); only the parity of
--                    the number of alpha/beta corners at points of angle sum pi is needed, and that is `#alpha = #beta` there (alpha not in Q pi);
--   `sides_all_c`  : `NotComb c b a` (no c-relation), no gamma at any polygon vertex  ==>  every side of the polygon is a positive integer multiple of `c`
--                    (status chain along each side = all tile edges on it have length c, or none; "none" is excluded by `side_has_c`).
-- NOTE, UNAUDITED.  Credit: Beeson-Zhang (arXiv 2604.01314v1, Lemma 3.4), Laczkovich (DCG 48 (2012), Lemmas 4.4-4.7), Beeson.
import Erdos634.Draft.LaczFormalBZL7d4a

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

theorem caseG_of_pi (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hnc : NotComb (slen D 2) (slen D 1) (slen D 0))
    (hγ : D.model.angleAt 2 = 2 * Real.pi / 3) (hαβ : D.model.angleAt 0 + D.model.angleAt 1 = Real.pi / 3)
    (hα : ¬ ∃ r : ℚ, D.model.angleAt 0 = (r : ℝ) * Real.pi) : CaseG (relabelC D) (relabelCIdx idx) := by
  refine ⟨relabel_hidx D idx _ hidx, relabel_hidxA D idx _ hidxA, ?_, ?_⟩
  · unfold relabelC
    rw [relabel_slen, relabel_slen, relabel_slen, swap02_0, swap02_1, swap02_2]
    exact hnc
  · intro X hX
    have e0 := relabel_cnt D idx (Equiv.swap 0 2) X 0
    have e1 := relabel_cnt D idx (Equiv.swap 0 2) X 1
    have e2 := relabel_cnt D idx (Equiv.swap 0 2) X 2
    rw [swap02_0] at e0; rw [swap02_1] at e1; rw [swap02_2] at e2
    have hsum : ∑ l, (cnt D idx X l : ℝ) * D.model.angleAt l = Real.pi := by
      rw [← hX]
      have : ∀ l, (cnt (relabelC D) (relabelCIdx idx) X l : ℝ) * (relabelC D).model.angleAt l
          = (cnt D idx X (Equiv.swap 0 2 l) : ℝ) * D.model.angleAt (Equiv.swap 0 2 l) := by
        intro l
        unfold relabelC relabelCIdx
        rw [relabel_cnt]
        exact congrArg _ (relabel_angleAt D (Equiv.swap 0 2) l)
      simp only [this]
      exact (Equiv.sum_comp (Equiv.swap (0 : Fin 3) 2) (fun l => (cnt D idx X l : ℝ) * D.model.angleAt l)).symm
    have hexp : ∑ l, (cnt D idx X l : ℝ) * D.model.angleAt l = (cnt D idx X 0 : ℝ) * D.model.angleAt 0 + (cnt D idx X 1 : ℝ) * D.model.angleAt 1 + (cnt D idx X 2 : ℝ) * D.model.angleAt 2 := by
      rw [Fin.sum_univ_three]
    have := type_arith hαβ hγ hα (cnt D idx X 0) (cnt D idx X 1) (cnt D idx X 2) 3 (by rw [← hexp, hsum]; push_cast; ring)
    show (cnt (relabelC D) (relabelCIdx idx) X 1 + cnt (relabelC D) (relabelCIdx idx) X 2) % 2 = 0
    unfold relabelC relabelCIdx at *
    rw [e1, e2]
    omega

/-- **Every side of the polygon is a positive integer multiple of `c`** (Beeson-Zhang, Lemma 3.4: "the boundary is a union of only c-edges"), when there is no `c`-relation and no polygon vertex carries a `γ`. -/
theorem sides_all_c (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hnc : NotComb (slen D 2) (slen D 1) (slen D 0))
    (hγ : D.model.angleAt 2 = 2 * Real.pi / 3) (hαβ : D.model.angleAt 0 + D.model.angleAt 1 = Real.pi / 3)
    (hα : ¬ ∃ r : ℚ, D.model.angleAt 0 = (r : ℝ) * Real.pi)
    (hcorn : ∀ k : Fin M, cnt D idx (P.v (k + 1)) 2 = 0) :
    ∀ i : Fin M, ∃ m : ℕ, 0 < m ∧ P.side i = m * slen D 2 := by
  classical
  intro i
  have hG := caseG_of_pi D idx hidx hidxA hnc hγ hαβ hα
  set D' := relabelC D with hD'
  set idx' := relabelCIdx idx with hidx'
  haveI : HasFansC D'.toRegionDissection := (inferInstance : HasFansC D.toRegionDissection)
  have hD'0 : slen D' 0 = slen D 2 := relabelC_slen0 D
  obtain ⟨L, e0, el, hW, hh, hl, hs1, hs2, hT0, hT1⟩ := edge_data D P hreg i
  have hU : ∃ s : ℝ, 0 ≤ s ∧ toV2 (P.v i - P.v i) = (s * (toV2 (P.e i)).1, s * (toV2 (P.e i)).2) :=
    ⟨0, le_rfl, by unfold toV2; ext <;> simp⟩
  have hchain : ∀ e ∈ L, (dist e.2.1 e.2.2 = slen D 2 ↔ dist e0.2.1 e0.2.2 = slen D 2) := by
    intro e he
    have := walk_status_chain D' idx' hG P hreg i rfl hW hU e0 hh e he
    rwa [hD'0] at this
  obtain ⟨e, he, hec⟩ := side_has_c D P hreg idx hidx hidxA hγ hcorn i hW e0 hh
  have hc0 : dist e0.2.1 e0.2.2 = slen D 2 := (hchain e he).mp hec
  have hall : ∀ e ∈ L, dist e.2.1 e.2.2 = slen D 2 := fun e he => (hchain e he).mpr hc0
  have hsum := walkT_dist_sum hW
  have hLne : L ≠ [] := by
    intro hL0
    rw [hL0] at hh; simp at hh
  have hsumA : (L.map fun e => dist e.2.1 e.2.2).sum = (L.map fun e => dist e.2.1 e.2.2).length • slen D 2 :=
    List.sum_eq_card_nsmul _ _ (fun x hx => by
      obtain ⟨e', he', rfl⟩ := List.mem_map.mp hx
      exact hall e' he')
  rw [List.length_map, nsmul_eq_mul] at hsumA
  exact ⟨L.length, List.length_pos_of_ne_nil hLne, by rw [ConvPoly.side, ← hsum, hsumA]⟩

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.caseG_of_pi
#print axioms Erdos634.Draft.LaczFormal.RG.sides_all_c

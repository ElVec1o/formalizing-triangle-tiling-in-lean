-- Draft/LaczFormalIIcWN91.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3, Lemma 6.2): AN EDGE OF Gamma_except MISSES THE EDGES OF Gamma_kite (printed: "Clearly, the segment VW is in the exterior of C1 (except the points V and W)").
-- `gexc_open_miss_gkite`: if `V` is an inner point of an edge `X -> Y` of Gamma_except then `V` is on no (closed) edge `A -> B` of Gamma_kite.
-- Route: endpoints of the kite edge are Gamma_kite vertices, excluded by `gexc_interior_not_kite` (printed (i)); an inner point of a non-parallel kite side is excluded by `no_inner_cross` (B1);
-- a parallel kite side is a side of a tile `t` on the left of `d` (`TriStep.of_par`, using the other tile of the kite if the sides are oppositely directed), whose labels at both ends are `alpha`, `beta`, while the
-- left element of the edge at `V` has `gamma` at its head (`EndLeftG`): the two tiles coincide (`left_tile_eq_inner` / `left_tile_eq_head`), a contradiction with the labels or with `inner_not_vertex`.
-- NOTE, UNAUDITED.  Hypotheses: the Case IIc block + AngGen.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN90
import Erdos634.Draft.LaczFormalIIcSharp1
import Erdos634.Draft.LaczFormalRG12GExcWalk
import Erdos634.Draft.LaczFormalIIcL8l
import Erdos634.Draft.LaczFormalIIcL8k

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

/-- The left element of an edge of Gamma_except at an inner point `V` cannot be a tile `t` having `V` in its open side along `d` with labels `<> gamma` at both ends of that side. -/
theorem endleft_contra (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {d : V2} {V : Plane}
    (hL : EndLeftG D idx d V) {t : Fin N} {U U' : Plane} (ht : TriStep (D.tile t) d U U') (hV : V ∈ openSegment ℝ U U')
    (hlab : ∀ k, ((D.tile t).pts k = U ∨ (D.tile t).pts k = U') → idx t k ≠ 2) : False := by
  obtain ⟨iL, A0, B0, hS, hcase⟩ := hL
  rcases hcase with ⟨hVB, k, hk, hk2⟩ | ⟨hVo, k, hk, hk2⟩
  · -- V is the head of the left element
    subst hVB
    have heq := left_tile_eq_head D.toRegionDissection hS ht hV
    subst heq
    obtain ⟨kk, f, g, hkk, hf, hfk, hgk, hgf, hpar, hleft⟩ := hS
    obtain ⟨kk1, f1, g1, hkk1, hf1, hfk1, hgk1, hgf1, hpar1, hleft1⟩ := ht
    exact inner_not_vertex (D.tile iL) hfk1.symm (by rw [hkk1, hf1]; exact hV) (by rw [hf])
  · have heq := left_tile_eq_inner D.toRegionDissection hS ht hVo hV
    subst heq
    obtain ⟨kk, f, g, hkk, hf, hfk, hgk, hgf, hpar, hleft⟩ := hS
    obtain ⟨kk1, f1, g1, hkk1, hf1, hfk1, hgk1, hgf1, hpar1, hleft1⟩ := ht
    have hu := tri_inner_side_unique (D.tile iL) hfk.symm hfk1.symm hkk hf hkk1 hf1 hVo hV
    rcases hu with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · -- B0 = U'
      apply hlab k (Or.inr _) hk2
      rw [← hf1, ← hb] at *
      rw [hk]; exact hf.symm.trans (by rw [hb])
    · apply hlab k (Or.inl _) hk2
      rw [hk, ← hf, hb, hkk1]

set_option maxHeartbeats 3200000 in
/-- **An edge of Gamma_except misses the edges of Gamma_kite.** -/
theorem gexc_open_miss_gkite [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (G : AngGen (fun l => D.model.angleAt l))
    {X Y V A B : Plane} (hE : GExc D idx X Y) (hV : V ∈ openSegment ℝ X Y) (hK : GKite D idx A B) (hVK : V ∈ segment ℝ A B) : False := by
  classical
  by_cases hVA : V = A
  · subst hVA
    exact gexc_interior_not_kite D P hreg idx hC hab hac h1 h3 G hE hV (Or.inr ⟨B, hK⟩)
  by_cases hVB : V = B
  · subst hVB
    exact gexc_interior_not_kite D P hreg idx hC hab hac h1 h3 G hE hV (Or.inl ⟨A, hK⟩)
  have hVo : V ∈ openSegment ℝ A B := mem_openSegment_of_ne_left_right (Ne.symm hVA) (Ne.symm hVB) hVK
  obtain ⟨d, hd0, hnb, hpar, ⟨Z, L, T, v, WU, hT, hQd, hv0, hvT⟩, hL, hR, -, -⟩ := gexc_inner_split D idx hE hV
  obtain ⟨i, j, dk, kk, f, kk', f', hij, hSi, hSj, hk, hf, hik, hif, hk', hf', hjk, hjf⟩ := hK
  by_cases hnp : crs dk d = 0
  · -- parallel: the kite side lies along d
    have hdk0 : dk ≠ 0 := tristep_dir_ne hSi
    have hdt : dt dk d ≠ 0 := by
      intro h0
      have := crs_dt_sq dk d
      rw [hnp, h0] at this
      have h1' := nsq_pos hdk0
      have h2' := nsq_pos hd0
      nlinarith
    rcases lt_or_gt_of_ne hdt with hneg | hpos
    · -- opposite directions: use the other tile of the kite
      have hp : Par (neg2 dk) d := by
        refine ⟨?_, ?_⟩
        · unfold crs at hnp; unfold crs neg2; simp only; linarith
        · unfold dt at hneg; unfold dt neg2; simp only; linarith
      have hSj' : TriStep (D.tile j) d B A := TriStep.of_par hp.symm hSj
      refine endleft_contra D idx hL hSj' (by rw [openSegment_symm]; exact hVo) ?_
      intro k0 hk0
      have hinj := (D.tile j).indep.injective
      rcases hk0 with h | h
      · have : k0 = kk' := hinj (h.trans hk'.symm); rw [this, hjk]; decide
      · have : k0 = f' := hinj (h.trans hf'.symm); rw [this, hjf]; decide
    · have hp : Par dk d := ⟨hnp, hpos⟩
      have hSi' : TriStep (D.tile i) d A B := TriStep.of_par hp.symm hSi
      refine endleft_contra D idx hL hSi' hVo ?_
      intro k0 hk0
      have hinj := (D.tile i).indep.injective
      rcases hk0 with h | h
      · have : k0 = kk := hinj (h.trans hk.symm); rw [this, hik]; decide
      · have : k0 = f := hinj (h.trans hf.symm); rw [this, hif]; decide
  · exact no_inner_cross D.toRegionDissection hSi hVo hd0 WU hT hQd hv0 hvT hnp

#print axioms gexc_open_miss_gkite

end Erdos634.Draft.LaczFormal.RG

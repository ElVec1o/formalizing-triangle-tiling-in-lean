-- Draft/LaczFormalIIcG11g.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.3, Lemma 6.3 INCLUDING the printed inequality of (v) (G11), and Case IIc for generic angles modulo ONLY Lemma 6.2 (NoKites).
--  `lemma63_two_full : Concl5 D P`  (two exceptional points; `Concl5` now accepts either label order, see the note in LaczFormalThm21Def: the paper's alpha, beta are interchangeable),
--  `lemma63_full : Concl7 D P \/ Concl5 D P`,
--  `iic_ang_g11 : IIcNoKites -> Thm21Concl T.C T.P` for regular polygon tilings of class IIc with `AngGen` model angles.
-- Inputs NOT proved: (1) `IIcNoKites` (Lemma 6.2 for generic angles); (2) the subclass of IIc where `AngGen` fails (alpha = beta; right angles and alpha or beta = gamma are vacuous, see G11-W); (3) [the IIc block is witnessed by GenWitK (204-tile octagon, genTiling_thm21) and IsoWitM].
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.1-6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcG11e
import Erdos634.Draft.LaczFormalIIcG11f

open scoped Classical Fin.NatCast
open EuclideanGeometry Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

set_option maxHeartbeats 25600000 in
/-- **Lemma 6.3, two exceptional points, with the printed inequality** (conclusion (v) of Theorem 2.1, labels free). -/
theorem lemma63_two_full {k : ℕ} [NeZero (2 * k)] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly (2 * k)) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (G : AngGen (fun l => D.model.angleAt l))
    (hcor : ∀ j : Fin (2 * k), cnt D idx (P.v j) 0 = 1 ∧ cnt D idx (P.v j) 1 = 1 ∧ cnt D idx (P.v j) 2 = 0)
    (hNK : kiteB D idx = ∅) (W : Fin (2 * k) → Plane) (hW : ∀ j, GExc D idx (P.v j) (W j)) (hdiff : ∃ j, W j ≠ W 0) : Concl5 D P := by
  obtain ⟨hrest, -⟩ := lemma63_two D P hreg idx hC hab hac h1 h3 G hcor hNK W hW hdiff
  obtain ⟨a, b, s0, hab', hg, hineq⟩ := g11_two D P hreg idx hC hab hac h1 h3 G hcor hNK W hW hdiff
  have hαβγ := angleAt_sum D.model
  have hp0 := model_angle_pos' D 0
  have hp1 := model_angle_pos' D 1
  have hp2 := model_angle_pos' D 2
  have hsin0 : 0 < Real.sin (D.model.angleAt 0) := Real.sin_pos_of_pos_of_lt_pi hp0 (by linarith)
  have hsin1 : 0 < Real.sin (D.model.angleAt 1) := Real.sin_pos_of_pos_of_lt_pi hp1 (by linarith)
  have hsymm : ∀ i : Fin (2 * k), P.side i = P.side (i + (k : Fin (2 * k))) := fun i => by
    have := hrest.2.2.2.2 i; rwa [ofNat_cast_fin'] at this
  rcases hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨q, hq, s, rev, aa, e1, e2, e3⟩ := reading_exists P hrest.2.1 hsymm _ _ hsin0 hsin1 s0 hg hineq
    exact ⟨k, hrest.1, hrest.2.1, hrest.2.2.1, hrest.2.2.2.1, hrest.2.2.2.2, q, hq, s, rev, aa, e1, e2, e3⟩
  · obtain ⟨q, hq, s, rev, aa, e1, e2, e3⟩ := reading_exists P hrest.2.1 hsymm _ _ hsin1 hsin0 s0 hg hineq
    exact ⟨k, hrest.1, hrest.2.1, hrest.2.2.1, hrest.2.2.2.1, hrest.2.2.2.2, q, hq.symm, s, rev, aa, e1, e2, e3⟩

/-- **Lemma 6.3 with the printed inequality** (conditional on `kiteB = empty`). -/
theorem lemma63_full [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (G : AngGen (fun l => D.model.angleAt l))
    (hcor : ∀ j : Fin M, cnt D idx (P.v j) 0 = 1 ∧ cnt D idx (P.v j) 1 = 1 ∧ cnt D idx (P.v j) 2 = 0)
    (hNK : kiteB D idx = ∅) (W : Fin M → Plane) (hW : ∀ j, GExc D idx (P.v j) (W j)) :
    Concl7 D P ∨ Concl5 D P := by
  by_cases hdiff : ∃ j, W j ≠ W 0
  · obtain ⟨k, rfl⟩ := M_even_of_two D P hreg idx hC hab hac h1 h3 G hcor hNK W hW hdiff
    exact Or.inr (lemma63_two_full D P hreg idx hC hab hac h1 h3 G hcor hNK W hW hdiff)
  · push Not at hdiff
    exact Or.inl (lemma63_one D P hreg idx hC hab hac h1 h3 G hcor W hW (fun j => hdiff j))

set_option maxHeartbeats 12800000 in
/-- **Case IIc, generic angles, modulo Lemma 6.2 (NoKites) ONLY**: Theorem 2.1's conclusion. -/
theorem iic_ang_g11 (hNK : IIcNoKites) {N M : ℕ} [NeZero M] (T : PolyTiling N M) (hreg : RegularPQ T.C) (hex : Thm21Excluded4 T)
    (hAng : AngGen (fun l => T.C.model.angleAt l)) : Thm21Concl T.C T.P := by
  classical
  obtain ⟨h1, h3, hab, hac⟩ := hex
  rcases lemma61 T hreg h1 h3 hab hac with hc1 | hangs
  · exact Or.inl hc1
  · obtain ⟨idx, hA, hcnt⟩ := hreg
    haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
    have hC : CaseC T.C idx := ⟨idx_dist_of_angle T.C idx hA, hA, fun X => hcnt X, notComb_c_of_comm (slen_pos T.C 2) hab hac⟩
    rcases lemma61_core T.C T.P T.region_eq idx hC h1 h3 with hP | ⟨-, a, ha1, -, -⟩
    · have hcor := corners_of_cntP0 T.C T.P T.region_eq idx hC h1 hP
      have hW : ∀ j : Fin M, ∃ W, GExc T.C idx (T.P.v j) W := fun j => gexc_start_of_corner T.C T.P T.region_eq idx hC h1 h3 hcor j
      choose W hW using hW
      have hNK' := hNK N M T idx hC h1 h3 hab hac hAng hcor
      rcases lemma63_full T.C T.P T.region_eq idx hC hab hac h1 h3 hAng hcor hNK' W hW with h7 | h5
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h7))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5))))
    · exfalso
      have := hangs (a + 1)
      have ha1' : T.P.angle (a + 1) = angleAt T.C.model 2 := ha1
      rw [ha1'] at this
      linarith

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.lemma63_two_full
#print axioms Erdos634.Draft.LaczFormal.RG.lemma63_full
#print axioms Erdos634.Draft.LaczFormal.RG.iic_ang_g11

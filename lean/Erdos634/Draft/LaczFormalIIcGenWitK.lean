-- Draft/LaczFormalIIcGenWitK.lean -- WITNESS of the GENERIC Case IIc block (alpha != beta), step K: `kiteB genDiss idx = empty` (the 204-tile octagon has no kite edge), hence `lemma63_full` applies UNCONDITIONALLY to it
-- and returns `Concl5` (Laczkovich's type (v)); `Thm21Concl genTiling.C genTiling.P` holds through the Lean pipeline.  NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcGenWitJ
import Erdos634.Draft.LaczFormalIIcGenWitD3
import Erdos634.Draft.LaczFormalRG12GKite

namespace Erdos634.Draft.LaczFormal.GenWit

open Erdos634.Geometry Erdos634.CertCoord Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Thm21 Erdos634.Draft.LaczFormal.RG Erdos634.Draft.LaczFormal.Graph Z2

theorem abL_getElem (i : Fin 204) : abL[i.val]'(by simp [abL, tileTab_length]) = ((TT i).p0, (TT i).p1) := by
  unfold abL
  rw [List.getElem_map, TT_eq]

theorem genDiss_noGKite (X Y : Plane) : ¬ GKite genDiss idx X Y := by
  rintro ⟨i, j, d, kk, f, kk', f', hij, -, -, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp only [idx, Equiv.Perm.coe_one, id_eq] at h3 h4 h7 h8
  subst h3 h4 h7 h8
  have e0 : (TT i).p0 = (TT j).p0 := by
    apply ptR_inj
    have a : (triZ (TT i)).pts 0 = ptR ((TT i).pt 0) := triZ_pts (TT_props i).1 0
    have b : (triZ (TT j)).pts 0 = ptR ((TT j).pt 0) := triZ_pts (TT_props j).1 0
    have h1' : (triZ (TT i)).pts 0 = X := h1
    have h6' : (triZ (TT j)).pts 0 = X := h6
    exact (a.symm.trans (h1'.trans h6'.symm)).trans b
  have e1 : (TT i).p1 = (TT j).p1 := by
    apply ptR_inj
    have a : (triZ (TT i)).pts 1 = ptR ((TT i).pt 1) := triZ_pts (TT_props i).1 1
    have b : (triZ (TT j)).pts 1 = ptR ((TT j).pt 1) := triZ_pts (TT_props j).1 1
    have h2' : (triZ (TT i)).pts 1 = Y := h2
    have h5' : (triZ (TT j)).pts 1 = Y := h5
    exact (a.symm.trans (h2'.trans h5'.symm)).trans b
  have := (ab_nodup.getElem_inj_iff (i := i.val) (j := j.val)).mp (by
    rw [abL_getElem i, abL_getElem j]
    exact Prod.ext e0 e1)
  exact hij (Fin.ext this)

open scoped Classical in
theorem genDiss_kiteB : kiteB genDiss idx = ∅ := by
  unfold kiteB
  apply Finset.filter_eq_empty_iff.mpr
  rintro Y - ⟨⟨Z, hZ⟩, -⟩
  exact genDiss_noGKite Y Z hZ

/-- **`lemma63_full` applied to the 204-tile octagon, all hypotheses discharged**: conclusion (v). -/
theorem genDiss_concl5 : Concl5 genDiss octP := genBlock_concl5 genDiss_kiteB

/-- **Theorem 2.1's conclusion on the 204-tile octagon**, through the Lean pipeline (this is the paper's own type-(v) example). -/
theorem genTiling_thm21 : Thm21Concl genTiling.C genTiling.P :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl genDiss_concl5))))

end Erdos634.Draft.LaczFormal.GenWit

#print axioms Erdos634.Draft.LaczFormal.GenWit.genDiss_kiteB
#print axioms Erdos634.Draft.LaczFormal.GenWit.genDiss_concl5
#print axioms Erdos634.Draft.LaczFormal.GenWit.genTiling_thm21

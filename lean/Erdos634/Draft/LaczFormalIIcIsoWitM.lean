-- Draft/LaczFormalIIcIsoWitM.lean -- NON-VACUITY witness for `IIcIsoCore`, step M: the octagon as a `PolyTiling 8 8`; `RegularPQ`, `Thm21Excluded4`, `AngGenI`; `lemma63_one_iso` and `iic_iso_claim` applied to it.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcIsoWitL

open Erdos634.Geometry Erdos634.CertCoord Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Thm21 Erdos634.Draft.LaczFormal.RG Erdos634.Draft.LaczFormal.Graph

namespace Erdos634.Draft.LaczFormal.IsoWit

/-- the regular octagon tiling as a `PolyTiling 8 8` -/
noncomputable def octTiling : PolyTiling 8 8 where
  C := octDiss
  P := oct
  region_eq := rfl

theorem octTiling_regular : RegularPQ octTiling.C :=
  ⟨idx, octDiss_hidxA, octDiss_hregc⟩

theorem octTiling_excluded4 : Thm21Excluded4 octTiling :=
  ⟨octDiss_angle2_lt, octDiss_angle2_ne, octDiss_comm, octDiss_notComm⟩

theorem octDiss_angGenI : AngGenI (fun l => octDiss.model.angleAt l) := by
  have hs := Erdos634.Draft.LaczFormal.angleAt_sum octDiss.model
  have h2 := octDiss_angle2
  have h01 : octDiss.model.angleAt 0 = octDiss.model.angleAt 1 := octDiss_angle01
  have hpi := Real.pi_pos
  have ha : octDiss.model.angleAt 0 = 3 * Real.pi / 8 := by linarith
  have hb : octDiss.model.angleAt 1 = 3 * Real.pi / 8 := by linarith
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, h01⟩
  · intro l; fin_cases l
    · show 0 < octDiss.model.angleAt 0; rw [ha]; positivity
    · show 0 < octDiss.model.angleAt 1; rw [hb]; positivity
    · show 0 < octDiss.model.angleAt 2; rw [h2]; positivity
  · show octDiss.model.angleAt 0 + octDiss.model.angleAt 1 + octDiss.model.angleAt 2 = _; exact hs
  · show octDiss.model.angleAt 0 ≠ octDiss.model.angleAt 2; rw [ha, h2]; intro h; linarith
  · show octDiss.model.angleAt 1 ≠ octDiss.model.angleAt 2; rw [hb, h2]; intro h; linarith
  · show octDiss.model.angleAt 0 ≠ _; rw [ha]; intro h; linarith
  · show octDiss.model.angleAt 1 ≠ _; rw [hb]; intro h; linarith
  · show octDiss.model.angleAt 2 ≠ _; rw [h2]; intro h; linarith

/-- `lemma63_one_iso` is non-vacuous: it applies to the octagon (all exceptional points are the centre) and returns `Concl7`. -/
theorem lemma63_one_iso_octagon : Concl7 octDiss oct :=
  lemma63_one_iso octDiss oct rfl idx octDiss_caseC octDiss_comm octDiss_notComm octDiss_angle2_lt octDiss_angle2_ne octDiss_angGenI
    (fun j => ⟨octDiss_cnt0 j, octDiss_cnt1 j, octDiss_cnt2 j⟩) (fun _ => mkPt 0 0) (fun j => gexc_at j) (fun _ => rfl)

/-- `iic_iso_claim` is non-vacuous: it applies to the octagon `PolyTiling 8 8` and returns Theorem 2.1's conclusion. -/
theorem iic_iso_claim_octagon : Thm21Concl octTiling.C octTiling.P :=
  iic_iso_claim 8 8 octTiling octTiling_regular octTiling_excluded4 octDiss_angle01

end Erdos634.Draft.LaczFormal.IsoWit

#print axioms Erdos634.Draft.LaczFormal.IsoWit.iic_iso_core_octagon
#print axioms Erdos634.Draft.LaczFormal.IsoWit.lemma63_one_iso_octagon
#print axioms Erdos634.Draft.LaczFormal.IsoWit.iic_iso_claim_octagon

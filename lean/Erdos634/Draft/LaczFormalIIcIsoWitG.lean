-- Draft/LaczFormalIIcIsoWitG.lean -- NON-VACUITY witness for `IIcIsoCore`, step G: model side lengths (1, 1, s) with s/1 irrational (`Comm`, `NotComb`), model angles (3pi/8, 3pi/8, pi/4).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcIsoWitF

open Erdos634.Geometry Erdos634.CertCoord Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Thm21 Erdos634.Draft.LaczFormal.RG

namespace Erdos634.Draft.LaczFormal.IsoWit

theorem hh_two : 2 * hh = Real.sqrt 2 := by unfold hh; ring

/-- the base of the model tile -/
theorem dist_V01 : dist (mkPt 1 0) (mkPt hh hh) ^ 2 = 2 - 2 * hh := by
  rw [dist_sq_mkPt]; nlinarith [hh_sq]
theorem dist_V0O : dist (mkPt 1 0) (mkPt 0 0) = 1 := by
  have h := dist_sq_mkPt 1 0 0 0
  have := dist_nonneg (x := mkPt 1 0) (y := mkPt 0 0)
  nlinarith
theorem dist_V1O : dist (mkPt hh hh) (mkPt 0 0) = 1 := by
  have h := dist_sq_mkPt hh hh 0 0
  have := dist_nonneg (x := mkPt hh hh) (y := mkPt 0 0)
  nlinarith [hh_sq]

theorem model_pts : (octDiss.model).pts = ![mkPt 1 0, mkPt hh hh, mkPt 0 0] := by
  show (tile 0).pts = _
  rw [tile_pts]
  simp [cx, cy]

theorem slen0 : RG.slen octDiss 0 = 1 := by
  unfold RG.slen; rw [model_pts]; simpa using dist_V1O
theorem slen1 : RG.slen octDiss 1 = 1 := by
  unfold RG.slen; rw [model_pts]; simpa [dist_comm] using dist_V0O
theorem slen2_sq : RG.slen octDiss 2 ^ 2 = 2 - 2 * hh := by
  unfold RG.slen; rw [model_pts]; simpa using dist_V01

theorem slen2_irr (r p : ℕ) (hr : 0 < r) : (r : ℝ) * RG.slen octDiss 2 ≠ p := by
  intro h
  have hr' : (0:ℝ) < r := by exact_mod_cast hr
  have hsq := slen2_sq
  have h2 : (r : ℝ) ^ 2 * (2 - 2 * hh) = (p : ℝ) ^ 2 := by
    rw [← hsq, ← h]; ring
  apply irrational_sqrt_two
  refine ⟨2 - (p : ℚ) ^ 2 / (r : ℚ) ^ 2, ?_⟩
  push_cast
  rw [← hh_two]
  field_simp
  nlinarith [h2]

theorem octDiss_comm : Comm (RG.slen octDiss 0) (RG.slen octDiss 1) := ⟨1, 1, one_pos, one_pos, by rw [slen0, slen1]⟩

theorem octDiss_notComm : ¬ Comm (RG.slen octDiss 0) (RG.slen octDiss 2) := by
  rintro ⟨p, q, hp, hq, h⟩
  rw [slen0] at h
  exact slen2_irr q p hq (by linarith)

theorem octDiss_notComb : Erdos634.Draft.LaczFormal.Graph.NotComb (RG.slen octDiss 2) (RG.slen octDiss 1) (RG.slen octDiss 0) := by
  intro r p q hr h
  rw [slen0, slen1] at h
  exact slen2_irr r (p + q) hr (by push_cast; linarith)

end Erdos634.Draft.LaczFormal.IsoWit

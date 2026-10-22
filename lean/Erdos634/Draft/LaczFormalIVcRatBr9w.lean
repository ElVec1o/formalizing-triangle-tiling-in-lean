-- Draft/LaczFormalIVcRatBr9w.lean -- Laczkovich DCG 48 (2012), Sect. 8.3 (Subcase IVc, rational branch): NON-VACUITY of the bridge hypothesis bundle `BrHyp` (Br3c) and of `vwOf` (Br4b).
--   Witness: the two-tile 30-60-90 parallelogram `vTiling` (tile (a,b,c) = (2,1,sqrt 3), alpha = pi/2, beta = pi/6, gamma = pi/3; M = 4, regular, a ~ b, c not ~ a).
--   `vW_hint`: every c-edge (the shared diagonal) has an interior open-segment point (its midpoint (1, sqrt 3 / 2)); `brHyp_witness`: `BrHyp vTiling.C vTiling.P idx 1 0 1` for the idx of regularity;
--   `vwOf_witness`: the V/W tiling `vwOf` of the region exists.  CAVEAT: M = 4 and 2 tiles: it does NOT witness the hypotheses of `ivc_rat_final` (which has M >= 5); no tiling with M >= 5 and these data is exhibited.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 8.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIVcRatBr8a
import Erdos634.Draft.LaczFormalRG6IVcWit

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

noncomputable instance vTiling_fans : HasFansC vTiling.C.toRegionDissection := hasFansC_poly _ vTiling.P vTiling.region_eq

theorem vT_sq : vT ^ 2 = 3 := Real.sq_sqrt (by norm_num)

theorem dist_mkPt_sq (a b c d : ℝ) : dist (mkPt a b) (mkPt c d) ^ 2 = (a - c) ^ 2 + (b - d) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs, mkPt]

theorem t00 : (vTiling.C.tile 0).pts 0 = mkPt 1 0 := rfl
theorem t01 : (vTiling.C.tile 0).pts 1 = mkPt 1 vT := rfl
theorem t02 : (vTiling.C.tile 0).pts 2 = mkPt 0 0 := rfl
theorem t10 : (vTiling.C.tile 1).pts 0 = mkPt 1 vT := rfl
theorem t11 : (vTiling.C.tile 1).pts 1 = mkPt 1 0 := rfl
theorem t12 : (vTiling.C.tile 1).pts 2 = mkPt (1 + 1) vT := rfl

theorem vW_mid (i : Fin 2) (kk f : Fin 3) (hfk : f ≠ kk)
    (h : dist ((vTiling.C.tile i).pts kk) ((vTiling.C.tile i).pts f) = Real.sqrt 3) :
    (1 - 1 / 2 : ℝ) • (vTiling.C.tile i).pts kk + (1 / 2 : ℝ) • (vTiling.C.tile i).pts f = mkPt 1 (vT / 2) := by
  have h2 : dist ((vTiling.C.tile i).pts kk) ((vTiling.C.tile i).pts f) ^ 2 = 3 := by rw [h, Real.sq_sqrt (by norm_num)]
  have hv := vT_sq
  have hp := vT_pos
  revert hfk h h2
  fin_cases i <;> fin_cases kk <;> fin_cases f <;> intro hfk h h2 <;>
  simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue] at hfk h h2 ⊢ <;>
  simp only [t00, t01, t02, t10, t11, t12] at h2 ⊢ <;>
  first
  | exact absurd rfl hfk
  | (exfalso; rw [dist_mkPt_sq] at h2; nlinarith)
  | (ext j; fin_cases j <;> simp [mkPt] <;> ring)

theorem vW_hint : ∀ (i : Fin 2) (d : V2) (U V : Plane), TriStep (vTiling.C.tile i) d U V → dist U V = slen vTiling.C 2 →
    ∃ m ∈ openSegment ℝ U V, m ∈ interior vTiling.C.region := by
  intro i d U V hS hc
  obtain ⟨kk, f, g, hk, hf, hfk, -⟩ := hS
  rw [vDiss_slen2] at hc
  subst hk hf
  have hm := vW_mid i kk f hfk hc
  refine ⟨_, ⟨1 - 1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩, ?_⟩
  rw [hm]
  show mkPt 1 (vT / 2) ∈ interior vTiling.P.carrier
  apply vTiling.P.interior_of_pos
  have hv := vT_sq
  have hp := vT_pos
  intro j
  fin_cases j <;> simp [vTiling, pTiling, parPoly, ConvPoly.c, ConvPoly.e, cross2, mkPt] <;> nlinarith

theorem vTiling_data : ∃ idx : Fin 2 → Equiv.Perm (Fin 3), CaseC vTiling.C idx := by
  obtain ⟨idx, hA, hcnt⟩ := (pDiss_regular (b := 1) (s := 1) (t := vT) one_pos vT_pos : RegularPQ vTiling.C)
  exact ⟨idx, ⟨idx_dist_of_angle vTiling.C idx hA, hA, fun X => hcnt X,
    notComb_c_of_comm (slen_pos vTiling.C 2) vTiling_comm vTiling_notComm⟩⟩

/-- The hypothesis bundle `BrHyp` is satisfiable: the two-tile parallelogram (s = 1, rho = 0, pi = 1). -/
theorem brHyp_witness : ∃ idx : Fin 2 → Equiv.Perm (Fin 3), BrHyp vTiling.C vTiling.P idx 1 0 1 := by
  obtain ⟨idx, hC⟩ := vTiling_data
  refine ⟨idx, hC, vTiling.region_eq, vTiling_comm, vTiling_notComm, one_pos, by decide, by decide, by decide, ?_, ?_, ?_, vW_hint⟩
  · rw [vDiss_slen0]; norm_num
  · rw [vDiss_slen1]
  · rw [vDiss_slen2]; norm_num

/-- ... and the V/W tiling of the bridge exists for it. -/
theorem vwOf_witness : ∃ (idx : Fin 2 → Equiv.Perm (Fin 3)) (h : BrHyp vTiling.C vTiling.P idx 1 0 1),
    Nonempty (VWTiling 1 vTiling.C.region (KIdx h) (RIdx h × Fin 2)) := by
  obtain ⟨idx, h⟩ := brHyp_witness
  exact ⟨idx, h, ⟨vwOf h⟩⟩

#print axioms Erdos634.Draft.LaczFormal.RG.brHyp_witness
#print axioms Erdos634.Draft.LaczFormal.RG.vwOf_witness

end Erdos634.Draft.LaczFormal.RG

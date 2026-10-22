-- Draft/LaczFormalIIcWN113.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3, Fig. 5, 8), R4: the arrival direction of a chord at a CONVEX vertex of the cycle in the form of oriented rotations (`RotPos`).
-- `arrive_rot`: for a convex vertex `Y = C k` (`sigma * extAng = gamma`) and an edge `U -> Y` of Gamma_except: if `sigma = 1` the cycle edges satisfy `RotPos (Z-Y) (X-Y) (a+b)` and the chord `RotPos (Z-Y) (U-Y) (pi+b)`;
-- if `sigma = -1`: `RotPos (X-Y) (Z-Y) (a+b)`, `RotPos (X-Y) (U-Y) (pi+a)` (`a`, `b` = model angles alpha, beta).  From `gexc_arrive_dir` (WN92) and `ext_caseA/B` (WN89), `toC_par_rot` (WN94).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN112
import Erdos634.Draft.LaczFormalIIcWN95

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG
open Erdos634.Draft.LaczFormal.WN (edgeSet wind extAng OrientOK RotPos)

local notation "tc" => Erdos634.Draft.LaczFormal.WN.toC

variable {N M : ℕ}

set_option maxHeartbeats 6400000 in
theorem arrive_rot [NeZero N] [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3)
    (G : AngGen (fun l => D.model.angleAt l))
    {m : ℕ} [NeZero m] (C : Fin m → Plane) (hCy : ∀ k : Fin m, GKite D idx (C k) (C (k + 1))) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (k : Fin m) (hconv : σ * extAng (cyc C) k = D.model.angleAt 2) {U : Plane} (hU : GExc D idx U (C k)) :
    (σ = 1 ∧ RotPos (tc (C (k + 1)) - tc (C k)) (tc (C (k - 1)) - tc (C k)) (D.model.angleAt 0 + D.model.angleAt 1) ∧
        RotPos (tc (C (k + 1)) - tc (C k)) (tc U - tc (C k)) (Real.pi + D.model.angleAt 1)) ∨
    (σ = -1 ∧ RotPos (tc (C (k - 1)) - tc (C k)) (tc (C (k + 1)) - tc (C k)) (D.model.angleAt 0 + D.model.angleAt 1) ∧
        RotPos (tc (C (k - 1)) - tc (C k)) (tc U - tc (C k)) (Real.pi + D.model.angleAt 0)) := by
  have hXY : GKite D idx (C (k - 1)) (C k) := by simpa using hCy (k - 1)
  have hYZ := hCy k
  have hα := G.pos 0
  have hβ := G.pos 1
  have hγ := G.pos 2
  have hsum := G.sum
  have hne1 : tc (C (k - 1)) ≠ tc (C k) := fun e => gkite_ne D idx hXY (Erdos634.Draft.LaczFormal.WN.toC.injective e)
  have hne2 : tc (C (k + 1)) ≠ tc (C k) := fun e => gkite_ne D idx hYZ (Erdos634.Draft.LaczFormal.WN.toC.injective e).symm
  rcases gexc_arrive_dir D P hreg idx hC h1 h3 G hXY hYZ hU with ⟨hA, hP⟩ | ⟨hB, hP⟩
  · -- case A: Z - Y = rot (a+b) (X - Y), turn -gamma, so sigma = -1
    have hZ := toC_rot hA
    rw [toC_sub, toC_sub] at hZ
    have hext := Erdos634.Draft.LaczFormal.WN.ext_caseA (cyc C) k hα hβ (by linarith) hne1 (by simpa using hZ)
    have hσ1 : σ = -1 := by
      rcases hσ with h | h
      · exfalso; rw [h, hext] at hconv; linarith
      · exact h
    right
    refine ⟨hσ1, ⟨1, one_pos, by simpa using hZ⟩, ?_⟩
    have hP' : Graph.Par (toV2 (U - C k)) (Graph.rot (D.model.angleAt 0) (toV2 (C k - C (k - 1)))) := by
      have e : toV2 (C k - C (k - 1)) = neg2 (toV2 (C (k - 1) - C k)) := toV2_neg_sub _ _
      rw [e, rot_neg2']; exact hP
    obtain ⟨c, hc, hcw⟩ := toC_par_rot hP'
    rw [toC_sub, toC_sub] at hcw
    have hflip : RotPos (tc (C (k - 1)) - tc (C k)) (tc (C k) - tc (C (k - 1))) Real.pi := Erdos634.Draft.LaczFormal.WN.rotPos_flip _ _
    have h2 : RotPos (tc (C k) - tc (C (k - 1))) (tc U - tc (C k)) (D.model.angleAt 0) := ⟨c, hc, hcw⟩
    exact hflip.trans h2
  · -- case B: X - Y = rot (a+b) (Z - Y), turn +gamma, so sigma = 1
    have hX := toC_rot hB
    rw [toC_sub, toC_sub] at hX
    have hext := Erdos634.Draft.LaczFormal.WN.ext_caseB (cyc C) k hα hβ (by linarith) hne1 hne2 (by simpa using hX)
    have hσ1 : σ = 1 := by
      rcases hσ with h | h
      · exact h
      · exfalso; rw [h, hext] at hconv; linarith
    left
    refine ⟨hσ1, ⟨1, one_pos, by simpa using hX⟩, ?_⟩
    have hP' : Graph.Par (toV2 (U - C k)) (Graph.rot (D.model.angleAt 1) (toV2 (C k - C (k + 1)))) := by
      have e : toV2 (C k - C (k + 1)) = neg2 (toV2 (C (k + 1) - C k)) := toV2_neg_sub _ _
      rw [e, rot_neg2']; exact hP
    obtain ⟨c, hc, hcw⟩ := toC_par_rot hP'
    rw [toC_sub, toC_sub] at hcw
    have hflip : RotPos (tc (C (k + 1)) - tc (C k)) (tc (C k) - tc (C (k + 1))) Real.pi := Erdos634.Draft.LaczFormal.WN.rotPos_flip _ _
    have h2 : RotPos (tc (C k) - tc (C (k + 1))) (tc U - tc (C k)) (D.model.angleAt 1) := ⟨c, hc, hcw⟩
    exact hflip.trans h2

#print axioms arrive_rot

end Erdos634.Draft.LaczFormal.RG

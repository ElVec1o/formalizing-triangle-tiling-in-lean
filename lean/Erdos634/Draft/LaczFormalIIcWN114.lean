-- Draft/LaczFormalIIcWN114.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3, Fig. 8), R4: the OUTER corners `V_{i-1}`, `V_i` of a ring quadrilateral as oriented rotations.
-- From `spokes_angle` (Spoke5: the spoke makes the model angle `a` with the outgoing side and `b` with the incoming side of every corner of `A`, the same `(a, b)` at every corner) and the interiority of the ends `W_j`
-- (the chord lies to the LEFT of the counter-clockwise edges): `RotPos (V_{j+1} - V_j) (W_{j+1} - V_{j+1}) (pi - b)` and `RotPos (V_{j+1} - V_j) (V_j - W_j) (a + pi)`.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3, Fig. 6, 8), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN113
import Erdos634.Draft.LaczFormalIIcSpoke5
import Erdos634.Draft.LaczFormalIIcWN78

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG
open Erdos634.Draft.LaczFormal.WN (edgeSet wind extAng OrientOK RotPos sideFn)

local notation "tc" => Erdos634.Draft.LaczFormal.WN.toC

variable {N M : ℕ}

theorem angle_toC (p1 p2 p3 : Plane) :
    EuclideanGeometry.angle p1 p2 p3 = InnerProductGeometry.angle (tc p1 - tc p2) (tc p3 - tc p2) := by
  unfold EuclideanGeometry.angle
  rw [vsub_eq_sub, vsub_eq_sub, ← LinearIsometry.angle_map Erdos634.Draft.LaczFormal.WN.toC.toLinearIsometry]
  simp [map_sub]

theorem im_div_shift (P0 P1 z : ℂ) (h : P1 - P0 ≠ 0) : ((z - P1) / (P1 - P0)).im = ((z - P0) / (P1 - P0)).im := by
  have : (z - P1) / (P1 - P0) = (z - P0) / (P1 - P0) - 1 := by field_simp; ring
  rw [this, Complex.sub_im, Complex.one_im, sub_zero]

/-- The two outer rotations of the ring quadrilateral at index `j`. -/
theorem v_rot_of_angles [NeZero M] (P : ConvPoly M) (Wp : Fin M → Plane) (hWint : ∀ j, Wp j ∈ interior P.carrier)
    (a b : ℝ)
    (hin : ∀ j : Fin M, EuclideanGeometry.angle (P.v j) (P.v (j + 1)) (Wp (j + 1)) = b)
    (hout : ∀ j : Fin M, EuclideanGeometry.angle (P.v (j + 1)) (P.v j) (Wp j) = a) (j : Fin M) :
    RotPos (tc (P.v (j + 1)) - tc (P.v j)) (tc (Wp (j + 1)) - tc (P.v (j + 1))) (Real.pi - b) ∧
    RotPos (tc (P.v (j + 1)) - tc (P.v j)) (tc (P.v j) - tc (Wp j)) (a + Real.pi) := by
  have hu : tc (P.v (j + 1)) - tc (P.v j) ≠ 0 := by
    intro e
    exact Erdos634.Draft.LaczFormal.WN.convPoly_e_ne P j (Erdos634.Draft.LaczFormal.WN.toC.injective (sub_eq_zero.1 e))
  have hne : ∀ (i : Fin M) (l : Fin M), tc (Wp l) - tc (P.v i) ≠ 0 := by
    intro i l e
    have : Wp l = P.v i := Erdos634.Draft.LaczFormal.WN.toC.injective (sub_eq_zero.1 e)
    exact vertex_not_interior P i (this ▸ hWint l)
  constructor
  · -- at P1 = V_{j+1}
    have hsg : 0 < ((tc (Wp (j + 1)) - tc (P.v (j + 1))) / (tc (P.v (j + 1)) - tc (P.v j))).im := by
      rw [im_div_shift _ _ _ hu]
      have := Erdos634.Draft.LaczFormal.WN.convPoly_inside P (hWint (j + 1)) j
      rw [one_mul] at this
      exact this
    have hz1 : tc (P.v j) - tc (P.v (j + 1)) ≠ 0 := by
      intro e; apply hu; linear_combination -e
    have hneg : ((tc (Wp (j + 1)) - tc (P.v (j + 1))) / (tc (P.v j) - tc (P.v (j + 1)))).im < 0 := by
      have : (tc (Wp (j + 1)) - tc (P.v (j + 1))) / (tc (P.v j) - tc (P.v (j + 1))) =
          -((tc (Wp (j + 1)) - tc (P.v (j + 1))) / (tc (P.v (j + 1)) - tc (P.v j))) := by
        rw [show tc (P.v j) - tc (P.v (j + 1)) = -(tc (P.v (j + 1)) - tc (P.v j)) by ring, div_neg]
      rw [this, Complex.neg_im]; linarith
    have hang : InnerProductGeometry.angle (tc (P.v j) - tc (P.v (j + 1))) (tc (Wp (j + 1)) - tc (P.v (j + 1))) = b := by
      rw [← angle_toC]; exact hin j
    have h := Erdos634.Draft.LaczFormal.WN.rotPos_of_angle_neg hz1 (hne (j + 1) (j + 1)) hang hneg
    have hflip := Erdos634.Draft.LaczFormal.WN.rotPos_flip (tc (P.v (j + 1))) (tc (P.v j))
    exact (hflip.trans h).congr_angle (by ring)
  · -- at P0 = V_j
    have hsg : 0 < ((tc (Wp j) - tc (P.v j)) / (tc (P.v (j + 1)) - tc (P.v j))).im := by
      have := Erdos634.Draft.LaczFormal.WN.convPoly_inside P (hWint j) j
      rw [one_mul] at this
      exact this
    have hang : InnerProductGeometry.angle (tc (P.v (j + 1)) - tc (P.v j)) (tc (Wp j) - tc (P.v j)) = a := by
      rw [← angle_toC]; exact hout j
    have h := Erdos634.Draft.LaczFormal.WN.rotPos_of_angle hu (hne j j) hang hsg
    have hflip := Erdos634.Draft.LaczFormal.WN.rotPos_flip (tc (Wp j)) (tc (P.v j))
    exact h.trans hflip

#print axioms v_rot_of_angles

end Erdos634.Draft.LaczFormal.RG

-- Draft/LaczFormalIVcRatBr6a.lean -- Laczkovich DCG 48 (2012), Sect. 8.3 (Subcase IVc, rational branch): BRIDGE item (2), stage Br6a.
--   `polygon_corner_vol`: at EVERY vertex v_m of a strictly convex polygon, small balls meet the polygon in area (angle m)/2 * r^2.  This is the area hypothesis `hX`
--   of `corner_piece` (B6) / `vw_star` (B9a,b) once the interior angle at v_m is pi/3 (`polygon_corner_vol_pi3`).  Route: `vertex_local_T` (the polygon agrees near v_m with
--   the local triangle) + `Tri.volume_inter_ball_localAngle` + `Tri.localAngle_vertex`.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 8.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalThm21Loc
import Erdos634.AngleSumDissection

open scoped Classical Fin.NatCast
open MeasureTheory Erdos634.Geometry Erdos634.Draft.LaczFormal.Thm21

namespace Erdos634.Draft.LaczFormal.RG

variable {M : ℕ} [NeZero M]

theorem polygon_corner_vol (P : ConvPoly M) (m : Fin M) :
    ∃ ρ > 0, ∀ r, 0 < r → r ≤ ρ → volume (P.carrier ∩ Metric.ball (P.v m) r) = ENNReal.ofReal (P.angle m / 2 * r ^ 2) := by
  have hm : m - 1 + 1 = m := (ConvPoly.fin_facts P.three_le m).2.2.2.2.1
  obtain ⟨ρ1, hρ1, hiff⟩ := P.vertex_local_T P.three_le (m - 1)
  rw [hm] at hiff
  set T := P.locTri P.three_le (m - 1) with hT
  have hT1' : T.pts 1 = P.v (m - 1 + 1) := rfl
  have hT1 : T.pts 1 = P.v m := by rw [hT1', hm]
  obtain ⟨r0, hr0, hvol⟩ := T.volume_inter_ball_localAngle (P.v m)
  have hang : T.localAngle (P.v m) = P.angle m := by
    rw [← hT1, Tri.localAngle_vertex]
    have e1 : (1 : Fin 3) + 1 = 2 := by decide
    have e2 : (1 : Fin 3) + 2 = 0 := by decide
    rw [e1, e2]
    have h0 : T.pts 0 = P.v (m - 1) := rfl
    have h2 : T.pts 2 = P.v (m - 1 + 2) := rfl
    have h2' : m - 1 + 2 = m + 1 := by rw [← fin_one_add_one (M := M), ← add_assoc, hm]
    rw [h0, h2, h2', hT1, ConvPoly.angle]
    exact EuclideanGeometry.angle_comm _ _ _
  refine ⟨min (ρ1 / 2) r0, lt_min (by positivity) hr0, fun r hr hle => ?_⟩
  have hset : P.carrier ∩ Metric.ball (P.v m) r = T.carrier ∩ Metric.ball (P.v m) r := by
    ext y
    constructor
    · rintro ⟨hy, hb⟩
      exact ⟨(hiff y (by have := Metric.mem_ball.1 hb; linarith [min_le_left (ρ1 / 2) r0])).1 hy, hb⟩
    · rintro ⟨hy, hb⟩
      exact ⟨(hiff y (by have := Metric.mem_ball.1 hb; linarith [min_le_left (ρ1 / 2) r0])).2 hy, hb⟩
  rw [hset, hvol r hr (hle.trans (min_le_right _ _)), hang]

#print axioms Erdos634.Draft.LaczFormal.RG.polygon_corner_vol

/-- The area hypothesis `hX` of B6/B9 at a corner of angle pi/3. -/
theorem polygon_corner_vol_pi3 (P : ConvPoly M) (m : Fin M) (h : P.angle m = Real.pi / 3) :
    ∃ ρ > 0, ∀ r, 0 < r → r ≤ ρ → volume (P.carrier ∩ Metric.ball (P.v m) r) = ENNReal.ofReal (Real.pi / 3 / 2 * r ^ 2) := by
  obtain ⟨ρ, hρ, hv⟩ := polygon_corner_vol P m
  exact ⟨ρ, hρ, fun r hr hle => by rw [hv r hr hle, h]⟩

end Erdos634.Draft.LaczFormal.RG

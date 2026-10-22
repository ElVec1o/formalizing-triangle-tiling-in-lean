-- Draft/LaczFormalRGCaseVgen.lean -- Case V (gamma = pi/2) for a convex polygon with ANY number `M` of vertices: all angles are `pi/2` (`polygon_angle_pi2`) and the angle sum
-- `poly_angle_sum` forces `M = 4`; then `caseV` (quadrilateral) applies.  Removes the "PolyTiling N 4" assumption of `caseV` (the gap recorded in (private working notes, not included) 2026-10-21, step 4).
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 9), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRGCaseV3
import Erdos634.Draft.LaczFormalRG4AngleSum

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

/-- **Case V for polygons with any number of sides.**  `γ = π/2`, regular tiling of a convex `M`-gon: the polygon is a rectangle and conclusion (i) holds. -/
theorem caseV_general {N M : ℕ} [NeZero M] (T : PolyTiling N M) (hreg : RegularPQ T.C) (hγ : angleAt T.C.model 2 = Real.pi / 2) : Concl1 T.C T.P := by
  classical
  obtain ⟨idx, hA, hcnt⟩ := hreg
  haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  have hang : ∀ i : Fin M, T.P.angle i = Real.pi / 2 := by
    intro i
    have := polygon_angle_pi2 T.C idx hA hγ (fun X => hcnt X) T.P T.region_eq (i - 1)
    rwa [sub_add_cancel] at this
  have hsum := poly_angle_sum T.P
  have hM3 : 3 ≤ M := T.P.three_le
  have hpi := Real.pi_pos
  have h1 : ∑ i : Fin M, T.P.angle i = (M : ℝ) * (Real.pi / 2) := by
    rw [Finset.sum_congr rfl (fun i _ => hang i), Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hMr : ((M - 2 : ℕ) : ℝ) = (M : ℝ) - 2 := by rw [Nat.cast_sub (by omega)]; norm_num
  rw [hsum, hMr] at h1
  have hM : (M : ℝ) = 4 := by
    have : ((M : ℝ) - 4) * Real.pi = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact absurd h hpi.ne'
  have hM4 : M = 4 := by exact_mod_cast hM
  subst hM4
  exact caseV T ⟨idx, hA, hcnt⟩ hγ

/-- **Case V of Theorem 2.1, as stated in `LaczFormalThm21Def.Thm21_V`: PROVED** (all convex polygons, regular tilings, `γ = π/2`; conclusion (i)). -/
theorem thm21_V : Thm21_V := fun N M _ T hreg hγ => caseV_general T hreg hγ

end Erdos634.Draft.LaczFormal.RG

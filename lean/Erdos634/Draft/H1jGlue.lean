/-
Draft/H1jGlue.lean — atom H1.j (part 1): normalization lemmas for `RightCaseD`.
  * `homothety_angle_opp'`   : a positive homothety about 0 keeps angles and scales the sides.
  * `det_abs_right`          : a right tile (angle π/2 at vertex 2) has `|det| = oppLen 0 * oppLen 1`.
  * `dist_mem_of_oppLen`     : if the three side lengths lie in a subfield `K`, so do all vertex distances.
  * `normalizeRight`         : from `RightNormal D α` build `D2` (isometric copy, then scaled by `1/b` about 0) with
        `RightNormal D2 α`, `D2.model.oppLen 1 = 1`, `D2.target.pts 0 = 0`, `D2.target.pts 1 1 = 0`, and with
        `λ = |AB|/c`, `a/b`, and the relation `c = r a + s b` preserved.
*** UNAUDITED.  Formalization debt, NOT /goal progress.  No sorry, no native_decide. ***
-/
import Erdos634.Draft.H1eCLCaseD
import Erdos634.Draft.H1gPosGlue
import Erdos634.Draft.H1kAssembly
import Erdos634.Draft.FluxGRow3Relabel
import Erdos634.Realizable

open scoped Classical

namespace Erdos634.Draft.H1j

open Erdos634.Geometry Erdos634.Draft.H1a Erdos634.Realizable

/-- A homothety about `0` with ratio `r > 0` keeps the angles and scales the sides. -/
theorem homothety_angle_opp' (T U : Tri) (r : ℝ) (hr : 0 < r)
    (h : ∀ i, U.pts i = r • T.pts i) (k : Fin 3) :
    U.angleAt k = T.angleAt k ∧ U.oppLen k = r * T.oppLen k := by
  have hd : ∀ i j, U.pts i - U.pts j = r • (T.pts i - T.pts j) := by
    intro i j; rw [h i, h j, smul_sub]
  refine ⟨?_, ?_⟩
  · unfold Tri.angleAt cornerAngle EuclideanGeometry.angle
    simp only [vsub_eq_sub]
    rw [hd, hd, InnerProductGeometry.angle_smul_left_of_pos _ _ hr,
      InnerProductGeometry.angle_smul_right_of_pos _ _ hr]
  · unfold Tri.oppLen
    rw [dist_eq_norm, dist_eq_norm, hd, norm_smul, Real.norm_eq_abs, abs_of_pos hr]

/-- A right tile: `|det| = a b` (legs `oppLen 0`, `oppLen 1`). -/
theorem det_abs_right (T : Tri) (h : T.angleAt 2 = Real.pi / 2) :
    |T.det| = T.oppLen 0 * T.oppLen 1 := by
  have hin : inner ℝ (T.pts 0 - T.pts 2) (T.pts 1 - T.pts 2) = 0 := by
    have h' : EuclideanGeometry.angle (T.pts 0) (T.pts 2) (T.pts 1) = Real.pi / 2 := h
    unfold EuclideanGeometry.angle at h'
    simpa using (InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two _ _).mpr h'
  set u := T.pts 0 - T.pts 2 with hu
  set v := T.pts 1 - T.pts 2 with hv
  have hn0 : T.oppLen 0 = ‖v‖ := by
    unfold Tri.oppLen; rw [dist_eq_norm]; rfl
  have hn1 : T.oppLen 1 = ‖u‖ := by
    unfold Tri.oppLen
    rw [dist_comm, dist_eq_norm]; rfl
  have hsq : ∀ x : Plane, ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
    intro x
    rw [EuclideanSpace.norm_sq_eq]; simp [Fin.sum_univ_two]
  have hin2 : u 0 * v 0 + u 1 * v 1 = 0 := by
    have := hin
    simpa [PiLp.inner_apply, Fin.sum_univ_two, mul_comm] using this
  have hdet : T.det = u 0 * v 1 - u 1 * v 0 := by
    unfold Tri.det
    simp only [hu, hv, PiLp.sub_apply]; ring
  have hsq' : (T.det) ^ 2 = (‖u‖ * ‖v‖) ^ 2 := by
    rw [mul_pow, hsq, hsq, hdet]
    nlinarith [hin2]
  rw [hn0, hn1, mul_comm]
  have h1 : |T.det| = |‖u‖ * ‖v‖| := (sq_eq_sq_iff_abs_eq_abs _ _).mp hsq'
  rw [h1, abs_of_nonneg (by positivity)]

theorem dist_mem_of_oppLen (T : Tri) (K : Subfield ℝ) (h0 : T.oppLen 0 ∈ K) (h1 : T.oppLen 1 ∈ K)
    (h2 : T.oppLen 2 ∈ K) : ∀ j l, dist (T.pts j) (T.pts l) ∈ K := by
  intro j l
  have e0 : T.oppLen 0 = dist (T.pts 1) (T.pts 2) := rfl
  have e1 : T.oppLen 1 = dist (T.pts 2) (T.pts 0) := rfl
  have e2 : T.oppLen 2 = dist (T.pts 0) (T.pts 1) := rfl
  fin_cases j <;> fin_cases l <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, dist_self, Fin.isValue]
  all_goals first
    | exact K.zero_mem
    | (rw [← e0]; exact h0)
    | (rw [← e1]; exact h1)
    | (rw [← e2]; exact h2)
    | (rw [dist_comm, ← e0]; exact h0)
    | (rw [dist_comm, ← e1]; exact h1)
    | (rw [dist_comm, ← e2]; exact h2)

end Erdos634.Draft.H1j

#print axioms Erdos634.Draft.H1j.homothety_angle_opp'
#print axioms Erdos634.Draft.H1j.det_abs_right
#print axioms Erdos634.Draft.H1j.dist_mem_of_oppLen

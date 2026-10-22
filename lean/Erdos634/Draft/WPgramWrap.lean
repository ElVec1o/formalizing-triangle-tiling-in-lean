/-
Draft/WPgramWrap.lean -- `lem:wpgram` (companion paper) as a theorem.

For `e = 1`, `f ≥ 2`, tile `(a, b, c) = (f, f² − 1, f²)`: the parallelogram spanned by `f·b = f(f² − 1)` and `2f² − 1`,
with included angle `α + β`, has a tiling by `2(2f² − 1)` tiles.

`lem_wpgram`: there are unit vectors `u`, `v` and a triangle `M` with sides `f² − 1`, `f`, `f²` (the side `f²` opposite
`M.pts 1`) such that the angle between `u` and `v` is the sum of the two angles of `M` at the ends of its longest side
(that is `α + β = π − γ`), and the parallelogram `{s u + t v : 0 ≤ s ≤ f(f² − 1), 0 ≤ t ≤ 2f² − 1}` is tiled by
`2(2f² − 1)` triangles congruent to `M`.  The tiling is `WPgramF.pgramF` (an `f × f` grid of one two-tile brick and one
row of `f² − 1` copies of the other brick).

Formalization debt; not prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.WPgramF
import Erdos634.Draft.WtoDeltaF
import Erdos634.Draft.FluxTurn

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Rect RTiling.cast)

namespace Erdos634.Draft.WPgramWrap

open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF Erdos634.Draft.WPgramF
open Erdos634.Draft.WtoDeltaF (MF_pts)

theorem Phi_zero (F : ℝ) : Phi F (0, 0) = 0 := by simp [Phi]

theorem Phi_10 (F : ℝ) : Phi F (1, 0) = g1 := by simp [Phi]

theorem Phi_01 (F : ℝ) : Phi F (0, 1) = g2 F := by simp [Phi]

theorem norm_g1 {F : ℝ} (hF : 1 < F) : ‖g1‖ = 1 := by
  have h := sq_Phi hF (1, 0) (0, 0)
  rw [Phi_10, Phi_zero, dist_zero_right] at h
  have h1 : ‖g1‖ ^ 2 = (1 : ℝ) ^ 2 := by rw [h]; simp
  exact Erdos634.Draft.SumTwoSquares.eqsq (norm_nonneg _) zero_le_one h1

theorem norm_g2 {F : ℝ} (hF : 1 < F) : ‖g2 F‖ = 1 := by
  have h := sq_Phi hF (0, 1) (0, 0)
  rw [Phi_01, Phi_zero, dist_zero_right] at h
  have h1 : ‖g2 F‖ ^ 2 = (1 : ℝ) ^ 2 := by rw [h]; simp
  exact Erdos634.Draft.SumTwoSquares.eqsq (norm_nonneg _) zero_le_one h1

theorem MF_p0 {F : ℝ} (hF : 1 < F) : (MF F hF).pts 0 = Phi F (0, 0) := by rw [MF_pts]; rfl

theorem MF_p1 {F : ℝ} (hF : 1 < F) : (MF F hF).pts 1 = Phi F (F ^ 2 - 1, 0) := by rw [MF_pts]; rfl

theorem MF_p2 {F : ℝ} (hF : 1 < F) : (MF F hF).pts 2 = Phi F (F ^ 2 - 1, F) := by rw [MF_pts]; rfl

/-- the sides of the model tile `MF F`: `F² − 1`, `F`, `F²` -/
theorem MF_sides {F : ℝ} (hF : 1 < F) :
    dist ((MF F hF).pts 0) ((MF F hF).pts 1) = F ^ 2 - 1 ∧
    dist ((MF F hF).pts 1) ((MF F hF).pts 2) = F ∧
    dist ((MF F hF).pts 0) ((MF F hF).pts 2) = F ^ 2 := by
  have hF0 : (0 : ℝ) < F := by linarith
  have hA : (0 : ℝ) < F ^ 2 - 1 := by nlinarith
  rw [MF_p0 hF, MF_p1 hF, MF_p2 hF]
  refine ⟨?_, ?_, ?_⟩
  · apply Erdos634.Draft.SumTwoSquares.eqsq dist_nonneg hA.le
    rw [sq_Phi hF]
    dsimp only
    ring
  · apply Erdos634.Draft.SumTwoSquares.eqsq dist_nonneg hF0.le
    rw [sq_Phi hF]
    dsimp only
    ring
  · apply Erdos634.Draft.SumTwoSquares.eqsq dist_nonneg (by positivity)
    rw [sq_Phi hF]
    dsimp only
    have hd := diag_id hF
    rw [← hd]
    ring

/-- the angle of `MF F` at `pts 1` (opposite the side `F²`) is the supplement of the angle of the frame -/
theorem MF_angle_one {F : ℝ} (hF : 1 < F) :
    (MF F hF).angleAt 1 = Real.pi - InnerProductGeometry.angle g1 (g2 F) := by
  have hF0 : (0 : ℝ) < F := by linarith
  have hA : (0 : ℝ) < F ^ 2 - 1 := by nlinarith
  have e21 : (MF F hF).pts 2 -ᵥ (MF F hF).pts 1 = F • g2 F := by
    rw [MF_p2 hF, MF_p1 hF, vsub_eq_sub]
    unfold Phi
    dsimp only
    module
  have e01 : (MF F hF).pts 0 -ᵥ (MF F hF).pts 1 = (-(F ^ 2 - 1)) • g1 := by
    rw [MF_p0 hF, MF_p1 hF, vsub_eq_sub]
    unfold Phi
    dsimp only
    module
  unfold Tri.angleAt cornerAngle EuclideanGeometry.angle
  rw [show ((1 : Fin 3) + 1) = 2 from rfl, show ((1 : Fin 3) + 2) = 0 from rfl, e21, e01,
    InnerProductGeometry.angle_smul_left_of_pos _ _ hF0,
    InnerProductGeometry.angle_smul_right_of_neg _ _ (by linarith : -(F ^ 2 - 1) < 0),
    InnerProductGeometry.angle_neg_right, InnerProductGeometry.angle_comm]

/-- **`lem:wpgram`.** -/
theorem lem_wpgram (f : ℕ) (hf : 2 ≤ f) :
    ∃ (u v : Plane) (M : Tri), ‖u‖ = 1 ∧ ‖v‖ = 1 ∧
      dist (M.pts 0) (M.pts 1) = (f : ℝ) ^ 2 - 1 ∧ dist (M.pts 1) (M.pts 2) = f ∧
      dist (M.pts 0) (M.pts 2) = (f : ℝ) ^ 2 ∧
      InnerProductGeometry.angle u v = M.angleAt 0 + M.angleAt 2 ∧
      Nonempty (RTiling {p : Plane | ∃ s t : ℝ, 0 ≤ s ∧ s ≤ (f : ℝ) * ((f : ℝ) ^ 2 - 1) ∧ 0 ≤ t ∧
          t ≤ 2 * (f : ℝ) ^ 2 - 1 ∧ p = s • u + t • v} M (2 * (2 * f ^ 2 - 1))) := by
  have h1 := hF f hf
  obtain ⟨s1, s2, s3⟩ := MF_sides h1
  refine ⟨g1, g2 (f : ℝ), MF (f : ℝ) h1, norm_g1 h1, norm_g2 h1, s1, s2, s3, ?_, ⟨?_⟩⟩
  · have hsum := (MF (f : ℝ) h1).angleAt_sum
    rw [MF_angle_one h1] at hsum
    linarith
  · refine RTiling.cast ?_ (pgramF f hf)
    ext p
    constructor
    · rintro ⟨⟨s, t⟩, ⟨a1, a2, a3, a4⟩, rfl⟩
      exact ⟨s, t, a1, a2, a3, a4, rfl⟩
    · rintro ⟨s, t, a1, a2, a3, a4, rfl⟩
      exact ⟨(s, t), ⟨a1, a2, a3, a4⟩, rfl⟩

end Erdos634.Draft.WPgramWrap

#print axioms Erdos634.Draft.WPgramWrap.lem_wpgram

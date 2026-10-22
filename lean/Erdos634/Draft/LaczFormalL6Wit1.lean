-- Draft/LaczFormalL6Wit1.lean -- WITNESS for `LaczFormalL6Rat.equilateral_tile_i`: the scale-2 ladder of an
-- equilateral tile, a real `CongruentDissection (2*2)` of an equilateral triangle by an equilateral tile.
-- Also the general fact `bigTri_angleAt`: a ladder target has the angles of its tile.
-- UNAUDITED.  Credit: Beeson-Rosu (reptiles), Laczkovich.
import Erdos634.Draft.LaczFormalL6Rat
import Erdos634.Draft.G3CAng
import Erdos634.CellCoord

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional
  Erdos634.Subdivision
open Erdos634.Draft.FluxPaperWitness (cornerAngle_mem' dist_eq_of_sq)

namespace Erdos634.Draft.LaczFormal

theorem bigTri_pts_eq (A B C : Plane) (h : AffineIndependent ℝ ![A, B, C]) (k : ℕ) (hk : 0 < k)
    (m : Fin 3) :
    (bigTri A B C h k hk).pts m = A + (k : ℝ) • ((⟨![A, B, C], h⟩ : Tri).pts m - A) := by
  fin_cases m <;> simp [bigTri, P]

theorem bigTri_oppLen (A B C : Plane) (h : AffineIndependent ℝ ![A, B, C]) (k : ℕ) (hk : 0 < k)
    (j : Fin 3) :
    (bigTri A B C h k hk).oppLen j = (k : ℝ) * (⟨![A, B, C], h⟩ : Tri).oppLen j := by
  unfold Tri.oppLen
  rw [bigTri_pts_eq, bigTri_pts_eq, dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub,
    ← smul_sub, sub_sub_sub_cancel_right, norm_smul, Real.norm_natCast]

theorem angleAt_of_scaled (T U : Tri) (c : ℝ) (hc : 0 < c) (h : ∀ j, U.oppLen j = c * T.oppLen j)
    (j : Fin 3) : U.angleAt j = T.angleAt j := by
  refine Erdos634.Draft.G3CAng.angle_eq_of_cos j j ?_
  rw [Erdos634.Draft.G3CAng.cos_angleAt_opp U j (by rw [h]; exact mul_pos hc (T.oppLen_pos _))
      (by rw [h]; exact mul_pos hc (T.oppLen_pos _)),
    Erdos634.Draft.G3CAng.cos_angleAt_opp T j (T.oppLen_pos _) (T.oppLen_pos _)]
  simp only [h]
  have h1 := (T.oppLen_pos (j + 1)).ne'
  have h2 := (T.oppLen_pos (j + 2)).ne'
  field_simp

theorem bigTri_angleAt (A B C : Plane) (h : AffineIndependent ℝ ![A, B, C]) (k : ℕ) (hk : 0 < k)
    (j : Fin 3) :
    (bigTri A B C h k hk).angleAt j = (⟨![A, B, C], h⟩ : Tri).angleAt j :=
  angleAt_of_scaled _ _ (k : ℝ) (by exact_mod_cast hk) (bigTri_oppLen A B C h k hk) j

/-! ### The equilateral tile `(0,0),(2,0),(1,√3)` -/

theorem detE : det3 0 0 2 0 1 (Real.sqrt 3) ≠ 0 := by
  rw [show det3 0 0 2 0 1 (Real.sqrt 3) = 2 * Real.sqrt 3 by unfold det3; ring]
  have : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  positivity

noncomputable def TE : Tri := mkTri 0 0 2 0 1 (Real.sqrt 3) detE

theorem s3sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

theorem TE_opp (k : Fin 3) : TE.oppLen k = 2 := by
  unfold Tri.oppLen
  fin_cases k
  · simp only [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl]
    apply dist_eq_of_sq (by norm_num)
    show dist (mkPt 2 0) (mkPt 1 (Real.sqrt 3)) ^ 2 = 2 ^ 2
    rw [dist_sq_mkPt]; nlinarith [s3sq]
  · simp only [show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl]
    apply dist_eq_of_sq (by norm_num)
    show dist (mkPt 1 (Real.sqrt 3)) (mkPt 0 0) ^ 2 = 2 ^ 2
    rw [dist_sq_mkPt]; nlinarith [s3sq]
  · simp only [show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl]
    apply dist_eq_of_sq (by norm_num)
    show dist (mkPt 0 0) (mkPt 2 0) ^ 2 = 2 ^ 2
    rw [dist_sq_mkPt]; norm_num

/-- A triangle with three equal sides has all angles `π/3`. -/
theorem angles_third_of_sides (T : Tri) (s : ℝ) (hs : 0 < s) (h : ∀ k, T.oppLen k = s) (k : Fin 3) :
    T.angleAt k = Real.pi / 3 := by
  have hpi := Real.pi_pos
  have key : Real.cos (T.angleAt k) = 1 / 2 := by
    rw [Erdos634.Draft.G3CAng.cos_angleAt_opp T k (by rw [h]; exact hs) (by rw [h]; exact hs),
      h, h, h]
    field_simp; ring
  exact Real.injOn_cos (cornerAngle_mem' _ _ _) ⟨by positivity, by linarith⟩
    (key.trans Real.cos_pi_div_three.symm)

/-- **Witness (i)**: the scale-2 ladder of the equilateral tile `TE`: a `CongruentDissection (2*2)`. -/
noncomputable def D_i : CongruentDissection (2 * 2) where
  toDissection := ladderDissection (mkPt 0 0) (mkPt 2 0) (mkPt 1 (Real.sqrt 3)) TE.indep 2
    (by norm_num)
  model := TE
  tiles_congruent := fun n => (ladderDissection_congruent (mkPt 0 0) (mkPt 2 0)
    (mkPt 1 (Real.sqrt 3)) TE.indep 2 (by norm_num) n).symm

theorem D_i_equilateral : Equilateral D_i := fun k => by
  show (bigTri (mkPt 0 0) (mkPt 2 0) (mkPt 1 (Real.sqrt 3)) TE.indep 2 (by norm_num)).angleAt k = _
  rw [bigTri_angleAt]
  exact angles_third_of_sides TE 2 (by norm_num) TE_opp k

theorem D_i_tile : TileAngles D_i (Real.pi / 3) (Real.pi / 3) (Real.pi / 3) :=
  ⟨1, angles_third_of_sides TE 2 (by norm_num) TE_opp 0, angles_third_of_sides TE 2 (by norm_num) TE_opp 1,
    angles_third_of_sides TE 2 (by norm_num) TE_opp 2⟩

theorem equilateral_tile_i_witness :
    ∃ (N : ℕ) (D : CongruentDissection N), Equilateral D ∧
      TileAngles D (Real.pi / 3) (Real.pi / 3) (Real.pi / 3) :=
  ⟨_, D_i, D_i_equilateral, D_i_tile⟩

/-- Consistency check: `equilateral_tile_i` applied to the witness gives `4 = m²`. -/
theorem D_i_square : ∃ m : ℕ, 2 * 2 = m ^ 2 := equilateral_tile_i D_i D_i_equilateral D_i_tile

end Erdos634.Draft.LaczFormal

#print axioms Erdos634.Draft.LaczFormal.bigTri_angleAt
#print axioms Erdos634.Draft.LaczFormal.equilateral_tile_i_witness
#print axioms Erdos634.Draft.LaczFormal.D_i_square

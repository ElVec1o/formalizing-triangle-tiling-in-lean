import Erdos634.Draft.LaczFormalTrapChart

/-!
# Vertex-form trapezoids: Laczkovich Theorem 3.1 trapezoid `S` and a Lemma 2.2 (ii) witness

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Thm 3.1 and Lemma 2.2), Beeson, Beeson-Zhang, Zhang.

* `thm31_trapezoid_vert`: the trapezoid `S` of the printed proof of Thm 3.1, GIVEN BY ITS VERTICES
  `A = (0,0)`, `B = (2,0)`, `C = (3/2, √3/2)`, `D = (1/2, √3/2)` (angles `π/3, π/3, 2π/3, 2π/3`, `AB = 2`, `AD = DC = BC = 1`),
  is a finite union of rational triangles similar to every rational tile `Δ` with `vang Δ 1 = π/3` (Lemma 2.2 (iii) in vertex form).
  The data-form version in a gram chart is `LaczThm33If.piece_ratsim`.
* `wit_ii_vert`: Lemma 2.2 (ii) in vertex form for the tile `(2,3,4)`, base `4`, leg `1`, `τ = 25/32`, with explicit vertices.
-/

namespace Erdos634.LaczTrapChart

open Erdos634 Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL24 Erdos634.LaczL35 Erdos634.LaczL37
  EuclideanGeometry

theorem mkPt_sub (x y x' y' : ℝ) : mkPt x y - mkPt x' y' = mkPt (x - x') (y - y') := by
  ext i; fin_cases i <;> simp

theorem mkPt_smul (r x y : ℝ) : r • mkPt x y = mkPt (r * x) (r * y) := by
  ext i; fin_cases i <;> simp

theorem inner_mkPt (x y x' y' : ℝ) : inner ℝ (mkPt x y) (mkPt x' y') = x * x' + y * y' := by
  simp only [PiLp.inner_apply, Fin.sum_univ_two, mkPt_zero, mkPt_one, RCLike.inner_apply, conj_trivial]
  ring

theorem norm_mkPt_of (x y n : ℝ) (hn : 0 ≤ n) (h : x * x + y * y = n ^ 2) : ‖mkPt x y‖ = n := by
  have : ‖mkPt x y‖ ^ 2 = n ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_mkPt]; exact h
  exact (sq_eq_sq₀ (norm_nonneg _) hn).mp this

/-- `tTauI = 1/2` when the angle at vertex 1 is `π/3` (as `LaczThm33If.tTauI_half`, re-proved to avoid the import). -/
theorem tTauI_half' (R : RTri) (hβ : vang R.Δ 1 = Real.pi / 3) : tTauI R.a R.b R.c 2 1 = 1 / 2 := by
  have hc := RTri.cos_vang1 R
  rw [hβ, Real.cos_pi_div_three] at hc
  have ha : (R.a : ℝ) ≠ 0 := by exact_mod_cast R.pa.ne'
  have hcc : (R.c : ℝ) ≠ 0 := by exact_mod_cast R.pc.ne'
  have h1 : (R.a : ℝ) ^ 2 + R.c ^ 2 - R.b ^ 2 = R.a * R.c := by
    field_simp at hc; nlinarith [hc]
  have h2 : R.a ^ 2 + R.c ^ 2 - R.b ^ 2 = R.a * R.c := by exact_mod_cast h1
  unfold tTauI
  rw [h2]
  have : R.a ≠ 0 := R.pa.ne'
  have : R.c ≠ 0 := R.pc.ne'
  field_simp
  norm_num

theorem thm31_trapezoid_vert (R : RTri) (hβ : vang R.Δ 1 = Real.pi / 3) :
    RatSimDiss R.Δ (convexHull ℝ {mkPt 0 0, mkPt 2 0, mkPt (3 / 2) (Real.sqrt 3 / 2), mkPt (1 / 2) (Real.sqrt 3 / 2)}) := by
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hτ := tTauI_half' R hβ
  have hwn : ‖mkPt 2 0 - mkPt 0 0‖ = ((2 : ℚ) : ℝ) := by
    rw [mkPt_sub]; exact norm_mkPt_of _ _ _ (by norm_num) (by norm_num)
  have hdn : ‖mkPt (1 / 2) (Real.sqrt 3 / 2) - mkPt 0 0‖ = ((1 : ℚ) : ℝ) := by
    rw [mkPt_sub]; exact norm_mkPt_of _ _ _ (by norm_num) (by push_cast; nlinarith)
  have hang : ∠ (mkPt 2 0) (mkPt 0 0) (mkPt (1 / 2) (Real.sqrt 3 / 2)) = vang R.Δ 1 := by
    rw [hβ, angle_vert]
    apply angle_eq_of_cos (InnerProductGeometry.angle_nonneg _ _) (InnerProductGeometry.angle_le_pi _ _)
      (by positivity) (by linarith [Real.pi_pos])
    rw [InnerProductGeometry.cos_angle]
    rw [hwn, hdn, mkPt_sub, mkPt_sub, inner_mkPt, Real.cos_pi_div_three]
    norm_num
  have hC : mkPt (3 / 2) (Real.sqrt 3 / 2) - mkPt (1 / 2) (Real.sqrt 3 / 2)
      = ((tTauI R.a R.b R.c 2 1 : ℚ) : ℝ) • (mkPt 2 0 - mkPt 0 0) := by
    rw [hτ, mkPt_sub, mkPt_sub, mkPt_smul]
    congr 1 <;> push_cast <;> ring
  exact lemma22_iii_vert R _ _ _ _ 2 1 (by norm_num) (by norm_num) hwn hdn hang
    (by rw [hτ]; norm_num) hC

#print axioms thm31_trapezoid_vert

/-- **Lemma 2.2 (ii), vertex form, witness**: tile `(2,3,4)` (`cos` at vertex 1 `= 11/16`), base `4`, leg `1`,
`τ = tTau 2 3 4 4 1 = 25/32`; vertices `A = (0,0)`, `B = (4,0)`, `D = (11/16, √135/16)`, `C = D + τ (B - A)`. -/
theorem wit_ii_vert :
    RatSimDiss R234.Δ (convexHull ℝ {mkPt 0 0, mkPt 4 0, mkPt (61 / 16) (Real.sqrt 135 / 16),
      mkPt (11 / 16) (Real.sqrt 135 / 16)}) := by
  have h135 : Real.sqrt 135 * Real.sqrt 135 = 135 := Real.mul_self_sqrt (by norm_num)
  have hc1 : R234.cos1 = 11 / 16 := by simp [RTri.cos1, R234]; norm_num
  have hτ : tTau R234.a R234.b R234.c 4 1 = 25 / 32 := by simp [tTau, R234]; norm_num
  have hwn : ‖mkPt 4 0 - mkPt 0 0‖ = ((4 : ℚ) : ℝ) := by
    rw [mkPt_sub]; exact norm_mkPt_of _ _ _ (by norm_num) (by norm_num)
  have hdn : ‖mkPt (11 / 16) (Real.sqrt 135 / 16) - mkPt 0 0‖ = ((1 : ℚ) : ℝ) := by
    rw [mkPt_sub]; exact norm_mkPt_of _ _ _ (by norm_num) (by push_cast; nlinarith)
  have hang : ∠ (mkPt 4 0) (mkPt 0 0) (mkPt (11 / 16) (Real.sqrt 135 / 16)) = vang R234.Δ 1 := by
    rw [angle_vert]
    apply angle_eq_of_cos (InnerProductGeometry.angle_nonneg _ _) (InnerProductGeometry.angle_le_pi _ _)
      (angle_nonneg _ _ _) (angle_le_pi _ _ _)
    rw [InnerProductGeometry.cos_angle, hwn, hdn, mkPt_sub, mkPt_sub, inner_mkPt]
    show _ = Real.cos (vang R234.Δ 1)
    rw [RTri.cos_vang1]
    simp [R234]; norm_num
  have hC : mkPt (61 / 16) (Real.sqrt 135 / 16) - mkPt (11 / 16) (Real.sqrt 135 / 16)
      = (((25 / 32 : ℚ)) : ℝ) • (mkPt 4 0 - mkPt 0 0) := by
    rw [mkPt_sub, mkPt_sub, mkPt_smul]
    congr 1 <;> push_cast <;> ring
  exact lemma22_ii_vert R234 _ _ _ _ 4 1 (by norm_num) (by norm_num) hwn hdn hang (25 / 32) hτ.symm (by norm_num) hC

#print axioms wit_ii_vert

end Erdos634.LaczTrapChart

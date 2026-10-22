import Erdos634.Draft.LaczFormalL25Thm

/-!
# Witnesses for Laczkovich Theorem 2.5, first triple

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94), Beeson, Beeson-Zhang, Zhang.

The hypothesis of `thm25_first` is a rational triangle with `c² = a² + ab + b²` (angle `γ = 2π/3`).  Witnesses: the
project's tiles `(a, b, c) = (5, 3, 7)` and `(3, 5, 7)` (`25 + 15 + 9 = 49`), with explicit coordinates.
-/

namespace Erdos634.LaczL25

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL21 Erdos634.LaczL24 Erdos634.Realizable

/-- Triangle with `|Δ₀Δ₁| = 7`, `|Δ₂Δ₀| = 3`, `|Δ₁Δ₂| = 5`. -/
noncomputable def Δ537 : Tri :=
  mkTri 0 0 7 0 (33 / 14) (15 * Real.sqrt 3 / 14) (by
    have : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    intro h; simp only [det3] at h; nlinarith)

theorem Δ537_dists : dist (Δ537.pts 1) (Δ537.pts 2) = 5 ∧ dist (Δ537.pts 2) (Δ537.pts 0) = 3 ∧
    dist (Δ537.pts 0) (Δ537.pts 1) = 7 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · refine eq_of_sq_eq' dist_nonneg (by norm_num) ?_
    show dist (mkPt 7 0) (mkPt (33 / 14) (15 * Real.sqrt 3 / 14)) ^ 2 = 5 ^ 2
    rw [dist_sq_mkPt]; nlinarith [h3]
  · refine eq_of_sq_eq' dist_nonneg (by norm_num) ?_
    show dist (mkPt (33 / 14) (15 * Real.sqrt 3 / 14)) (mkPt 0 0) ^ 2 = 3 ^ 2
    rw [dist_sq_mkPt]; nlinarith [h3]
  · refine eq_of_sq_eq' dist_nonneg (by norm_num) ?_
    show dist (mkPt 0 0) (mkPt 7 0) ^ 2 = 7 ^ 2
    rw [dist_sq_mkPt]; norm_num

noncomputable def R537 : RTri where
  Δ := Δ537
  a := 5
  b := 3
  c := 7
  ha := by rw [Δ537_dists.1]; norm_num
  hb := by rw [Δ537_dists.2.1]; norm_num
  hc := by rw [Δ537_dists.2.2]; norm_num
  pa := by norm_num
  pb := by norm_num
  pc := by norm_num

theorem wit_thm25_first_537 :
    ∃ (T : Tri) (q : ℕ) (hq : 0 < q) (M : ℕ)
      (C : Erdos634.RegionDissection.CongruentRegionDissection M),
      C.region = T.carrier ∧
      C.model = scaleTri (1 / (q : ℝ)) (one_div_pos.mpr (Nat.cast_pos.mpr hq)).ne' R537.Δ ∧
      cornerAngle (T.pts 1) (T.pts 0) (T.pts 2)
        = cornerAngle (R537.Δ.pts 1) (R537.Δ.pts 0) (R537.Δ.pts 2) ∧
      cornerAngle (T.pts 2) (T.pts 1) (T.pts 0) = Real.pi / 3 :=
  thm25_first R537 (by simp [R537]; norm_num)

/-- Triangle with `|Δ₀Δ₁| = 7`, `|Δ₂Δ₀| = 5`, `|Δ₁Δ₂| = 3`. -/
noncomputable def Δ357 : Tri :=
  mkTri 0 0 7 0 (65 / 14) (15 * Real.sqrt 3 / 14) (by
    have : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    intro h; simp only [det3] at h; nlinarith)

theorem Δ357_dists : dist (Δ357.pts 1) (Δ357.pts 2) = 3 ∧ dist (Δ357.pts 2) (Δ357.pts 0) = 5 ∧
    dist (Δ357.pts 0) (Δ357.pts 1) = 7 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · refine eq_of_sq_eq' dist_nonneg (by norm_num) ?_
    show dist (mkPt 7 0) (mkPt (65 / 14) (15 * Real.sqrt 3 / 14)) ^ 2 = 3 ^ 2
    rw [dist_sq_mkPt]; nlinarith [h3]
  · refine eq_of_sq_eq' dist_nonneg (by norm_num) ?_
    show dist (mkPt (65 / 14) (15 * Real.sqrt 3 / 14)) (mkPt 0 0) ^ 2 = 5 ^ 2
    rw [dist_sq_mkPt]; nlinarith [h3]
  · refine eq_of_sq_eq' dist_nonneg (by norm_num) ?_
    show dist (mkPt 0 0) (mkPt 7 0) ^ 2 = 7 ^ 2
    rw [dist_sq_mkPt]; norm_num

noncomputable def R357 : RTri where
  Δ := Δ357
  a := 3
  b := 5
  c := 7
  ha := by rw [Δ357_dists.1]; norm_num
  hb := by rw [Δ357_dists.2.1]; norm_num
  hc := by rw [Δ357_dists.2.2]; norm_num
  pa := by norm_num
  pb := by norm_num
  pc := by norm_num

theorem wit_thm25_first_357 :
    ∃ (T : Tri) (q : ℕ) (hq : 0 < q) (M : ℕ)
      (C : Erdos634.RegionDissection.CongruentRegionDissection M),
      C.region = T.carrier ∧
      C.model = scaleTri (1 / (q : ℝ)) (one_div_pos.mpr (Nat.cast_pos.mpr hq)).ne' R357.Δ ∧
      cornerAngle (T.pts 1) (T.pts 0) (T.pts 2)
        = cornerAngle (R357.Δ.pts 1) (R357.Δ.pts 0) (R357.Δ.pts 2) ∧
      cornerAngle (T.pts 2) (T.pts 1) (T.pts 0) = Real.pi / 3 :=
  thm25_first R357 (by simp [R357]; norm_num)

#print axioms thm25_first
#print axioms wit_thm25_first_537
#print axioms wit_thm25_first_357

end Erdos634.LaczL25

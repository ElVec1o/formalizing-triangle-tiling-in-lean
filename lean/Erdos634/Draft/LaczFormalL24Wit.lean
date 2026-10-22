import Erdos634.Draft.LaczFormalL24Main

/-!
# Witnesses for the Laczkovich Sect. 2 formalization

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94), Beeson, Beeson-Zhang, Zhang.

The project's tile `(2, 3, 4)` (sides `a = 2, b = 3, c = 4` opposite the angles `α, β, γ` with `3α + 2β = π`,
`a₀ = a/c = 1/2`, `b/c = 1 - a₀²`) satisfies every hypothesis of `thm24_first`; so does `(12, 7, 16)`
(`a₀ = 3/4`).  The hypotheses of `trap_ii` and `trap_iii` are witnessed for `(2, 3, 4)`.
-/

namespace Erdos634.LaczL24

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL21 Erdos634.Realizable

/-- The triangle with `|Δ₀Δ₁| = 4`, `|Δ₂Δ₀| = 3`, `|Δ₁Δ₂| = 2`. -/
noncomputable def Δ234 : Tri :=
  mkTri 0 0 4 0 (21 / 8) (3 * Real.sqrt 15 / 8) (by
    have : 0 < Real.sqrt 15 := Real.sqrt_pos.mpr (by norm_num)
    intro h; simp only [det3] at h; nlinarith)

theorem Δ234_dists : dist (Δ234.pts 1) (Δ234.pts 2) = 2 ∧ dist (Δ234.pts 2) (Δ234.pts 0) = 3 ∧
    dist (Δ234.pts 0) (Δ234.pts 1) = 4 := by
  have h15 : Real.sqrt 15 ^ 2 = 15 := Real.sq_sqrt (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · refine eq_of_sq_eq' dist_nonneg (by norm_num) ?_
    show dist (mkPt 4 0) (mkPt (21 / 8) (3 * Real.sqrt 15 / 8)) ^ 2 = 2 ^ 2
    rw [dist_sq_mkPt]; nlinarith [h15]
  · refine eq_of_sq_eq' dist_nonneg (by norm_num) ?_
    show dist (mkPt (21 / 8) (3 * Real.sqrt 15 / 8)) (mkPt 0 0) ^ 2 = 3 ^ 2
    rw [dist_sq_mkPt]; nlinarith [h15]
  · refine eq_of_sq_eq' dist_nonneg (by norm_num) ?_
    show dist (mkPt 0 0) (mkPt 4 0) ^ 2 = 4 ^ 2
    rw [dist_sq_mkPt]; norm_num

noncomputable def R234 : RTri where
  Δ := Δ234
  a := 2
  b := 3
  c := 4
  ha := by rw [Δ234_dists.1]; norm_num
  hb := by rw [Δ234_dists.2.1]; norm_num
  hc := by rw [Δ234_dists.2.2]; norm_num
  pa := by norm_num
  pb := by norm_num
  pc := by norm_num

/-- `thm24_first` fires on the tile `(2, 3, 4)` (`a₀ = 1/2`): the isosceles triangle with base angles `α` is
cut into congruent copies of a triangle similar to `(2, 3, 4)`. -/
theorem wit_thm24_first_234 :
    ∃ (T : Tri) (q : ℕ) (hq : 0 < q) (M : ℕ)
      (C : Erdos634.RegionDissection.CongruentRegionDissection M),
      C.region = T.carrier ∧
      C.model = scaleTri (1 / (q : ℝ)) (one_div_pos.mpr (Nat.cast_pos.mpr hq)).ne' R234.Δ ∧
      dist (T.pts 1) (T.pts 0) = dist (T.pts 1) (T.pts 2) ∧
      cornerAngle (T.pts 1) (T.pts 0) (T.pts 2)
        = cornerAngle (R234.Δ.pts 1) (R234.Δ.pts 0) (R234.Δ.pts 2) :=
  thm24_first R234 (1 / 2) (by norm_num) (by norm_num) (by simp [R234]; norm_num)
    (by simp [R234]; norm_num)

/-- Witness for the lemma-2.2 chain: a chart for `(2, 3, 4)` at the angle `β` (`cos β = 11/16`) with `W = 4`,
`D = 1`; hypotheses of `trap_ii` (`τ = 1/8 + ...`) and `trap_iii` hold and both conclusions are obtained. -/
theorem wit_trap_234 :
    ∃ (w d : Plane) (h : w 0 * d 1 - w 1 * d 0 ≠ 0),
      ChartRSD R234 0 w d h (trapSet ((tTau R234.a R234.b R234.c 4 1 : ℚ) : ℝ)) ∧
      ChartRSD R234 0 w d h (trapSet ((tTauI R234.a R234.b R234.c 4 1 : ℚ) : ℝ)) := by
  have hc1 : R234.cos1 = 11 / 16 := by simp [RTri.cos1, R234]; norm_num
  obtain ⟨w, d, hw, hd, hwd, hdet⟩ := exists_gram_chart 4 1 ((11 / 16 : ℚ) : ℝ) (by norm_num) (by norm_num)
    (by norm_num)
  have hw' : inner ℝ w w = ((4 : ℚ) : ℝ) ^ 2 := by simpa using hw
  have hd' : inner ℝ d d = ((1 : ℚ) : ℝ) ^ 2 := by simpa using hd
  have hwd' : inner ℝ w d = ((4 : ℚ) : ℝ) * ((1 : ℚ) : ℝ) * (R234.cos1 : ℝ) := by
    rw [hc1]; simpa using hwd
  refine ⟨w, d, hdet, ?_, ?_⟩
  · exact trap_ii R234 0 w d hdet 4 1 (by norm_num) (by norm_num) hw' hd' hwd' _ rfl
      (by simp [tTau, R234]; norm_num)
  · exact trap_iii R234 0 w d hdet 4 1 (by norm_num) (by norm_num) hw' hd' hwd'
      (by simp [tTauI, R234]; norm_num)


/-- The triangle with `|Δ₀Δ₁| = 16`, `|Δ₂Δ₀| = 7`, `|Δ₁Δ₂| = 12`. -/
noncomputable def Δ12716 : Tri :=
  mkTri 0 0 16 0 (161 / 32) (21 * Real.sqrt 55 / 32) (by
    have : 0 < Real.sqrt 55 := Real.sqrt_pos.mpr (by norm_num)
    intro h; simp only [det3] at h; nlinarith)

theorem Δ12716_dists : dist (Δ12716.pts 1) (Δ12716.pts 2) = 12 ∧
    dist (Δ12716.pts 2) (Δ12716.pts 0) = 7 ∧ dist (Δ12716.pts 0) (Δ12716.pts 1) = 16 := by
  have h55 : Real.sqrt 55 ^ 2 = 55 := Real.sq_sqrt (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · refine eq_of_sq_eq' dist_nonneg (by norm_num) ?_
    show dist (mkPt 16 0) (mkPt (161 / 32) (21 * Real.sqrt 55 / 32)) ^ 2 = 12 ^ 2
    rw [dist_sq_mkPt]; nlinarith [h55]
  · refine eq_of_sq_eq' dist_nonneg (by norm_num) ?_
    show dist (mkPt (161 / 32) (21 * Real.sqrt 55 / 32)) (mkPt 0 0) ^ 2 = 7 ^ 2
    rw [dist_sq_mkPt]; nlinarith [h55]
  · refine eq_of_sq_eq' dist_nonneg (by norm_num) ?_
    show dist (mkPt 0 0) (mkPt 16 0) ^ 2 = 16 ^ 2
    rw [dist_sq_mkPt]; norm_num

noncomputable def R12716 : RTri where
  Δ := Δ12716
  a := 12
  b := 7
  c := 16
  ha := by rw [Δ12716_dists.1]; norm_num
  hb := by rw [Δ12716_dists.2.1]; norm_num
  hc := by rw [Δ12716_dists.2.2]; norm_num
  pa := by norm_num
  pb := by norm_num
  pc := by norm_num

/-- `thm24_first` fires on the tile `(12, 7, 16)` (`a₀ = 3/4`). -/
theorem wit_thm24_first_12716 :
    ∃ (T : Tri) (q : ℕ) (hq : 0 < q) (M : ℕ)
      (C : Erdos634.RegionDissection.CongruentRegionDissection M),
      C.region = T.carrier ∧
      C.model = scaleTri (1 / (q : ℝ)) (one_div_pos.mpr (Nat.cast_pos.mpr hq)).ne' R12716.Δ ∧
      dist (T.pts 1) (T.pts 0) = dist (T.pts 1) (T.pts 2) ∧
      cornerAngle (T.pts 1) (T.pts 0) (T.pts 2)
        = cornerAngle (R12716.Δ.pts 1) (R12716.Δ.pts 0) (R12716.Δ.pts 2) :=
  thm24_first R12716 (3 / 4) (by norm_num) (by norm_num) (by simp [R12716]; norm_num)
    (by simp [R12716]; norm_num)

end Erdos634.LaczL24

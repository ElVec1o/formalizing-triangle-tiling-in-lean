import Erdos634.Draft.LaczFormalL27Thm

/-!
# Laczkovich Theorem 2.4, triples 2, 3, 5 of (1), for `N(a₀) > 0`

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Theorem 2.4, Fig. 5), Beeson (arXiv 1206.2229,
Sect. 13.3, Theorem 23, Lemma 52), Beeson-Zhang, Zhang.

PRINT GAP (same as for the fourth triple): the paper says only "Similar constructions apply for the other triples listed in
(1); see Fig. 5".  Decoded from Fig. 5 (four pictures, by their angle labels):

* picture 1 (tall isosceles, apex `α`, base angles `α+β`): fourth triple (`LaczFormalL26Thm`);
* picture 2 (apex `2α = α+α`, base angles `β`, `α+β`): FIFTH triple `(β, 2α, α+β)` = tile `(α,β,γ)` + picture-1 triangle;
* picture 3 (apex `3α`, base angles `β, β`): SECOND triple `(β, β, 3α)` = tile + picture-1 triangle + tile;
* picture 4 (angles `α`, `2β = β+β`, `2α = α+α`): THIRD triple `(α, 2α, 2β)` = tile + tile + picture-1 triangle
  (picture-1 triangle with apex at the vertex `2α`).

Every piece size is determined by the picture (tile scales `K/b²` and `K(2-a²)/b²`, `K = a² + b²`, `b = 1 - a²`, in the chart
of the fourth triple).  The only non-tile piece is the picture-1 triangle, so the validity range is that of the fourth triple,
`N(a₀) = a₀⁴ - (1-a₀²)³ > 0`.  Each statement below is also stated for an ARBITRARY triangle of the shape (`_any`).
-/

namespace Erdos634.LaczL27

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL24 Erdos634.LaczL26 EuclideanGeometry
  Erdos634.DissectionMap Erdos634.Realizable

theorem std_chart_exists (R : RTri) (a0 : ℚ) (ha0 : 0 < a0) (ha1 : a0 < 1) :
    ∃ (w1 d1 : Plane) (hdet : w1 0 * d1 1 - w1 1 * d1 0 ≠ 0),
      inner ℝ w1 w1 = (((R.c / (a0 * (1 - a0 ^ 2)) : ℚ) : ℝ)) ^ 2 ∧
      inner ℝ d1 d1 = (((R.c / (a0 * (1 - a0 ^ 2)) : ℚ) : ℝ)) ^ 2 ∧
      inner ℝ w1 d1 = (((R.c / (a0 * (1 - a0 ^ 2)) : ℚ) : ℝ)) ^ 2 * (2 - (a0 : ℝ) ^ 2) / 2 := by
  have hc := R.pc
  have ha0r : (0 : ℝ) < a0 := by exact_mod_cast ha0
  have ha1r : (a0 : ℝ) < 1 := by exact_mod_cast ha1
  have hupos : (0 : ℚ) < R.c / (a0 * (1 - a0 ^ 2)) := by
    have : (0 : ℚ) < 1 - a0 ^ 2 := by nlinarith
    positivity
  have hu0 : (0 : ℝ) < (a0 : ℝ) ^ 2 := by positivity
  have hu1 : (a0 : ℝ) ^ 2 < 1 := by nlinarith
  have hcos2 : (((2 - (a0 : ℝ) ^ 2) / 2) : ℝ) ^ 2 < 1 := by nlinarith
  obtain ⟨w1, d1, hw0, hd0, hwd0, hdet⟩ := exists_gram_chart
    (((R.c / (a0 * (1 - a0 ^ 2)) : ℚ) : ℝ)) (((R.c / (a0 * (1 - a0 ^ 2)) : ℚ) : ℝ))
    ((2 - (a0 : ℝ) ^ 2) / 2) (by exact_mod_cast hupos) (by exact_mod_cast hupos) hcos2
  refine ⟨w1, d1, hdet, hw0, hd0, ?_⟩
  rw [hwd0]; ring

section thms

variable (R : RTri) (a0 : ℚ) (ha0 : 0 < a0) (ha1 : a0 < 1)
  (hA : R.a = a0 * R.c) (hB : R.b = (1 - a0 ^ 2) * R.c)
  (hN : T4RSD R a0 ha0 ha1)

include ha0 ha1 hA hB hN

/-- **Laczkovich Theorem 2.4, FIFTH triple `(β, 2α, α+β)`, for `N(a₀) > 0`.**  Vertices `T₀` (angle `2α`), `T₁` (angle `β`),
`T₂` (angle `α+β`). -/
theorem thm24_fifth_gen :
    ∃ (T : Tri) (q : ℕ) (hq : 0 < q) (M : ℕ) (C : Erdos634.RegionDissection.CongruentRegionDissection M),
      C.region = T.carrier ∧
      C.model = scaleTri (1 / (q : ℝ)) (one_div_pos.mpr (Nat.cast_pos.mpr hq)).ne' R.Δ ∧
      ∠ (T.pts 0) (T.pts 1) (T.pts 2) = ∠ (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2) ∧
      ∠ (T.pts 1) (T.pts 2) (T.pts 0)
        = ∠ (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) + ∠ (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2) := by
  obtain ⟨w1, d1, hdet, hw, hd, hwd⟩ := std_chart_exists R a0 ha0 ha1
  have key := fifth_chart R a0 ha0 ha1 hA hB hN w1 d1 hdet hw hd hwd
  unfold ChartRSD at key
  obtain ⟨q, hq, M, C, hC1, hC2⟩ := RatSimDiss.toCongruent R.rational key
  have hyp := hyp0_of_q a0 ha0 ha1
  have fa := fifth_angles R a0 ha0 ha1 hA hB hN w1 d1 hdet hw hd hwd
  refine ⟨mapTri (chartEquiv 0 w1 d1 hdet) (B5 hyp), q, hq, M, C, ?_, hC2, fa.1, fa.2⟩
  rw [hC1, mapTri_carrier, B5_carrier]

/-- **Laczkovich Theorem 2.4, SECOND triple `(β, β, 3α)`, for `N(a₀) > 0`.**  Vertices `T₀` (angle `3α`), `T₁, T₂` (angle `β`). -/
theorem thm24_second_gen :
    ∃ (T : Tri) (q : ℕ) (hq : 0 < q) (M : ℕ) (C : Erdos634.RegionDissection.CongruentRegionDissection M),
      C.region = T.carrier ∧
      C.model = scaleTri (1 / (q : ℝ)) (one_div_pos.mpr (Nat.cast_pos.mpr hq)).ne' R.Δ ∧
      ∠ (T.pts 0) (T.pts 1) (T.pts 2) = ∠ (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2) ∧
      ∠ (T.pts 1) (T.pts 2) (T.pts 0) = ∠ (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2) := by
  obtain ⟨w1, d1, hdet, hw, hd, hwd⟩ := std_chart_exists R a0 ha0 ha1
  have key := second_chart R a0 ha0 ha1 hA hB hN w1 d1 hdet hw hd hwd
  unfold ChartRSD at key
  obtain ⟨q, hq, M, C, hC1, hC2⟩ := RatSimDiss.toCongruent R.rational key
  have hyp := hyp0_of_q a0 ha0 ha1
  have fa := second_angles R a0 ha0 ha1 hA hB hN w1 d1 hdet hw hd hwd
  refine ⟨mapTri (chartEquiv 0 w1 d1 hdet) (B2 hyp), q, hq, M, C, ?_, hC2, fa.1, fa.2⟩
  rw [hC1, mapTri_carrier, B2_carrier]

/-- **Laczkovich Theorem 2.4, THIRD triple `(α, 2α, 2β)`, for `N(a₀) > 0`.**  Vertices `T₀` (angle `2β`), `T₁` (angle
`2α = α+α`), `T₂` (angle `α`). -/
theorem thm24_third_gen :
    ∃ (T : Tri) (q : ℕ) (hq : 0 < q) (M : ℕ) (C : Erdos634.RegionDissection.CongruentRegionDissection M),
      C.region = T.carrier ∧
      C.model = scaleTri (1 / (q : ℝ)) (one_div_pos.mpr (Nat.cast_pos.mpr hq)).ne' R.Δ ∧
      ∠ (T.pts 0) (T.pts 1) (T.pts 2)
        = ∠ (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) + ∠ (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) ∧
      ∠ (T.pts 1) (T.pts 2) (T.pts 0) = ∠ (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) := by
  obtain ⟨w1, d1, hdet, hw, hd, hwd⟩ := std_chart_exists R a0 ha0 ha1
  have key := third_chart R a0 ha0 ha1 hA hB hN w1 d1 hdet hw hd hwd
  unfold ChartRSD at key
  obtain ⟨q, hq, M, C, hC1, hC2⟩ := RatSimDiss.toCongruent R.rational key
  have hyp := hyp0_of_q a0 ha0 ha1
  have fa := third_angles R a0 ha0 ha1 hA hB hN w1 d1 hdet hw hd hwd
  refine ⟨mapTri (chartEquiv 0 w1 d1 hdet) (B3 hyp), q, hq, M, C, ?_, hC2, fa.1, fa.2⟩
  rw [hC1, mapTri_carrier, B3_carrier]

end thms

/-! ### the original statements for `N(a₀) > 0` (the dissection of `T` is `fourth_chart`) -/

section thmsN

variable (R : RTri) (a0 : ℚ) (ha0 : 0 < a0) (ha1 : a0 < 1)
  (hA : R.a = a0 * R.c) (hB : R.b = (1 - a0 ^ 2) * R.c)
  (hN : 0 < a0 ^ 4 - (1 - a0 ^ 2) ^ 3)

include ha0 ha1 hA hB hN

theorem thm24_fifth :
    ∃ (T : Tri) (q : ℕ) (hq : 0 < q) (M : ℕ) (C : Erdos634.RegionDissection.CongruentRegionDissection M),
      C.region = T.carrier ∧
      C.model = scaleTri (1 / (q : ℝ)) (one_div_pos.mpr (Nat.cast_pos.mpr hq)).ne' R.Δ ∧
      ∠ (T.pts 0) (T.pts 1) (T.pts 2) = ∠ (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2) ∧
      ∠ (T.pts 1) (T.pts 2) (T.pts 0)
        = ∠ (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) + ∠ (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2) := thm24_fifth_gen R a0 ha0 ha1 hA hB (T4RSD_of_N R a0 ha0 ha1 hA hB hN)

theorem thm24_second :
    ∃ (T : Tri) (q : ℕ) (hq : 0 < q) (M : ℕ) (C : Erdos634.RegionDissection.CongruentRegionDissection M),
      C.region = T.carrier ∧
      C.model = scaleTri (1 / (q : ℝ)) (one_div_pos.mpr (Nat.cast_pos.mpr hq)).ne' R.Δ ∧
      ∠ (T.pts 0) (T.pts 1) (T.pts 2) = ∠ (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2) ∧
      ∠ (T.pts 1) (T.pts 2) (T.pts 0) = ∠ (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2) := thm24_second_gen R a0 ha0 ha1 hA hB (T4RSD_of_N R a0 ha0 ha1 hA hB hN)

theorem thm24_third :
    ∃ (T : Tri) (q : ℕ) (hq : 0 < q) (M : ℕ) (C : Erdos634.RegionDissection.CongruentRegionDissection M),
      C.region = T.carrier ∧
      C.model = scaleTri (1 / (q : ℝ)) (one_div_pos.mpr (Nat.cast_pos.mpr hq)).ne' R.Δ ∧
      ∠ (T.pts 0) (T.pts 1) (T.pts 2)
        = ∠ (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) + ∠ (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) ∧
      ∠ (T.pts 1) (T.pts 2) (T.pts 0) = ∠ (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) := thm24_third_gen R a0 ha0 ha1 hA hB (T4RSD_of_N R a0 ha0 ha1 hA hB hN)

end thmsN

end Erdos634.LaczL27

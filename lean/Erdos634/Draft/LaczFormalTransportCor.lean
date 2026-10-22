import Erdos634.Draft.LaczFormalTransport

/-!
# Laczkovich Theorems 2.4 (first and fourth triple) and 2.5 (first triple) for ARBITRARY triangles of the shape

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94), Beeson (1206.2229v4), Beeson-Zhang, Zhang.

The explicit triangles of `thm24_first` (`LaczL24`), `thm25_first` (`LaczL25`) and `thm24_fourth` (`LaczL26`) are moved to any
triangle `T'` with the same angles by `transport_similar`.  Conclusion in each case: a `CongruentDissection` of (a
triangle with carrier equal to that of) `T'` whose tiles are congruent to `scaleTri s Δ`, `s > 0`.
-/

namespace Erdos634.LaczTransport

open Erdos634.Geometry Erdos634.Realizable Erdos634.DissectionMap EuclideanGeometry

/-- Transport of the output of a region-dissection theorem (target `T`, model `scaleTri (1/q) Δ`). -/
theorem transport_region (Δ : Tri) (T : Tri) (q : ℕ) (hq : 0 < q) (M : ℕ)
    (C : Erdos634.RegionDissection.CongruentRegionDissection M) (hC1 : C.region = T.carrier)
    (hC2 : C.model = scaleTri (1 / (q : ℝ)) (one_div_pos.mpr (Nat.cast_pos.mpr hq)).ne' Δ)
    (T' : Tri) (a b c : Fin 3) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (h1 : ∠ (T.pts a) (T.pts b) (T.pts c) = ∠ (T'.pts a) (T'.pts b) (T'.pts c))
    (h2 : ∠ (T.pts b) (T.pts c) (T.pts a) = ∠ (T'.pts b) (T'.pts c) (T'.pts a)) :
    ∃ (s : ℝ) (hs : 0 < s) (D' : CongruentDissection M),
      D'.target.carrier = T'.carrier ∧ D'.model.Congruent (scaleTri s hs.ne' Δ) := by
  have hqr : (0 : ℝ) < 1 / (q : ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr hq)
  set D := C.toCongruentDissection T hC1 with hD
  have hDt : D.target = T := rfl
  have hDm : D.model = scaleTri (1 / (q : ℝ)) hqr.ne' Δ := hC2
  obtain ⟨r, hr, D', hD1, hD2⟩ := transport_similar D T' a b c hab hbc hac (by rw [hDt]; exact h1)
    (by rw [hDt]; exact h2)
  refine ⟨r * (1 / (q : ℝ)), mul_pos hr hqr, D', hD1, ?_⟩
  rw [hDm, scaleTri_scaleTri _ _ hr.ne' hqr.ne' (mul_pos hr hqr).ne'] at hD2
  exact hD2

/-- Base angles of an isosceles triangle with apex `S₂`. -/
theorem base_angle (S : Tri) (h : dist (S.pts 2) (S.pts 0) = dist (S.pts 2) (S.pts 1)) :
    ∠ (S.pts 0) (S.pts 2) (S.pts 1) + 2 * ∠ (S.pts 2) (S.pts 1) (S.pts 0) = Real.pi := by
  have hne : S.pts 2 ≠ S.pts 0 := fun he => by
    have := S.indep.injective he; exact absurd this (by decide)
  have hsum := angle_add_angle_add_angle_eq_pi (S.pts 1) hne
  have hiso := angle_eq_angle_of_dist_eq h
  rw [angle_comm (S.pts 1) (S.pts 0) (S.pts 2)] at hsum
  linarith

open Erdos634.LaczL24 Erdos634.LaczL22 in
/-- **Theorem 2.4, first triple, for every triangle of the shape `(α, α, π - 2α)`** (apex `T'₁`, angle `α` at `T'₀`):
`T'` is the union of finitely many congruent triangles similar to `Δ` (a `CongruentDissection` of a triangle with the
carrier of `T'`; the model is congruent to `scaleTri s Δ`). -/
theorem thm24_first_any (R : RTri) (a0 : ℚ) (ha0q : 0 < a0) (ha1q : a0 < 1)
    (hA : R.a = a0 * R.c) (hB : R.b = (1 - a0 ^ 2) * R.c) (T' : Tri)
    (hiso : dist (T'.pts 1) (T'.pts 0) = dist (T'.pts 1) (T'.pts 2))
    (hang : cornerAngle (T'.pts 1) (T'.pts 0) (T'.pts 2)
      = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2)) :
    ∃ (s : ℝ) (hs : 0 < s) (M : ℕ) (D' : CongruentDissection M),
      D'.target.carrier = T'.carrier ∧ D'.model.Congruent (scaleTri s hs.ne' R.Δ) := by
  obtain ⟨T, q, hq, M, C, hC1, hC2, hiso0, hang0⟩ := thm24_first R a0 ha0q ha1q hA hB
  have hb : ∀ S : Tri, dist (S.pts 1) (S.pts 0) = dist (S.pts 1) (S.pts 2) →
      ∠ (S.pts 0) (S.pts 2) (S.pts 1) = ∠ (S.pts 1) (S.pts 0) (S.pts 2) := by
    intro S h
    rw [angle_comm (S.pts 0) (S.pts 2) (S.pts 1)]
    exact (angle_eq_angle_of_dist_eq h).symm
  obtain ⟨s, hs, D', h1, h2⟩ := transport_region R.Δ T q hq M C hC1 hC2 T' 1 0 2 (by decide) (by decide)
    (by decide) (hang0.trans hang.symm)
    (by rw [hb T hiso0, hb T' hiso]; exact hang0.trans hang.symm)
  exact ⟨s, hs, M, D', h1, h2⟩

open Erdos634.LaczL25 Erdos634.LaczL22 in
/-- **Theorem 2.5, first triple, for every triangle with angles `α` at `T'₀` and `π/3 = α + β` at `T'₁`.** -/
theorem thm25_first_any (R : RTri) (hγ : R.a ^ 2 + R.a * R.b + R.b ^ 2 = R.c ^ 2) (T' : Tri)
    (h0 : cornerAngle (T'.pts 1) (T'.pts 0) (T'.pts 2)
      = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2))
    (h1 : cornerAngle (T'.pts 2) (T'.pts 1) (T'.pts 0) = Real.pi / 3) :
    ∃ (s : ℝ) (hs : 0 < s) (M : ℕ) (D' : CongruentDissection M),
      D'.target.carrier = T'.carrier ∧ D'.model.Congruent (scaleTri s hs.ne' R.Δ) := by
  obtain ⟨T, q, hq, M, C, hC1, hC2, hang0, hang1⟩ := thm25_first R hγ
  obtain ⟨s, hs, D', e1, e2⟩ := transport_region R.Δ T q hq M C hC1 hC2 T' 2 0 1 (by decide) (by decide)
    (by decide)
    (by rw [angle_comm (T.pts 2) (T.pts 0) (T.pts 1), angle_comm (T'.pts 2) (T'.pts 0) (T'.pts 1)]
        exact hang0.trans h0.symm)
    (by rw [angle_comm (T.pts 0) (T.pts 1) (T.pts 2), angle_comm (T'.pts 0) (T'.pts 1) (T'.pts 2)]
        exact hang1.trans h1.symm)
  exact ⟨s, hs, M, D', e1, e2⟩

open Erdos634.LaczL26 Erdos634.LaczL22 in
/-- **Theorem 2.4, fourth triple `(α, α+β, α+β)` (range `N(a₀) > 0`), for every triangle isosceles at `T'₂` with apex
angle `α`.** -/
theorem thm24_fourth_any (R : RTri) (a0 : ℚ) (ha0 : 0 < a0) (ha1 : a0 < 1)
    (hA : R.a = a0 * R.c) (hB : R.b = (1 - a0 ^ 2) * R.c) (hN : 0 < a0 ^ 4 - (1 - a0 ^ 2) ^ 3)
    (T' : Tri) (hiso : dist (T'.pts 2) (T'.pts 0) = dist (T'.pts 2) (T'.pts 1))
    (hang : cornerAngle (T'.pts 0) (T'.pts 2) (T'.pts 1)
      = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2)) :
    ∃ (s : ℝ) (hs : 0 < s) (M : ℕ) (D' : CongruentDissection M),
      D'.target.carrier = T'.carrier ∧ D'.model.Congruent (scaleTri s hs.ne' R.Δ) := by
  obtain ⟨T, q, hq, M, C, hC1, hC2, hiso0, hang0⟩ := thm24_fourth R a0 ha0 ha1 hA hB hN
  have hT := base_angle T hiso0
  have hT' := base_angle T' hiso
  obtain ⟨s, hs, D', e1, e2⟩ := transport_region R.Δ T q hq M C hC1 hC2 T' 0 2 1 (by decide) (by decide)
    (by decide) (hang0.trans hang.symm)
    (by
      have : ∠ (T.pts 2) (T.pts 1) (T.pts 0) = ∠ (T'.pts 2) (T'.pts 1) (T'.pts 0) := by
        have h1 : cornerAngle (T.pts 0) (T.pts 2) (T.pts 1)
          = cornerAngle (T'.pts 0) (T'.pts 2) (T'.pts 1) := hang0.trans hang.symm
        unfold cornerAngle at h1
        linarith
      exact this)
  exact ⟨s, hs, M, D', e1, e2⟩

end Erdos634.LaczTransport

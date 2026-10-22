import Erdos634.Draft.LaczFormalL29T1
import Erdos634.Draft.LaczFormalL25Wit
import Erdos634.Draft.LaczFormalTransportCor

/-!
# Laczkovich Theorem 2.5, triple `(α, α, π - 2α)`: arbitrary triangles of the shape, witnesses, negative control

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Theorem 2.5, Fig. 7), Beeson, Beeson-Zhang, Zhang.
Witnesses: tiles `(5, 3, 7)` (`a > b`) and `(3, 5, 7)` (`a < b`), both with `γ = 2π/3`.  Negative control: `(2, 3, 4)`
is not of the form `c² = a² + ab + b²`.
-/

namespace Erdos634.LaczL29

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL24 Erdos634.LaczL25 Erdos634.Realizable
  Erdos634.DissectionMap Erdos634.LaczTransport EuclideanGeometry

/-- **Theorem 2.5, triple `(α, α, π - 2α)`, for every triangle isosceles at `T'₁` with angle `α` at `T'₀`.** -/
theorem thm25_t1_any (R : RTri) (hγ : R.a ^ 2 + R.a * R.b + R.b ^ 2 = R.c ^ 2) (T' : Tri)
    (hiso : dist (T'.pts 1) (T'.pts 0) = dist (T'.pts 1) (T'.pts 2))
    (hang : cornerAngle (T'.pts 1) (T'.pts 0) (T'.pts 2)
      = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2)) :
    ∃ (s : ℝ) (hs : 0 < s) (M : ℕ) (D' : CongruentDissection M),
      D'.target.carrier = T'.carrier ∧ D'.model.Congruent (scaleTri s hs.ne' R.Δ) := by
  obtain ⟨T, q, hq, M, C, hC1, hC2, hiso0, hang0⟩ := thm25_t1 R hγ
  have hb : ∀ S : Tri, dist (S.pts 1) (S.pts 0) = dist (S.pts 1) (S.pts 2) →
      ∠ (S.pts 0) (S.pts 2) (S.pts 1) = ∠ (S.pts 1) (S.pts 0) (S.pts 2) := by
    intro S h
    rw [angle_comm (S.pts 0) (S.pts 2) (S.pts 1)]
    exact (angle_eq_angle_of_dist_eq h).symm
  obtain ⟨s, hs, D', h1, h2⟩ := transport_region R.Δ T q hq M C hC1 hC2 T' 1 0 2 (by decide) (by decide)
    (by decide) (hang0.trans hang.symm)
    (by rw [hb T hiso0, hb T' hiso]; exact hang0.trans hang.symm)
  exact ⟨s, hs, M, D', h1, h2⟩

theorem wit_t1_537 :
    ∃ T' : Tri, dist (T'.pts 1) (T'.pts 0) = dist (T'.pts 1) (T'.pts 2) ∧
      cornerAngle (T'.pts 1) (T'.pts 0) (T'.pts 2) = cornerAngle (R537.Δ.pts 1) (R537.Δ.pts 0) (R537.Δ.pts 2) ∧
      ∃ (s : ℝ) (hs : 0 < s) (M : ℕ) (D' : CongruentDissection M),
        D'.target.carrier = T'.carrier ∧ D'.model.Congruent (scaleTri s hs.ne' R537.Δ) := by
  obtain ⟨T, q, hq, M, C, hC1, hC2, g1, g2⟩ := thm25_t1 R537 (by simp [R537]; norm_num)
  exact ⟨T, g1, g2, thm25_t1_any R537 (by simp [R537]; norm_num) T g1 g2⟩

theorem wit_t1_357 :
    ∃ T' : Tri, dist (T'.pts 1) (T'.pts 0) = dist (T'.pts 1) (T'.pts 2) ∧
      cornerAngle (T'.pts 1) (T'.pts 0) (T'.pts 2) = cornerAngle (R357.Δ.pts 1) (R357.Δ.pts 0) (R357.Δ.pts 2) ∧
      ∃ (s : ℝ) (hs : 0 < s) (M : ℕ) (D' : CongruentDissection M),
        D'.target.carrier = T'.carrier ∧ D'.model.Congruent (scaleTri s hs.ne' R357.Δ) := by
  obtain ⟨T, q, hq, M, C, hC1, hC2, g1, g2⟩ := thm25_t1 R357 (by simp [R357]; norm_num)
  exact ⟨T, g1, g2, thm25_t1_any R357 (by simp [R357]; norm_num) T g1 g2⟩

/-- Negative control: the tile `(2, 3, 4)` does not satisfy `c² = a² + ab + b²`. -/
theorem range_control_t25 : ¬ ((2 : ℚ) ^ 2 + 2 * 3 + 3 ^ 2 = 4 ^ 2) := by norm_num

#print axioms thm25_t1
#print axioms thm25_t1_any
#print axioms wit_t1_537
#print axioms wit_t1_357

end Erdos634.LaczL29

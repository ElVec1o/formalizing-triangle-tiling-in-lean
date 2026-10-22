import Erdos634.Draft.LaczFormalL27Final
import Erdos634.Draft.LaczFormalTransportWit

/-!
# Laczkovich Theorem 2.4, triples 2, 3, 5: arbitrary triangles of the shape, witnesses, negative control

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Theorem 2.4, Fig. 5), Beeson (arXiv 1206.2229),
Beeson-Zhang, Zhang.

`_any`: the explicit triangles of `thm24_second/third/fifth` are moved to ANY triangle with the stated angles by
`transport_region` (AAA similarity).  Witnesses: tile `(12, 7, 16)`, `a₀ = 3/4`, `N(3/4) = 81/256 - 343/4096 > 0`.
Negative control: tile `(2, 3, 4)` has `a₀ = 1/2` and `N(1/2) < 0`: the hypothesis `N > 0` is a genuine restriction.
-/

namespace Erdos634.LaczL27

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL24 Erdos634.LaczL26 EuclideanGeometry
  Erdos634.DissectionMap Erdos634.Realizable Erdos634.LaczTransport

section any

variable (R : RTri) (a0 : ℚ) (ha0 : 0 < a0) (ha1 : a0 < 1)
  (hA : R.a = a0 * R.c) (hB : R.b = (1 - a0 ^ 2) * R.c)
  (hN : 0 < a0 ^ 4 - (1 - a0 ^ 2) ^ 3)

include ha0 ha1 hA hB hN

/-- **Theorem 2.4, fifth triple, for every triangle with angles `β` at `T'₁`, `α+β` at `T'₂`** (so `2α` at `T'₀`). -/
theorem thm24_fifth_any (T' : Tri)
    (h1 : ∠ (T'.pts 0) (T'.pts 1) (T'.pts 2) = ∠ (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2))
    (h2 : ∠ (T'.pts 1) (T'.pts 2) (T'.pts 0)
      = ∠ (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) + ∠ (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2)) :
    ∃ (s : ℝ) (hs : 0 < s) (M : ℕ) (D' : CongruentDissection M),
      D'.target.carrier = T'.carrier ∧ D'.model.Congruent (scaleTri s hs.ne' R.Δ) := by
  obtain ⟨T, q, hq, M, C, hC1, hC2, g1, g2⟩ := thm24_fifth R a0 ha0 ha1 hA hB hN
  obtain ⟨s, hs, D', e1, e2⟩ := transport_region R.Δ T q hq M C hC1 hC2 T' 0 1 2 (by decide) (by decide) (by decide)
    (g1.trans h1.symm) (g2.trans h2.symm)
  exact ⟨s, hs, M, D', e1, e2⟩

/-- **Theorem 2.4, second triple, for every triangle with angles `β` at `T'₁` and at `T'₂`** (so `3α` at `T'₀`). -/
theorem thm24_second_any (T' : Tri)
    (h1 : ∠ (T'.pts 0) (T'.pts 1) (T'.pts 2) = ∠ (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2))
    (h2 : ∠ (T'.pts 1) (T'.pts 2) (T'.pts 0) = ∠ (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2)) :
    ∃ (s : ℝ) (hs : 0 < s) (M : ℕ) (D' : CongruentDissection M),
      D'.target.carrier = T'.carrier ∧ D'.model.Congruent (scaleTri s hs.ne' R.Δ) := by
  obtain ⟨T, q, hq, M, C, hC1, hC2, g1, g2⟩ := thm24_second R a0 ha0 ha1 hA hB hN
  obtain ⟨s, hs, D', e1, e2⟩ := transport_region R.Δ T q hq M C hC1 hC2 T' 0 1 2 (by decide) (by decide) (by decide)
    (g1.trans h1.symm) (g2.trans h2.symm)
  exact ⟨s, hs, M, D', e1, e2⟩

/-- **Theorem 2.4, third triple, for every triangle with angles `2α` at `T'₁` and `α` at `T'₂`** (so `2β` at `T'₀`). -/
theorem thm24_third_any (T' : Tri)
    (h1 : ∠ (T'.pts 0) (T'.pts 1) (T'.pts 2)
      = ∠ (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) + ∠ (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2))
    (h2 : ∠ (T'.pts 1) (T'.pts 2) (T'.pts 0) = ∠ (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2)) :
    ∃ (s : ℝ) (hs : 0 < s) (M : ℕ) (D' : CongruentDissection M),
      D'.target.carrier = T'.carrier ∧ D'.model.Congruent (scaleTri s hs.ne' R.Δ) := by
  obtain ⟨T, q, hq, M, C, hC1, hC2, g1, g2⟩ := thm24_third R a0 ha0 ha1 hA hB hN
  obtain ⟨s, hs, D', e1, e2⟩ := transport_region R.Δ T q hq M C hC1 hC2 T' 0 1 2 (by decide) (by decide) (by decide)
    (g1.trans h1.symm) (g2.trans h2.symm)
  exact ⟨s, hs, M, D', e1, e2⟩

end any

/-! ### the same with the abstract fourth-triple input `T4RSD` (both ranges, see `LaczFormalL28*`) -/

section anyGen

variable (R : RTri) (a0 : ℚ) (ha0 : 0 < a0) (ha1 : a0 < 1)
  (hA : R.a = a0 * R.c) (hB : R.b = (1 - a0 ^ 2) * R.c)
  (hN : T4RSD R a0 ha0 ha1)

include ha0 ha1 hA hB hN

/-- **Theorem 2.4, fifth triple, (any `T4RSD`) for every triangle with angles `β` at `T'₁`, `α+β` at `T'₂`** (so `2α` at `T'₀`). -/
theorem thm24_fifth_any_gen (T' : Tri)
    (h1 : ∠ (T'.pts 0) (T'.pts 1) (T'.pts 2) = ∠ (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2))
    (h2 : ∠ (T'.pts 1) (T'.pts 2) (T'.pts 0)
      = ∠ (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) + ∠ (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2)) :
    ∃ (s : ℝ) (hs : 0 < s) (M : ℕ) (D' : CongruentDissection M),
      D'.target.carrier = T'.carrier ∧ D'.model.Congruent (scaleTri s hs.ne' R.Δ) := by
  obtain ⟨T, q, hq, M, C, hC1, hC2, g1, g2⟩ := thm24_fifth_gen R a0 ha0 ha1 hA hB hN
  obtain ⟨s, hs, D', e1, e2⟩ := transport_region R.Δ T q hq M C hC1 hC2 T' 0 1 2 (by decide) (by decide) (by decide)
    (g1.trans h1.symm) (g2.trans h2.symm)
  exact ⟨s, hs, M, D', e1, e2⟩

/-- **Theorem 2.4, second triple, (any `T4RSD`) for every triangle with angles `β` at `T'₁` and at `T'₂`** (so `3α` at `T'₀`). -/
theorem thm24_second_any_gen (T' : Tri)
    (h1 : ∠ (T'.pts 0) (T'.pts 1) (T'.pts 2) = ∠ (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2))
    (h2 : ∠ (T'.pts 1) (T'.pts 2) (T'.pts 0) = ∠ (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2)) :
    ∃ (s : ℝ) (hs : 0 < s) (M : ℕ) (D' : CongruentDissection M),
      D'.target.carrier = T'.carrier ∧ D'.model.Congruent (scaleTri s hs.ne' R.Δ) := by
  obtain ⟨T, q, hq, M, C, hC1, hC2, g1, g2⟩ := thm24_second_gen R a0 ha0 ha1 hA hB hN
  obtain ⟨s, hs, D', e1, e2⟩ := transport_region R.Δ T q hq M C hC1 hC2 T' 0 1 2 (by decide) (by decide) (by decide)
    (g1.trans h1.symm) (g2.trans h2.symm)
  exact ⟨s, hs, M, D', e1, e2⟩

/-- **Theorem 2.4, third triple, (any `T4RSD`) for every triangle with angles `2α` at `T'₁` and `α` at `T'₂`** (so `2β` at `T'₀`). -/
theorem thm24_third_any_gen (T' : Tri)
    (h1 : ∠ (T'.pts 0) (T'.pts 1) (T'.pts 2)
      = ∠ (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) + ∠ (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2))
    (h2 : ∠ (T'.pts 1) (T'.pts 2) (T'.pts 0) = ∠ (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2)) :
    ∃ (s : ℝ) (hs : 0 < s) (M : ℕ) (D' : CongruentDissection M),
      D'.target.carrier = T'.carrier ∧ D'.model.Congruent (scaleTri s hs.ne' R.Δ) := by
  obtain ⟨T, q, hq, M, C, hC1, hC2, g1, g2⟩ := thm24_third_gen R a0 ha0 ha1 hA hB hN
  obtain ⟨s, hs, D', e1, e2⟩ := transport_region R.Δ T q hq M C hC1 hC2 T' 0 1 2 (by decide) (by decide) (by decide)
    (g1.trans h1.symm) (g2.trans h2.symm)
  exact ⟨s, hs, M, D', e1, e2⟩

end anyGen

/-! ### witnesses (tile `(12, 7, 16)`, `a₀ = 3/4`) -/

theorem wit_fifth_12716 :
    ∃ T' : Tri, ∠ (T'.pts 0) (T'.pts 1) (T'.pts 2) = ∠ (R12716.Δ.pts 0) (R12716.Δ.pts 1) (R12716.Δ.pts 2) ∧
      ∠ (T'.pts 1) (T'.pts 2) (T'.pts 0)
        = ∠ (R12716.Δ.pts 1) (R12716.Δ.pts 0) (R12716.Δ.pts 2) + ∠ (R12716.Δ.pts 0) (R12716.Δ.pts 1) (R12716.Δ.pts 2) ∧
      ∃ (s : ℝ) (hs : 0 < s) (M : ℕ) (D' : CongruentDissection M),
        D'.target.carrier = T'.carrier ∧ D'.model.Congruent (scaleTri s hs.ne' R12716.Δ) := by
  obtain ⟨T, q, hq, M, C, hC1, hC2, g1, g2⟩ := thm24_fifth R12716 (3 / 4) (by norm_num) (by norm_num)
    (by simp [R12716]; norm_num) (by simp [R12716]; norm_num) (by norm_num)
  exact ⟨T, g1, g2, thm24_fifth_any R12716 (3 / 4) (by norm_num) (by norm_num) (by simp [R12716]; norm_num)
    (by simp [R12716]; norm_num) (by norm_num) T g1 g2⟩

theorem wit_second_12716 :
    ∃ T' : Tri, ∠ (T'.pts 0) (T'.pts 1) (T'.pts 2) = ∠ (R12716.Δ.pts 0) (R12716.Δ.pts 1) (R12716.Δ.pts 2) ∧
      ∠ (T'.pts 1) (T'.pts 2) (T'.pts 0) = ∠ (R12716.Δ.pts 0) (R12716.Δ.pts 1) (R12716.Δ.pts 2) ∧
      ∃ (s : ℝ) (hs : 0 < s) (M : ℕ) (D' : CongruentDissection M),
        D'.target.carrier = T'.carrier ∧ D'.model.Congruent (scaleTri s hs.ne' R12716.Δ) := by
  obtain ⟨T, q, hq, M, C, hC1, hC2, g1, g2⟩ := thm24_second R12716 (3 / 4) (by norm_num) (by norm_num)
    (by simp [R12716]; norm_num) (by simp [R12716]; norm_num) (by norm_num)
  exact ⟨T, g1, g2, thm24_second_any R12716 (3 / 4) (by norm_num) (by norm_num) (by simp [R12716]; norm_num)
    (by simp [R12716]; norm_num) (by norm_num) T g1 g2⟩

theorem wit_third_12716 :
    ∃ T' : Tri, ∠ (T'.pts 0) (T'.pts 1) (T'.pts 2)
        = ∠ (R12716.Δ.pts 1) (R12716.Δ.pts 0) (R12716.Δ.pts 2) + ∠ (R12716.Δ.pts 1) (R12716.Δ.pts 0) (R12716.Δ.pts 2) ∧
      ∠ (T'.pts 1) (T'.pts 2) (T'.pts 0) = ∠ (R12716.Δ.pts 1) (R12716.Δ.pts 0) (R12716.Δ.pts 2) ∧
      ∃ (s : ℝ) (hs : 0 < s) (M : ℕ) (D' : CongruentDissection M),
        D'.target.carrier = T'.carrier ∧ D'.model.Congruent (scaleTri s hs.ne' R12716.Δ) := by
  obtain ⟨T, q, hq, M, C, hC1, hC2, g1, g2⟩ := thm24_third R12716 (3 / 4) (by norm_num) (by norm_num)
    (by simp [R12716]; norm_num) (by simp [R12716]; norm_num) (by norm_num)
  exact ⟨T, g1, g2, thm24_third_any R12716 (3 / 4) (by norm_num) (by norm_num) (by simp [R12716]; norm_num)
    (by simp [R12716]; norm_num) (by norm_num) T g1 g2⟩

/-- Negative control: the tile `(2, 3, 4)` is `a₀ = 1/2` of the right shape but `N(1/2) < 0`, outside the range. -/
theorem range_control_234 :
    R234.a = (1 / 2 : ℚ) * R234.c ∧ R234.b = (1 - (1 / 2 : ℚ) ^ 2) * R234.c ∧
      ¬ (0 < (1 / 2 : ℚ) ^ 4 - (1 - (1 / 2 : ℚ) ^ 2) ^ 3) := by
  refine ⟨by simp [R234]; norm_num, by simp [R234]; norm_num, by norm_num⟩

#print axioms thm24_fifth
#print axioms thm24_second
#print axioms thm24_third
#print axioms tile_relation
#print axioms thm24_fifth_any
#print axioms thm24_second_any
#print axioms thm24_third_any
#print axioms wit_fifth_12716
#print axioms wit_second_12716
#print axioms wit_third_12716
#print axioms range_control_234

end Erdos634.LaczL27

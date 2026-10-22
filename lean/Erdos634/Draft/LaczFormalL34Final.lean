import Erdos634.Draft.LaczFormalL32Main
import Erdos634.Draft.LaczFormalL33Equi
import Erdos634.Draft.LaczFormalL25Wit
import Erdos634.Draft.LaczFormalL29T1Any

/-!
# Laczkovich Theorem 2.5, all six triples of list (2), for every rational tile with `γ = 2π/3`

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Theorem 2.5, Figs. 6 and 7), Beeson, Beeson-Zhang, Zhang.

`thm25_all_triples`: let `Δ` be a rational tile with `γ = 2π/3` (`c² = a² + ab + b²`; the paper's hypothesis "`√3 sin α` and
`cos α` rational").  A triangle `T'` with angles
(1) `(α, α, π-2α)` [apex `T'₁`, `α` at `T'₀`], (2) `(α, 2α, π-3α)`, (3) `(α, 2β, 2α+β)`, (4) `(α, α+β, α+2β)`,
(5) `(2α, 2β, α+β)`, (6) `(α+β, α+β, α+β)` (the angles listed at `T'₀, T'₁, ...`)
is `Dissectable`: a union of finitely many congruent triangles similar to `Δ`.

Sources of the pieces: (4) `LaczL25.thm25_first` (Fig. 6); (1) `LaczL29.thm25_t1` (tile + Fig. 6); (5) `LaczL30` (trapezoid of
Lemma 2.2 (ii) + three tiles, Fig. 7 second picture); (3), (2) `LaczL31.attach` of one tile to the triangle of (5)
(third and fourth pictures); (6) `LaczL33` (three tiles + trapezoid, Fig. 7 fifth picture).  For `a < b` the roles of `α`, `β`
are exchanged inside (5), (6); `a = b` is impossible.
-/

namespace Erdos634.LaczL34

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL24 Erdos634.LaczL25 Erdos634.Realizable
  Erdos634.DissectionMap Erdos634.LaczTransport Erdos634.LaczL32 Erdos634.LaczL33 Erdos634.LaczL30 EuclideanGeometry

section

variable (R : RTri) (hγ : R.a ^ 2 + R.a * R.b + R.b ^ 2 = R.c ^ 2)

include hγ

theorem thm25_t2_any (T' : Tri)
    (h1 : cornerAngle (T'.pts 1) (T'.pts 0) (T'.pts 2) = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2))
    (h2 : cornerAngle (T'.pts 2) (T'.pts 1) (T'.pts 0)
      = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) + cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2)) :
    LaczL28.Dissectable R T' := by
  obtain ⟨T, hT, -, g1, g2⟩ := thm25_t2_rsd R hγ
  exact any_of_rsd R T hT T' (h1.trans g1.symm) (h2.trans g2.symm)

theorem thm25_t3_any (T' : Tri)
    (h1 : cornerAngle (T'.pts 1) (T'.pts 0) (T'.pts 2) = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2))
    (h2 : cornerAngle (T'.pts 2) (T'.pts 1) (T'.pts 0)
      = cornerAngle (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2) + cornerAngle (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2)) :
    LaczL28.Dissectable R T' := by
  obtain ⟨T, hT, -, g1, g2⟩ := thm25_t3_rsd R hγ
  exact any_of_rsd R T hT T' (h1.trans g1.symm) (h2.trans g2.symm)

theorem thm25_t5_any (T' : Tri)
    (h1 : cornerAngle (T'.pts 1) (T'.pts 0) (T'.pts 2)
      = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) + cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2))
    (h2 : cornerAngle (T'.pts 2) (T'.pts 1) (T'.pts 0)
      = cornerAngle (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2) + cornerAngle (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2)) :
    LaczL28.Dissectable R T' := by
  obtain ⟨T, hT, -, g1, g2⟩ := thm25_t5_rsd R hγ
  exact any_of_rsd R T hT T' (h1.trans g1.symm) (h2.trans g2.symm)

theorem thm25_t6_any (T' : Tri) (h1 : cornerAngle (T'.pts 1) (T'.pts 0) (T'.pts 2) = Real.pi / 3)
    (h2 : cornerAngle (T'.pts 2) (T'.pts 1) (T'.pts 0) = Real.pi / 3) :
    LaczL28.Dissectable R T' := by
  obtain ⟨T, hT, -, g1, g2, -⟩ := equi_all R hγ
  exact any_of_rsd R T hT T' (h1.trans g1.symm) (h2.trans g2.symm)

/-- **Laczkovich Theorem 2.5 (all six triples of (2)), every rational tile with `γ = 2π/3`.** -/
theorem thm25_all_triples :
    (∀ T' : Tri, dist (T'.pts 1) (T'.pts 0) = dist (T'.pts 1) (T'.pts 2) →
      cornerAngle (T'.pts 1) (T'.pts 0) (T'.pts 2) = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) →
      LaczL28.Dissectable R T') ∧
    (∀ T' : Tri, cornerAngle (T'.pts 1) (T'.pts 0) (T'.pts 2) = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) →
      cornerAngle (T'.pts 2) (T'.pts 1) (T'.pts 0)
        = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) + cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) →
      LaczL28.Dissectable R T') ∧
    (∀ T' : Tri, cornerAngle (T'.pts 1) (T'.pts 0) (T'.pts 2) = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) →
      cornerAngle (T'.pts 2) (T'.pts 1) (T'.pts 0)
        = cornerAngle (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2) + cornerAngle (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2) →
      LaczL28.Dissectable R T') ∧
    (∀ T' : Tri, cornerAngle (T'.pts 1) (T'.pts 0) (T'.pts 2) = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) →
      cornerAngle (T'.pts 2) (T'.pts 1) (T'.pts 0) = Real.pi / 3 → LaczL28.Dissectable R T') ∧
    (∀ T' : Tri, cornerAngle (T'.pts 1) (T'.pts 0) (T'.pts 2)
        = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) + cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) →
      cornerAngle (T'.pts 2) (T'.pts 1) (T'.pts 0)
        = cornerAngle (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2) + cornerAngle (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2) →
      LaczL28.Dissectable R T') ∧
    (∀ T' : Tri, cornerAngle (T'.pts 1) (T'.pts 0) (T'.pts 2) = Real.pi / 3 →
      cornerAngle (T'.pts 2) (T'.pts 1) (T'.pts 0) = Real.pi / 3 → LaczL28.Dissectable R T') :=
  ⟨fun T' h1 h2 => LaczL29.thm25_t1_any R hγ T' h1 h2,
   fun T' h1 h2 => thm25_t2_any R hγ T' h1 h2,
   fun T' h1 h2 => thm25_t3_any R hγ T' h1 h2,
   fun T' h1 h2 => thm25_first_any R hγ T' h1 h2,
   fun T' h1 h2 => thm25_t5_any R hγ T' h1 h2,
   fun T' h1 h2 => thm25_t6_any R hγ T' h1 h2⟩

end

#print axioms thm25_all_triples

/-! ### witnesses: tiles `(5,3,7)` (`a > b`) and `(3,5,7)` (`a < b`), triples (2), (3), (5), (6) -/

theorem wit_t2_537 :
    ∃ T' : Tri, cornerAngle (T'.pts 1) (T'.pts 0) (T'.pts 2) = cornerAngle (R537.Δ.pts 1) (R537.Δ.pts 0) (R537.Δ.pts 2) ∧
      cornerAngle (T'.pts 2) (T'.pts 1) (T'.pts 0)
        = cornerAngle (R537.Δ.pts 1) (R537.Δ.pts 0) (R537.Δ.pts 2) + cornerAngle (R537.Δ.pts 1) (R537.Δ.pts 0) (R537.Δ.pts 2) ∧
      LaczL28.Dissectable R537 T' := by
  have hγ : R537.a ^ 2 + R537.a * R537.b + R537.b ^ 2 = R537.c ^ 2 := by simp [R537]; norm_num
  obtain ⟨T, hT, -, g1, g2⟩ := thm25_t2_rsd R537 hγ
  exact ⟨T, g1, g2, thm25_t2_any R537 hγ T g1 g2⟩

theorem wit_t2_357 :
    ∃ T' : Tri, cornerAngle (T'.pts 1) (T'.pts 0) (T'.pts 2) = cornerAngle (R357.Δ.pts 1) (R357.Δ.pts 0) (R357.Δ.pts 2) ∧
      cornerAngle (T'.pts 2) (T'.pts 1) (T'.pts 0)
        = cornerAngle (R357.Δ.pts 1) (R357.Δ.pts 0) (R357.Δ.pts 2) + cornerAngle (R357.Δ.pts 1) (R357.Δ.pts 0) (R357.Δ.pts 2) ∧
      LaczL28.Dissectable R357 T' := by
  have hγ : R357.a ^ 2 + R357.a * R357.b + R357.b ^ 2 = R357.c ^ 2 := by simp [R357]; norm_num
  obtain ⟨T, hT, -, g1, g2⟩ := thm25_t2_rsd R357 hγ
  exact ⟨T, g1, g2, thm25_t2_any R357 hγ T g1 g2⟩

theorem wit_t3_537 :
    ∃ T' : Tri, cornerAngle (T'.pts 1) (T'.pts 0) (T'.pts 2) = cornerAngle (R537.Δ.pts 1) (R537.Δ.pts 0) (R537.Δ.pts 2) ∧
      cornerAngle (T'.pts 2) (T'.pts 1) (T'.pts 0)
        = cornerAngle (R537.Δ.pts 0) (R537.Δ.pts 1) (R537.Δ.pts 2) + cornerAngle (R537.Δ.pts 0) (R537.Δ.pts 1) (R537.Δ.pts 2) ∧
      LaczL28.Dissectable R537 T' := by
  have hγ : R537.a ^ 2 + R537.a * R537.b + R537.b ^ 2 = R537.c ^ 2 := by simp [R537]; norm_num
  obtain ⟨T, hT, -, g1, g2⟩ := thm25_t3_rsd R537 hγ
  exact ⟨T, g1, g2, thm25_t3_any R537 hγ T g1 g2⟩

theorem wit_t3_357 :
    ∃ T' : Tri, cornerAngle (T'.pts 1) (T'.pts 0) (T'.pts 2) = cornerAngle (R357.Δ.pts 1) (R357.Δ.pts 0) (R357.Δ.pts 2) ∧
      cornerAngle (T'.pts 2) (T'.pts 1) (T'.pts 0)
        = cornerAngle (R357.Δ.pts 0) (R357.Δ.pts 1) (R357.Δ.pts 2) + cornerAngle (R357.Δ.pts 0) (R357.Δ.pts 1) (R357.Δ.pts 2) ∧
      LaczL28.Dissectable R357 T' := by
  have hγ : R357.a ^ 2 + R357.a * R357.b + R357.b ^ 2 = R357.c ^ 2 := by simp [R357]; norm_num
  obtain ⟨T, hT, -, g1, g2⟩ := thm25_t3_rsd R357 hγ
  exact ⟨T, g1, g2, thm25_t3_any R357 hγ T g1 g2⟩

theorem wit_t5_537 :
    ∃ T' : Tri, cornerAngle (T'.pts 1) (T'.pts 0) (T'.pts 2)
        = cornerAngle (R537.Δ.pts 1) (R537.Δ.pts 0) (R537.Δ.pts 2) + cornerAngle (R537.Δ.pts 1) (R537.Δ.pts 0) (R537.Δ.pts 2) ∧
      cornerAngle (T'.pts 2) (T'.pts 1) (T'.pts 0)
        = cornerAngle (R537.Δ.pts 0) (R537.Δ.pts 1) (R537.Δ.pts 2) + cornerAngle (R537.Δ.pts 0) (R537.Δ.pts 1) (R537.Δ.pts 2) ∧
      LaczL28.Dissectable R537 T' := by
  have hγ : R537.a ^ 2 + R537.a * R537.b + R537.b ^ 2 = R537.c ^ 2 := by simp [R537]; norm_num
  obtain ⟨T, hT, -, g1, g2⟩ := thm25_t5_rsd R537 hγ
  exact ⟨T, g1, g2, thm25_t5_any R537 hγ T g1 g2⟩

theorem wit_t5_357 :
    ∃ T' : Tri, cornerAngle (T'.pts 1) (T'.pts 0) (T'.pts 2)
        = cornerAngle (R357.Δ.pts 1) (R357.Δ.pts 0) (R357.Δ.pts 2) + cornerAngle (R357.Δ.pts 1) (R357.Δ.pts 0) (R357.Δ.pts 2) ∧
      cornerAngle (T'.pts 2) (T'.pts 1) (T'.pts 0)
        = cornerAngle (R357.Δ.pts 0) (R357.Δ.pts 1) (R357.Δ.pts 2) + cornerAngle (R357.Δ.pts 0) (R357.Δ.pts 1) (R357.Δ.pts 2) ∧
      LaczL28.Dissectable R357 T' := by
  have hγ : R357.a ^ 2 + R357.a * R357.b + R357.b ^ 2 = R357.c ^ 2 := by simp [R357]; norm_num
  obtain ⟨T, hT, -, g1, g2⟩ := thm25_t5_rsd R357 hγ
  exact ⟨T, g1, g2, thm25_t5_any R357 hγ T g1 g2⟩

theorem wit_t6_537 :
    ∃ T' : Tri, cornerAngle (T'.pts 1) (T'.pts 0) (T'.pts 2) = Real.pi / 3 ∧
      cornerAngle (T'.pts 2) (T'.pts 1) (T'.pts 0) = Real.pi / 3 ∧ LaczL28.Dissectable R537 T' := by
  have hγ : R537.a ^ 2 + R537.a * R537.b + R537.b ^ 2 = R537.c ^ 2 := by simp [R537]; norm_num
  obtain ⟨T, hT, -, g1, g2, -⟩ := equi_all R537 hγ
  exact ⟨T, g1, g2, thm25_t6_any R537 hγ T g1 g2⟩

theorem wit_t6_357 :
    ∃ T' : Tri, cornerAngle (T'.pts 1) (T'.pts 0) (T'.pts 2) = Real.pi / 3 ∧
      cornerAngle (T'.pts 2) (T'.pts 1) (T'.pts 0) = Real.pi / 3 ∧ LaczL28.Dissectable R357 T' := by
  have hγ : R357.a ^ 2 + R357.a * R357.b + R357.b ^ 2 = R357.c ^ 2 := by simp [R357]; norm_num
  obtain ⟨T, hT, -, g1, g2, -⟩ := equi_all R357 hγ
  exact ⟨T, g1, g2, thm25_t6_any R357 hγ T g1 g2⟩

#print axioms wit_t2_537
#print axioms wit_t2_357
#print axioms wit_t3_537
#print axioms wit_t3_357
#print axioms wit_t5_537
#print axioms wit_t5_357
#print axioms wit_t6_537
#print axioms wit_t6_357

end Erdos634.LaczL34

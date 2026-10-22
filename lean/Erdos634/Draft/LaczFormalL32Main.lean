import Erdos634.Draft.LaczFormalL31Attach
import Erdos634.Draft.LaczFormalL28All
import Erdos634.Draft.LaczFormalL29T1Any

/-!
# Laczkovich Theorem 2.5: triples `(2α, 2β, α+β)`, `(α, 2β, 2α+β)`, `(α, 2α, π-3α)` for every rational tile with `γ = 2π/3`

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Theorem 2.5, Fig. 7), Beeson, Beeson-Zhang, Zhang.

Decoded from Fig. 7 (by the angle labels; every piece size is determined by the picture):
* second picture: `Θ = (A L V)`, angles `2α, 2β, α+β`: tiles `AOM`, `AVO` (scale 1), `VLO'` (scale `ν`) and the trapezoid
  `MLO'O` of Lemma 2.2 (ii) (`LaczFormalL30*`; `theta_all`, valid for `b < a`; for `a < b` exchange `α` and `β`);
* third picture `(α, 2β, 2α+β)`: `Θ` plus the tile `(X, U, S)` on the side `A V` (`U = A`, angle `2α`), `X` on `L V` beyond `V`;
* fourth picture `(α, 2α, π-3α)`: `Θ` plus the tile on the side `L V` (`U = L`, angle `2β`), `X` on `A V` beyond `V`.
Both gluings are `LaczFormalL31Attach.attach`.
-/

namespace Erdos634.LaczL32

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL21 Erdos634.LaczL24 Erdos634.Realizable
  Erdos634.DissectionMap Erdos634.LaczTransport Erdos634.LaczL30 Erdos634.LaczL31 EuclideanGeometry

/-- Any triangle with the same two angles at `T'₀`, `T'₁` is a union of congruent tiles similar to `Δ`. -/
theorem any_of_rsd (R : RTri) (T : Tri) (hT : RatSimDiss R.Δ T.carrier) (T' : Tri)
    (h1 : cornerAngle (T'.pts 1) (T'.pts 0) (T'.pts 2) = cornerAngle (T.pts 1) (T.pts 0) (T.pts 2))
    (h2 : cornerAngle (T'.pts 2) (T'.pts 1) (T'.pts 0) = cornerAngle (T.pts 2) (T.pts 1) (T.pts 0)) :
    LaczL28.Dissectable R T' := by
  obtain ⟨q, hq, M, C, hC1, hC2⟩ := RatSimDiss.toCongruent R.rational hT
  obtain ⟨s, hs, D', e1, e2⟩ := transport_region R.Δ T q hq M C hC1 hC2 T' 2 1 0 (by decide) (by decide) (by decide)
    h2.symm h1.symm
  exact ⟨s, hs, M, D', e1, e2⟩

/-- `RatSimDiss` gives the congruent region dissection. -/
theorem region_of_rsd (R : RTri) (T : Tri) (hT : RatSimDiss R.Δ T.carrier) :
    ∃ (q : ℕ) (hq : 0 < q) (M : ℕ) (C : Erdos634.RegionDissection.CongruentRegionDissection M),
      C.region = T.carrier ∧
      C.model = scaleTri (1 / (q : ℝ)) (one_div_pos.mpr (Nat.cast_pos.mpr hq)).ne' R.Δ :=
  RatSimDiss.toCongruent R.rational hT

section

variable (R : RTri) (hγ : R.a ^ 2 + R.a * R.b + R.b ^ 2 = R.c ^ 2)

include hγ

/-- **Third picture, triple `(α, 2β, 2α+β)`.** -/
theorem thm25_t3_rsd :
    ∃ T : Tri, RatSimDiss R.Δ T.carrier ∧ IsRationalTri T ∧
      cornerAngle (T.pts 1) (T.pts 0) (T.pts 2) = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) ∧
      cornerAngle (T.pts 2) (T.pts 1) (T.pts 0)
        = cornerAngle (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2) + cornerAngle (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2) := by
  obtain ⟨Θ, h1, h2, a1, a2, a3⟩ := theta_all R hγ
  obtain ⟨T', g1, g2, g3, g4⟩ := attach R hγ Θ h1 h2 (by
    unfold cornerAngle at a3 ⊢; exact a3)
  refine ⟨T', g1, g2, g3, ?_⟩
  rw [g4, ← a2]
  unfold cornerAngle
  exact EuclideanGeometry.angle_comm _ _ _

/-- **Fourth picture, triple `(α, 2α, π-3α)`.** -/
theorem thm25_t2_rsd :
    ∃ T : Tri, RatSimDiss R.Δ T.carrier ∧ IsRationalTri T ∧
      cornerAngle (T.pts 1) (T.pts 0) (T.pts 2) = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) ∧
      cornerAngle (T.pts 2) (T.pts 1) (T.pts 0)
        = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) + cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) := by
  obtain ⟨Θ, h1, h2, a1, a2, a3⟩ := theta_all R hγ
  have hcar : (Θ.relabel (Equiv.swap 0 1)).carrier = Θ.carrier := by
    show convexHull ℝ (Set.range (Θ.pts ∘ (Equiv.swap 0 1))) = convexHull ℝ (Set.range Θ.pts)
    rw [(Equiv.swap (0 : Fin 3) 1).surjective.range_comp Θ.pts]
  have e0 : (Equiv.swap (0 : Fin 3) 1) 0 = 1 := by decide
  have e1 : (Equiv.swap (0 : Fin 3) 1) 1 = 0 := by decide
  have e2 : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := by decide
  obtain ⟨T', g1, g2, g3, g4⟩ := attach R hγ (Θ.relabel (Equiv.swap 0 1)) (by rw [hcar]; exact h1)
    (by
      intro j k
      obtain ⟨s, hs⟩ := h2 ((Equiv.swap 0 1) j) ((Equiv.swap 0 1) k)
      exact ⟨s, hs⟩)
    (by
      show cornerAngle (Θ.pts ((Equiv.swap 0 1) 0)) (Θ.pts ((Equiv.swap 0 1) 2)) (Θ.pts ((Equiv.swap 0 1) 1)) = _
      rw [e0, e1, e2]
      unfold cornerAngle at a3 ⊢
      rw [EuclideanGeometry.angle_comm]; exact a3)
  refine ⟨T', g1, g2, g3, ?_⟩
  rw [g4]
  show cornerAngle (Θ.pts ((Equiv.swap 0 1) 0)) (Θ.pts ((Equiv.swap 0 1) 1)) (Θ.pts ((Equiv.swap 0 1) 2)) = _
  rw [e0, e1, e2]
  unfold cornerAngle at a1 ⊢
  exact a1

/-- **Second picture, triple `(2α, 2β, α+β)`.** -/
theorem thm25_t5_rsd :
    ∃ T : Tri, RatSimDiss R.Δ T.carrier ∧ IsRationalTri T ∧
      cornerAngle (T.pts 1) (T.pts 0) (T.pts 2)
        = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) + cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) ∧
      cornerAngle (T.pts 2) (T.pts 1) (T.pts 0)
        = cornerAngle (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2) + cornerAngle (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2) := by
  obtain ⟨Θ, h1, h2, a1, a2, a3⟩ := theta_all R hγ
  exact ⟨Θ, h1, h2, a1, a2⟩

end

#print axioms thm25_t3_rsd
#print axioms thm25_t2_rsd
#print axioms thm25_t5_rsd

end Erdos634.LaczL32

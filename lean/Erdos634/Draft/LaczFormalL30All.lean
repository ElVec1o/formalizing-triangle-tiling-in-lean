import Erdos634.Draft.LaczFormalL30Theta2

/-!
# Laczkovich Theorem 2.5, triple `(2α, 2β, α+β)`: the triangle `Θ`, every rational tile with `γ = 2π/3`

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Theorem 2.5, Fig. 7), Beeson, Beeson-Zhang, Zhang.
-/

namespace Erdos634.LaczL30

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL21 Erdos634.LaczL24 Erdos634.Realizable
  Erdos634.DissectionMap

/-- the shape of `Θ`: `T₀` has angle `2α`, `T₁` angle `2β`, `T₂` angle `π/3 = α + β`. -/
def ThetaShape (R : RTri) (T : Tri) : Prop :=
  cornerAngle (T.pts 1) (T.pts 0) (T.pts 2)
      = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) + cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) ∧
    cornerAngle (T.pts 2) (T.pts 1) (T.pts 0)
      = cornerAngle (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2) + cornerAngle (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2) ∧
    cornerAngle (T.pts 0) (T.pts 2) (T.pts 1) = Real.pi / 3

theorem theta_lt (R : RTri) (hγ : R.a ^ 2 + R.a * R.b + R.b ^ 2 = R.c ^ 2) (hab : R.b < R.a) :
    ∃ T : Tri, RatSimDiss R.Δ T.carrier ∧ IsRationalTri T ∧ ThetaShape R T := by
  have ha : (0 : ℝ) < R.a := by exact_mod_cast R.pa
  obtain ⟨w, d, hw, hd, hwd, hdet⟩ := exists_gram_chart (R.a : ℝ) (R.a : ℝ) (-1 / 2) ha ha (by norm_num)
  set K : ℝ := ((kq R : ℚ) : ℝ) with hKdef
  have hk0 := hK0 R
  have hk1 := hK1 R hab
  obtain ⟨T, h1, h2, e0, e1, e2⟩ := theta_chart_T R hγ hab w d hdet hw hd hwd K rfl hk0 hk1
  have hc := thm25_t5_chart R hγ hab w d hdet hw hd hwd K rfl hk0 hk1
  have hv := theta_angleV R hγ hab w d hdet hw hd hwd K rfl hk0 hk1
  refine ⟨T, h1, h2, ?_, ?_, ?_⟩
  · show cornerAngle (T.pts 1) (T.pts 0) (T.pts 2) = _
    rw [e0, e1, e2]; exact hc.1
  · show cornerAngle (T.pts 2) (T.pts 1) (T.pts 0) = _
    rw [e0, e1, e2]; exact hc.2
  · show cornerAngle (T.pts 0) (T.pts 2) (T.pts 1) = _
    rw [e0, e1, e2]; exact hv

/-- A rational tile with `γ = 2π/3` has `a ≠ b` (else `c² = 3a²`, impossible). -/
theorem a_ne_b (R : RTri) (hγ : R.a ^ 2 + R.a * R.b + R.b ^ 2 = R.c ^ 2) : R.a ≠ R.b := by
  intro h
  have ha := R.pa
  have h3 : ((R.c / R.a : ℚ)) ^ 2 = 3 := by
    rw [div_pow]; field_simp; rw [h] at hγ ⊢; nlinarith [hγ]
  have hirr : Irrational (Real.sqrt (3 : ℕ)) := Nat.Prime.irrational_sqrt (by norm_num)
  apply hirr
  refine ⟨R.c / R.a, ?_⟩
  have hnn : (0 : ℝ) ≤ ((R.c / R.a : ℚ) : ℝ) := by
    have : (0 : ℚ) ≤ R.c / R.a := by have := R.pc; positivity
    exact_mod_cast this
  have h3r : (((R.c / R.a : ℚ)) : ℝ) ^ 2 = 3 := by exact_mod_cast h3
  rw [← Real.sqrt_sq hnn, h3r]
  norm_num

theorem theta_all (R : RTri) (hγ : R.a ^ 2 + R.a * R.b + R.b ^ 2 = R.c ^ 2) :
    ∃ T : Tri, RatSimDiss R.Δ T.carrier ∧ IsRationalTri T ∧ ThetaShape R T := by
  rcases lt_trichotomy R.b R.a with hab | hab | hab
  · exact theta_lt R hγ hab
  · exact absurd hab.symm (a_ne_b R hγ)
  · -- exchange the roles of `α` and `β`
    have hγ' : R.sw01.a ^ 2 + R.sw01.a * R.sw01.b + R.sw01.b ^ 2 = R.sw01.c ^ 2 := by
      simp only [RTri.sw01]; linarith [hγ]
    have hlt : R.sw01.b < R.sw01.a := by simp only [RTri.sw01]; exact hab
    obtain ⟨T0, h1, h2, a1, a2, a3⟩ := theta_lt R.sw01 hγ' hlt
    have e0 : (Equiv.swap (0 : Fin 3) 1) 0 = 1 := by decide
    have e1 : (Equiv.swap (0 : Fin 3) 1) 1 = 0 := by decide
    have e2 : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := by decide
    have hcar : (T0.relabel (Equiv.swap 0 1)).carrier = T0.carrier := by
      show convexHull ℝ (Set.range (T0.pts ∘ (Equiv.swap 0 1))) = convexHull ℝ (Set.range T0.pts)
      rw [(Equiv.swap (0 : Fin 3) 1).surjective.range_comp T0.pts]
    refine ⟨T0.relabel (Equiv.swap 0 1), ?_, ?_, ?_⟩
    · rw [hcar]; exact RatSimDiss.relabel (Δ := R.Δ) (Equiv.swap 0 1) h1
    · intro j k
      obtain ⟨s, hs⟩ := h2 ((Equiv.swap 0 1) j) ((Equiv.swap 0 1) k)
      exact ⟨s, hs⟩
    · have hα : cornerAngle (R.sw01.Δ.pts 1) (R.sw01.Δ.pts 0) (R.sw01.Δ.pts 2)
          = cornerAngle (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2) := by
        simp only [RTri.sw01, Tri.relabel_pts, e0, e1, e2]
      have hβ : cornerAngle (R.sw01.Δ.pts 0) (R.sw01.Δ.pts 1) (R.sw01.Δ.pts 2)
          = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) := by
        simp only [RTri.sw01, Tri.relabel_pts, e0, e1, e2]
      rw [hα] at a1
      rw [hβ] at a2
      refine ⟨?_, ?_, ?_⟩
      · show cornerAngle (T0.pts ((Equiv.swap 0 1) 1)) (T0.pts ((Equiv.swap 0 1) 0)) (T0.pts ((Equiv.swap 0 1) 2)) = _
        rw [e0, e1, e2]
        unfold cornerAngle at a2 ⊢
        rw [EuclideanGeometry.angle_comm]; exact a2
      · show cornerAngle (T0.pts ((Equiv.swap 0 1) 2)) (T0.pts ((Equiv.swap 0 1) 1)) (T0.pts ((Equiv.swap 0 1) 0)) = _
        rw [e0, e1, e2]
        unfold cornerAngle at a1 ⊢
        rw [EuclideanGeometry.angle_comm]; exact a1
      · show cornerAngle (T0.pts ((Equiv.swap 0 1) 0)) (T0.pts ((Equiv.swap 0 1) 2)) (T0.pts ((Equiv.swap 0 1) 1)) = _
        rw [e0, e1, e2]
        unfold cornerAngle at a3 ⊢
        rw [EuclideanGeometry.angle_comm]; exact a3

#print axioms theta_all

end Erdos634.LaczL30

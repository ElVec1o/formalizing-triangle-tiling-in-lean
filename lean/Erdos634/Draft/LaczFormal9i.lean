import Erdos634.Draft.LaczFormal9h
import Erdos634.Draft.LaczFormalL56Final
import Erdos634.Draft.LaczFormalL2b
import Erdos634.Draft.LaczFormalGraphFinal

/-!
# Laczkovich, Discrete Math. 140 (1995), Theorem 5.3: the `c(T)` clause (congruent tiles)

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) Thm 5.1, 5.3), Beeson, Beeson-Rosu, Beeson-Zhang.
Formalization debt, not progress on the /goal outcomes.

Printed Thm 5.3: if the angles of `T` are rational multiples of `pi` and `T` is not equilateral then `s(T) <= 4` and `c(T) <= 2`;
more exactly, `c(T) = 1` if `T` is not isosceles or is the isosceles right triangle, and `c(T) = 2` if `T` is isosceles but neither
right nor equilateral.  `c(T)` counts the non-similar triangles `Delta` such that `T` is dissected into congruent copies of a triangle
similar to `Delta`.

* `thm53_c_classify`: any `CongruentDissection` of a non-equilateral commensurable target is by a tile of the SAME shape as the target,
  or by the right tile `(alpha, pi/2 - alpha, pi/2)` where `alpha` is an angle that occurs twice in the target.
* `thm53_c_scalene`: a target with three distinct angles is tiled only by tiles of its own shape (`c(T) = 1`).
* `thm53_c_right_isosceles`: the isosceles right target is tiled only by tiles of its own shape (`c(T) = 1`).
This is the "upper bound" half of the `c(T)` clause; existence of the second (right) tile for an isosceles `T` is `LaczFormal9j`.
The cardinality `c(T)` itself (a `Set.ncard` of similarity classes) and the clause `s(T) <= 4` (non-congruent pieces) are not stated.
-/

open scoped Classical
open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.LaczFormal Erdos634.Draft.LaczFormal.Graph

namespace Erdos634.Laczkovich9

theorem exists_perm_02 : ∀ k l : Fin 3, l ≠ k → ∃ σ : Equiv.Perm (Fin 3), σ 0 = l ∧ σ 2 = k := by decide

/-- **Thm 5.3, `c(T)` clause, classification form.** -/
theorem thm53_c_classify {N : ℕ} (D : CongruentDissection N) (hne : ¬ Equilateral D) (hcomm : CommAngles D.target) :
    (∃ σ : Equiv.Perm (Fin 3), ∀ k, D.model.angleAt (σ k) = D.target.angleAt k) ∨
    ∃ (α : ℝ) (j₁ j₂ : Fin 3), j₁ ≠ j₂ ∧ D.target.angleAt j₁ = α ∧ D.target.angleAt j₂ = α ∧
      TileAngles D α (Real.pi / 2 - α) (Real.pi / 2) := by
  have hm := lemma1b D hne hcomm
  have hpi := Real.pi_pos
  rcases classify_rational D hm with hsim | ⟨k, l, hlk, hk, j₁, j₂, hj, h1, h2⟩ | hexc
  · obtain ⟨μ, τ, h⟩ := hsim
    exact Or.inl ⟨τ, fun k => (h k).1.symm⟩
  · right
    obtain ⟨σ, hσ0, hσ2⟩ := exists_perm_02 k l hlk
    refine ⟨D.model.angleAt l, j₁, j₂, hj, h1, h2, σ, ?_, ?_, ?_⟩
    · rw [hσ0]
    · have hs := Erdos634.Draft.G3CAng.sum_perm D.model σ
      rw [hσ0, hσ2, hk] at hs
      linarith
    · rw [hσ2, hk]
  · right
    rcases hexc with ⟨ht, hg⟩ | ⟨ht, hg⟩ | ⟨ht, hg⟩
    · exact absurd (fun j => by rw [tgt_all D hg j]; ring) hne
    · obtain ⟨σ, g0, g1, g2⟩ := hg
      refine ⟨1 * Real.pi / 6, σ 0, σ 1, σ.injective.ne (by decide), g0, g1, ?_⟩
      have : (Real.pi / 2 - 1 * Real.pi / 6) = 2 * Real.pi / 6 := by ring
      rw [this]
      have : (Real.pi / 2) = 3 * Real.pi / 6 := by ring
      rw [this]
      exact ht
    · exact absurd (fun j => by rw [tgt_all D hg j]; ring) hne

/-- **Thm 5.3, `c(T) = 1` for a target with three distinct angles.** -/
theorem thm53_c_scalene {N : ℕ} (D : CongruentDissection N) (hne : ¬ Equilateral D) (hcomm : CommAngles D.target)
    (hs : ∀ i j : Fin 3, i ≠ j → D.target.angleAt i ≠ D.target.angleAt j) :
    ∃ σ : Equiv.Perm (Fin 3), ∀ k, D.model.angleAt (σ k) = D.target.angleAt k := by
  rcases thm53_c_classify D hne hcomm with h | ⟨α, j₁, j₂, hj, h1, h2, -⟩
  · exact h
  · exact absurd (h1.trans h2.symm) (hs j₁ j₂ hj)

/-- **Thm 5.3, `c(T) = 1` for the isosceles right triangle** (target angles `pi/4, pi/4, pi/2`): the tile has the same angles. -/
theorem thm53_c_right_isosceles {N : ℕ} (D : CongruentDissection N) (hcomm : CommAngles D.target)
    (hT : TgtAngles D (Real.pi / 4) (Real.pi / 4) (Real.pi / 2)) :
    TileAngles D (Real.pi / 4) (Real.pi / 4) (Real.pi / 2) := by
  have hpi := Real.pi_pos
  have hne : ¬ Equilateral D := by
    intro hE
    obtain ⟨σ, g0, -, -⟩ := hT
    have := hE (σ 0)
    rw [g0] at this
    linarith
  rcases thm53_c_classify D hne hcomm with ⟨σ, hσ⟩ | ⟨α, j₁, j₂, hj, h1, h2, ht⟩
  · -- same shape: the tile angles are the target angles
    obtain ⟨τ, g0, g1, g2⟩ := hT
    refine ⟨τ.trans σ, ?_, ?_, ?_⟩
    · simp only [Equiv.trans_apply]; rw [hσ]; exact g0
    · simp only [Equiv.trans_apply]; rw [hσ]; exact g1
    · simp only [Equiv.trans_apply]; rw [hσ]; exact g2
  · -- a right tile with acute angle alpha, alpha an angle occurring twice in the target: alpha = pi/4
    obtain ⟨τ, g0, g1, g2⟩ := hT
    have hα : α = Real.pi / 4 := by
      -- two distinct indices carry the equal angle alpha; the only repeated value of (pi/4, pi/4, pi/2) is pi/4
      obtain ⟨a, ha⟩ := τ.surjective j₁
      obtain ⟨b, hb⟩ := τ.surjective j₂
      have hab : a ≠ b := by rintro rfl; exact hj (by rw [← ha, ← hb])
      have va : D.target.angleAt j₁ = ![Real.pi / 4, Real.pi / 4, Real.pi / 2] a := by
        rw [← ha]; fin_cases a <;> simp [g0, g1, g2]
      have vb : D.target.angleAt j₂ = ![Real.pi / 4, Real.pi / 4, Real.pi / 2] b := by
        rw [← hb]; fin_cases b <;> simp [g0, g1, g2]
      rw [h1] at va
      rw [h2] at vb
      fin_cases a <;> fin_cases b <;> simp at hab va vb <;> first | linarith | (exfalso; linarith)
    subst hα
    have e : Real.pi / 2 - Real.pi / 4 = Real.pi / 4 := by ring
    rw [e] at ht
    exact ht

end Erdos634.Laczkovich9

#print axioms Erdos634.Laczkovich9.thm53_c_classify
#print axioms Erdos634.Laczkovich9.thm53_c_scalene
#print axioms Erdos634.Laczkovich9.thm53_c_right_isosceles

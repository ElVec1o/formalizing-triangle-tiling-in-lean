import Erdos634.Draft.LaczFormalThm33if4

/-!
# Laczkovich DCG 48 (2012) Thm 3.3, "if" direction and the equivalence, module 5 of 5

NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012) 330-372, Thm 3.3; Discrete Math. 140 (1995) 79-94, Thm 3.1), Beeson, Beeson-Zhang.

* `Thm33Clauses x y z` : the printed clauses (i), (ii), (iii) for the ordered triple.
* `thm33_if`            : `x, y, z > 0`, `x + y + z = π`, `Thm33Clauses x y z`  =>  `Thm33If x y z` (an equilateral triangle is
                          dissected into congruent triangles with angles `x, y, z`).
* `thm33_iff`           : the printed Theorem 3.3: such a dissection exists iff a permutation of `(x, y, z)` satisfies the clauses.
                          The "only if" is `thm33_only_if` (`LaczFormalThm33iii3`, which is stated for an arbitrary `CongruentDissection`).
-/

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional
  Erdos634.Draft.LaczFormal Erdos634.Draft.LaczFormal.Thm21 Erdos634.Draft.LaczFormal.RG

namespace Erdos634.LaczThm33If

def Thm33Clauses (x y z : ℝ) : Prop :=
  (x = Real.pi / 6 ∧ y = Real.pi / 6 ∧ z = 2 * Real.pi / 3) ∨
  (x = Real.pi / 6 ∧ y = Real.pi / 2 ∧ z = Real.pi / 3) ∨
  ((z = Real.pi / 3 ∨ z = 2 * Real.pi / 3) ∧ Comm (Real.sin x) (Real.sin y) ∧ Comm (Real.sin y) (Real.sin z) ∧
    Comm (Real.sin x) (Real.sin z))

theorem thm33_if (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hsum : x + y + z = Real.pi)
    (h : Thm33Clauses x y z) : Thm33If x y z := by
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨h3, h1, h2, h4⟩
  · exact clause_i
  · exact clause_ii
  · exact thm33_if_iii x y z hx hy hz hsum h3 h1 h2 h4

theorem tileAngles_iff {N : ℕ} (D : CongruentDissection N) (x y z : ℝ) :
    TileAngles D x y z ↔ ∃ σ : Equiv.Perm (Fin 3), ∀ i, D.model.angleAt (σ i) = ![x, y, z] i := by
  constructor
  · rintro ⟨σ, h0, h1, h2⟩
    refine ⟨σ, fun i => ?_⟩
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  · rintro ⟨σ, h⟩
    exact ⟨σ, h 0, h 1, h 2⟩

theorem thm33_iff (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hsum : x + y + z = Real.pi) :
    Thm33If x y z ↔ ∃ ρ : Equiv.Perm (Fin 3),
      Thm33Clauses (![x, y, z] (ρ 0)) (![x, y, z] (ρ 1)) (![x, y, z] (ρ 2)) := by
  constructor
  · rintro ⟨N, D, hE, hT⟩
    obtain ⟨x', y', z', hT', hcl⟩ := thm33_only_if D hE
    obtain ⟨σ1, h1⟩ := (tileAngles_iff D x y z).mp hT
    obtain ⟨σ2, h2⟩ := (tileAngles_iff D x' y' z').mp hT'
    refine ⟨σ2.trans σ1.symm, ?_⟩
    have key : ∀ i, ![x', y', z'] i = ![x, y, z] ((σ2.trans σ1.symm) i) := by
      intro i
      rw [← h2 i, Equiv.trans_apply, ← h1 (σ1.symm (σ2 i)), Equiv.apply_symm_apply]
    have e0 := key 0
    have e1 := key 1
    have e2 := key 2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at e0 e1 e2
    rw [← e0, ← e1, ← e2]
    exact hcl
  · rintro ⟨ρ, hcl⟩
    have hpos : ∀ k, 0 < ![x, y, z] k := by
      intro k; fin_cases k
      · exact hx
      · exact hy
      · exact hz
    have hs : ![x, y, z] (ρ 0) + ![x, y, z] (ρ 1) + ![x, y, z] (ρ 2) = Real.pi := by
      have := Equiv.sum_comp ρ (fun k => ![x, y, z] k)
      rw [Fin.sum_univ_three, Fin.sum_univ_three] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons] at this
      linarith
    obtain ⟨N, D, hE, hT⟩ := thm33_if _ _ _ (hpos _) (hpos _) (hpos _) hs hcl
    obtain ⟨σ, h⟩ := (tileAngles_iff D _ _ _).mp hT
    refine ⟨N, D, hE, (tileAngles_iff D x y z).mpr ⟨ρ.symm.trans σ, fun i => ?_⟩⟩
    have hv : ∀ k, (![![x, y, z] (ρ 0), ![x, y, z] (ρ 1), ![x, y, z] (ρ 2)] : Fin 3 → ℝ) k = ![x, y, z] (ρ k) := by
      intro k; fin_cases k <;> rfl
    simp only [Equiv.trans_apply]
    rw [h (ρ.symm i), hv, Equiv.apply_symm_apply]

#print axioms Erdos634.LaczThm33If.thm33_if
#print axioms Erdos634.LaczThm33If.thm33_iff

end Erdos634.LaczThm33If

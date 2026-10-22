-- Draft/LaczFormalL5Comm.lean -- atom L5, COMMENSURABLE half (covered denominators): Table 3 lines 1-2 of Beeson-Rosu / Beeson, assembled from Laczkovich 1995 Thm 5.3.
-- A congruent dissection (any N, reflections allowed) of a NON-EQUILATERAL triangle by a tile with angles a_k pi/n (gcd 1, `Covered3 n`):
-- the tile is similar to the target (line 1), or the tile is right-angled `(alpha, beta, pi/2)` and the target is `(beta, beta, 2 alpha)` (line 2).
-- Built from `classify_commensurable_final3`: the three ExcPair3 shapes at n = 6 are the equilateral ones (excluded by hypothesis) and the 30-60-90 tile with target (pi/6, pi/6, 2pi/3) (= line 2).
-- Missing for all n: the uncovered denominators (5-smooth n >= 160 except the five certified, and n = 135 < n pending) = the uniform R(a) = R0(a) of PLAN_L9_L7.md.
-- UNAUDITED (NOTE).  Credit: Laczkovich (DCG 48 (2012); Discrete Math 140 (1995) Thm 5.1/5.3; Combinatorica 1990), Beeson-Rosu, Beeson.
import Erdos634.Draft.LaczFormalClassifyFinal3
import Erdos634.Draft.LaczFormalL5
import Erdos634.Draft.LaczFormalCaseVI

open scoped BigOperators Classical
open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional

namespace Erdos634.Draft.LaczFormal

variable {N : ℕ}

theorem tgt_cast3 {D : CongruentDissection N} {x y z x' y' z' : ℝ} (h : TgtAngles D x y z)
    (ex : x = x') (ey : y = y') (ez : z = z') : TgtAngles D x' y' z' := by
  subst ex ey ez; exact h

theorem table3_comm (D : CongruentDissection N) (hne : ¬ Equilateral D) {n : ℕ} (hn : 0 < n) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n)
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1) (hcov : Covered3 n) :
    SimilarTM D ∨ ∃ α β : ℝ, TileAngles D α β (Real.pi / 2) ∧ TgtAngles D β β (2 * α) := by
  have hpi := Real.pi_pos
  have hEq : ∀ {x : ℝ}, TgtAngles D x x x → x = Real.pi / 3 → False := by
    intro x hG hx
    apply hne
    intro j
    rw [Graph.tgt_all D hG j, hx]
  rcases classify_commensurable_final3 D hn a ha hgcd hcov with h | h | h
  · exact Or.inl h
  · right
    obtain ⟨k, l, hlk, hk, j₁, j₂, hj, h1, h2⟩ := h
    refine ⟨Real.pi - Real.pi / 2 - D.model.angleAt l, D.model.angleAt l, ?_, ?_⟩
    · exact (((tile_of_two D k l hlk.symm (Real.pi / 2) _ hk rfl).swap).swap23).swap
    · exact tgt_congr3 (tgt_of_two D j₁ j₂ hj _ h1 h2) (by ring)
  · right
    rcases h with ⟨hT, hG⟩ | ⟨hT, hG⟩ | ⟨hT, hG⟩
    · exact (hEq (tgt_cast3 hG rfl rfl rfl) (by ring)).elim
    · refine ⟨Real.pi / 3, Real.pi / 6, ?_, ?_⟩
      · exact (hT.cast (by ring) (by ring) (by ring)).swap
      · exact tgt_cast3 hG (by ring) (by ring) (by ring)
    · exact (hEq (tgt_cast3 hG rfl rfl rfl) (by ring)).elim

/-- Non-vacuity of the hypotheses: the ladder dissection of the `(pi/6, 2pi/6, 3pi/6)` triangle (N = 4) has a NON-equilateral target
(the target is similar to the tile, so it has a right angle) and satisfies the angle hypotheses. -/
theorem table3_comm_hyps_witness :
    ∃ (N : ℕ) (D : CongruentDissection N), ¬ Equilateral D ∧ ∃ a : Fin 3 → ℕ,
      (∀ k, D.model.angleAt k = a k * Real.pi / (6 : ℕ)) ∧
      Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1 ∧ Covered3 6 := by
  have hpi := Real.pi_pos
  obtain ⟨N, D, ⟨σ, m0, m1, m2⟩, ⟨τ, t0, -, -⟩⟩ := ladder_with_angles (α := Real.pi / 6) (β := 2 * Real.pi / 6)
    (by positivity) (by positivity) (by linarith)
  refine ⟨N, D, ?_, fun l => (![1, 2, 3] : Fin 3 → ℕ) (σ.symm l), ?_, ?_,
    Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))⟩
  · intro hE
    have := hE (τ 0)
    rw [t0] at this
    linarith
  · intro l
    have : ∀ k, D.model.angleAt (σ k) = ((![1, 2, 3] : Fin 3 → ℕ) k : ℕ) * Real.pi / (6 : ℕ) := by
      intro k; fin_cases k
      · simpa using m0
      · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.head_cons]; push_cast; rw [m1]; try ring
      · simp only [Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]; push_cast
        rw [m2]; try ring
    simpa using this (σ.symm l)
  · have hdvd : ∀ l, Nat.gcd ((![1, 2, 3] : Fin 3 → ℕ) (σ.symm 0))
        (Nat.gcd ((![1, 2, 3] : Fin 3 → ℕ) (σ.symm 1)) ((![1, 2, 3] : Fin 3 → ℕ) (σ.symm 2))) ∣
        (![1, 2, 3] : Fin 3 → ℕ) (σ.symm l) := by
      intro l; fin_cases l
      · exact Nat.gcd_dvd_left _ _
      · exact (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)
      · exact (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)
    have := hdvd (σ 0)
    simp only [Equiv.symm_apply_apply, Matrix.cons_val_zero] at this
    exact Nat.dvd_one.mp this

end Erdos634.Draft.LaczFormal

#print axioms Erdos634.Draft.LaczFormal.table3_comm

/-
Draft/G2AFinal.lean — `Row4.not_squarefree`: a `γ = 2α` tile (α ∉ ℚπ, reflections allowed, not edge-to-edge) cannot tile the base-α
isosceles target with SQUAREFREE `N` tiles (Beeson [Iso Thm 11.7], squarefree case), and the any-label form
`GammaTwoAlpha_of_squarefree : Squarefree N → CaseGClosed N`.
Proof: `Row4.sqfree_legs` (every leg word has `q ∈ {0,k}`, `k ≥ 2`); a leg with `q = k` is `b^k`: `Row4.bk_leg`;
both legs with `q = 0`: `Row4.L8_nob`.  CONDITIONAL AT THE GEOMETRIC LEVEL as `Row4.not_prime` (no Lean witness tiling).
UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.G2AAssembly

open scoped Classical

namespace Erdos634.Geometry

variable {N : ℕ}

theorem Row4.not_squarefree (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoAlphaData α a b c)
    (hA : D.target.angleAt 0 = α) (hC : D.target.angleAt 1 = α) (hsq : Squarefree N) : False := by
  obtain ⟨k, hk2, hwords⟩ := Row4.sqfree_legs D hα h hA hC hsq
  obtain ⟨-, -, -, -, -, -, -, -, hX1⟩ := Row4.sides D h hA hC
  obtain ⟨hα0, hα3, -⟩ := Row4.model_sides D h
  have hB : D.target.angleAt 2 = Real.pi - 2 * α := by
    have := D.target.angleAt_sum; rw [hA, hC] at this; linarith
  obtain ⟨hBγ, -⟩ := Row4.corner_B D hα h hα0 hα3 hB
  have hne : ∀ i j : Fin 3, i ≠ j → D.target.pts i ≠ D.target.pts j := fun i j hij e =>
    hij (D.target.indep.injective e)
  -- the word of each leg
  have hw : ∀ i : Fin 3, (i = 0 ∨ i = 1) →
      (((D.sideEdges (i + 1)).filter (fun e => D.eLen e = a)).card = 0 ∧
        ((D.sideEdges (i + 1)).filter (fun e => D.eLen e = b)).card = k ∧
        ((D.sideEdges (i + 1)).filter (fun e => D.eLen e = c)).card = 0) ∨
      ((D.sideEdges (i + 1)).filter (fun e => D.eLen e = b)).card = 0 := by
    intro i hi
    have := hwords _ _ _ (by
      rw [← Row4.side_word_counts D hα h i]
      rcases hi with rfl | rfl
      · rfl
      · exact hX1.symm)
    rcases this with ⟨h1, h2, h3⟩ | h1
    · exact Or.inl ⟨h2, h1, h3⟩
    · exact Or.inr h1
  have hbk : ∀ j : Fin 3,
      ((D.sideEdges j).filter (fun e => D.eLen e = a)).card = 0 →
      ((D.sideEdges j).filter (fun e => D.eLen e = c)).card = 0 →
      ∀ e ∈ D.sideEdges j, D.eLen e = b := by
    intro j h1 h3 e he
    rcases Row4.eLen_abc D h e with e1 | e1 | e1
    · exfalso
      have : e ∈ (D.sideEdges j).filter (fun e => D.eLen e = a) := Finset.mem_filter.mpr ⟨he, e1⟩
      rw [Finset.card_eq_zero.mp h1] at this; simp at this
    · exact e1
    · exfalso
      have : e ∈ (D.sideEdges j).filter (fun e => D.eLen e = c) := Finset.mem_filter.mpr ⟨he, e1⟩
      rw [Finset.card_eq_zero.mp h3] at this; simp at this
  have hnob : ∀ j : Fin 3, ((D.sideEdges j).filter (fun e => D.eLen e = b)).card = 0 →
      ∀ e ∈ D.sideEdges j, D.eLen e ≠ b := by
    intro j hj e he heq
    have : e ∈ (D.sideEdges j).filter (fun e => D.eLen e = b) := Finset.mem_filter.mpr ⟨he, heq⟩
    rw [Finset.card_eq_zero.mp hj] at this; simp at this
  rcases hw 0 (Or.inl rfl) with ⟨h1, h2, h3⟩ | h0
  · -- leg CB = `[pts 1, pts 2]` is `b^k`
    refine Row4.bk_leg D hα h (hne 1 2 (by decide)) rfl rfl ?_
      (fun i => (Row4.corner_A D hα h hα0 hα3 hC i).2) hBγ hk2 h2 (hbk 1 h1 h3)
    intro v hv
    have h3' : v = 0 ∨ v = 1 ∨ v = 2 := by fin_cases v <;> simp
    rcases h3' with rfl | rfl | rfl
    · exact absurd hv (Row4.third_not_on_side D.target 1)
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hw 1 (Or.inr rfl) with ⟨h1', h2', h3'⟩ | h1
  · -- leg AB = `[pts 0, pts 2]` is `b^k`
    have hsAB : D.target.edge 2 = segment ℝ (D.target.pts 0) (D.target.pts 2) := by
      show segment ℝ (D.target.pts 2) (D.target.pts (2 + 1)) = _
      rw [show (2 : Fin 3) + 1 = 0 from rfl, segment_symm]
    refine Row4.bk_leg D hα h (hne 0 2 (by decide)) hsAB (by rw [dist_comm]; rfl) ?_
      (fun i => (Row4.corner_A D hα h hα0 hα3 hA i).2) hBγ hk2 h2' (hbk 2 h1' h3')
    intro v hv
    have h3'' : v = 0 ∨ v = 1 ∨ v = 2 := by fin_cases v <;> simp
    rcases h3'' with rfl | rfl | rfl
    · exact Or.inl rfl
    · rw [segment_symm] at hv
      exact absurd hv (Row4.third_not_on_side D.target 2)
    · exact Or.inr rfl
  · -- no `b` on either leg
    exact Row4.L8_nob D hα h hA hC (hnob 2 h1) (hnob 1 h0)

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Row4.not_squarefree

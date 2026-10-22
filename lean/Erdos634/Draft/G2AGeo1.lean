/-
Draft/G2AGeo1.lean — facts on tile edges of the `γ = 2α` tile used by the leg argument without `b`-edges:
`edge_beta_end` (an edge not of length `b` has exactly one endpoint carrying `β = π − 3α`),
`two_edges_one_tile` (a tile has at most one edge on a target side).  UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.FluxDRow4Bk
import Erdos634.Draft.G2AChain

open scoped Classical

namespace Erdos634.Geometry

variable {N : ℕ}

/-- **An edge not of length `b` has exactly one endpoint carrying `β`** (the `β`-vertex of the tile is opposite `b`). -/
theorem Row4.edge_beta_end (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoAlphaData α a b c) (i : Fin N)
    (k : Fin 3) (hnb : D.eLen (i, k) ≠ b) :
    ((D.tile i).angleAt k = Real.pi - 3 * α ∧ (D.tile i).angleAt (k + 1) ≠ Real.pi - 3 * α) ∨
    ((D.tile i).angleAt k ≠ Real.pi - 3 * α ∧ (D.tile i).angleAt (k + 1) = Real.pi - 3 * α) := by
  obtain ⟨hab, hac, hbc⟩ := Row4.scalene D hα h
  obtain ⟨hα0, hα3, -⟩ := Row4.model_sides D h
  have hπ := Real.pi_pos
  have d1 : α ≠ Real.pi - 3 * α := fun e => hα ⟨1 / 4, by push_cast; linarith⟩
  have d6 : Real.pi - 3 * α ≠ 2 * α := fun e => hα ⟨1 / 5, by push_cast; linarith⟩
  have d2 : α ≠ 2 * α := by intro e; linarith
  have hopp : (D.tile i).oppLen (k + 2) = D.eLen (i, k) := by
    unfold Tri.oppLen Dissection.eLen
    rw [show k + 2 + 1 = k by fin_cases k <;> rfl, show k + 2 + 2 = k + 1 by fin_cases k <;> rfl]
  obtain ⟨σ', hσ'⟩ := (D.tiles_congruent i).exists_perm
  -- the vertex opposite the edge is not the β-vertex
  have hk2 : (D.tile i).angleAt (k + 2) ≠ Real.pi - 3 * α := by
    intro hb
    obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
    rw [(hσ' (k + 2)).1] at hb
    obtain ⟨m, hm⟩ := σ.surjective (σ' (k + 2))
    rw [← hm] at hb
    have h3 : m = 0 ∨ m = 1 ∨ m = 2 := by fin_cases m <;> simp
    rcases h3 with rfl | rfl | rfl
    · rw [h0] at hb; exact d1 hb
    · apply hnb
      rw [← hopp, (hσ' (k + 2)).2, ← hm, o1]
    · rw [h2] at hb; exact d6 hb.symm
  have hne0 : k ≠ k + 2 := by fin_cases k <;> decide
  have hne1 : k + 1 ≠ k + 2 := by fin_cases k <;> decide
  have hne01 : k ≠ k + 1 := by fin_cases k <;> decide
  have a0 := Row4.tile_angles_ne D hα h i hne0
  have a1 := Row4.tile_angles_ne D hα h i hne1
  have a01 := Row4.tile_angles_ne D hα h i hne01
  have m0 := Row4.tile_angle_mem D h i k
  have m1 := Row4.tile_angle_mem D h i (k + 1)
  have m2 := Row4.tile_angle_mem D h i (k + 2)
  by_cases hk0 : (D.tile i).angleAt k = Real.pi - 3 * α
  · left
    refine ⟨hk0, fun e => a01 (hk0.trans e.symm)⟩
  · right
    refine ⟨hk0, ?_⟩
    by_contra hk1
    rcases m0 with e0 | e0 | e0 <;> rcases m1 with e1 | e1 | e1 <;> rcases m2 with e2 | e2 | e2
    all_goals first
      | exact hk0 e0
      | exact hk1 e1
      | exact hk2 e2
      | exact a01 (e0.trans e1.symm)
      | exact a0 (e0.trans e2.symm)
      | exact a1 (e1.trans e2.symm)

/-- **A tile has at most one edge on a target side.**  (All three vertices on the supporting line would put the whole
tile on it, contradicting its non-empty interior.) -/
theorem Row4.two_edges_one_tile (D : CongruentDissection N) (j : Fin 3)
    {e e' : Fin N × Fin 3} (he : e ∈ D.sideEdges j) (he' : e' ∈ D.sideEdges j) (h1 : e.1 = e'.1) :
    e.2 = e'.2 := by
  by_contra hk
  obtain ⟨g, c, hg, hle, hj, hj1, hj2⟩ := exists_supporting D.target j
  have hS : {x ∈ D.target.carrier | g x = c} = D.target.edge j :=
    target_contact_side D.target g c hle hj hj1 hj2
  have hon : ∀ e ∈ D.sideEdges j, ∀ y ∈ (D.tile e.1).edge e.2, g y = c := by
    intro e he y hy
    unfold Dissection.sideEdges at he
    have hy' : y ∈ {x ∈ D.target.carrier | g x = c} := by
      rw [hS]; exact (Finset.mem_filter.mp he).2 hy
    exact hy'.2
  set T := D.tile e.1 with hT
  have hv : ∀ m : Fin 3, g (T.pts m) = c := by
    intro m
    have hmem : ∀ (e : Fin N × Fin 3), e ∈ D.sideEdges j → e.1 = e.1 →
        g ((D.tile e.1).pts e.2) = c ∧ g ((D.tile e.1).pts (e.2 + 1)) = c := by
      intro e he _
      exact ⟨hon e he _ (left_mem_segment ℝ _ _), hon e he _ (right_mem_segment ℝ _ _)⟩
    have A := hmem e he rfl
    have B := hmem e' he' rfl
    rw [← h1] at B
    have hk' : e.2 = e'.2 → False := hk
    -- vertices e.2, e.2+1 are on the line; e'.2 ∈ {e.2+1, e.2+2}
    have hcases : m = e.2 ∨ m = e.2 + 1 ∨ m = e.2 + 2 := by
      have := (show ∀ k m : Fin 3, m = k ∨ m = k + 1 ∨ m = k + 2 by decide) e.2 m
      exact this
    have hcases' : e'.2 = e.2 + 1 ∨ e'.2 = e.2 + 2 := by
      have : ∀ k k' : Fin 3, k ≠ k' → k' = k + 1 ∨ k' = k + 2 := by decide
      exact this e.2 e'.2 hk
    rcases hcases with rfl | rfl | rfl
    · exact A.1
    · exact A.2
    · rcases hcases' with h' | h'
      · -- e'.2 = e.2+1: vertices e'.2 = e.2 + 1, e'.2 + 1 = e.2 + 2
        have := B.2
        rw [h'] at this
        rw [(show ∀ k : Fin 3, k + 1 + 1 = k + 2 by decide) e.2] at this
        exact this
      · have := B.1
        rw [h'] at this
        exact this
  -- the tile lies in `g = c`
  obtain ⟨y₀, hy₀⟩ := T.interior_nonempty
  have hleT : ∀ y ∈ T.carrier, g y ≤ c := fun y hy => hle y (tile_subset_target D.toDissection e.1 hy)
  have hlt := T.interior_lt_of_le g c hg hleT hy₀
  have hcar : T.carrier = convexHull ℝ (Set.range T.pts) := rfl
  have hall : ∀ y ∈ T.carrier, g y = c := by
    intro y hy
    have hsub : T.carrier ⊆ {x | g x = c} := by
      rw [hcar]
      apply convexHull_min
      · rintro _ ⟨m, rfl⟩; exact hv m
      · -- `{x | g x = c}` is convex
        intro x hx y hy a b ha hb hab
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [map_add, map_smul, map_smul, hx, hy, smul_eq_mul, smul_eq_mul, ← add_mul, hab, one_mul]
    exact hsub hy
  have hy₀c : y₀ ∈ T.carrier := interior_subset hy₀
  exact absurd (hall y₀ hy₀c) (ne_of_lt hlt)

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Row4.edge_beta_end
#print axioms Erdos634.Geometry.Row4.two_edges_one_tile

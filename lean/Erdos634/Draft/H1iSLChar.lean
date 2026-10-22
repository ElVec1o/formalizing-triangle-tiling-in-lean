/-
Draft/H1iSLChar.lean — atom H1.i (sign lemma SL), part 1: the side partition is CHARACTERISED algebraically.
`Dissection.side_partition`/`side_walk` give an existential `part`.  Here we prove that ANY `part` with the
partition properties (cover of the side by whole tile edges, pairwise-subsingleton overlaps) is exactly
`{ e | both endpoints of the edge e are collinear with the side }`, where collinearity is the POLYNOMIAL condition
`Col P Q p`.  Polynomial conditions are transported by ring homomorphisms, which is the step the paper's SL proof
glosses ("σ preserves 'both endpoints on the line' because it preserves collinearity").
*** UNAUDITED.  Formalization debt (SCOPE_H1_full H1.i), NOT /goal progress.  No sorry. ***
-/
import Erdos634.EdgeChain

namespace Erdos634.H1iSL

open Erdos634.Geometry Set

/-- Collinearity of `p` with the line through `P`, `Q` (a polynomial condition in the coordinates). -/
def Col (P Q p : Plane) : Prop :=
  (Q 0 - P 0) * (p 1 - P 1) - (Q 1 - P 1) * (p 0 - P 0) = 0

theorem col_iff_f {f : Plane →ₗ[ℝ] ℝ} (hf : f ≠ 0) {c : ℝ} {P Q : Plane} (hPQ : P ≠ Q)
    (hP : f P = c) (hQ : f Q = c) (x : Plane) : Col P Q x ↔ f x = c := by
  have hQP : Q - P ≠ 0 := sub_ne_zero.mpr hPQ.symm
  have hcr : Col P Q x ↔ cross (Q - P) (x - P) = 0 := by
    simp only [Col, cross, PiLp.sub_apply]
  rw [hcr]
  constructor
  · intro h
    obtain ⟨τ, hτ⟩ := parallel_of_cross_eq_zero hQP h
    have h1 : f (x - P) = τ * f (Q - P) := by rw [hτ, map_smul, smul_eq_mul]
    rw [map_sub, map_sub, hP, hQ] at h1
    linarith
  · intro h
    have hn := rotVec_ne_zero hf
    have h1 : cross (rotVec f) (x - P) = 0 := by
      rw [← rotVec_spec, map_sub, h, hP]; ring
    have h2 : cross (rotVec f) (Q - P) = 0 := by
      rw [← rotVec_spec, map_sub, hQ, hP]; ring
    have := cross_eq_zero_of_common_ker hn h1 h2
    simp only [cross, PiLp.sub_apply] at this ⊢
    linarith

/-- **Characterisation of the side partition.**  Any `part` covering the side `i` of the target by whole tile
edges (the overlap hypothesis is not even needed: same-side edges of distinct tiles meet in at most a point by
`sameside_edges_subsingleton`) consists exactly of the edges both of whose endpoints are
collinear with the side. -/
theorem part_char {N : ℕ} (D : Dissection N) (i : Fin 3) (part : Finset (Fin N × Fin 3))
    (hcov : (⋃ e ∈ part, (D.tile e.1).edge e.2)
          = segment ℝ (D.target.pts i) (D.target.pts (i + 1)))
    (e : Fin N × Fin 3) :
    e ∈ part ↔ (Col (D.target.pts i) (D.target.pts (i + 1)) ((D.tile e.1).pts e.2) ∧
      Col (D.target.pts i) (D.target.pts (i + 1)) ((D.tile e.1).pts (e.2 + 1))) := by
  classical
  obtain ⟨f, c, hf, hle, hi, hi1, hi2⟩ := exists_supporting D.target i
  have hS : {x ∈ D.target.carrier | f x = c}
      = segment ℝ (D.target.pts i) (D.target.pts (i + 1)) :=
    target_contact_side D.target f c hle hi hi1 hi2
  have hPQ : D.target.pts i ≠ D.target.pts (i + 1) :=
    D.target.indep.injective.ne (by fin_cases i <;> decide)
  have hsub : ∀ e ∈ part, (D.tile e.1).edge e.2
      ⊆ segment ℝ (D.target.pts i) (D.target.pts (i + 1)) := by
    intro e he y hy
    rw [← hcov]
    exact Set.mem_iUnion₂.mpr ⟨e, he, hy⟩
  have hlineE : ∀ e ∈ part, ∀ y ∈ (D.tile e.1).edge e.2, f y = c := by
    intro e he y hy
    have h1 : y ∈ {x ∈ D.target.carrier | f x = c} := by
      rw [hS]; exact hsub e he hy
    exact h1.2
  have hleT : ∀ e : Fin N × Fin 3, ∀ y ∈ (D.tile e.1).carrier, f y ≤ c :=
    fun e y hy => hle y (Erdos634.Geometry.tile_subset_target D e.1 hy)
  constructor
  · intro he
    have h1 := hlineE e he _ (left_mem_segment ℝ _ _)
    have h2 := hlineE e he _ (right_mem_segment ℝ _ _)
    exact ⟨(col_iff_f hf hPQ hi hi1 _).mpr h1, (col_iff_f hf hPQ hi hi1 _).mpr h2⟩
  · rintro ⟨h1, h2⟩
    by_contra hne
    set p := (D.tile e.1).pts e.2 with hp
    set q := (D.tile e.1).pts (e.2 + 1) with hq
    have hfp : f p = c := (col_iff_f hf hPQ hi hi1 _).mp h1
    have hfq : f q = c := (col_iff_f hf hPQ hi hi1 _).mp h2
    have hk : ∀ k : Fin 3, k ≠ k + 1 := by decide
    have hpq : p ≠ q := (D.tile e.1).indep.injective.ne (hk e.2)
    have hline : ∀ y ∈ (D.tile e.1).edge e.2, f y = c := by
      intro y hy
      obtain ⟨a, b, ha, hb, hab, rfl⟩ := hy
      rw [map_add, map_smul, map_smul, hfp, hfq, smul_eq_mul, smul_eq_mul]
      rw [← add_mul, hab, one_mul]
    have hsubs : ∀ e₂ ∈ part, ((D.tile e.1).edge e.2 ∩ (D.tile e₂.1).edge e₂.2).Subsingleton := by
      intro e₂ he₂
      exact D.sameside_edges_subsingleton f c hf (fun h => hne (h ▸ he₂)) (hleT e) (hleT e₂)
        hline (hlineE e₂ he₂)
    -- the edge is covered by the finitely many subsingletons
    have hcover : (D.tile e.1).edge e.2 ⊆ ⋃ e₂ ∈ part, ((D.tile e.1).edge e.2 ∩ (D.tile e₂.1).edge e₂.2) := by
      intro y hy
      have hy' : y ∈ segment ℝ (D.target.pts i) (D.target.pts (i + 1)) := by
        rw [← hS]
        exact ⟨Erdos634.Geometry.tile_subset_target D e.1 (segment_subset_convexHull
          (Set.mem_range_self _) (Set.mem_range_self _) hy), hline y hy⟩
      rw [← hcov] at hy'
      obtain ⟨e₂, he₂, hy₂⟩ := Set.mem_iUnion₂.mp hy'
      exact Set.mem_iUnion₂.mpr ⟨e₂, he₂, hy, hy₂⟩
    have hfin : ((D.tile e.1).edge e.2).Finite := by
      refine Set.Finite.subset ?_ hcover
      exact Set.Finite.biUnion part.finite_toSet (fun e₂ he₂ => (hsubs e₂ he₂).finite)
    have hinf : ((D.tile e.1).edge e.2).Infinite := by
      show (segment ℝ p q).Infinite
      rw [segment_eq_image']
      refine Set.Infinite.image ?_ (Set.Icc_infinite zero_lt_one)
      intro s _ t _ hst
      have : s • (q - p) = t • (q - p) := add_left_cancel hst
      exact smul_left_injective ℝ (sub_ne_zero.mpr hpq.symm) this
    exact hinf hfin

end Erdos634.H1iSL

#print axioms Erdos634.H1iSL.part_char

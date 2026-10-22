-- Draft/FluxCRow5TwoPiThreeFull.lean — Theorem E, 2π/3 branch, end to end: discharges the side
-- decomposition hypothesis `hside` (and `haPos`/`hbPos`) of `Row5.twoPiThree_forces_le_three`
-- (FluxCRow5Complete.lean) for a REAL `CongruentDissection`.  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
-- Formalization debt on a paper-level PROVED result ((private working notes, not included) §4);
-- not progress on the three /goal outcomes.
--
-- SURVEY / REDISCOVERY NOTE.  Every ingredient already existed:
-- * `Row5.twoPiThree_closedForms` (FluxCRow5Complete.lean) supplies `hc2`, `hD`, `hab2`.
-- * `Row5.equilateral_boundary` (FluxCRow5.lean) supplies the target side equalities.
-- * `Dissection.side_len_sum` (Draft/FluxBoundary.lean): edges on a side sum to its length.
-- * `Row5SideBridge.row5_side_decomposition_int` (Draft/FluxCRow5SideBridge.lean) ALREADY gives the
--   side decomposition for any `CongruentDissection`, but with `a, b, c` pinned to the model's
--   `oppLen 0/1/2`; `TwoPiThreeData` carries an unknown permutation `σ`, so here the decomposition is
--   re-assembled directly from `side_len_sum` (each boundary edge has length `a`, `b` or `c`), the
--   same pattern as `Row5Hr0.side_decomposition_r0`.  Unlike the π/3 branch, NO sign/E7b input is
--   needed: `r` is arbitrary in `twoPiThree_forces_le_three`.
-- * `Tri.TwoPiThreeData.tri_ineq` (Draft/FluxPaperCorIntAnchored.lean) gives `a, b > 0`.
-- New here is only the assembly.
import Erdos634.Draft.FluxCRow5Complete
import Erdos634.Draft.FluxPaperCorIntAnchored
import Erdos634.Draft.FluxCRow5Hr0

open scoped Classical
open Finset

namespace Erdos634.Geometry

namespace Row5TwoPiThreeFull

variable {N : ℕ}

/-- Every tile edge has length `a`, `b` or `c` (the tile is congruent to the `TwoPiThreeData`
model). -/
theorem edge_len (D : CongruentDissection N) {α a b c : ℝ}
    (h : D.model.TwoPiThreeData α a b c) (e : Fin N × Fin 3) :
    D.toDissection.eLen e = a ∨ D.toDissection.eLen e = b ∨ D.toDissection.eLen e = c := by
  obtain ⟨σ, hσ⟩ := (D.tiles_congruent e.1).exists_perm
  obtain ⟨τ, -, o0, -, o1, -, o2⟩ := h
  have hlen : D.toDissection.eLen e = (D.tile e.1).oppLen (e.2 + 2) := by
    unfold Dissection.eLen Tri.oppLen
    have k1 : ∀ k : Fin 3, k + 2 + 1 = k := by decide
    have k2 : ∀ k : Fin 3, k + 2 + 2 = k + 1 := by decide
    rw [k1, k2]
  obtain ⟨m, hm⟩ := τ.surjective (σ (e.2 + 2))
  rw [hlen, (hσ _).2, ← hm]
  have hm3 : m = 0 ∨ m = 1 ∨ m = 2 := by fin_cases m <;> simp
  rcases hm3 with rfl | rfl | rfl
  · exact Or.inl o0
  · exact Or.inr (Or.inl o1)
  · exact Or.inr (Or.inr o2)

/-- **E8 side decomposition, derived.**  Side `01` of the target is `p·a + q·b + r·c`,
`p, q, r ∈ ℕ`. -/
theorem side_decomposition (D : CongruentDissection N) {α a b c : ℝ}
    (h : D.model.TwoPiThreeData α a b c) :
    ∃ p q r : ℕ, dist (D.target.pts 0) (D.target.pts 1)
      = (p : ℝ) * a + (q : ℝ) * b + (r : ℝ) * c := by
  set s := D.toDissection.sideEdges 0
  set len := D.toDissection.eLen
  have hsum := D.toDissection.side_len_sum 0
  rw [show (0 : Fin 3) + 1 = 1 from rfl] at hsum
  set s' := s.filter fun e => ¬ len e = a
  refine ⟨(s.filter fun e => len e = a).card, (s'.filter fun e => len e = b).card,
    (s'.filter fun e => ¬ len e = b).card, ?_⟩
  rw [← hsum, ← Finset.sum_filter_add_sum_filter_not s (fun e => len e = a),
    ← Finset.sum_filter_add_sum_filter_not s' (fun e => len e = b)]
  have hA : ∑ e ∈ s.filter (fun e => len e = a), len e
      = ((s.filter fun e => len e = a).card : ℝ) * a := by
    rw [Finset.sum_congr rfl (fun e he => (Finset.mem_filter.mp he).2),
      Finset.sum_const, nsmul_eq_mul]
  have hB : ∑ e ∈ s'.filter (fun e => len e = b), len e
      = ((s'.filter fun e => len e = b).card : ℝ) * b := by
    rw [Finset.sum_congr rfl (fun e he => (Finset.mem_filter.mp he).2),
      Finset.sum_const, nsmul_eq_mul]
  have hC : ∑ e ∈ s'.filter (fun e => ¬ len e = b), len e
      = ((s'.filter fun e => ¬ len e = b).card : ℝ) * c := by
    rw [Finset.sum_congr rfl (fun e he => ?_), Finset.sum_const, nsmul_eq_mul]
    have hm := Finset.mem_filter.mp he
    have hm' := Finset.mem_filter.mp hm.1
    rcases edge_len D h e with h1 | h1 | h1
    · exact absurd h1 hm'.2
    · exact absurd h1 hm.2
    · exact h1
  rw [hA, hB, hC]; ring

/-- **Theorem E, `2π/3` branch, end to end, NO side-decomposition hypothesis.**  An equilateral
target (all angles `π/3`) `N`-tiled by congruent copies (reflections allowed, not necessarily
edge-to-edge) of an `(α, π/3 − α, 2π/3)` tile with `α/π ∉ ℚ` has `N` not a prime `> 3`. -/
theorem Row5.theoremE_twoPiThree_full (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoPiThreeData α a b c)
    (hP : ∀ k, D.target.angleAt k = Real.pi / 3) : ¬ (N.Prime ∧ 3 < N) := by
  rintro ⟨hNp, hN3⟩
  obtain ⟨hc2, hD, hab2⟩ := Row5.twoPiThree_closedForms D hα h hP hNp
  obtain ⟨p, q, r, hpqr⟩ := side_decomposition D h
  obtain ⟨-, e2, -⟩ := Row5.equilateral_boundary D hα 0
    (fun k => D.model.data_angles_mem hα h 0 k) hP
  have hd : dist (D.target.pts 0) (D.target.pts 1) = D.target.oppLen 0 := by
    rw [← e2]; unfold Tri.oppLen; rfl
  rw [hd] at hpqr
  obtain ⟨t1, t2, t3⟩ := h.tri_ineq
  have ha : 0 < a := by linarith
  have hb : 0 < b := by linarith
  have := Row5.twoPiThree_forces_le_three hNp hc2 hD hab2 (D.target.oppLen_pos 0) ha hb
    (p : ℤ) (q : ℤ) (r : ℤ) (by positivity) (by positivity) (by rw [hpqr]; push_cast; ring)
  omega

/-! ## Non-vacuity.
`TwoPiThreeData` with `α/π ∉ ℚ` is witnessed by `data357` (Draft/FluxPaperWitness.lean, the
`(3,5,7)` tile) and the equilateral target hypothesis by `E2` (Draft/FluxCRow5Witness.lean).  A
JOINT Lean witness (a `CongruentDissection` of an equilateral triangle by such a tile) does not
exist in the corpus; at prime `N > 3` the theorem says the bundle is unsatisfiable. -/

/-- **Theorem E, as written (AUDIT.md §4): both halves in ONE statement.**  An equilateral target
`N`-tiled by congruent copies (reflections allowed, not necessarily edge-to-edge) of a tile with
`γ ∈ {π/3, 2π/3}` and `α/π ∉ ℚ` has `N` not a prime `> 3`. -/
theorem Row5.theoremE_full (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : D.model.SixtyData α a b c ∨ D.model.TwoPiThreeData α a b c)
    (hP : ∀ k, D.target.angleAt k = Real.pi / 3) : ¬ (N.Prime ∧ 3 < N) := by
  rcases h with h | h
  · exact Row5Hr0.Row5.theoremE_sixty_full D hα h hP
  · exact Row5.theoremE_twoPiThree_full D hα h hP

end Row5TwoPiThreeFull

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Row5TwoPiThreeFull.edge_len
#print axioms Erdos634.Geometry.Row5TwoPiThreeFull.side_decomposition
#print axioms Erdos634.Geometry.Row5TwoPiThreeFull.Row5.theoremE_twoPiThree_full
#print axioms Erdos634.Geometry.Row5TwoPiThreeFull.Row5.theoremE_full

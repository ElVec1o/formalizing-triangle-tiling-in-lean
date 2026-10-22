-- Draft/FluxDRow2S1.lean — ROW 2, S1 ((private working notes, not included) §4 "S1 (sides are words
-- of edges)", equation (1) `D v = μ v`) on a REAL `CongruentDissection`, and Lemma D composed with it.
-- Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
--
-- * `CongruentDissection.sideCount D i k` — THE side matrix: the number of tile edges lying on target
--   side `i` (opposite target vertex `i`) whose length is the model's side `k`.  This is the file's
--   `D_ik` (a typed count), not merely some word of the side's length: for a scalene model the type of
--   an edge is its length.  Built on the flux layer's `Dissection.sideEdges` / `Dissection.side_len_sum`
--   (Draft/FluxCore, Draft/FluxBoundary) and `EdgeWordConversion.chain_edge_length_mem_model`.
-- * `CongruentDissection.sideCount_sum` (S1): `Σ_k D_ik · model_k = target side i` (scalene model).
-- * `Row2.sideCount_eigen`, `Row2.sideCount_rows`: for a tile-similar target (`target_k = μ·model_k`),
--   `D v = μ v` with every row nonzero — equation (1).
-- * `Row2.mu_irrational`: with S3 (`Row2.area_scale`, `N = μ²`), `N` not a square ⇒ `μ ∉ ℚ`.
-- * `Row2.lemmaD_tiling`: Lemma D (Draft/FluxDRow2D) on the real side matrix: if the corner
--   conditions (A), (B) hold for `sideCount`, it has the survivor shape.
-- NOT formalized (named blocker): S2 at the corners — that (A), (B) hold for a real tiling (the corner
-- tile at A is a single α-corner with its b- and c-edges on AB, AC; at B a single β-corner, which
-- needs Lemma E's `β ∉ ℤα`).  Lemmas K, Q, E, R are not started.
--
-- Witness (Draft/FluxDRow2S1Witness.lean): the real `FluxRow2Witness.D2` (`N = 4`, `μ = 2`, scalene
-- model `(24, 32, 16)`) meets every hypothesis of `sideCount_sum`, `sideCount_eigen`, `sideCount_rows`;
-- for `lemmaD_tiling` it meets all but `¬ IsSquare N` (4 is a square; no real tile-similar tiling with
-- non-square `N` is in the corpus), and (A)/(B) are not evaluated on it.
--
-- Formalization debt; not progress on the three /goal outcomes.
import Erdos634.Draft.FluxDRow2D
import Erdos634.Draft.FluxCRow2

open scoped Classical

namespace Erdos634.Geometry

variable {N : ℕ}

/-- **The side matrix** `D_ik`: tile edges on target side `i` (the side opposite target vertex `i`,
i.e. `target.edge (i + 1)`) whose length is the model's side `k`. -/
noncomputable def CongruentDissection.sideCount (D : CongruentDissection N) (i k : Fin 3) : ℕ :=
  ((D.sideEdges (i + 1)).filter (fun e => D.eLen e = D.model.oppLen k)).card

/-- Every tile edge has one of the model's three lengths. -/
theorem CongruentDissection.eLen_mem (D : CongruentDissection N) (e : Fin N × Fin 3) :
    ∃ k, D.eLen e = D.model.oppLen k := by
  obtain ⟨k, hk⟩ := Erdos634.EdgeWordConversion.chain_edge_length_mem_model D e
  exact ⟨k + 2, hk.trans (D.sideLen_eq_oppLen k)⟩

/-- **S1**: for a scalene model, `Σ_k D_ik · model.oppLen k = target.oppLen i`. -/
theorem CongruentDissection.sideCount_sum (D : CongruentDissection N)
    (hscal : ∀ k k', k ≠ k' → D.model.oppLen k ≠ D.model.oppLen k') (i : Fin 3) :
    ∑ k, (D.sideCount i k : ℝ) * D.model.oppLen k = D.target.oppLen i := by
  have hlen := D.toDissection.side_len_sum (i + 1)
  have hopp : D.target.oppLen i = dist (D.target.pts (i + 1)) (D.target.pts (i + 1 + 1)) := by
    unfold Tri.oppLen
    rw [show i + 1 + 1 = i + 2 by fin_cases i <;> rfl]
  rw [hopp, ← hlen]
  have hsplit : ∀ e ∈ D.sideEdges (i + 1), D.eLen e
      = ∑ k, if D.eLen e = D.model.oppLen k then D.model.oppLen k else 0 := by
    intro e _
    obtain ⟨k, hk⟩ := D.eLen_mem e
    rw [Finset.sum_eq_single k]
    · rw [if_pos hk, hk]
    · intro k' _ hk'
      rw [if_neg]
      intro h
      exact hscal k' k hk' (h.symm.trans hk)
    · intro h; exact absurd (Finset.mem_univ k) h
  rw [Finset.sum_congr rfl hsplit, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold CongruentDissection.sideCount
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

/-- **Equation (1)** for a tile-similar target `target_k = μ·model_k` (scalene model): `D v = μ v`. -/
theorem Row2.sideCount_eigen (D : CongruentDissection N) (μ : ℝ)
    (hside : ∀ k, D.target.oppLen k = μ * D.model.oppLen k)
    (hscal : ∀ k k', k ≠ k' → D.model.oppLen k ≠ D.model.oppLen k') (i : Fin 3) :
    ∑ j, (D.sideCount i j : ℝ) * D.model.oppLen j = μ * D.model.oppLen i := by
  rw [D.sideCount_sum hscal i, hside i]

/-- Every row of the side matrix is nonzero (each side has positive length). -/
theorem Row2.sideCount_rows (D : CongruentDissection N)
    (hscal : ∀ k k', k ≠ k' → D.model.oppLen k ≠ D.model.oppLen k') (i : Fin 3) :
    ∃ j, 0 < D.sideCount i j := by
  by_contra h
  push Not at h
  have h0 : ∀ j, D.sideCount i j = 0 := fun j => by have := h j; omega
  have hs := D.sideCount_sum hscal i
  simp only [h0, Nat.cast_zero, zero_mul, Finset.sum_const_zero] at hs
  exact (D.target.oppLen_pos i).ne' hs.symm

/-- **S3 ⇒ `μ ∉ ℚ`**: for a tile-similar target, `N = μ²` (`Row2.area_scale`), so `μ` is irrational
unless `N` is a perfect square. -/
theorem Row2.mu_irrational (D : CongruentDissection N) (μ : ℝ)
    (hside : ∀ k, D.target.oppLen k = μ * D.model.oppLen k) (hN : ¬ IsSquare N) :
    (¬ ∃ r : ℚ, μ = r) ∧ μ ^ 2 = ((N : ℤ) : ℝ) := by
  have harea := Row2.area_scale D μ hside
  refine ⟨?_, by push_cast; exact harea.symm⟩
  rintro ⟨r, hr⟩
  have hq : ((N : ℚ) : ℝ) = ((r * r : ℚ) : ℝ) := by
    push_cast; rw [harea, hr]; ring
  have hq' : (N : ℚ) = r * r := Rat.cast_injective hq
  exact hN (Rat.isSquare_natCast_iff.mp ⟨r, hq'⟩)

/-- **Lemma D on a real tiling.**  For an `N`-tiling of a tile-similar target (ratio `μ`, scalene
model, `N` not a square), if the real side matrix satisfies the corner conditions (A), (B), it has the
survivor shape `[[0,0,A],[0,0,B],[D_ca,D_cb,0]]`.  (A), (B) themselves are S2 — not formalized. -/
theorem Row2.lemmaD_tiling (D : CongruentDissection N) (μ : ℝ)
    (hside : ∀ k, D.target.oppLen k = μ * D.model.oppLen k)
    (hscal : ∀ k k', k ≠ k' → D.model.oppLen k ≠ D.model.oppLen k') (hN : ¬ IsSquare N)
    (hA : (0 < D.sideCount 2 1 ∧ 0 < D.sideCount 1 2) ∨ (0 < D.sideCount 2 2 ∧ 0 < D.sideCount 1 1))
    (hB : (0 < D.sideCount 2 0 ∧ 0 < D.sideCount 0 2) ∨ (0 < D.sideCount 2 2 ∧ 0 < D.sideCount 0 0)) :
    D.sideCount 0 0 = 0 ∧ D.sideCount 0 1 = 0 ∧ D.sideCount 1 0 = 0 ∧ D.sideCount 1 1 = 0 ∧
      D.sideCount 2 2 = 0 ∧ 0 < D.sideCount 0 2 ∧ 0 < D.sideCount 1 2 ∧ 0 < D.sideCount 2 0 ∧
      0 < D.sideCount 2 1 := by
  obtain ⟨hμ, hp⟩ := Row2.mu_irrational D μ hside hN
  exact Row2.lemmaD D.sideCount D.model.oppLen D.model.oppLen_pos hμ hp
    (Row2.sideCount_eigen D μ hside hscal) (Row2.sideCount_rows D hscal) hA hB

end Erdos634.Geometry

#print axioms Erdos634.Geometry.CongruentDissection.eLen_mem
#print axioms Erdos634.Geometry.CongruentDissection.sideCount_sum
#print axioms Erdos634.Geometry.Row2.sideCount_eigen
#print axioms Erdos634.Geometry.Row2.sideCount_rows
#print axioms Erdos634.Geometry.Row2.mu_irrational
#print axioms Erdos634.Geometry.Row2.lemmaD_tiling

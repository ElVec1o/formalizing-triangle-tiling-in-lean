-- Draft/FluxDSideWord.lean — SIDE WORDS `W` (row11/ROW11_RATIONALITY.md P2 "W";
-- rationality/rationality_proofs.md §0 F3) as a shared lemma in the flux layer's `Tri.oppLen`
-- language: every target side of a `CongruentDissection` has length `n_a·a + n_b·b + n_c·c`,
-- `n_• ∈ ℕ`, where `a, b, c` are the model's sides under any labelling.  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
--
-- ASSEMBLED, NOT RE-PROVED.  The content is `EdgeWordConversion.side_walk_congruent` (verified
-- corpus, in All.lean), which rests on `Dissection.side_walk` / `side_walk_abc` (EdgeChain: the side
-- is partitioned by whole tile edges meeting pairwise in at most a point, lengths summed by
-- 1-dimensional Hausdorff measure) and `EdgeWordConversion.chain_edge_length_mem_model` (each tile
-- edge has one of the model's three lengths).  New here is only the re-indexing:
-- `sideLen D i = model.oppLen (i + 2)`, target side `j` is `dist (pts (j+1)) (pts (j+2))`, and a
-- permutation `σ` of the labels (so `ThreeAlphaData`/`TwoAlphaData` placements apply directly).
-- The flux layer's own `Dissection.side_len_sum` (Draft/FluxBoundary) is a second proof of the
-- length half; it is not used here.
--
-- Formalization debt; not progress on the three /goal outcomes.
import Erdos634.EdgeWordConversion
import Erdos634.Draft.FluxRow11
import Erdos634.Draft.FluxRow4

open scoped Classical

namespace Erdos634.Geometry

variable {N : ℕ}

/-- `EdgeWordConversion.sideLen D i` (the model's edge `i → i+1`) is `model.oppLen (i + 2)`. -/
theorem CongruentDissection.sideLen_eq_oppLen (D : CongruentDissection N) (i : Fin 3) :
    Erdos634.EdgeWordConversion.sideLen D i = D.model.oppLen (i + 2) := by
  unfold Erdos634.EdgeWordConversion.sideLen Tri.oppLen
  fin_cases i <;> rfl

/-- **W, index form.**  Every target side `j` (opposite target vertex `j`) is a nonnegative integer
combination of the model's three sides: `oppLen j = Σ_k n_k·model.oppLen k`. -/
theorem CongruentDissection.oppLen_word (D : CongruentDissection N) (j : Fin 3) :
    ∃ n : Fin 3 → ℕ, D.target.oppLen j = ∑ k, (n k : ℝ) * D.model.oppLen k := by
  obtain ⟨P, Q, R, h, -⟩ := Erdos634.EdgeWordConversion.side_walk_congruent D (j + 1)
  rw [D.sideLen_eq_oppLen, D.sideLen_eq_oppLen, D.sideLen_eq_oppLen] at h
  refine ⟨![Q, R, P], ?_⟩
  have hj : D.target.oppLen j = dist (D.target.pts (j + 1)) (D.target.pts (j + 1 + 1)) := by
    unfold Tri.oppLen
    rw [show j + 1 + 1 = j + 2 by fin_cases j <;> rfl]
  rw [hj, ← h, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [show (0 : Fin 3) + 2 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl,
    show (2 : Fin 3) + 2 = 1 from rfl]
  ring

/-- **W, labelled form.**  If the model's sides are `a, b, c` under a relabelling `σ`
(`oppLen (σ 0) = a`, …), every target side is `n_a·a + n_b·b + n_c·c` with `n_• ∈ ℕ`. -/
theorem CongruentDissection.side_word (D : CongruentDissection N) (σ : Equiv.Perm (Fin 3))
    {a b c : ℝ} (ha : D.model.oppLen (σ 0) = a) (hb : D.model.oppLen (σ 1) = b)
    (hc : D.model.oppLen (σ 2) = c) (j : Fin 3) :
    ∃ na nb nc : ℕ, D.target.oppLen j = na * a + nb * b + nc * c := by
  obtain ⟨n, hn⟩ := D.oppLen_word j
  refine ⟨n (σ 0), n (σ 1), n (σ 2), ?_⟩
  rw [hn, ← Equiv.sum_comp σ (fun k => (n k : ℝ) * D.model.oppLen k), Fin.sum_univ_three, ha, hb,
    hc]

/-- W for a `3α + 2β = π` placement of the model (`Tri.ThreeAlphaData`, rows 11–15). -/
theorem CongruentDissection.side_word_threeAlpha (D : CongruentDissection N) {α β a b c : ℝ}
    (h : D.model.ThreeAlphaData α β a b c) (j : Fin 3) :
    ∃ na nb nc : ℕ, D.target.oppLen j = na * a + nb * b + nc * c := by
  obtain ⟨σ, -, ha, -, hb, -, hc⟩ := h
  exact D.side_word σ ha hb hc j

/-- W for a `γ = 2α` placement of the model (`Tri.TwoAlphaData`, row 4). -/
theorem CongruentDissection.side_word_twoAlpha (D : CongruentDissection N) {α a b c : ℝ}
    (h : D.model.TwoAlphaData α a b c) (j : Fin 3) :
    ∃ na nb nc : ℕ, D.target.oppLen j = na * a + nb * b + nc * c := by
  obtain ⟨σ, -, ha, -, hb, -, hc⟩ := h
  exact D.side_word σ ha hb hc j

end Erdos634.Geometry

#print axioms Erdos634.Geometry.CongruentDissection.sideLen_eq_oppLen
#print axioms Erdos634.Geometry.CongruentDissection.oppLen_word
#print axioms Erdos634.Geometry.CongruentDissection.side_word
#print axioms Erdos634.Geometry.CongruentDissection.side_word_threeAlpha
#print axioms Erdos634.Geometry.CongruentDissection.side_word_twoAlpha

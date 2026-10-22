import Erdos634.Draft.BeesonT6

/-!
# Beeson (arXiv 1206.2229v4) Theorem 17, the "second tiling equation" part (shape `(2alpha, alpha, 2beta)`)

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Thm 17, Lemmas 27, 49), Laczkovich (DCG 48 (2012)),
Beeson-Zhang.  Formalization debt, not progress on the /goal outcomes.

Printed Theorem 17 is an algorithm (rational root theorem on `p(s) = N (1-s)^2 (2+s)^2 - M^2 (2-s^2)(3-s^2)`).
Formalized here ONLY the mathematical input: for an `N`-tiling of a target `(2alpha, alpha, 2beta)` by the tile with
`3 alpha + 2 beta = pi`, `s = a/c` is rational, `0 < s < 1`, and there is an integer `M > 0` with the second tiling equation
`N (1-s)^2 (2+s)^2 = M^2 (2-s^2)(3-s^2)` (from `t4_M1`, `lemma27`).  NOT formalized: the algorithm itself (finite search,
`f | N - M^2`, `e | 4N - 6M^2`), and the bound `0 < M^2 < N` (Lemma 49).  (H1) `alpha notin Q*pi` through `t4_M1`, `t6`.
-/

open scoped Classical

namespace Erdos634.BeesonColoring

open Erdos634.Geometry Erdos634.Geometry.A1Field

variable {N : ℕ}

theorem second_tiling_eq (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (e0 : D.target.angleAt 0 = 2 * α) (e1 : D.target.angleAt 1 = α) (e2 : D.target.angleAt 2 = 2 * β) :
    ∃ (M : ℤ) (q : ℚ), 0 < M ∧ (q : ℝ) = a / c ∧ 0 < a / c ∧ a / c < 1 ∧
      (N : ℝ) * ((1 - a / c) ^ 2 * (2 + a / c) ^ 2) = (M : ℝ) ^ 2 * ((2 - (a / c) ^ 2) * (3 - (a / c) ^ 2)) := by
  obtain ⟨hΛ, hs0, hs1⟩ := t4_aux D hrel h
  obtain ⟨M, hMp, hM⟩ := (t4_M1 D hα hrel h).2.2.2.1 ⟨e0, e1, e2⟩
  have hN := (lemma27 D hrel h).2.2.2.2 ⟨e0, e1, e2⟩
  obtain ⟨M2, M3, -, -, -, -, ⟨q, hq⟩⟩ := (t6 D hα hrel h).2 ⟨e0, e1, e2⟩
  refine ⟨M, q, hMp, hq, hs0, hs1, ?_⟩
  set Λ := circD D.target / circD D.model
  set s := a / c
  have p1 : 0 < 1 - s := by linarith
  have p2 : 0 < 2 + s := by linarith
  rw [hN, hM]
  ring

end Erdos634.BeesonColoring

#print axioms Erdos634.BeesonColoring.second_tiling_eq

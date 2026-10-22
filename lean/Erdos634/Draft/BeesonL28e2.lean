import Erdos634.Draft.BeesonL28e1

/-!
# Beeson (arXiv 1206.2229v4) Lemma 28 with printed `M1, M2`: UNCONDITIONAL (no `AnchorCoset` hypothesis)

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Lemmas 19, 28, Thm 3, Thm 4), Laczkovich (DCG 48 (2012)),
Beeson-Zhang.  Formalization debt, not progress on the /goal outcomes.

`anchorCoset_of_threeAlpha` (BeesonL28e1) supplies the printed data `(k_i, n_i, eps_i)` for every tile
(`exists_printed`), and `lemma28_printed3` then gives the printed conclusions.  Remaining hypotheses: exactly those of
the printed Lemma 28 (`3 alpha + 2 beta = pi`, `delta/pi` irrational, `ThreeAlphaData`).
-/

open scoped Classical

namespace Erdos634.BeesonColoring

open Erdos634.Geometry Erdos634.Geometry.A1Field

variable {N : ℕ}

/-- The printed data exist for every tile of every such dissection (Lemma 19 consequence, unconditional). -/
theorem exists_printed_unc (D : CongruentDissection N) {α β a b c : ℝ}
    (hδ : ¬ ∃ r : ℚ, α + β = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c) :
    ∃ (k : Fin N → Fin 3) (n e : Fin N → ℤ), (∀ i, (D.tile i).angleAt (k i + 2) = α) ∧
      ∀ i, ((D.tile i).leftUnit (k i)).angle
        = (D.target.leftUnit 0).angle + (((n i : ℝ) * (α + β) + (e i : ℝ) * Real.pi : ℝ) : Real.Angle) := by
  have hα := (delta_irr_iff hrel).mpr hδ
  have := exists_printed D hα hrel h (anchorCoset_of_threeAlpha D hα hrel h)
  choose k n e hk hd using this
  exact ⟨k, n, e, hk, hd⟩

end Erdos634.BeesonColoring

#print axioms Erdos634.BeesonColoring.exists_printed_unc

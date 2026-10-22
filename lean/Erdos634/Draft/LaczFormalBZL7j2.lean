import Erdos634.Draft.LaczFormalBZL7j1
import Erdos634.Draft.LaczFormalBZL7i4

-- Draft/LaczFormalBZL7j2.lean -- NON-VACUITY of the polygon statements of BZL7j1 (hypotheses `PolyTiling`, TwoPiThreeData, alpha irrational, `NoGammaCorner`):
--   `noGamma_tri`        : a triangle target not similar to the tile (as a `PolyTiling N 3`) satisfies `NoGammaCorner` (this is `corner_gamma_zero`);
--   `witness_poly_row4`  : the N = 7800 tiling of the (alpha, 2 alpha, pi - 3 alpha) triangle (Zhang Prop 11(1), BZL7i4) as a `PolyTiling 7800 3` meets every hypothesis of `bz_poly_ab_comm`, `bz_poly_sides_all_c`.
-- Only M = 3 is witnessed; no M >= 4 tiling by a gamma = 2pi/3 tile with irrational alpha and no gamma corner is known to the author.  NOTE, UNAUDITED.
-- Credit: Zhang (arXiv 2512.22696v4), Beeson-Zhang (arXiv 2604.01314), Laczkovich (DCG 48 (2012)).

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

theorem noGamma_tri (D : CongruentDissection N) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : D.model.TwoPiThreeData α a b c) (hNS : NotSim D) :
    ∃ T : PolyTiling N 3, T.C.model.TwoPiThreeData α a b c ∧ NoGammaCorner T.C T.P := by
  refine tri_setup D h ?_
  intro Dr _ P hreg idx hidx hidxA e0 e1 e2 hA0 hA1 hA2 hsum hpos hlt hns
  have hcorn := corner_gamma_zero Dr P hreg idx hidxA hα hA0 hA1 hA2 hsum hpos (hns hNS)
  refine ⟨⟨Dr, P, hreg⟩, ⟨1, by simpa using hA0, by simpa [slen] using e0, by simpa using hA1, by simpa [slen] using e1, by simpa using hA2, by simpa [slen] using e2⟩, ?_⟩
  intro k i v hv hang
  have hpi := Real.pi_pos
  have hr0 := hA0
  have hk1 : k - 1 + 1 = k := by simp
  have hc := hcorn (k - 1)
  rw [hk1] at hc
  unfold cnt at hc
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hc
  apply hc (Finset.mem_univ (i, v))
  refine ⟨hv, ?_⟩
  have hm := hidxA i v
  have hang' : (Dr.tile i).angleAt v = 2 * Real.pi / 3 := hang
  rw [hang'] at hm
  obtain ⟨hr0', hr1'⟩ := h.alpha_range
  have f3 : ∀ l : Fin 3, l = 0 ∨ l = 1 ∨ l = 2 := by decide
  rcases f3 (idx i v) with e | e | e
  · rw [e, hA0] at hm; linarith
  · rw [e, hA1] at hm; linarith
  · exact e

end Erdos634.Draft.LaczFormal.RG

namespace Erdos634.Draft.LaczFormal.BZL7i

open Erdos634.Draft.LaczFormal.RG

theorem witness_poly_row4 : ∃ (T : PolyTiling 7800 3) (α a b c : ℝ), T.C.model.TwoPiThreeData α a b c ∧
    (¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) ∧ NoGammaCorner T.C T.P ∧ Comm a b := by
  obtain ⟨D, α, a, b, c, data, hirr, hNS, -, -, -, -, -⟩ := witness_row4
  obtain ⟨T, data', hn⟩ := noGamma_tri D hirr data hNS
  exact ⟨T, α, a, b, c, data', hirr, hn, bz_poly_ab_comm T hirr data' hn⟩

end Erdos634.Draft.LaczFormal.BZL7i

#print axioms Erdos634.Draft.LaczFormal.RG.noGamma_tri
#print axioms Erdos634.Draft.LaczFormal.BZL7i.witness_poly_row4

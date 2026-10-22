-- Draft/LaczFormalBZL7h5.lean -- Beeson (arXiv 1206.1974v7) Theorem 10.7: the ASSEMBLY with exactly THREE named open hypotheses (`Thm107Open`), replacing `Thm107Gaps` (BZL7g1).
--   G1a / G1b : every centre (counts (0,2,3)) starts an outgoing `GaEdge` of the a-type resp. b-type side (printed Lemma 10.3 + Lemma 10.4, centre part).  OPEN: the bridge from the real fan at a centre to
--               `ga_edge_of_local` (cyclic fan, parity `centre_ab_or_ac_bc`).
--   G5c       : some boundary vertex starts a `Gamma_c` edge (printed Lemmas 10.5-10.6: c-run / non-c transition on a side; `side_has_c_step` (BZL7h1) is the pigeonhole; `half_fan_edge` is the half-plane fan).  OPEN.
-- Everything else of Lemmas 10.4/10.6 (in-degree, heads, interior, parity, stars, boundary) is PROVED in BZL7h2-h4; the printed treatment of stars is replaced by weights (printed gap, see (private working notes, not included)).
-- NOTE, UNAUDITED.  Credit: Beeson (arXiv 1206.1974v7), Laczkovich (DCG 48 (2012)), Herdt, Zhang, Beeson-Zhang.
import Erdos634.Draft.LaczFormalBZL7h4

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

/-- The three OPEN geometric hypotheses of Theorem 10.7 (centre out-edges for `Gamma_a`, `Gamma_b`; a boundary start of `Gamma_c`). -/
structure Thm107Open (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) : Prop where
  G1a : NotComb (slen D 0) (slen D 1) (slen D 2) → ∀ v ∈ vtxSet D.toRegionDissection, cnt D idx v 0 = 0 → cnt D idx v 1 = 2 → cnt D idx v 2 = 3 →
    ∃ H, GaEdge D.toRegionDissection (slen D 0) v H
  G1b : NotComb (slen D 1) (slen D 0) (slen D 2) → ∀ v ∈ vtxSet D.toRegionDissection, cnt D idx v 0 = 0 → cnt D idx v 1 = 2 → cnt D idx v 2 = 3 →
    ∃ H, GaEdge D.toRegionDissection (slen D 1) v H
  G5c : NotComb (slen D 2) (slen D 0) (slen D 1) → ∃ Q, Q ∉ interior D.region ∧ ∃ H, GaEdge D.toRegionDissection (slen D 2) Q H

/-- **Beeson Theorem 10.7, assembly with the three named open hypotheses.**  An `(alpha, pi - 3 alpha, 2 alpha)`-tiling of a convex polygon with corner angles `alpha` or `pi - 2 alpha`
(at least one of the latter), `alpha` not in `Q pi`: `a / b` and `c / a` are rational. -/
theorem beeson_thm107_partial (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hβ : D.model.angleAt 1 = Real.pi - 3 * D.model.angleAt 0) (hγ : D.model.angleAt 2 = 2 * D.model.angleAt 0)
    (hα : ¬ ∃ r : ℚ, D.model.angleAt 0 = (r : ℝ) * Real.pi)
    (hPang : ∀ k : Fin M, P.angle (k + 1) = D.model.angleAt 0 ∨ P.angle (k + 1) = Real.pi - 2 * D.model.angleAt 0)
    (k0 : Fin M) (hk0 : P.angle (k0 + 1) = Real.pi - 2 * D.model.angleAt 0)
    (G : Thm107Open D idx) :
    ∃ r s : ℚ, slen D 0 = (r : ℝ) * slen D 1 ∧ slen D 2 = (s : ℝ) * slen D 0 := by
  have ha := slen_pos D 0
  have hb := slen_pos D 1
  have hc := slen_pos D 2
  have hA : ¬ NotComb (slen D 0) (slen D 1) (slen D 2) := by
    intro hN
    exact centre_contra D P hreg idx hidx hidxA hβ hγ hα hPang k0 hk0 (Equiv.refl _) (Or.inl rfl) hN (G.G1a hN)
  have hB : ¬ NotComb (slen D 1) (slen D 0) (slen D 2) := by
    intro hN
    have e0 : (Equiv.swap (0 : Fin 3) 1) 0 = 1 := by decide
    have e1 : (Equiv.swap (0 : Fin 3) 1) 1 = 0 := by decide
    have e2 : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := by decide
    refine centre_contra D P hreg idx hidx hidxA hβ hγ hα hPang k0 hk0 (Equiv.swap 0 1) (Or.inr e0) (by rw [e0, e1, e2]; exact hN) ?_
    rw [e0]; exact G.G1b hN
  have hC : ¬ NotComb (slen D 2) (slen D 0) (slen D 1) := fun hN => c_contra D idx hidx hidxA hβ hγ hα hN (G.G5c hN)
  obtain ⟨j, p, q, hj, h1⟩ := notComb_neg hA
  obtain ⟨J, P', Q, hJ, h2⟩ := notComb_neg hB
  obtain ⟨j', p', q', hj', h3⟩ := notComb_neg hC
  exact thm107_algebra ha hb hc j p q J P' Q j' p' q' hj hJ hj' h1 h2 h3

/-- A vertex correspondence with both properties exists (so `hidx`, `hidxA` are witnessed, not assumed in vain). -/
theorem thm107_idx_exists (D : CongruentRegionDissection N) :
    ∃ idx : Fin N → Equiv.Perm (Fin 3),
      (∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k'))) ∧
      (∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) := exists_idx_both D

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.beeson_thm107_partial

-- Draft/LaczFormalBZL7h13.lean -- Beeson (arXiv 1206.1974v7) Theorem 10.7: assembly with exactly TWO named open hypotheses (`Thm107G1`: G1a, G1b = every centre starts a Gamma_a / Gamma_b edge).
--   G5c is now PROVED (BZL7h12, `g5c_of_corner`) from one extra hypothesis: a polygon corner of angle alpha exists (true for the triangle ABC: two such corners).
-- NOTE, UNAUDITED.  Credit: Beeson (arXiv 1206.1974v7), Laczkovich (DCG 48 (2012)), Herdt, Zhang, Beeson-Zhang.
import Erdos634.Draft.LaczFormalBZL7h12

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

/-- The two remaining open hypotheses of Theorem 10.7: a centre starts an outgoing `Gamma_a` / `Gamma_b` edge. -/
structure Thm107G1 (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) : Prop where
  G1a : NotComb (slen D 0) (slen D 1) (slen D 2) → ∀ v ∈ vtxSet D.toRegionDissection, cnt D idx v 0 = 0 → cnt D idx v 1 = 2 → cnt D idx v 2 = 3 →
    ∃ H, GaEdge D.toRegionDissection (slen D 0) v H
  G1b : NotComb (slen D 1) (slen D 0) (slen D 2) → ∀ v ∈ vtxSet D.toRegionDissection, cnt D idx v 0 = 0 → cnt D idx v 1 = 2 → cnt D idx v 2 = 3 →
    ∃ H, GaEdge D.toRegionDissection (slen D 1) v H

theorem Thm107G1.toOpen {D : CongruentRegionDissection N} {idx : Fin N → Equiv.Perm (Fin 3)} [HasFansC D.toRegionDissection] (G : Thm107G1 D idx)
    (P : ConvPoly M) (hreg : D.region = P.carrier)
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hβ : D.model.angleAt 1 = Real.pi - 3 * D.model.angleAt 0) (hγ : D.model.angleAt 2 = 2 * D.model.angleAt 0)
    (hα : ¬ ∃ r : ℚ, D.model.angleAt 0 = (r : ℝ) * Real.pi)
    (hPang : ∀ k : Fin M, P.angle (k + 1) = D.model.angleAt 0 ∨ P.angle (k + 1) = Real.pi - 2 * D.model.angleAt 0)
    (kA : Fin M) (hkA : P.angle (kA + 1) = D.model.angleAt 0) : Thm107Open D idx :=
  ⟨G.G1a, G.G1b, fun hnc => g5c_of_corner D P hreg idx hidx hidxA hβ hγ hα hPang hnc kA hkA⟩

/-- **Beeson Theorem 10.7 with two named open hypotheses** (`Thm107G1`: G1a, G1b). -/
theorem beeson_thm107_partial2 (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hβ : D.model.angleAt 1 = Real.pi - 3 * D.model.angleAt 0) (hγ : D.model.angleAt 2 = 2 * D.model.angleAt 0)
    (hα : ¬ ∃ r : ℚ, D.model.angleAt 0 = (r : ℝ) * Real.pi)
    (hPang : ∀ k : Fin M, P.angle (k + 1) = D.model.angleAt 0 ∨ P.angle (k + 1) = Real.pi - 2 * D.model.angleAt 0)
    (k0 : Fin M) (hk0 : P.angle (k0 + 1) = Real.pi - 2 * D.model.angleAt 0)
    (kA : Fin M) (hkA : P.angle (kA + 1) = D.model.angleAt 0)
    (G : Thm107G1 D idx) :
    ∃ r s : ℚ, slen D 0 = (r : ℝ) * slen D 1 ∧ slen D 2 = (s : ℝ) * slen D 0 :=
  beeson_thm107_partial D P hreg idx hidx hidxA hβ hγ hα hPang k0 hk0 (G.toOpen P hreg hidx hidxA hβ hγ hα hPang kA hkA)

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.beeson_thm107_partial2

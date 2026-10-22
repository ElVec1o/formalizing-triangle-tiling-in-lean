-- Draft/LaczFormalBZL7h16.lean -- Beeson (arXiv 1206.1974v7) THEOREM 10.7, ASSEMBLED WITH NO NAMED GAP HYPOTHESIS: an `(alpha, pi - 3 alpha, 2 alpha)`-tiling of a convex polygon (necessarily the isosceles
-- triangle ABC) whose corner angles are alpha or pi - 2 alpha (at least one of each), alpha not in Q pi, has a rational tile: a/b and c/a are rational.
--   Gaps G1-G6 of `Thm107Gaps` (BZL7g1): G6 = `side_has_c_step` (h1); G2/G3 (Fig 13/14) = Laczkovich parity `ga_head_data` (h2); G4 moot (Laczkovich links used throughout); the printed claim at stars REPLACED by weights (h3, h4);
--   G5 = `g5c_of_corner` (h6-h12); G1 = `g1_of_centre` (h14, h15).  The only side conditions are the angle hypotheses and the existence of a corner of angle alpha (`hkA`, true for the triangle).
-- NOTE, UNAUDITED.  Credit: Beeson (arXiv 1206.1974v7, Theorem 10.7), Laczkovich (DCG 48 (2012)), Herdt, Zhang, Beeson-Zhang.
import Erdos634.Draft.LaczFormalBZL7h15

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

theorem thm107G1_of_centre (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hβ : D.model.angleAt 1 = Real.pi - 3 * D.model.angleAt 0) (hγ : D.model.angleAt 2 = 2 * D.model.angleAt 0)
    (hα : ¬ ∃ r : ℚ, D.model.angleAt 0 = (r : ℝ) * Real.pi) : Thm107G1 D idx := by
  refine ⟨fun hnc v hv h0 h1 h2 => ?_, fun hnc v hv h0 h1 h2 => ?_⟩
  · exact g1_of_centre D P hreg idx hidx hidxA hβ hγ hα (Equiv.refl _) (Or.inl rfl) hnc (mem_vtxSet.mp hv) h0 h1 h2
  · have e0 : (Equiv.swap (0 : Fin 3) 1) 0 = 1 := by decide
    have e1 : (Equiv.swap (0 : Fin 3) 1) 1 = 0 := by decide
    have e2 : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := by decide
    have := g1_of_centre D P hreg idx hidx hidxA hβ hγ hα (Equiv.swap 0 1) (Or.inr e0) (by rw [e0, e1, e2]; exact hnc) (mem_vtxSet.mp hv) h0 h1 h2
    rw [e0] at this
    exact this

/-- **Beeson Theorem 10.7.**  Let `D` be a dissection of a convex polygon `P` into tiles congruent to a triangle with angles `(alpha, pi - 3 alpha, 2 alpha)`, `alpha` not a rational multiple of `pi`, every
corner angle of `P` equal to `alpha` or `pi - 2 alpha`, at least one of each kind.  Then the sides of the tile are commensurable: `a = r b`, `c = s a` with `r, s` rational. -/
theorem beeson_thm107_proved (D : CongruentRegionDissection N) (P : ConvPoly M) (hreg : D.region = P.carrier)
    (hβ : D.model.angleAt 1 = Real.pi - 3 * D.model.angleAt 0) (hγ : D.model.angleAt 2 = 2 * D.model.angleAt 0)
    (hα : ¬ ∃ r : ℚ, D.model.angleAt 0 = (r : ℝ) * Real.pi)
    (hPang : ∀ k : Fin M, P.angle (k + 1) = D.model.angleAt 0 ∨ P.angle (k + 1) = Real.pi - 2 * D.model.angleAt 0)
    (k0 : Fin M) (hk0 : P.angle (k0 + 1) = Real.pi - 2 * D.model.angleAt 0)
    (kA : Fin M) (hkA : P.angle (kA + 1) = D.model.angleAt 0) :
    ∃ r s : ℚ, slen D 0 = (r : ℝ) * slen D 1 ∧ slen D 2 = (s : ℝ) * slen D 0 := by
  haveI : HasFansC D.toRegionDissection := hasFansC_poly D.toRegionDissection P hreg
  obtain ⟨idx, hidx, hidxA⟩ := exists_idx_both D
  exact beeson_thm107_partial2 D P hreg idx hidx hidxA hβ hγ hα hPang k0 hk0 kA hkA (thm107G1_of_centre D P hreg idx hidx hidxA hβ hγ hα)

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.beeson_thm107_proved

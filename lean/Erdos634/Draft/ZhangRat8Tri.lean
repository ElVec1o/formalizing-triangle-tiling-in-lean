import Erdos634.Draft.LaczFormalBZL7h16
import Erdos634.Draft.LaczFormalBZL7d5b

/-!
# Triangle-to-polygon bridge for Beeson Thm 10.7 (Zhang Thm 1 row "(a,a,pi-2a), tile (a,pi-3a,2a)")

A `CongruentDissection` of a TRIANGLE with angles `(alpha, alpha, pi-2 alpha)` (`TgtAngles`), tile `(alpha, pi-3 alpha, 2 alpha)` at model
vertices `0,1,2`, `alpha` irrational, gives `r s : Q` with `a = r b`, `c = s a`: the hypotheses of `beeson_thm107_proved` (convex polygon `P`, corners,
`hkA`) are all derived from the target angles via `exists_convpoly_of_tri'`.  NOTE, UNAUDITED.
Credit: Zhang (arXiv 2512.22696v4, Thm 1), Beeson (arXiv 1206.1974v7, Thm 10.7), Beeson-Zhang, Laczkovich.
-/

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional

namespace Erdos634.Draft.ZhangRat8Tri
open Erdos634.Draft.LaczFormal.RG

theorem beeson_thm107_tri {N : ℕ} (D : CongruentDissection N)
    (hβ : D.model.angleAt 1 = Real.pi - 3 * D.model.angleAt 0) (hγ : D.model.angleAt 2 = 2 * D.model.angleAt 0)
    (hα : ¬ ∃ r : ℚ, D.model.angleAt 0 = (r : ℝ) * Real.pi)
    (hT : TgtAngles D (D.model.angleAt 0) (D.model.angleAt 0) (Real.pi - 2 * D.model.angleAt 0)) :
    ∃ r s : ℚ, slen D.toRegion 0 = (r : ℝ) * slen D.toRegion 1 ∧ slen D.toRegion 2 = (s : ℝ) * slen D.toRegion 0 := by
  obtain ⟨P, hc, τ, hτ, -⟩ := exists_convpoly_of_tri' D.target
  obtain ⟨σ, t0, t1, t2⟩ := hT
  have hreg : D.toRegion.region = P.carrier := by rw [hc]; rfl
  have hall : ∀ j : Fin 3, D.target.angleAt j = D.model.angleAt 0 ∨ D.target.angleAt j = Real.pi - 2 * D.model.angleAt 0 := by
    intro j
    obtain ⟨k, rfl⟩ := σ.surjective j
    fin_cases k
    · exact Or.inl t0
    · exact Or.inl t1
    · exact Or.inr t2
  refine beeson_thm107_proved D.toRegion P hreg hβ hγ hα (fun k => by rw [hτ]; exact hall _)
    (τ.symm (σ 2) - 1) ?_ (τ.symm (σ 0) - 1) ?_
  · rw [sub_add_cancel, hτ]; simpa using t2
  · rw [sub_add_cancel, hτ]; simpa using t0

end Erdos634.Draft.ZhangRat8Tri
#print axioms Erdos634.Draft.ZhangRat8Tri.beeson_thm107_tri

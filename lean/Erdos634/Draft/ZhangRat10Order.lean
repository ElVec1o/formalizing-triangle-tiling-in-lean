import Erdos634.Draft.ZhangRat7Lem5
import Erdos634.Draft.FluxDRow4AnyLabel
import Erdos634.Draft.FluxFRow14AnyLabel

/-!
# Zhang Lemma 5, geometric form, for EVERY order of the target's vertices (G2)

`ZhangRat7Lem5.zhang_lemma5_geom` fixes the target angles `(2 alpha, 2 beta, alpha + beta)` at the target vertices `0, 1, 2`.  Zhang's Lemma 5 says only "some triangle with
angles `(2 alpha, 2 beta, alpha + beta)`".  Here the angles are required at the target vertices in ANY order (`tau`, one of the six permutations), via `relabelTarget'`
(same tiles, same model, target vertices permuted).  Zhang's Lemma 3 (equilateral target) has no vertex order.
NOTE, UNAUDITED.  Credit: Zhang (arXiv 2512.22696v4, Lemma 5), Beeson, Beeson-Zhang.
-/

open scoped Classical
open Erdos634.Geometry Erdos634.Geometry.Dissection Erdos634.SideWall Erdos634.TilePlacement Erdos634.AreaDet

namespace Erdos634.ZhangRat10Order
open Erdos634.ZhangRat7Int Erdos634.ZhangRat7Lem5

/-- Angles of the relabelled target. -/
theorem relabelTarget'_angleAt {N : ℕ} (D : CongruentDissection N) (τ : Equiv.Perm (Fin 3)) (k : Fin 3) :
    (D.relabelTarget' τ).target.angleAt k = D.target.angleAt (τ k) :=
  Erdos634.Geometry.Row14AnyLabel.angleAt_of_pts τ (fun _ => rfl) k

/-- **Zhang Lemma 5, geometric form, any order of the target's vertices.** -/
theorem zhang_lemma5_geom_any {N : ℕ} (A B C : ℕ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hh : C * C = A * A + B * B + A * B) (hcop : Nat.Coprime A B) (h3 : A % 3 ≠ B % 3)
    (D : CongruentDissection N) (hN : 0 < N)
    (h0 : sideOpp D.model 0 = A) (h1 : sideOpp D.model 1 = B) (h2 : sideOpp D.model 2 = C)
    (τ : Equiv.Perm (Fin 3))
    (hφ0 : angleAt D.target (τ 0) = 2 * angleAt D.model 0)
    (hφ1 : angleAt D.target (τ 1) = 2 * angleAt D.model 1)
    (hφ2 : angleAt D.target (τ 2) = angleAt D.model 0 + angleAt D.model 1) :
    ∃ k : ℕ, N = (A + 2 * B) * (B + 2 * A) * k ^ 2 :=
  zhang_lemma5_geom A B C hA hB hC hh hcop h3 (D.relabelTarget' τ) hN h0 h1 h2
    (by rw [show angleAt (D.relabelTarget' τ).target 0 = (D.relabelTarget' τ).target.angleAt 0 from rfl, relabelTarget'_angleAt]; exact hφ0)
    (by rw [show angleAt (D.relabelTarget' τ).target 1 = (D.relabelTarget' τ).target.angleAt 1 from rfl, relabelTarget'_angleAt]; exact hφ1)
    (by rw [show angleAt (D.relabelTarget' τ).target 2 = (D.relabelTarget' τ).target.angleAt 2 from rfl, relabelTarget'_angleAt]; exact hφ2)

end Erdos634.ZhangRat10Order
#print axioms Erdos634.ZhangRat10Order.zhang_lemma5_geom_any

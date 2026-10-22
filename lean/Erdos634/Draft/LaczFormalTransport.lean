import Erdos634.Draft.LaczFormalL26Beeson
import Erdos634.Draft.LaczFormalL25Thm
import Erdos634.Draft.LaczFormalL24Main
import Erdos634.TranslateDissection
import Erdos634.Ladder
import Mathlib.Geometry.Euclidean.Similarity

/-!
# Transport of a congruent dissection to an arbitrary triangle of the same shape (AAA)

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94), Beeson, Beeson-Zhang, Zhang.

`transport_similar`: a `CongruentDissection` of a triangle `T` gives, for every triangle `T'` with two equal corresponding
angles (hence similar, Mathlib's `similar_of_angle_angle`), a `CongruentDissection` of `T'` whose model is congruent to the
`r`-scale of the old model (`r` the similarity ratio).  Construction: homothety (`scaleDissection`), then the ambient isometry
given by SSS (`congruent_of_dist`).  The corollaries `thm24_first_any`, `thm25_first_any`, `thm24_fourth_any` transport the
explicit triangles of those theorems to ANY triangle with the stated angles.
-/

namespace Erdos634.LaczTransport

open Erdos634.Geometry Erdos634.Realizable Erdos634.DissectionMap Erdos634.TranslateDissection Erdos634.Ladder
  Erdos634.SssCongruent EuclideanGeometry

theorem all_idx : ∀ a b c : Fin 3, a ≠ b → b ≠ c → a ≠ c → ∀ x : Fin 3, x = a ∨ x = b ∨ x = c := by decide

theorem sim_of_angles (T T' : Tri) (a b c : Fin 3) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (h1 : ∠ (T.pts a) (T.pts b) (T.pts c) = ∠ (T'.pts a) (T'.pts b) (T'.pts c))
    (h2 : ∠ (T.pts b) (T.pts c) (T.pts a) = ∠ (T'.pts b) (T'.pts c) (T'.pts a)) :
    ∃ r : ℝ, 0 < r ∧ ∀ x y, dist (T'.pts x) (T'.pts y) = r * dist (T.pts x) (T.pts y) := by
  have hinj : Function.Injective (![a, b, c] : Fin 3 → Fin 3) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  have hind : AffineIndependent ℝ ![T'.pts a, T'.pts b, T'.pts c] := by
    have e : (![T'.pts a, T'.pts b, T'.pts c]) = T'.pts ∘ (![a, b, c] : Fin 3 → Fin 3) := by
      funext i; fin_cases i <;> rfl
    rw [e]
    exact T'.indep.comp_embedding ⟨![a, b, c], hinj⟩
  have hnc : ¬ Collinear ℝ {T'.pts a, T'.pts b, T'.pts c} := by
    have := affineIndependent_iff_not_collinear_set.1 hind
    simpa using this
  have hsim := EuclideanGeometry.similar_of_angle_angle hnc h1.symm h2.symm
  obtain ⟨r, hr0, hr⟩ := similar_iff_exists_pos_dist_eq.1 hsim
  refine ⟨r, hr0, fun x y => ?_⟩
  have key : ∀ i j : Fin 3, dist (![T'.pts a, T'.pts b, T'.pts c] i) (![T'.pts a, T'.pts b, T'.pts c] j)
      = r * dist (![T.pts a, T.pts b, T.pts c] i) (![T.pts a, T.pts b, T.pts c] j) := hr
  rcases all_idx a b c hab hbc hac x with hx | hx | hx <;>
    rcases all_idx a b c hab hbc hac y with hy | hy | hy <;> rw [hx, hy]
  · simp
  · exact key 0 1
  · exact key 0 2
  · exact key 1 0
  · simp
  · exact key 1 2
  · exact key 2 0
  · exact key 2 1
  · simp

/-- An isometry applied to a whole congruent dissection (the model is unchanged). -/
noncomputable def isoCongruentDissection {N : ℕ} (f : Plane ≃ᵃⁱ[ℝ] Plane) (D : CongruentDissection N) :
    CongruentDissection N where
  toDissection := mapDissection f.toAffineEquiv D.toDissection
  model := D.model
  tiles_congruent := fun i => by
    rw [mapDissection_tile]
    exact (D.tiles_congruent i).map_left f

theorem iso_target {N : ℕ} (f : Plane ≃ᵃⁱ[ℝ] Plane) (D : CongruentDissection N) :
    (isoCongruentDissection f D).target = mapTri f.toAffineEquiv D.target := rfl

theorem iso_model {N : ℕ} (f : Plane ≃ᵃⁱ[ℝ] Plane) (D : CongruentDissection N) :
    (isoCongruentDissection f D).model = D.model := rfl

/-- **Transport to a similar triangle.**  Two equal angles of corresponding vertices (any three distinct indices
`a, b, c`) make `T'` similar to the target `D.target`; the dissection is carried over. -/
theorem transport_similar {N : ℕ} (D : CongruentDissection N) (T' : Tri) (a b c : Fin 3)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (h1 : ∠ (D.target.pts a) (D.target.pts b) (D.target.pts c) = ∠ (T'.pts a) (T'.pts b) (T'.pts c))
    (h2 : ∠ (D.target.pts b) (D.target.pts c) (D.target.pts a) = ∠ (T'.pts b) (T'.pts c) (T'.pts a)) :
    ∃ (r : ℝ) (hr : 0 < r) (D' : CongruentDissection N),
      D'.target.carrier = T'.carrier ∧ D'.model.Congruent (scaleTri r hr.ne' D.model) := by
  obtain ⟨r, hr, hdist⟩ := sim_of_angles D.target T' a b c hab hbc hac h1 h2
  set p : Plane := D.target.pts 0 with hp
  set hom := homothetyEquiv p r hr.ne' with hhom
  have hU : (mapTri hom D.target).Congruent T' := by
    refine congruent_of_dist (fun i j => ?_)
    show dist (hom (D.target.pts i)) (hom (D.target.pts j)) = _
    rw [hhom, homothetyEquiv_dist, abs_of_pos hr, hdist]
  obtain ⟨f, σ, hf⟩ := hU
  let D₁ := scaleDissection p r hr.ne' D
  let g : Plane ≃ᵃⁱ[ℝ] Plane := f.toRealAffineIsometryEquiv
  refine ⟨r, hr, isoCongruentDissection g D₁, ?_, ?_⟩
  · rw [iso_target, mapTri_carrier]
    show g.toAffineEquiv '' (mapTri hom D.target).carrier = T'.carrier
    rw [← mapTri_carrier]
    simp only [Tri.carrier, mapTri]
    have hpts : (g.toAffineEquiv ∘ (hom ∘ D.target.pts)) = T'.pts ∘ σ := by
      funext k
      exact hf k
    rw [hpts, Function.Surjective.range_comp σ.surjective]
  · rw [iso_model]
    refine congruent_of_dist (fun i j => ?_)
    show dist (hom (D.model.pts i)) (hom (D.model.pts j)) = dist ((scaleTri r hr.ne' D.model).pts i)
      ((scaleTri r hr.ne' D.model).pts j)
    rw [hhom, homothetyEquiv_dist, scaleTri_pts, scaleTri_pts, dist_homothety]

end Erdos634.LaczTransport

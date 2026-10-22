import Erdos634.TileAt
import Erdos634.AngleSumDissection

/-!
# Reversing the vertex labelling of one tile of a `CongruentDissection`

Erdős #634, base-`β` band.  Credit: AI assistant (band lemma / item-3 proposal), Beeson–Roșu, Beeson,
Laczkovich, Paliy.

The tiles of a `CongruentDissection` come with an arbitrary vertex labelling (`Tri.Congruent` allows
any permutation), so a statement "tile `i` has `pts j = P`, `pts (j+1) = G`, `pts (j+2) = Q`" covers
only one of the two cyclic orientations of the three vertices.  `Tri.rev` reverses the orientation
(`pts' k = pts (-k)`); it has the same carrier, the same local angles and is congruent to the
original, so `CongruentDissection.revAt D i` (tile `i` replaced by its reverse) is again a
`CongruentDissection` with the same target and the same carriers, and every orientation-specific
theorem applies to the other orientation by passing from `D` to `D.revAt i`.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.LaczJunction

open Erdos634.Geometry

variable {N : ℕ}

/-- The tile with the opposite vertex orientation: `pts' k = pts (-k)`. -/
def _root_.Erdos634.Geometry.Tri.rev (T : Tri) : Tri where
  pts := fun k => T.pts (-k)
  indep := T.indep.comp_embedding (Equiv.neg (Fin 3)).toEmbedding

theorem rev_pts (T : Tri) (k : Fin 3) : T.rev.pts k = T.pts (-k) := rfl

theorem rev_carrier (T : Tri) : T.rev.carrier = T.carrier := by
  unfold Tri.carrier
  congr 1
  show Set.range (fun k => T.pts (-k)) = Set.range T.pts
  exact (Equiv.neg (Fin 3)).surjective.range_comp T.pts

theorem rev_basis (T : Tri) : T.rev.basis = T.basis.reindex (Equiv.neg (Fin 3)) := by
  apply AffineBasis.ext
  funext k
  show T.pts (-k) = (T.basis.reindex (Equiv.neg (Fin 3))) k
  rw [AffineBasis.coe_reindex]
  rfl

theorem rev_coord (T : Tri) (k : Fin 3) (p : Plane) :
    T.rev.basis.coord k p = T.basis.coord (-k) p := by
  rw [rev_basis, AffineBasis.coord_reindex]
  rfl

theorem rev_congruent (T : Tri) : T.rev.Congruent T :=
  ⟨IsometryEquiv.refl Plane, Equiv.neg (Fin 3), fun k => by simp [IsometryEquiv.refl, rev_pts]⟩

theorem rev_localAngle (T : Tri) (p : Plane) : T.rev.localAngle p = T.localAngle p := by
  classical
  by_cases hv : ∃ m, p = T.pts m
  · obtain ⟨m, rfl⟩ := hv
    have h1 : T.pts m = T.rev.pts (-m) := by rw [rev_pts, neg_neg]
    rw [Tri.localAngle_vertex, h1, Tri.localAngle_vertex, rev_pts, rev_pts, rev_pts]
    have e1 : -(-m + 1) = m + 2 := by fin_cases m <;> rfl
    have e2 : -(-m + 2) = m + 1 := by fin_cases m <;> rfl
    have e3 : -(-m) = m := neg_neg m
    rw [e1, e2, e3]
    unfold cornerAngle
    exact EuclideanGeometry.angle_comm _ _ _
  · have hv' : ¬ ∃ m, p = T.rev.pts m := by
      rintro ⟨m, hm⟩
      exact hv ⟨-m, hm⟩
    unfold Tri.localAngle
    rw [dif_neg hv, dif_neg hv']
    simp only [rev_coord]
    have hneg : ∀ (P : Fin 3 → Prop), (∀ j, P (-j)) ↔ (∀ j, P j) :=
      fun P => ⟨fun h j => by simpa using h (-j), fun h j => h _⟩
    have hneg' : ∀ (P : Fin 3 → Prop), (∃ j, P (-j)) ↔ (∃ j, P j) :=
      fun P => ⟨fun ⟨j, h⟩ => ⟨_, h⟩, fun ⟨j, h⟩ => ⟨-j, by simpa using h⟩⟩
    have c1 : (∀ j, 0 < T.basis.coord (-j) p) ↔ (∀ j, 0 < T.basis.coord j p) :=
      hneg (fun j => 0 < T.basis.coord j p)
    have c2 : (∃ k, T.basis.coord (-k) p = 0 ∧ ∀ j, j ≠ k → 0 < T.basis.coord (-j) p) ↔
        (∃ k, T.basis.coord k p = 0 ∧ ∀ j, j ≠ k → 0 < T.basis.coord j p) := by
      constructor
      · rintro ⟨k, hk, h⟩
        refine ⟨-k, hk, fun j hj => ?_⟩
        have := h (-j) (fun h' => hj (by rw [← h', neg_neg]))
        simpa using this
      · rintro ⟨k, hk, h⟩
        refine ⟨-k, by simpa using hk, fun j hj => ?_⟩
        exact h (-j) (fun h' => hj (by rw [← h', neg_neg]))
    simp only [c1, c2]

/-- Replace the vertex labelling of tile `i₁` by its reverse. -/
noncomputable def _root_.Erdos634.Geometry.CongruentDissection.revAt (D : CongruentDissection N)
    (i₁ : Fin N) : CongruentDissection N where
  target := D.target
  tile := Function.update D.tile i₁ (D.tile i₁).rev
  covers := by
    have : ∀ i, (Function.update D.tile i₁ (D.tile i₁).rev i).carrier = (D.tile i).carrier := by
      intro i
      by_cases h : i = i₁
      · subst h; simp [rev_carrier]
      · simp [Function.update_of_ne h]
    simp only [this]; exact D.covers
  interiors_disjoint := by
    have : ∀ i, (Function.update D.tile i₁ (D.tile i₁).rev i).carrier = (D.tile i).carrier := by
      intro i
      by_cases h : i = i₁
      · subst h; simp [rev_carrier]
      · simp [Function.update_of_ne h]
    intro i j hij
    simp only [this]; exact D.interiors_disjoint hij
  model := D.model
  tiles_congruent := by
    intro i
    by_cases h : i = i₁
    · subst h; simp only [Function.update_self]
      exact (rev_congruent _).trans (D.tiles_congruent i)
    · simp only [Function.update_of_ne h]; exact D.tiles_congruent i

theorem revAt_target (D : CongruentDissection N) (i₁ : Fin N) : (D.revAt i₁).target = D.target := rfl
theorem revAt_model (D : CongruentDissection N) (i₁ : Fin N) : (D.revAt i₁).model = D.model := rfl
theorem revAt_tile_ne (D : CongruentDissection N) {i₁ i : Fin N} (h : i ≠ i₁) :
    (D.revAt i₁).tile i = D.tile i := by
  show Function.update D.tile i₁ (D.tile i₁).rev i = D.tile i
  simp [Function.update_of_ne h]
theorem revAt_tile_self (D : CongruentDissection N) (i₁ : Fin N) :
    (D.revAt i₁).tile i₁ = (D.tile i₁).rev := by
  show Function.update D.tile i₁ (D.tile i₁).rev i₁ = _
  simp

#print axioms rev_localAngle
#print axioms Erdos634.Geometry.CongruentDissection.revAt

end Erdos634.LaczJunction

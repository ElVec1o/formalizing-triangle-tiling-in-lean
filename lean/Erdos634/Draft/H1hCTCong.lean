-- Draft/H1hCTCong.lean — ATOM H1.h, part 2: CT for a real `CongruentDissection`.
--
-- If every corner of `D : CongruentDissection N` is `ι(c)`, `c ∈ F`, then for every ring hom
-- `ψ : F →+* ℝ` the vertexwise images `ψ(c)` form a `CongruentDissection N`: the conjugate tiles are
-- again pairwise congruent (SSS: squared distances are polynomial in the coordinates, so `ψ`
-- transports the equalities `ι(d²_i) = ι(d²_{t0})` that congruence gives).
-- Formalization debt (SCOPE_H1_full H1.h); NOT /goal progress.  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
import Erdos634.Draft.H1hCT
import Erdos634.Draft.KConjNormal
import Erdos634.Draft.FluxGRow3RP
import Erdos634.SssCongruent

namespace Erdos634.H1hCT

open Erdos634.Geometry Erdos634.KMoment Erdos634.CertCoord

variable {F : Type*} [Field F] [CharZero F]

/-- Squared distance between corners `k`, `l` in coordinates `c`. -/
def d2 (c : Fin 3 → Fin 2 → F) (k l : Fin 3) : F :=
  (c k 0 - c l 0) ^ 2 + (c k 1 - c l 1) ^ 2

theorem dist_sq_plane (p q : Plane) : dist p q ^ 2 = (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

theorem dist_sq_of_coords (φ : F →+* ℝ) (T : Tri) (c : Fin 3 → Fin 2 → F)
    (h : ∀ k v, T.pts k v = φ (c k v)) (k l : Fin 3) :
    dist (T.pts k) (T.pts l) ^ 2 = φ (d2 c k l) := by
  rw [dist_sq_plane, d2]
  simp only [map_add, map_pow, map_sub, ← h]

/-- **CT for congruent tilings.** -/
theorem conj_congruentDissection {N : ℕ} (D : CongruentDissection N) (ι ψ : F →+* ℝ)
    (c : Fin N → Fin 3 → Fin 2 → F) (cT' : Fin 3 → Fin 2 → F)
    (hc : ∀ i k v, (D.tile i).pts k v = ι (c i k v))
    (hcT : ∀ k v, D.target.pts k v = ι (cT' k v)) :
    ∃ D' : CongruentDissection N, (∀ i k v, (D'.tile i).pts k v = ψ (c i k v)) ∧
      (∀ k v, D'.target.pts k v = ψ (cT' k v)) := by
  have hN := D.pos
  set t0 : Fin N := ⟨0, hN⟩
  have hP : ∀ i, |(D.tile i).det| = |D.model.det| := fun i =>
    Erdos634.KConj.abs_det_congr (D.tiles_congruent i)
  have hPT : |D.target.det| = N * |D.model.det| := Erdos634.Geometry.Row3.RP.abs_det_target D
  obtain ⟨D1, h1, h2⟩ := conj_dissection D.toDissection ι ψ c cT' hc hcT _ hP hPT
  have hd : ∀ i, detc (c i) ≠ 0 := fun i => detc_ne_of_coords ι _ _ (hc i)
  -- squared distances of tile i vs tile t0
  have hsq : ∀ i, ∃ σ : Equiv.Perm (Fin 3), ∀ k l, d2 (c i) k l = d2 (c t0) (σ k) (σ l) := by
    intro i
    obtain ⟨σ, hσ⟩ := ((D.tiles_congruent i).trans (D.tiles_congruent t0).symm).dist_eq
    refine ⟨σ, fun k l => ι.injective ?_⟩
    rw [← dist_sq_of_coords ι _ _ (hc i), ← dist_sq_of_coords ι _ _ (hc t0), hσ k l]
  refine ⟨{ toDissection := D1, model := D1.tile t0, tiles_congruent := ?_ }, h1, h2⟩
  intro i
  obtain ⟨σ, hσ⟩ := hsq i
  refine Erdos634.SssCongruent.congruent_of_sq_dist_perm σ (fun k l => ?_)
  rw [dist_sq_of_coords ψ _ _ (h1 i), dist_sq_of_coords ψ _ _ (h1 t0), hσ k l]

/-- **CT, final form (the one the sign lemma / Case D consume).**
`K ⊆ ℝ` a subfield containing every tile and target corner coordinate; `ψ : K →+* ℝ` any ring
homomorphism of `K` itself (for `K = ℚ(√M)`: the nontrivial automorphism).  Then there is a
`CongruentDissection N` whose corners are the `ψ`-images of the corners (coordinatewise), and the
squared side lengths of its tiles are the `ψ`-images of the original squared side lengths.
NOTE: `ψ` must be defined on all of `K`.  An embedding of a SMALLER field `K₀ ⊆ K` does not in
general extend to `K → ℝ` (it needs `ψ` to preserve the positivity of every square in `K`), which
is why the field hypothesis is exactly "corners lie in the field on which `ψ` lives". -/
theorem conj_congruentDissection_subfield {N : ℕ} (D : CongruentDissection N) (K : Subfield ℝ)
    (ψ : K →+* ℝ)
    (hK : ∀ i k v, (D.tile i).pts k v ∈ K) (hKT : ∀ k v, D.target.pts k v ∈ K) :
    ∃ D' : CongruentDissection N,
      (∀ i k v, (D'.tile i).pts k v = ψ ⟨(D.tile i).pts k v, hK i k v⟩) ∧
      (∀ k v, D'.target.pts k v = ψ ⟨D.target.pts k v, hKT k v⟩) ∧
      (∀ i k l, dist ((D'.tile i).pts k) ((D'.tile i).pts l) ^ 2 =
        ψ ⟨dist ((D.tile i).pts k) ((D.tile i).pts l) ^ 2, by
          rw [dist_sq_plane]
          exact K.add_mem (K.pow_mem (K.sub_mem (hK i k 0) (hK i l 0)) 2)
            (K.pow_mem (K.sub_mem (hK i k 1) (hK i l 1)) 2)⟩) := by
  obtain ⟨D', h1, h2⟩ := conj_congruentDissection D K.subtype ψ
    (fun i k v => ⟨_, hK i k v⟩) (fun k v => ⟨_, hKT k v⟩) (fun i k v => rfl) (fun k v => rfl)
  refine ⟨D', h1, h2, fun i k l => ?_⟩
  rw [dist_sq_of_coords ψ (D'.tile i) (fun k v => ⟨_, hK i k v⟩) (h1 i) k l]
  congr 1
  apply K.subtype.injective
  show _ = dist ((D.tile i).pts k) ((D.tile i).pts l) ^ 2
  rw [dist_sq_of_coords K.subtype (D.tile i) (fun k v => ⟨_, hK i k v⟩) (fun _ _ => rfl) k l]

end Erdos634.H1hCT

#print axioms Erdos634.H1hCT.conj_congruentDissection
#print axioms Erdos634.H1hCT.conj_congruentDissection_subfield

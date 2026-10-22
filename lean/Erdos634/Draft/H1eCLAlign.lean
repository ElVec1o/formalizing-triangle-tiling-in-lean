/-
Draft/H1eCLAlign.lean — atom H1.e (CL), part 1: a tile whose local angle at a target vertex equals the FULL corner
angle of the target there has its two edges at that vertex along the two sides of the target (SameRay), in one order or
the other.  (Generic: any `Dissection`, any target vertex; this is the geometric half of the paper's "(B) the single
corner tile's sector equals the target cone".)  Adapted from `F1CornerAlign.f1_v1_edges_aligned`, whose counting part
is removed.
*** UNAUDITED.  Formalization debt, NOT /goal progress.  No sorry. ***
-/
import Erdos634.Draft.F1EdgeAlign
import Erdos634.ApexEdgesReal
import Erdos634.AngleSumDissection
import Erdos634.MarchFlank
import Erdos634.RouteOneVertexKill

open scoped Classical

namespace Erdos634.Draft.H1eCL

open Erdos634.Geometry

private instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp⟩

private lemma fin3_succ_ne (k : Fin 3) : k + 1 ≠ k := by fin_cases k <;> decide
private lemma fin3_succ2_ne (k : Fin 3) : k + 2 ≠ k := by fin_cases k <;> decide

/-- An orientation of the plane (any one). -/
noncomputable def plane_orientation : Orientation ℝ Plane (Fin 2) :=
  (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation

/-- **Single-tile corner alignment.**  If tile `i₀` has local angle at the target vertex `k₀` equal to the target's own
corner angle there, then `k₀` is a vertex `j` of tile `i₀` and the tile's two edges at it lie along the target's two
sides at `k₀` (as `SameRay` of the direction vectors), in one order or the other. -/
theorem corner_aligned {N : ℕ} (D : Dissection N) (k₀ : Fin 3) (i₀ : Fin N) {θ : ℝ}
    (hcorner : cornerAngle (D.target.pts (k₀ + 1)) (D.target.pts k₀) (D.target.pts (k₀ + 2)) = θ)
    (hloc : (D.tile i₀).localAngle (D.target.pts k₀) = θ) :
    ∃ j : Fin 3, D.target.pts k₀ = (D.tile i₀).pts j ∧
      ((SameRay ℝ (D.target.pts (k₀ + 1) - D.target.pts k₀)
                 ((D.tile i₀).pts (j + 1) - D.target.pts k₀) ∧
        SameRay ℝ (D.target.pts (k₀ + 2) - D.target.pts k₀)
                 ((D.tile i₀).pts (j + 2) - D.target.pts k₀)) ∨
       (SameRay ℝ (D.target.pts (k₀ + 2) - D.target.pts k₀)
                 ((D.tile i₀).pts (j + 1) - D.target.pts k₀) ∧
        SameRay ℝ (D.target.pts (k₀ + 1) - D.target.pts k₀)
                 ((D.tile i₀).pts (j + 2) - D.target.pts k₀))) := by
  set o := plane_orientation
  have hθ_pos : 0 < θ := by
    have := Erdos634.MarchFlank.cornerAngle_pos D.target k₀; rwa [hcorner] at this
  have hθ_lt : θ < Real.pi := by
    have := Erdos634.RouteOneVertexKill.cornerAngle_lt_pi D.target k₀; rwa [hcorner] at this
  have hθ_ne0 : θ ≠ 0 := hθ_pos.ne'
  have hθ_neπ : θ ≠ Real.pi := hθ_lt.ne
  have hθ_ne2π : θ ≠ 2 * Real.pi := by
    have := Real.pi_pos; intro h; linarith
  have htgt_inj := D.target.indep.injective
  have hu_ne0 : D.target.pts (k₀ + 1) - D.target.pts k₀ ≠ 0 :=
    sub_ne_zero.mpr (htgt_inj.ne (fin3_succ_ne k₀))
  have hv_ne0 : D.target.pts (k₀ + 2) - D.target.pts k₀ ≠ 0 :=
    sub_ne_zero.mpr (htgt_inj.ne (fin3_succ2_ne k₀))
  have hangle_tgt : InnerProductGeometry.angle
      (D.target.pts (k₀ + 1) - D.target.pts k₀)
      (D.target.pts (k₀ + 2) - D.target.pts k₀) = θ := by
    have : InnerProductGeometry.angle
        (D.target.pts (k₀ + 1) - D.target.pts k₀)
        (D.target.pts (k₀ + 2) - D.target.pts k₀)
      = cornerAngle (D.target.pts (k₀ + 1)) (D.target.pts k₀) (D.target.pts (k₀ + 2)) := by
      rw [cornerAngle, EuclideanGeometry.angle]; simp [vsub_eq_sub]
    rw [this, hcorner]
  obtain ⟨j, hjV₁⟩ := Erdos634.ApexEdgesReal.isVertex_of_localAngle_ne
      (D.tile i₀) hθ_ne2π hθ_neπ hθ_ne0 hloc
  set u  := D.target.pts (k₀ + 1) - D.target.pts k₀
  set v  := D.target.pts (k₀ + 2) - D.target.pts k₀
  set u' := (D.tile i₀).pts (j + 1) - D.target.pts k₀
  set v' := (D.tile i₀).pts (j + 2) - D.target.pts k₀
  have htile_inj := (D.tile i₀).indep.injective
  have hu'_ne0 : u' ≠ 0 := by
    show (D.tile i₀).pts (j + 1) - D.target.pts k₀ ≠ 0
    rw [hjV₁]; exact sub_ne_zero.mpr (htile_inj.ne (fin3_succ_ne j))
  have hv'_ne0 : v' ≠ 0 := by
    show (D.tile i₀).pts (j + 2) - D.target.pts k₀ ≠ 0
    rw [hjV₁]; exact sub_ne_zero.mpr (htile_inj.ne (fin3_succ2_ne j))
  have hangle_tile : InnerProductGeometry.angle u' v' = θ := by
    have hloc' : (D.tile i₀).localAngle ((D.tile i₀).pts j) = θ := by
      rw [← hjV₁]; exact hloc
    rw [Tri.localAngle_vertex] at hloc'
    have heq : InnerProductGeometry.angle u' v' =
        cornerAngle ((D.tile i₀).pts (j + 1)) ((D.tile i₀).pts j) ((D.tile i₀).pts (j + 2)) := by
      show InnerProductGeometry.angle
          ((D.tile i₀).pts (j + 1) - D.target.pts k₀)
          ((D.tile i₀).pts (j + 2) - D.target.pts k₀) =
          cornerAngle ((D.tile i₀).pts (j + 1)) ((D.tile i₀).pts j) ((D.tile i₀).pts (j + 2))
      rw [hjV₁, cornerAngle, EuclideanGeometry.angle]; simp [vsub_eq_sub]
    rw [heq]; exact hloc'
  have hcar_sub : (D.tile i₀).carrier ⊆ D.target.carrier := tile_subset_target D i₀
  have hj1_tgt : (D.tile i₀).pts (j + 1) ∈ D.target.carrier :=
    hcar_sub (subset_convexHull ℝ _ (Set.mem_range_self (j + 1)))
  have hj2_tgt : (D.tile i₀).pts (j + 2) ∈ D.target.carrier :=
    hcar_sub (subset_convexHull ℝ _ (Set.mem_range_self (j + 2)))
  obtain ⟨c₁, c₂, hc₁, hc₂, hcomb_u'⟩ :=
    tri_corner_cone_of_mem' D.target k₀ ((D.tile i₀).pts (j + 1)) hj1_tgt
  obtain ⟨d₁, d₂, hd₁, hd₂, hcomb_v'⟩ :=
    tri_corner_cone_of_mem' D.target k₀ ((D.tile i₀).pts (j + 2)) hj2_tgt
  have hmemu' : (o.oangle u u').toReal ∈ Set.uIcc 0 (o.oangle u v).toReal :=
    nonneg_comb_oangle_mem_uIcc o hu_ne0 hv_ne0 hu'_ne0 hc₁ hc₂ hcomb_u' hθ_pos hθ_lt hangle_tgt
  have hmemv' : (o.oangle u v').toReal ∈ Set.uIcc 0 (o.oangle u v).toReal :=
    nonneg_comb_oangle_mem_uIcc o hu_ne0 hv_ne0 hv'_ne0 hd₁ hd₂ hcomb_v' hθ_pos hθ_lt hangle_tgt
  rcases wedge_forces_ray_eq o u v u' v' hu_ne0 hv_ne0 hu'_ne0 hv'_ne0
      θ hθ_pos hθ_lt hangle_tgt hangle_tile hmemu' hmemv' with
    ⟨huu', hvv'⟩ | ⟨hvu', huv'⟩
  · exact ⟨j, hjV₁, Or.inl ⟨huu', hvv'⟩⟩
  · exact ⟨j, hjV₁, Or.inr ⟨hvu', huv'⟩⟩

end Erdos634.Draft.H1eCL

#print axioms Erdos634.Draft.H1eCL.corner_aligned

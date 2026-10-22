-- Draft/FluxCancel.lean — `lem:cancel` for arbitrary (not edge-to-edge) dissections.
-- Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).  Design: (private working notes, not included) §3.4.
import Erdos634.Draft.FluxInterior
import Erdos634.Draft.FluxBoundary
import Erdos634.Congruence

open scoped Classical

namespace Erdos634.Geometry

variable {N : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- **`lem:cancel`.** -/
theorem Dissection.flux_cancel (D : Dissection N) (f : Dir → E)
    (hodd : ∀ d, f (Dir.neg d) = - f d) :
    ∑ i, (D.tile i).flux f = D.target.flux f := by
  rw [D.flux_sum_eq, D.sum_split, D.interior_flux_zero f hodd, zero_add, D.side_flux]

theorem CongruentDissection.flux_cancel (D : CongruentDissection N) (f : Dir → E)
    (hodd : ∀ d, f (Dir.neg d) = - f d) :
    ∑ i, (D.tile i).flux f = D.target.flux f :=
  D.toDissection.flux_cancel f hodd

/-- **The paper's `Λ_int(θ) = Λ_int(θ+π)`**, finite-sum form: the interior edge lengths in
direction `d` and in direction `−d` agree.  (`interior_flux_zero` at the odd indicator weight
`[·=d] − [·=−d]`.)  This is the `hLint` of `InvariantCore.cancellation_core_real`, now a theorem
about real dissections. -/
theorem Dissection.interior_length_balance (D : Dissection N) (d : Dir) :
    ∑ e ∈ D.intEdges.filter (fun e => D.eDir e = d), D.eLen e
      = ∑ e ∈ D.intEdges.filter (fun e => D.eDir e = Dir.neg d), D.eLen e := by
  let w : Dir → ℝ := fun d' => (if d' = d then 1 else 0) - (if d' = Dir.neg d then 1 else 0)
  have hw : ∀ d', w (Dir.neg d') = - w d' := by
    intro d'
    have F1 : (Dir.neg d' = d) ↔ (d' = Dir.neg d) := by
      constructor
      · intro h; rw [← h, Dir.neg_involutive d']
      · intro h; rw [h, Dir.neg_involutive d]
    have F2 : (Dir.neg d' = Dir.neg d) ↔ (d' = d) :=
      ⟨fun h => Dir.neg_involutive.injective h, fun h => by rw [h]⟩
    show (if Dir.neg d' = d then (1:ℝ) else 0) - (if Dir.neg d' = Dir.neg d then 1 else 0)
      = -((if d' = d then (1:ℝ) else 0) - (if d' = Dir.neg d then 1 else 0))
    simp only [F1, F2]
    ring
  have h0 := D.interior_flux_zero w hw
  simp only [smul_eq_mul, w, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib] at h0
  rw [Finset.sum_filter, Finset.sum_filter]
  linarith

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Dissection.flux_cancel
#print axioms Erdos634.Geometry.CongruentDissection.flux_cancel
#print axioms Erdos634.Geometry.Dissection.interior_length_balance
#print axioms Erdos634.Geometry.Dissection.interior_flux_zero
#print axioms Erdos634.Geometry.Dissection.opposite_cover
#print axioms Erdos634.Geometry.Dissection.eDir_of_side
#print axioms Erdos634.Geometry.Dissection.side_len_sum
#print axioms Erdos634.Geometry.Dissection.sameDir_subsingleton
#print axioms Erdos634.Geometry.Dissection.edge_interior_or_side

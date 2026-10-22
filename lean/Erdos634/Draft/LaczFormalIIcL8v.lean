-- Draft/LaczFormalIIcL8v.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.3, two exceptional points: CENTRAL SYMMETRY with the index split `hI` DISCHARGED (`index_split`, L8u) -- `central_symmetry_two_exc`.
-- Also `k_ge_four`: from `M gamma = 2 pi`, `gamma < pi/2`, `gamma != pi/3` and `M = 2k` follows `4 <= k`.
-- NOTE, UNAUDITED.  CONDITIONAL on `kiteB = empty` (NoKites) and on the Case IIc hypothesis block (witnessed by GenWitK (204-tile octagon, genTiling_thm21) and IsoWitM).  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcL8u

open scoped Classical Fin.NatCast
open EuclideanGeometry Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

theorem k_ge_four {k : ℕ} {γ : ℝ} (hγ0 : 0 < γ) (h1 : γ < Real.pi / 2) (h3 : γ ≠ Real.pi / 3) (hM : ((2 * k : ℕ) : ℝ) * γ = 2 * Real.pi) : 4 ≤ k := by
  have hpi := Real.pi_pos
  push_cast at hM
  by_contra hlt
  push Not at hlt
  have hk : (k : ℝ) ≤ 3 := by exact_mod_cast (by omega : k ≤ 3)
  interval_cases k <;> norm_num at hM
  · linarith
  · linarith
  · apply h3; linarith

set_option maxHeartbeats 12800000 in
/-- **Central symmetry of the two-exceptional-point polygon**, unconditional on the index split (conditional on `kiteB = empty`). -/
theorem central_symmetry_two_exc {k : ℕ} [NeZero (2 * k)] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly (2 * k)) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (G : AngGen (fun l => D.model.angleAt l))
    (hcor : ∀ j : Fin (2 * k), cnt D idx (P.v j) 0 = 1 ∧ cnt D idx (P.v j) 1 = 1 ∧ cnt D idx (P.v j) 2 = 0)
    (hNK : kiteB D idx = ∅) (W : Fin (2 * k) → Plane) (hW : ∀ j, GExc D idx (P.v j) (W j)) (hdiff : ∃ j, W j ≠ W 0) :
    ∀ i : Fin (2 * k), P.side i = P.side (i + (k : Fin (2 * k))) := by
  obtain ⟨E, F, hEF, hI⟩ := index_split D P hreg idx hC hab hac h1 h3 G hcor hNK W hW hdiff
  obtain ⟨-, hMγ⟩ := corner_angles_gamma D P hreg idx hC h1 h3 hcor
  have hk4 := k_ge_four (model_angle_pos' D 2) h1 h3 hMγ
  have hint : ∀ E ∈ excVerts2 D idx P, E ∈ interior D.region := fun E hE =>
    (gexc_exc_interior_exact D P hreg idx hC hab hac h1 h3 G hcor E hE).1
  exact central_symmetry_of_spokes D P hreg idx hC h1 h3 hcor (by omega) hint W hW E F hI

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.central_symmetry_two_exc

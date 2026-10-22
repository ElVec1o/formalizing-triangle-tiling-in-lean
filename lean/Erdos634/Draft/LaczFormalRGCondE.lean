-- Draft/LaczFormalRGCondE.lean -- S3 of PLAN_THM21: the corner count `cnt` for a congruent dissection of a REGION (port of LaczFormalCondE.cnt).
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 2: the numbers p_i, q_i, r_i of the angles alpha, beta, gamma at the vertex V_i).
import Erdos634.Draft.LaczFormalRGExt
import Erdos634.Draft.LaczFormalCondE

open Erdos634.Geometry Erdos634.RegionDissection

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

/-- Number of tile corners located at `P` of model type `l`. -/
noncomputable def cnt (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (P : Plane) (l : Fin 3) : ℕ :=
  (Finset.univ.filter (fun p : Fin N × Fin 3 => (D.tile p.1).pts p.2 = P ∧ idx p.1 p.2 = l)).card

theorem fiber_sum_P (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (P : Plane)
    (g : Fin 3 → ℝ) :
    ∑ i, ∑ v, (if (D.tile i).pts v = P then g (idx i v) else 0) = ∑ l, (cnt D idx P l : ℝ) * g l := by
  have h1 : ∀ l, (cnt D idx P l : ℝ) * g l = ∑ p : Fin N × Fin 3,
      (if (D.tile p.1).pts p.2 = P ∧ idx p.1 p.2 = l then g l else 0) := by
    intro l
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, cnt]
  calc ∑ i, ∑ v, (if (D.tile i).pts v = P then g (idx i v) else 0)
      = ∑ p : Fin N × Fin 3, (if (D.tile p.1).pts p.2 = P then g (idx p.1 p.2) else 0) :=
        by rw [Fintype.sum_prod_type]
    _ = ∑ p : Fin N × Fin 3, ∑ l, (if (D.tile p.1).pts p.2 = P ∧ idx p.1 p.2 = l then g l else 0) := by
        refine Finset.sum_congr rfl (fun p _ => ?_)
        by_cases hp : (D.tile p.1).pts p.2 = P
        · simp only [hp, true_and, if_true]
          rw [Finset.sum_ite_eq]; simp
        · simp [hp]
    _ = ∑ l, ∑ p : Fin N × Fin 3, (if (D.tile p.1).pts p.2 = P ∧ idx p.1 p.2 = l then g l else 0) :=
        Finset.sum_comm
    _ = ∑ l, (cnt D idx P l : ℝ) * g l := by simp_rw [h1]

end Erdos634.Draft.LaczFormal.RG

-- Draft/PrimeWitness2.lean — non-vacuity control for the `CongruentDissection` framework at a PRIME
-- count: the right isosceles triangle cut by its altitude is a `CongruentDissection 2`.
-- (2 is prime; it is excluded from `theoremP_6` by `3 < N`, and 2 % 4 ≠ 3.)
-- Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).
import Erdos634.Draft.RAAssemble

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.RWGlue Erdos634.Draft.RWPieces
  Erdos634.Draft.RAAssemble
open Erdos634.RouteOneCrossing (selfDissection)

namespace Erdos634.Draft.PrimeWitness2

theorem det_T : det3 1 1 0 0 2 0 ≠ 0 := by unfold det3; norm_num
theorem det_T1 : det3 1 1 0 0 1 0 ≠ 0 := by unfold det3; norm_num
theorem det_T2 : det3 1 1 1 0 2 0 ≠ 0 := by unfold det3; norm_num

noncomputable def T : Tri := mkTri 1 1 0 0 2 0 det_T
noncomputable def T1 : Tri := mkTri 1 1 0 0 1 0 det_T1
noncomputable def T2 : Tri := mkTri 1 1 1 0 2 0 det_T2

theorem T2_cong_T1 : T2.Congruent T1 := by
  have hs : dist (mkPt (1 : ℝ) 1) (mkPt 2 0) = dist (mkPt (1 : ℝ) 1) (mkPt 0 0) := by
    refine eq_of_sq_eq dist_nonneg dist_nonneg ?_
    rw [dist_sq_mkPt, dist_sq_mkPt]; norm_num
  have hone : dist (mkPt (2 : ℝ) 0) (mkPt 1 0) = dist (mkPt (0 : ℝ) 0) (mkPt 1 0) := by
    refine eq_of_sq_eq dist_nonneg dist_nonneg ?_
    rw [dist_sq_mkPt, dist_sq_mkPt]; norm_num
  have hP : dist (mkPt (1 : ℝ) 0) (mkPt 1 1) = dist (mkPt (1 : ℝ) 0) (mkPt 1 1) := rfl
  refine (T2.congruent_relabel (Equiv.swap (1 : Fin 3) 2)).trans ?_
  refine SssCongruent.congruent_of_dist_three ?_ ?_ ?_
  · show dist (mkPt (1 : ℝ) 1) (mkPt 2 0) = dist (mkPt (1 : ℝ) 1) (mkPt 0 0)
    exact hs
  · show dist (mkPt (2 : ℝ) 0) (mkPt 1 0) = dist (mkPt (0 : ℝ) 0) (mkPt 1 0)
    exact hone
  · show dist (mkPt (1 : ℝ) 0) (mkPt 1 1) = dist (mkPt (1 : ℝ) 0) (mkPt 1 1)
    rfl

/-- **A tiling by a prime number of congruent triangles.** -/
theorem exists_prime_dissection : Nonempty (CongruentDissection 2) ∧ Nat.Prime 2 := by
  set D1 : CongruentDissection 1 :=
    { toDissection := selfDissection T1, model := T1, tiles_congruent := fun _ => Tri.Congruent.refl T1 }
  set D2 : CongruentDissection 1 :=
    { toDissection := selfDissection T2, model := T1, tiles_congruent := fun _ => T2_cong_T1 }
  have hlm : AffineMap.lineMap (mkPt (0 : ℝ) 0) (mkPt 2 0) (1 / 2 : ℝ) = mkPt 1 0 := by
    rw [lm]; congr 1; norm_num
  obtain ⟨D, -, -⟩ := glue_two T T1 T2 (1 / 2) (by norm_num) (by norm_num)
    (by show mkPt (1 : ℝ) 1 = mkPt 1 1; rfl) (by show mkPt (0 : ℝ) 0 = mkPt 0 0; rfl)
    (by show mkPt (1 : ℝ) 0 = AffineMap.lineMap (mkPt (0 : ℝ) 0) (mkPt 2 0) (1 / 2); rw [hlm])
    (by show mkPt (1 : ℝ) 1 = mkPt 1 1; rfl) (by show mkPt (1 : ℝ) 0 = AffineMap.lineMap (mkPt (0 : ℝ) 0) (mkPt 2 0) (1 / 2); rw [hlm])
    (by show mkPt (2 : ℝ) 0 = mkPt 2 0; rfl)
    D1 D2 (Tri.Congruent.refl _) (Tri.Congruent.refl _) (Tri.Congruent.refl _)
  exact ⟨⟨D⟩, Nat.prime_two⟩

end Erdos634.Draft.PrimeWitness2

#print axioms Erdos634.Draft.PrimeWitness2.exists_prime_dissection

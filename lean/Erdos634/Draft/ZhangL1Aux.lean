import Erdos634.Draft.GlueCut
import Erdos634.Ladder
import Erdos634.SssCongruent

/-!
# Auxiliary pieces for Zhang's Lemma 1: a scaled copy of a tile cut into `k*k` tiles

`scaledPiece`: if `U` is congruent to the model `R` and `T` is the homothety image of `U`
about its vertex `0` with integer ratio `k`, then `T` carries a `CongruentRegionDissection (k*k*1)`
with model `R` and region `T.carrier`.  (`Erdos634.Ladder.ladder` applied to the one-tile identity
dissection of `U`.)  Credit Zhang (arXiv 2512.22696), Beeson, Laczkovich.
-/

namespace Erdos634.ZhangL1

open Erdos634.Geometry Erdos634.CertCoord Erdos634.RegionDissection Erdos634.Subdivision

theorem tri_ext_pts {T T' : Tri} (h : T.pts = T'.pts) : T = T' := by
  cases T; cases T'; simp at h; subst h; rfl

theorem mkPt_add (x y x' y' : ℝ) : mkPt x y + mkPt x' y' = mkPt (x + x') (y + y') := by
  ext i; fin_cases i <;> simp

theorem mkPt_sub (x y x' y' : ℝ) : mkPt x y - mkPt x' y' = mkPt (x - x') (y - y') := by
  ext i; fin_cases i <;> simp

theorem mkPt_smul (k x y : ℝ) : k • mkPt x y = mkPt (k * x) (k * y) := by
  ext i; fin_cases i <;> simp

/-- **A scaled tile is cut into `k*k` tiles.** -/
theorem scaledPiece (U R T : Tri) (hUR : U.Congruent R) (k : ℕ) (hk : 0 < k)
    (h0 : T.pts 0 = U.pts 0)
    (h1 : T.pts 1 = U.pts 0 + (k : ℝ) • (U.pts 1 - U.pts 0))
    (h2 : T.pts 2 = U.pts 0 + (k : ℝ) • (U.pts 2 - U.pts 0)) :
    ∃ C : CongruentRegionDissection (k * k * 1), C.region = T.carrier ∧ C.model = R := by
  classical
  have hfun : (![U.pts 0, U.pts 1, U.pts 2] : Fin 3 → Plane) = U.pts := by
    funext x; fin_cases x <;> rfl
  have hind : AffineIndependent ℝ (![U.pts 0, U.pts 1, U.pts 2] : Fin 3 → Plane) := by
    rw [hfun]; exact U.indep
  set U' : Tri := ⟨![U.pts 0, U.pts 1, U.pts 2], hind⟩ with hU'
  have hU'U : U' = U := tri_ext_pts hfun
  let D : CongruentDissection 1 :=
    { target := U'
      tile := fun _ => U'
      covers := Set.iUnion_const _
      interiors_disjoint := by intro i j hij; exact absurd (Subsingleton.elim i j) hij
      model := R
      tiles_congruent := fun _ => by rw [hU'U]; exact hUR }
  obtain ⟨E, hEt, hEm⟩ := Erdos634.Ladder.ladder (U.pts 0) (U.pts 1) (U.pts 2) hind D rfl k hk
  have hTeq : bigTri (U.pts 0) (U.pts 1) (U.pts 2) hind k hk = T := by
    apply tri_ext_pts
    funext x
    fin_cases x
    · exact h0.symm
    · show Erdos634.Subdivision.P (U.pts 0) (U.pts 1) (U.pts 2) k 0 = T.pts 1
      rw [h1]; simp only [Erdos634.Subdivision.P]; simp
    · show Erdos634.Subdivision.P (U.pts 0) (U.pts 1) (U.pts 2) 0 k = T.pts 2
      rw [h2]; simp only [Erdos634.Subdivision.P]; simp
  refine ⟨E.toRegion, ?_, hEm.trans rfl⟩
  show E.target.carrier = T.carrier
  rw [hEt, hTeq]

end Erdos634.ZhangL1

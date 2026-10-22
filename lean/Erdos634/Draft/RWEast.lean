-- Draft/RWEast.lean — the east piece `(A,P,E)` of the cevian cut is dissected into `f²` tiles
-- (thm:ladder), model an arbitrary tile `M` with sides `(ef, f²−e², f²)`.
-- Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).
import Erdos634.Draft.RWPieces
import Erdos634.Ladder
import Erdos634.SssCongruent
import Erdos634.Draft.FluxTurn
import Erdos634.RouteOneCrossing

open scoped Classical
open Erdos634.RouteOneCrossing (selfDissection)
open Erdos634.Geometry Erdos634.BaseBetaTargetCoord Erdos634.CertCoord Erdos634.Draft.RWPieces

namespace Erdos634.Draft.RWEast

/-- Distances in the scale-`k` triangle. -/
theorem dist_bigTri (A B C : Plane) (h : AffineIndependent ℝ ![A, B, C]) (k : ℕ) (hk : 0 < k)
    (i j : Fin 3) :
    dist ((Erdos634.Subdivision.bigTri A B C h k hk).pts i) ((Erdos634.Subdivision.bigTri A B C h k hk).pts j)
      = (k : ℝ) * dist (![A, B, C] i) (![A, B, C] j) := by
  have hk' : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have htri : ∀ y : Fin 3, y = 0 ∨ y = 1 ∨ y = 2 := by decide
  have hpts : ∀ y : Fin 3, (Erdos634.Subdivision.bigTri A B C h k hk).pts y
      = Erdos634.Subdivision.bigMap A (k : ℝ) (![A, B, C] y) := by
    intro y
    rcases htri y with rfl | rfl | rfl <;>
      simp [Erdos634.Subdivision.bigTri, Erdos634.Subdivision.bigMap, Erdos634.Subdivision.P,
        AffineMap.homothety_apply, add_comm]
  have key : ∀ p q : Plane, dist (Erdos634.Subdivision.bigMap A (k : ℝ) p)
      (Erdos634.Subdivision.bigMap A (k : ℝ) q) = (k : ℝ) * dist p q := by
    intro p q
    simp only [Erdos634.Subdivision.bigMap, AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
    rw [dist_eq_norm, dist_eq_norm, show (k : ℝ) • (p - A) + A - ((k : ℝ) • (q - A) + A)
      = (k : ℝ) • (p - q) by module, norm_smul, Real.norm_eq_abs, abs_of_nonneg hk']
  rw [hpts i, hpts j]; exact key _ _

theorem tri_eta (T : Tri) :
    ∃ h : AffineIndependent ℝ ![T.pts 0, T.pts 1, T.pts 2], T = ⟨![T.pts 0, T.pts 1, T.pts 2], h⟩ := by
  have hfun : (![T.pts 0, T.pts 1, T.pts 2] : Fin 3 → Plane) = T.pts := by
    funext k; fin_cases k <;> rfl
  refine ⟨hfun ▸ T.indep, ?_⟩
  obtain ⟨p, i⟩ := T
  congr
  funext k; fin_cases k <;> rfl

/-- **East piece.**  For a tile `M` with sides `(ef, f²−e², f²)`, the east piece `(A,P,E)` of the
cut is dissected into `f²` copies of `M`. -/
theorem east_dissection (e f : ℝ) (fN : ℕ) (hfN : (fN : ℝ) = f) (hfpos : 0 < fN)
    (he : 0 < e) (hef : e < f) (M : Tri)
    (hM0 : M.oppLen 0 = e * f) (hM1 : M.oppLen 1 = f ^ 2 - e ^ 2) (hM2 : M.oppLen 2 = f ^ 2) :
    ∃ E : CongruentDissection (fN * fN * 1), E.target.Congruent (eTri he hef) ∧ E.model = M := by
  set M2 : Tri := M.relabel (Equiv.swap (1 : Fin 3) 2) with hM2def
  have hp0 : M2.pts 0 = M.pts 0 := by simp [hM2def, Tri.relabel_pts, Equiv.swap_apply_of_ne_of_ne]
  have hp1 : M2.pts 1 = M.pts 2 := by simp [hM2def, Tri.relabel_pts]
  have hp2 : M2.pts 2 = M.pts 1 := by simp [hM2def, Tri.relabel_pts]
  obtain ⟨hind, heta⟩ := tri_eta M2
  set D0 : CongruentDissection 1 :=
    { toDissection := selfDissection M2
      model := M
      tiles_congruent := fun _ => (M.congruent_relabel (Equiv.swap (1 : Fin 3) 2)).symm } with hD0
  obtain ⟨E, hEt, hEm⟩ := Erdos634.Ladder.ladder (M2.pts 0) (M2.pts 1) (M2.pts 2) hind D0
    (heta) fN hfpos
  refine ⟨E, ?_, hEm⟩
  rw [hEt]
  have hd := dist_bigTri (M2.pts 0) (M2.pts 1) (M2.pts 2) hind fN hfpos
  have o0 : dist (M.pts 1) (M.pts 2) = e * f := hM0
  have o1 : dist (M.pts 2) (M.pts 0) = f ^ 2 - e ^ 2 := hM1
  have o2 : dist (M.pts 0) (M.pts 1) = f ^ 2 := hM2
  refine SssCongruent.congruent_of_dist_three ?_ ?_ ?_
  · rw [hd 0 1]
    show (fN : ℝ) * dist (M2.pts 0) (M2.pts 1) = dist ((eTri he hef).pts 0) ((eTri he hef).pts 1)
    rw [hp0, hp1, dist_comm, o1, hfN]
    show f * (f ^ 2 - e ^ 2) = dist (mkPt (baseLen e f / 2) (height e f)) (mkPt (xP e f) 0)
    rw [d_AP he hef]
  · rw [hd 1 2]
    show (fN : ℝ) * dist (M2.pts 1) (M2.pts 2) = dist ((eTri he hef).pts 1) ((eTri he hef).pts 2)
    rw [hp1, hp2, dist_comm, o0, hfN]
    show f * (e * f) = dist (mkPt (xP e f) 0) (mkPt (baseLen e f) 0)
    rw [d_PE he hef]; ring
  · rw [hd 2 0]
    show (fN : ℝ) * dist (M2.pts 2) (M2.pts 0) = dist ((eTri he hef).pts 2) ((eTri he hef).pts 0)
    rw [hp2, hp0, dist_comm, o2, hfN]
    show f * f ^ 2 = dist (mkPt (baseLen e f) 0) (mkPt (baseLen e f / 2) (height e f))
    rw [dist_comm, d_AE he hef]; ring

end Erdos634.Draft.RWEast

#print axioms Erdos634.Draft.RWEast.east_dissection

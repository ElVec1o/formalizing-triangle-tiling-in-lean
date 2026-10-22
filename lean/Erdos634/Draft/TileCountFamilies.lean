-- Draft/TileCountFamilies.lean — existence side of "all N": the set of tile counts is closed under
-- N ↦ k²N (Ladder), and contains 1, 3, a²+b² (all a,b ≥ 1), hence every k², 3k², k²(a²+b²);
-- plus 11m² (m ≥ 2).  UNAUDITED.  Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).
import Erdos634.Ladder
import Erdos634.Draft.PrimeWitness2
import Erdos634.Draft.Equilateral3
import Erdos634.Draft.SumTwoSquares
import Erdos634.Draft.CollarInputs
import Erdos634.Draft.SixTiles

namespace Erdos634.Draft.TileCountFamilies
open Erdos634.Geometry

/-- The set of tile counts. -/
def TileCount (N : ℕ) : Prop := Nonempty (CongruentDissection N)

theorem tileCount_scale {N : ℕ} (h : TileCount N) {k : ℕ} (hk : 0 < k) : TileCount (k * k * N) := by
  obtain ⟨D⟩ := h
  have hT : D.target = (⟨![D.target.pts 0, D.target.pts 1, D.target.pts 2], by
      have := D.target.indep
      convert this using 1; funext i; fin_cases i <;> rfl⟩ : Tri) := by
    cases hD : D.target with
    | mk p ip => congr 1; funext i; fin_cases i <;> rfl
  obtain ⟨E, -, -⟩ := Erdos634.Ladder.ladder _ _ _ _ D hT k hk
  exact ⟨E⟩

theorem tileCount_two_squares (a b : ℕ) (ha : 0 < a) (hb : 0 < b) : TileCount (a * a + b * b) :=
  Erdos634.Draft.SumTwoSquares.sum_two_squares_tiling a b ha hb

theorem tileCount_one : TileCount 1 :=
  ⟨{ toDissection := Erdos634.RouteOneCrossing.selfDissection Erdos634.Draft.PrimeWitness2.T1
     model := Erdos634.Draft.PrimeWitness2.T1
     tiles_congruent := fun _ => Tri.Congruent.refl _ }⟩

theorem tileCount_sq {k : ℕ} (hk : 0 < k) : TileCount (k * k) := by
  simpa using tileCount_scale tileCount_one hk

theorem tileCount_three_sq {k : ℕ} (hk : 0 < k) : TileCount (3 * (k * k)) := by
  obtain ⟨D⟩ := Erdos634.Draft.Equilateral3.exists_dissection_3
  have := tileCount_scale ⟨D⟩ hk
  rwa [show k * k * 3 = 3 * (k * k) by ring] at this

theorem tileCount_sq_mul_two_squares {k a b : ℕ} (hk : 0 < k) (ha : 0 < a) (hb : 0 < b) :
    TileCount (k * k * (a * a + b * b)) :=
  tileCount_scale (tileCount_two_squares a b ha hb) hk

theorem tileCount_eleven_sq {m : ℕ} (hm : 2 ≤ m) : TileCount (11 * (m * m)) :=
  ⟨(Erdos634.Draft.CollarInputs.realize12 m hm).choose⟩

theorem tileCount_six_sq {k : ℕ} (hk : 0 < k) : TileCount (6 * (k * k)) := by
  have := tileCount_scale Erdos634.Draft.SixTiles.exists_dissection_6 hk
  rwa [show k * k * 6 = 6 * (k * k) by ring] at this

end Erdos634.Draft.TileCountFamilies

#print axioms Erdos634.Draft.TileCountFamilies.tileCount_eleven_sq
#print axioms Erdos634.Draft.TileCountFamilies.tileCount_sq_mul_two_squares
#print axioms Erdos634.Draft.TileCountFamilies.tileCount_three_sq
#print axioms Erdos634.Draft.TileCountFamilies.tileCount_six_sq

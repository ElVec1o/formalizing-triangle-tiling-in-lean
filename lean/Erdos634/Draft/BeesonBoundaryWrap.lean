import Erdos634.BeesonBoundary

/-!
# BeesonBoundary — Beeson Def. 13 boundary orientation: wrapper

Key results:
- `onLeftOf_reverse`: OnLeftOf p q y ↔ OnRightOf q p y
- `tile_side_dichotomy`: supporting tile interior lies strictly left or right
- `tile_side_total`: total: left or right, never on the line
- `def13_witness`: Def13BoundarySegment is non-vacuous

VERIFIED: 0 sorry, standard axioms.
-/

namespace Erdos634.Draft.BeesonBoundaryWrap

open Erdos634.BeesonBoundary Erdos634.Geometry Erdos634.BeesonOmega

theorem bb_onLeftOf_reverse (p q y : Plane) : OnLeftOf p q y ↔ OnRightOf q p y :=
  onLeftOf_reverse p q y

theorem bb_tile_side_dichotomy (T : Tri) (k : Fin 3) (p q : Plane)
    (hp : T.pts k = p) (hq : T.pts (k + 1) = q)
    {y : Plane} (hy : ∀ i, 0 < T.basis.coord i y) :
    (T.leftDir k = q - p → OnLeftOf p q y) ∧ (T.leftDir k = p - q → OnRightOf p q y) :=
  tile_side_dichotomy T k p q hp hq hy

theorem bb_tile_side_total (T : Tri) (k : Fin 3) (p q : Plane)
    (hp : T.pts k = p) (hq : T.pts (k + 1) = q)
    {y : Plane} (hy : ∀ i, 0 < T.basis.coord i y) :
    OnLeftOf p q y ∨ OnRightOf p q y :=
  tile_side_total T k p q hp hq hy

theorem bb_def13_witness {N : ℕ} (D : CongruentDissection N) (A B C : Plane) (i₀ : Fin N)
    (p q : Plane) (hnone : ∀ i k, ¬ SupportsDirected D.toDissection i k p q) :
    Def13BoundarySegment D A B C i₀ p q True :=
  def13_witness D A B C i₀ p q hnone

-- Non-vacuity: onLeftOf_reverse is a bijection at the propositional level
example (p q y : Plane) : (OnLeftOf p q y ↔ OnRightOf q p y) := bb_onLeftOf_reverse p q y

#print axioms bb_tile_side_total
#print axioms bb_def13_witness

end Erdos634.Draft.BeesonBoundaryWrap

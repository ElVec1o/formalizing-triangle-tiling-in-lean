import Erdos634.BeesonDef5

/-!
# BeesonDef5 — Beeson Def. 5 Type I/II placement: wrapper

Key results:
- `directionC_placement_isTypeI`: Direction-C placement is Type I
- `directionA_placement_isTypeII`: Direction-A placement is Type II
- `directionA_ne_directionC`: Directions A and C are distinct unless a = c

VERIFIED: 0 sorry, standard axioms.
-/

namespace Erdos634.Draft.BeesonDef5Wrap

open Erdos634.BeesonDef5 Erdos634.Geometry Erdos634.BeesonDirections

theorem bd5_directionC_placement_isTypeI (uAB uBC : Plane) (a c : ℝ)
    (ha : a ≠ 0) (hc : c ≠ 0) :
    TypeIDirs uAB uBC (a • uAB) (DirectionC uAB uBC a c) (c • uBC) (DirectionC uAB uBC a c) :=
  directionC_placement_isTypeI uAB uBC a c ha hc

theorem bd5_directionA_placement_isTypeII (uAB uBC : Plane) (a c : ℝ)
    (ha : a ≠ 0) (hc : c ≠ 0) :
    TypeIIDirs uAB uBC (a • uBC) (DirectionA uAB uBC a c) (c • uAB) (DirectionA uAB uBC a c) :=
  directionA_placement_isTypeII uAB uBC a c ha hc

theorem bd5_directionA_ne_directionC (uAB uBC : Plane) (a c : ℝ)
    (h : DirectionA uAB uBC a c = DirectionC uAB uBC a c)
    (hindep : ∀ s t : ℝ, s • uAB + t • uBC = 0 → s = 0 ∧ t = 0) : a = c :=
  directionA_ne_directionC uAB uBC a c h hindep

-- Non-vacuity: directionA_ne_directionC is stated as a conditional
example (uAB uBC : Plane) (a c : ℝ)
    (h : DirectionA uAB uBC a c = DirectionC uAB uBC a c)
    (hindep : ∀ s t : ℝ, s • uAB + t • uBC = 0 → s = 0 ∧ t = 0) : a = c :=
  bd5_directionA_ne_directionC uAB uBC a c h hindep

#print axioms bd5_directionC_placement_isTypeI
#print axioms bd5_directionA_ne_directionC

end Erdos634.Draft.BeesonDef5Wrap

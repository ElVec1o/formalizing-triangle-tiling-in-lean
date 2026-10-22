import Erdos634.BeesonDirections

/-!
# BeesonDirections — Beeson Type I/II tile directions: wrapper

Key results:
- `Par.refl/symm/trans/neg`: parallelism is an equivalence + negation
- `typeI_typeII_disjoint`: Type I and II are disjoint for non-collinear ABC
- `isTypeI_witness`: constructive witness for Type I
- `edgeDir_ne_zero`: edge directions are nonzero

VERIFIED: 0 sorry, standard axioms.
-/

namespace Erdos634.Draft.BeesonDirectionsWrap

open Erdos634.BeesonDirections Erdos634.Geometry

theorem bdir_par_refl {u : Plane} : Par u u := Par.refl

theorem bdir_par_symm {u v : Plane} (h : Par u v) : Par v u := Par.symm h

theorem bdir_par_trans {u v w : Plane} (h1 : Par u v) (h2 : Par v w) : Par u w :=
  Par.trans h1 h2

theorem bdir_typeI_typeII_disjoint (T : Tri) (ka kc : Fin 3) (A B C : Plane)
    (hncol : ¬ Collinear ℝ ({A, B, C} : Set Plane))
    (h1 : IsTypeI T ka kc A B C) (h2 : IsTypeII T ka kc A B C) : False :=
  typeI_typeII_disjoint T ka kc A B C hncol h1 h2

theorem bdir_isTypeI_witness (T : Tri) (ka kc : Fin 3) (A B C : Plane)
    (hc : EdgeDir T kc = C - B) (ha : EdgeDir T ka = B - A) : IsTypeI T ka kc A B C :=
  isTypeI_witness T ka kc A B C hc ha

theorem bdir_edgeDir_ne_zero (T : Tri) (k : Fin 3) : EdgeDir T k ≠ 0 :=
  edgeDir_ne_zero T k

-- Non-vacuity: Par.refl
example (u : Plane) : Par u u := bdir_par_refl

#print axioms bdir_typeI_typeII_disjoint
#print axioms bdir_edgeDir_ne_zero

end Erdos634.Draft.BeesonDirectionsWrap

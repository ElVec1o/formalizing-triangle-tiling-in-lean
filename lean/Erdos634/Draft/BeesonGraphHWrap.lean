import Erdos634.BeesonGraphH

/-!
# BeesonGraphH — Beeson's graph H connectivity: wrapper

Key results:
- `hAdj_irrefl/symm`: H-adjacency is irreflexive and symmetric
- `hConn_refl/trans/symm/equivalence`: HConn is an equivalence relation
- `hConn_of_hAdj`: adjacency implies connectivity

VERIFIED: 0 sorry, standard axioms.
-/

namespace Erdos634.Draft.BeesonGraphHWrap

open Erdos634.BeesonGraphH Erdos634.TilePlacement Erdos634.Geometry

variable {N : ℕ}

theorem bgh_hAdj_irrefl (D : Dissection N) (i : Fin N) : ¬ HAdj D i i :=
  hAdj_irrefl D i

theorem bgh_hAdj_symm (D : Dissection N) {i j : Fin N} (h : HAdj D i j) : HAdj D j i :=
  hAdj_symm D h

theorem bgh_hConn_refl (D : Dissection N) (i : Fin N) : HConn D i i :=
  hConn_refl D i

theorem bgh_hConn_trans (D : Dissection N) {i j k : Fin N} (h1 : HConn D i j) (h2 : HConn D j k) :
    HConn D i k :=
  hConn_trans D h1 h2

theorem bgh_hConn_symm (D : Dissection N) {i j : Fin N} (h : HConn D i j) : HConn D j i :=
  hConn_symm D h

theorem bgh_hConn_equivalence (D : Dissection N) : Equivalence (HConn D) :=
  hConn_equivalence D

theorem bgh_hConn_of_hAdj (D : Dissection N) {i j : Fin N} (h : HAdj D i j) : HConn D i j :=
  hConn_of_hAdj D h

-- Non-vacuity: hConn_refl
example (D : Dissection N) (i : Fin N) : HConn D i i := bgh_hConn_refl D i

#print axioms bgh_hConn_equivalence
#print axioms bgh_hAdj_symm

end Erdos634.Draft.BeesonGraphHWrap

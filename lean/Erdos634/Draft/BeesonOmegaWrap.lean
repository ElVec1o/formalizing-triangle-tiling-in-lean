import Erdos634.BeesonOmega

/-!
# BeesonOmega — Beeson's Ω region: wrapper

Key results:
- `inOmega_refl`: Ω is reflexive
- `inOmega_trans`: Ω is transitive
- `omegaAdj_symm`: OmegaAdj is symmetric
- `inOmega_symm`: Ω is symmetric
- `inOmega_isTypeIOrII`: Ω members are Type I or II
- `inOmega_connected`: Ω members are mutually reachable

VERIFIED: 0 sorry, standard axioms.
-/

namespace Erdos634.Draft.BeesonOmegaWrap

open Erdos634.BeesonOmega Erdos634.Geometry Erdos634.BeesonDirections Erdos634.BeesonGraphH

variable {N : ℕ}

theorem bo_inOmega_refl {D : Dissection N} (A B C : Plane) (i₀ : Fin N) :
    InOmega D A B C i₀ i₀ :=
  inOmega_refl D A B C i₀

theorem bo_inOmega_trans {D : Dissection N} (A B C : Plane) {i₀ i j : Fin N}
    (h1 : InOmega D A B C i₀ i) (h2 : InOmega D A B C i j) : InOmega D A B C i₀ j :=
  inOmega_trans D A B C h1 h2

theorem bo_omegaAdj_symm {D : Dissection N} (A B C : Plane) {i j : Fin N}
    (h : OmegaAdj D A B C i j) : OmegaAdj D A B C j i :=
  omegaAdj_symm D A B C h

theorem bo_inOmega_symm {D : Dissection N} (A B C : Plane) {i₀ i : Fin N}
    (h : InOmega D A B C i₀ i) : InOmega D A B C i i₀ :=
  inOmega_symm D A B C h

theorem bo_inOmega_isTypeIOrII {D : Dissection N} (A B C : Plane) {i₀ i : Fin N}
    (hi₀ : IsTypeIOrII D i₀ A B C) (h : InOmega D A B C i₀ i) : IsTypeIOrII D i A B C :=
  inOmega_isTypeIOrII D A B C hi₀ h

theorem bo_inOmega_connected {D : Dissection N} (A B C : Plane) {i₀ i j : Fin N}
    (hi : InOmega D A B C i₀ i) (hj : InOmega D A B C i₀ j) :
    Relation.ReflTransGen (OmegaAdj D A B C) i j :=
  inOmega_connected D A B C hi hj

-- Non-vacuity: inOmega_refl gives reflexivity
example {D : Dissection N} (A B C : Plane) (i₀ : Fin N) :
    InOmega D A B C i₀ i₀ := bo_inOmega_refl A B C i₀

#print axioms bo_inOmega_connected
#print axioms bo_omegaAdj_symm

end Erdos634.Draft.BeesonOmegaWrap

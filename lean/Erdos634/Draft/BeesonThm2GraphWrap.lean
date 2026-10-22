import Erdos634.BeesonThm2Graph

/-!
# BeesonThm2Graph — skeleton of Beeson's Theorem 2: wrapper

Key results:
- `indeg_eq_outdeg_of_le`: degree-balance lemma — if indeg ≤ outdeg everywhere then equal
- `exists_in_link_of_out_link`: at any node with positive out-degree, an in-link exists
- `beeson_thm2_skeleton`: the traversal skeleton — two geometric obligations named as hypotheses

VERIFIED: 0 sorry, standard axioms.
-/

namespace Erdos634.Draft.BeesonThm2GraphWrap

open Erdos634.BeesonGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem btg_indeg_eq_outdeg_of_le (L : Finset (V × V)) (h : ∀ q, indeg L q ≤ outdeg L q)
    (q : V) : indeg L q = outdeg L q :=
  indeg_eq_outdeg_of_le L h q

theorem btg_exists_in_link_of_out_link (L : Finset (V × V)) (h : ∀ q, indeg L q ≤ outdeg L q)
    {q : V} (hout : 0 < outdeg L q) : ∃ p, (p, q) ∈ L :=
  exists_in_link_of_out_link L h hout

theorem btg_beeson_thm2_skeleton (L : Finset (V × V)) (E : V)
    (Γstep : ∀ q, indeg L q ≤ outdeg L q)
    (Γexists : 0 < outdeg L E)
    (Γsouth : ∀ p, (p, E) ∉ L) : False :=
  beeson_thm2_skeleton L E Γstep Γexists Γsouth

-- Non-vacuity: the self-loop witness
example : indeg ({((0 : Fin 1), (0 : Fin 1))} : Finset (Fin 1 × Fin 1)) 0 = 1 := by decide
example : ∃ p, (p, (0 : Fin 1)) ∈ ({((0 : Fin 1), (0 : Fin 1))} : Finset (Fin 1 × Fin 1)) :=
  btg_exists_in_link_of_out_link _ (by decide) (by decide)

#print axioms btg_beeson_thm2_skeleton

end Erdos634.Draft.BeesonThm2GraphWrap

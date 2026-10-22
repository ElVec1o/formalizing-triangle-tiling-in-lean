import Erdos634.BeesonDelta

/-!
# BeesonDelta — Beeson Δ traversal and strict advancement: wrapper

Key results:
- `inDelta_subset_inOmega`: Δ-reachable ⊆ Ω-reachable
- `no_cycle`: strictly advancing → no cycles
- `delta_traversal_contradiction`: Lemma 35 + maximum → contradiction
- `advancing_witness`: concrete strictly advancing example

VERIFIED: 0 sorry, standard axioms.
-/

namespace Erdos634.Draft.BeesonDeltaWrap

open Erdos634.BeesonDelta Erdos634.Geometry Erdos634.BeesonOmega

variable {V : Type*}

theorem bd_inDelta_subset_inOmega {N : ℕ} (D : Dissection N) (A B C : Plane)
    (step : Fin N → Fin N → Prop) (hstep : ∀ u v, step u v → OmegaAdj D A B C u v)
    {t₀ v : Fin N} (h : InDelta step t₀ v) : InOmega D A B C t₀ v :=
  inDelta_subset_inOmega D A B C step hstep h

theorem bd_no_cycle {φ : V → ℝ} {link : V → V → Prop}
    (h : StrictlyAdvancing φ link) (p : V)
    (hcyc : Relation.TransGen link p p) : False :=
  no_cycle φ link h p hcyc

theorem bd_delta_traversal_contradiction {φ : V → ℝ} {link : V → V → Prop}
    [Fintype V] [DecidableEq V]
    (h : StrictlyAdvancing φ link) (m : V)
    (hmax : ∀ v, φ v ≤ φ m)
    (Lemma35 : ∀ q, (∃ p, link p q) → ∃ r, link q r)
    (hin : ∃ p, link p m) : False :=
  delta_traversal_contradiction φ link h m hmax Lemma35 hin

theorem bd_advancing_witness :
    StrictlyAdvancing (fun i : Fin 2 => (i : ℝ)) (fun p q => (p : ℕ) < (q : ℕ)) :=
  advancing_witness

-- Non-vacuity: advancing_witness is a ground fact
example : StrictlyAdvancing (fun i : Fin 2 => (i : ℝ)) (fun p q => (p : ℕ) < (q : ℕ)) :=
  bd_advancing_witness

#print axioms bd_inDelta_subset_inOmega
#print axioms bd_advancing_witness

end Erdos634.Draft.BeesonDeltaWrap

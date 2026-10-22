import Mathlib
import Erdos634.Draft.BeesonRosu37c2

/-!
# Beeson-Rosu Theorem 37, gap (1), part 1: the type arithmetic at the corner tile

NOTE, UNAUDITED.  Credit: Michael Beeson and Rosu (arXiv 2607.23453 v2, Theorem 37, last paragraph), Beeson, Laczkovich.
Formalization debt, not progress on the /goal outcomes.

The corner tile `T` at a `beta` corner `A` is the last tile of the chain of each of the two sides through `A`.  Its type `t1` on one side and `t2` on
the other have the opposite side `sL = b` (it shows `beta` at `A`), and the lengths of its two sides at `A` agree: either swapped
(`len t2 = sR t1`, `len t1 = sR t2`; the printed "one of the two edges at `A` is the `a` edge") or equal (the same edge on both sides).
* `swap_has_A`: swapped => one of the types is `A1` or `A2` (an `a` letter: `cA = 1`);
* `same_eq`: equal => the same type.
-/

set_option linter.unusedVariables false

namespace Erdos634.BeesonRosu37c3

open Erdos634.Draft.W2E1 Erdos634.Draft.SideRunG

variable {e f : ℝ}

theorem swap_has_A (T : TileOK e f) {t1 t2 : Ty}
    (h1 : t1.sLG e f = f ^ 2 - e ^ 2) (h2 : t2.sLG e f = f ^ 2 - e ^ 2)
    (h3 : t2.lenG e f = t1.sRG e f) (h4 : t1.lenG e f = t2.sRG e f) :
    1 ≤ t1.cA + t2.cA := by
  have hab := T.hab
  have hac := T.ac
  have hbc := T.bc
  cases t1 <;> cases t2 <;> simp only [Ty.sLG, Ty.sRG, Ty.lenG, Ty.cA] at h1 h2 h3 h4 ⊢ <;>
    first
    | omega
    | exact absurd h1 (by assumption)
    | exact absurd h2 (by assumption)
    | (exfalso; apply hab; linarith)
    | (exfalso; apply hac; linarith)
    | (exfalso; apply hbc; linarith)
    | (exfalso; apply hab; linarith [h3, h4])
    | (exfalso; apply hac; linarith [h3, h4])
    | (exfalso; apply hbc; linarith [h3, h4])

theorem same_eq (T : TileOK e f) {t1 t2 : Ty}
    (h1 : t1.sLG e f = f ^ 2 - e ^ 2) (h2 : t2.sLG e f = f ^ 2 - e ^ 2)
    (h3 : t1.lenG e f = t2.lenG e f) : t1 = t2 := by
  have hab := T.hab
  have hac := T.ac
  have hbc := T.bc
  cases t1 <;> cases t2 <;> simp only [Ty.sLG, Ty.sRG, Ty.lenG] at h1 h2 h3 ⊢ <;>
    first
    | rfl
    | (exfalso; apply hab; linarith)
    | (exfalso; apply hac; linarith)
    | (exfalso; apply hbc; linarith)
    | (exfalso; apply hab; linarith [h3])
    | (exfalso; apply hac; linarith [h3])
    | (exfalso; apply hbc; linarith [h3])
    | (exfalso; apply hab; linarith [h1, h2])
    | (exfalso; apply hac; linarith [h1, h2])
    | (exfalso; apply hbc; linarith [h1, h2])

end Erdos634.BeesonRosu37c3

#print axioms Erdos634.BeesonRosu37c3.swap_has_A
#print axioms Erdos634.BeesonRosu37c3.same_eq

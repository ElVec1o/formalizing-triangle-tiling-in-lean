import Erdos634.Draft.LaczFormalW2Mirror
import Erdos634.Draft.LaczFormalChainDims
import Erdos634.Draft.LaczFormalWalkRules

/-!
# Rule W2 is a theorem: `W2Rule`, `U2_dims` without hypothesis, the walk windows `W2`, `W2m`

Erdős #634, band program, rule W2 (`PROOF_W2.md`).  Credit: AI assistant (item 3, band program), Beeson–Roșu (the tile, the
relation lattice, Lemma 34), Beeson, Laczkovich (fans, chord covers), Paliy, Zhang.  UNAUDITED.

* `W2Rule_holds e f : W2Rule e f` (from `w2_holds`);
* `U2_dims_free`: `U2_dims` with the hypothesis `W2Rule e f` removed;
* `walk_noW2`, `walk_noW2m`: neither `W2` nor `W2m` occurs in the word of the base walk.
-/

namespace Erdos634.LaczJunction

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.BaseBetaTargetCoord
open Erdos634.LaczJunction.Grammar

variable {N : ℕ}

theorem W2Rule_holds (e f : ℕ) : W2Rule e f := by
  intro N D α β γ p q r S he2 hf3 hL2 i1 i2 i3 hne2 hne3 P1 P2 P3 G1 G2 Z3 x3 l3 r3 hlr t1 hG1 t2 t3
  exact Walk.w2_holds S he2 hf3 hL2 hne3 hlr t1 t2 t3

#print axioms W2Rule_holds

/-- **Theorem U2 for a dissection of `T_M(e,f)` (`d ≤ 2`), without any hypothesis on rule W2.** -/
theorem U2_dims_free (D : CongruentDissection N) (e f M : ℕ) (he : 2 ≤ e) (hef : e < f)
    (hcop : Nat.Coprime e f) (hM : 1 ≤ M)
    (hsa : sideOpp D.model 0 = (ta e f : ℝ)) (hsb : sideOpp D.model 1 = (tb e f : ℝ))
    (hsc : sideOpp D.model 2 = (tc e f : ℝ))
    {p q r : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hbase : dist (D.target.pts p) (D.target.pts q) = ((M * e * (3 * f ^ 2 - e ^ 2) : ℕ) : ℝ))
    (hlegL : dist (D.target.pts p) (D.target.pts r) = ((M * f ^ 3 : ℕ) : ℝ))
    (hlegR : dist (D.target.pts q) (D.target.pts r) = ((M * f ^ 3 : ℕ) : ℝ))
    (ch : BaseChain D e f (modelAlpha (e : ℝ) f) (modelBeta (e : ℝ) f)
      (2 * modelAlpha (e : ℝ) f + modelBeta (e : ℝ) f) p q r)
    (hno : ∀ t ∈ ch.word, t.side ≠ .a)
    (hfirst : ∃ t, ch.word.head? = some t ∧ okFirst t)
    (hlast : ∃ t, ch.word.getLast? = some t ∧ okLast t)
    (hrun : HasRun f ch.word) (hcount : countC ch.word = 2 * M * e) (hf : 3 ≤ f)
    (hd : 2 * M * e ≤ f + 2) : False :=
  U2_dims D e f M he hef hcop hM (W2Rule_holds e f) hsa hsb hsc hpq hpr hqr hbase hlegL hlegR ch hno hfirst hlast
    hrun hcount hf hd

#print axioms U2_dims_free

end Erdos634.LaczJunction

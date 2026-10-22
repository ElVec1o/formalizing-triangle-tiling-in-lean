import Erdos634.Draft.LaczFormalALStage1

/-!
# The induction statements T(m), A(m) (a-lattice, Lemma A(j))

Erdős \#634, base-`β` row, thick analogue of `M(j)` (Lemma A(j)).  Credit: AI assistant (Lemma A(k) proposal), Beeson–Roșu,
Beeson, Laczkovich, Paliy.  UNAUDITED.  Axiom-clean; no `sorry`.  Port of `LaczFormalMJStage2.lean` to the exchanged frame
`AF` (`e0` of length `a` along the base, `v` of length `c` along the left leg).
-/

namespace Erdos634.LaczAL

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Walk
  Erdos634.LaczJunction.Grammar Erdos634.Draft.TraceCovering Erdos634.LaczMJ Set

variable {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}

namespace AF

variable (F : AF D e f α β γ p q r)

/-- **The down-tile rule `T(m)`** (Lemma A(j)(b), `j = m+1`): at every level `lv` (`lv + m + 1 ≤ H`, `m + 1 ≤ f - 1`)
with ground below and `m+1` up tiles `UpCell 0 … UpCell m` on level `lv` (the `aBG` run), the down tile `DownCell m lv`
(`α` at `J = (m+1, lv)`) exists. -/
def TRule (H m : ℕ) : Prop :=
  ∀ lv : ℕ, lv + m + 1 ≤ H → m + 1 ≤ f - 1 → F.Ground lv (m + 1) →
    (∀ x : ℕ, x ≤ m → F.UpCell (x : ℝ) (lv : ℝ)) → F.DownCell (m : ℝ) (lv : ℝ)

/-- **The rule `A(m)`** (Lemma A(j)(a)): no `Y` with an `a`-, `b`- or `c`-edge `[J, K]` along `Λ_lv` from
`J = (m+1, lv)`, third vertex above, presents an angle other than `β` at `J`. -/
def ARule (H m : ℕ) : Prop :=
  ∀ lv : ℕ, lv + m + 1 ≤ H → m + 1 ≤ f - 1 → F.Ground lv (m + 1) →
    (∀ x : ℕ, x ≤ m → F.UpCell (x : ℝ) (lv : ℝ)) →
    ∀ (i : Fin N) (K Z : Plane) (t : ℝ),
      TileVerts (D.tile i) (F.pt ((m : ℝ) + 1) (lv : ℝ)) K Z →
      K = F.pt ((m : ℝ) + 1) (lv : ℝ) + t • F.e0 → 0 < t →
      (dist (F.pt ((m : ℝ) + 1) (lv : ℝ)) K = (ta e f : ℝ) ∨ dist (F.pt ((m : ℝ) + 1) (lv : ℝ)) K = (tb e f : ℝ) ∨
        dist (F.pt ((m : ℝ) + 1) (lv : ℝ)) K = (tc e f : ℝ)) →
      0 < cross F.e0 (Z - F.pt ((m : ℝ) + 1) (lv : ℝ)) →
      (D.tile i).localAngle (F.pt ((m : ℝ) + 1) (lv : ℝ)) ≠ β → False

end AF

end Erdos634.LaczAL

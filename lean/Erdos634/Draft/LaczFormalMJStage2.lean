import Erdos634.Draft.LaczFormalMJStage1

/-!
# The induction statements `T(m)`, `A(m)` and the row step (rule `M(j)`)

Erdős #634, base-`β` band, rule `M(j)`.  Credit: AI assistant (item 3, band program, rule `M(j)`, Claims Z and A),
Beeson–Roșu, Beeson, Laczkovich, Paliy.  UNAUDITED.  Axiom-clean; no `sorry`.

* `TRule H m`  (the *down-tile rule*): at every level `lv` (`lv + m + 1 ≤ H`, `m + 1 ≤ e`) with ground below and
  `m+1` up tiles `UpCell 0 … UpCell m` on level `lv`, the down tile `DownCell m lv` exists.
* `ARule H m`: in the same situation no tile `Y` with a `b`- or `c`-edge `[J, K]` along `Λ_lv` from `J = (m+1, lv)`,
  third vertex above, presents an angle other than `β` at `J`.
* `adv`: **the row step**.  If rows `lv, …, lv+s-1` of the triangle are standard (`Std lv m (s-1)`), no upper edge of
  `Λ_{lv+s}` passes through `D_s`, and `T(i)`, `A(i)` hold for `i < m`, then row `lv+s` is standard.
-/

namespace Erdos634.LaczMJ

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Walk
  Erdos634.LaczJunction.Grammar Erdos634.Draft.TraceCovering Set

variable {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}

namespace LFrame

variable (F : LFrame D e f α β γ p q r)

/-- **The down-tile rule `T(m)`.** -/
def TRule (H m : ℕ) : Prop :=
  ∀ lv : ℕ, lv + m + 1 ≤ H → m + 1 ≤ e → F.Ground lv (m + 1) →
    (∀ x : ℕ, x ≤ m → F.UpCell (x : ℝ) (lv : ℝ)) → F.DownCell (m : ℝ) (lv : ℝ)

/-- **The rule `A(m)`**: no `Y` with angle `≠ β` at `J`. -/
def ARule (H m : ℕ) : Prop :=
  ∀ lv : ℕ, lv + m + 1 ≤ H → m + 1 ≤ e → F.Ground lv (m + 1) →
    (∀ x : ℕ, x ≤ m → F.UpCell (x : ℝ) (lv : ℝ)) →
    ∀ (i : Fin N) (K Z : Plane) (t : ℝ),
      TileVerts (D.tile i) (F.pt ((m : ℝ) + 1) (lv : ℝ)) K Z →
      K = F.pt ((m : ℝ) + 1) (lv : ℝ) + t • F.e0 → 0 < t →
      (dist (F.pt ((m : ℝ) + 1) (lv : ℝ)) K = (tb e f : ℝ) ∨ dist (F.pt ((m : ℝ) + 1) (lv : ℝ)) K = (tc e f : ℝ)) →
      0 < cross F.e0 (Z - F.pt ((m : ℝ) + 1) (lv : ℝ)) →
      (D.tile i).localAngle (F.pt ((m : ℝ) + 1) (lv : ℝ)) ≠ β → False

end LFrame

end Erdos634.LaczMJ

import Erdos634.Draft.LaczFormalColumnStage1

/-!
# Column Lemma, wall frame: copy of `LaczFormalMJStage2` (LFrame blocks) for `WFrame`

Credit: AI assistant (Column Lemma proposal), Beeson–Roșu, Beeson, Laczkovich, Paliy.  UNAUDITED.  Generated from the audited
module by renaming `LFrame` to `WFrame`; the leg-specific facts are replaced as documented in `LaczFormalColumnLat`.
-/

namespace Erdos634.LaczCol

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Walk
  Erdos634.LaczJunction.Grammar Erdos634.Draft.TraceCovering Erdos634.LaczMJ Erdos634.LaczWall Set

variable {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}

namespace WFrame


variable (F : WFrame D e f α β γ p q r)

/-- **The down-tile rule `T(m)`.** -/
def TRule (H m : ℕ) : Prop :=
  ∀ lv : ℕ, 1 ≤ lv → lv + m + 1 ≤ H → m + 1 ≤ e → F.Ground lv (m + 1) →
    (∀ x : ℕ, x ≤ m → F.UpCell (x : ℝ) (lv : ℝ)) → F.DownCell (m : ℝ) (lv : ℝ)

/-- **The rule `A(m)`**: no `Y` with angle `≠ β` at `J`. -/
def ARule (H m : ℕ) : Prop :=
  ∀ lv : ℕ, 1 ≤ lv → lv + m + 1 ≤ H → m + 1 ≤ e → F.Ground lv (m + 1) →
    (∀ x : ℕ, x ≤ m → F.UpCell (x : ℝ) (lv : ℝ)) →
    ∀ (i : Fin N) (K Z : Plane) (t : ℝ),
      TileVerts (D.tile i) (F.pt ((m : ℝ) + 1) (lv : ℝ)) K Z →
      K = F.pt ((m : ℝ) + 1) (lv : ℝ) + t • F.e0 → 0 < t →
      (dist (F.pt ((m : ℝ) + 1) (lv : ℝ)) K = (tb e f : ℝ) ∨ dist (F.pt ((m : ℝ) + 1) (lv : ℝ)) K = (tc e f : ℝ)) →
      0 < cross F.e0 (Z - F.pt ((m : ℝ) + 1) (lv : ℝ)) →
      (D.tile i).localAngle (F.pt ((m : ℝ) + 1) (lv : ℝ)) ≠ β → False


end WFrame

end Erdos634.LaczCol

import Erdos634.Draft.LaczFormalColumnCell

/-!
# Column Lemma, wall frame: copy of `LaczFormalMJChord` (LFrame blocks) for `WFrame`

Credit: AI assistant (Column Lemma proposal), Beeson–Roșu, Beeson, Laczkovich, Paliy.  UNAUDITED.  Generated from the audited
module by renaming `LFrame` to `WFrame`; the leg-specific facts are replaced as documented in `LaczFormalColumnLat`.
-/

namespace Erdos634.LaczCol

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Walk
  Erdos634.LaczJunction.Grammar Erdos634.Draft.TraceCovering Erdos634.LaczMJ Erdos634.LaczWall Set

variable {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}

namespace WFrame


variable {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
  (F : WFrame D e f α β γ p q r)

theorem pt_lineMap (x1 y1 x2 y2 τ : ℝ) :
    AffineMap.lineMap (F.pt x1 y1) (F.pt x2 y2) τ =
      F.pt (x1 + τ * (x2 - x1)) (y1 + τ * (y2 - y1)) := by
  rw [AffineMap.lineMap_apply]
  simp only [pt, vsub_eq_sub, vadd_eq_add]
  module

/-- A lattice point of the target: `x, y ≥ 0` and `x/λ + y/μ < 1`. -/
def LatOK (x y : ℝ) : Prop := 0 ≤ x ∧ 0 ≤ y ∧ x / F.lam + y / F.mu < 1

/-- Open chords between `LatOK` lattice points lie in the interior of the target. -/
theorem chord_interior {x1 y1 x2 y2 : ℝ} (h1 : F.LatOK x1 y1) (h2 : F.LatOK x2 y2)
    (hx : 0 < x1 + x2) (hy : 0 < y1 + y2) :
    ∀ t : ℝ, 0 < t → t < 1 →
      AffineMap.lineMap (F.pt x1 y1) (F.pt x2 y2) t ∈ interior D.target.carrier := by
  intro t ht0 ht1
  rw [F.pt_lineMap]
  obtain ⟨a1, b1, c1⟩ := h1
  obtain ⟨a2, b2, c2⟩ := h2
  have hl := F.hlam
  have hm := F.hmu
  refine F.pt_interior ?_ ?_ ?_
  · exact pos_comb a1 a2 hx ht0 ht1
  · exact pos_comb b1 b2 hy ht0 ht1
  · have e1 : (x1 + t * (x2 - x1)) / F.lam + (y1 + t * (y2 - y1)) / F.mu =
        (1 - t) * (x1 / F.lam + y1 / F.mu) + t * (x2 / F.lam + y2 / F.mu) := by
      field_simp; ring
    rw [e1]
    nlinarith


end WFrame

end Erdos634.LaczCol

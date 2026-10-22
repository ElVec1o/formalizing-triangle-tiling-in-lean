import Erdos634.Draft.LaczFormalAllColumn
import Erdos634.Draft.SideRunGArith

/-!
# Lemma A(j) (thick analogue of M(j)): the exchanged frame, the exact statement, the arithmetic, the threshold control

Erdős #634, base-`β` row.  Credit: AI assistant (Lemma A(k) proposal), Beeson–Roșu, Beeson, Laczkovich, Paliy; hand proof
(private working notes, not included).  UNAUDITED.  Axiom-clean; no `sorry`.

PROVED here (unconditional): the cell angles of the exchanged frame (`AFrame`: `|e0| = a` along the base, `|v| = c` along the
leg, `|v − e0| = b`; `aBG` cells `UpA`: `β` at `(x,y)`, `γ` at `(x+1,y)`, `α` at `(x,y+1)`; `DownA`: `α` at `(x+1,y)`,
`γ` at `(x,y+1)`, `β` at `(x+1,y+1)`); the arithmetic (Aa), (A1), (A2) in the form used by the proof; the threshold control
(`A_threshold_fails_at_f`: `f b = (f−e)(a+c)`, so the induction's last step breaks at `j = f`).
STATED, NOT PROVED: `ALemma` (the exact Lean statement of Lemma A(j), (a) and (b)); its proof (Steps A–D of the hand proof:
the row induction on the line `l`, the walk bridge with the tokens `aBG`, `aGB`) is NOT in Lean.
-/

namespace Erdos634.LaczCol

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Walk Erdos634.LaczMJ

variable {N : ℕ}

/-- The exchanged lattice frame (`a` along the base, `c` along the leg). -/
structure AFrame (D : CongruentDissection N) (e f : ℕ) (α β γ : ℝ) (p q r : Fin 3) where
  S : BandSetup D e f α β γ p q r
  O : Plane
  e0 : Plane
  v : Plane
  he0 : ‖e0‖ = (ta e f : ℝ)
  hv : ‖v‖ = (tc e f : ℝ)
  hu : ‖v - e0‖ = (tb e f : ℝ)
  hcr : 0 < cross e0 v

namespace AFrame

variable {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3} (F : AFrame D e f α β γ p q r)

def pt (x y : ℝ) : Plane := F.O + x • F.e0 + y • F.v

theorem dist_pt_a (x y : ℝ) : dist (F.pt x y) (F.pt (x + 1) y) = (ta e f : ℝ) := by
  have : dist (F.pt x y) (F.pt (x + 1) y) = ‖(-1 : ℝ) • F.e0‖ := by
    rw [dist_eq_norm]; congr 1; simp only [pt]; module
  rw [this, norm_smul, F.he0]; simp

theorem dist_pt_c (x y : ℝ) : dist (F.pt x y) (F.pt x (y + 1)) = (tc e f : ℝ) := by
  have : dist (F.pt x y) (F.pt x (y + 1)) = ‖(-1 : ℝ) • F.v‖ := by
    rw [dist_eq_norm]; congr 1; simp only [pt]; module
  rw [this, norm_smul, F.hv]; simp

theorem dist_pt_b (x y : ℝ) : dist (F.pt (x + 1) y) (F.pt x (y + 1)) = (tb e f : ℝ) := by
  have : dist (F.pt (x + 1) y) (F.pt x (y + 1)) = ‖-(F.v - F.e0)‖ := by
    rw [dist_eq_norm]; congr 1; simp only [pt]; module
  rw [this, norm_neg, F.hu]

/-- The `aBG` cell: `β` at `(x,y)`, `γ` at `(x+1,y)`, `α` at `(x,y+1)`. -/
def UpA (x y : ℝ) : Prop := ∃ i : Fin N, TileVerts (D.tile i) (F.pt x y) (F.pt (x + 1) y) (F.pt x (y + 1))

/-- The down cell: `α` at `(x+1,y)`, `γ` at `(x,y+1)`, `β` at `(x+1,y+1)`. -/
def DownA (x y : ℝ) : Prop :=
  ∃ i : Fin N, TileVerts (D.tile i) (F.pt (x + 1) y) (F.pt x (y + 1)) (F.pt (x + 1) (y + 1))

theorem upA_angles {x y : ℝ} {i : Fin N}
    (hv : TileVerts (D.tile i) (F.pt x y) (F.pt (x + 1) y) (F.pt x (y + 1))) :
    (D.tile i).localAngle (F.pt x y) = β ∧ (D.tile i).localAngle (F.pt (x + 1) y) = γ ∧
      (D.tile i).localAngle (F.pt x (y + 1)) = α := by
  refine ⟨(LFrame.tileVerts_angle F.S hv).2.1 (F.dist_pt_b x y), ?_, ?_⟩
  · exact (LFrame.tileVerts_angle F.S hv.rot).2.2 (by rw [dist_comm]; exact F.dist_pt_c x y)
  · exact (LFrame.tileVerts_angle F.S hv.rot.rot).1 (F.dist_pt_a x y)

theorem downA_angles {x y : ℝ} {i : Fin N}
    (hv : TileVerts (D.tile i) (F.pt (x + 1) y) (F.pt x (y + 1)) (F.pt (x + 1) (y + 1))) :
    (D.tile i).localAngle (F.pt (x + 1) y) = α ∧ (D.tile i).localAngle (F.pt x (y + 1)) = γ ∧
      (D.tile i).localAngle (F.pt (x + 1) (y + 1)) = β := by
  refine ⟨?_, ?_, ?_⟩
  · exact (LFrame.tileVerts_angle F.S hv).1 (F.dist_pt_a x (y + 1))
  · exact (LFrame.tileVerts_angle F.S hv.rot).2.2 (by
      have := F.dist_pt_c (x + 1) y; rw [dist_comm] at this; simpa using this)
  · exact (LFrame.tileVerts_angle F.S hv.rot.rot).2.1 (F.dist_pt_b x y)

/-- **Lemma A(j), exact statement (NOT proved here).**  `j ≤ f − 1`; the wall frame `W` with the exchanged lattice `F`
(same origin and leg line: `F.O = W.O`, `F.v ∥ W.v`) is the hypothesis package; the run is the `j` cells `UpA 0 .. UpA (j-1)`
on the level `lv` over standard ground; `Y` is a tile with a vertex `J = pt j lv` and an edge `[J,K]` along the line to the right
(`K = J + t e0`, length `a`, `b` or `c`) with third vertex above.  (a) `Y` does not have angle `α` or `γ` at `J`; (b) the tile
in the `α`-wedge at `J` is the standard down cell: `DownA (j-1) lv`.  H4 (the chord triangle `L J D_j` lies in the target and the
far cover ends at `D_j` on the leg) is the explicit hypothesis `hH4`. -/
def ALemma (F : AFrame D e f α β γ p q r) (hH4 : Prop) (j lv : ℕ) : Prop :=
  hH4 → 1 ≤ j → j ≤ f - 1 →
    (∀ x : ℕ, x < j → F.UpA (x : ℝ) (lv : ℝ)) →
    (∀ (i : Fin N) (K Z : Plane) (t : ℝ), TileVerts (D.tile i) (F.pt (j : ℝ) (lv : ℝ)) K Z →
      K = F.pt (j : ℝ) (lv : ℝ) + t • F.e0 → 0 < t →
      (dist (F.pt (j : ℝ) (lv : ℝ)) K = (ta e f : ℝ) ∨ dist (F.pt (j : ℝ) (lv : ℝ)) K = (tb e f : ℝ) ∨
        dist (F.pt (j : ℝ) (lv : ℝ)) K = (tc e f : ℝ)) →
      0 < cross F.e0 (Z - F.pt (j : ℝ) (lv : ℝ)) →
      (D.tile i).localAngle (F.pt (j : ℝ) (lv : ℝ)) = β) ∧
    F.DownA ((j : ℝ) - 1) (lv : ℝ)

end AFrame

/-- **(A2)** for `1 ≤ r ≤ f − 1`: `r b − a` and `r b − c` are not sums of sides. -/
theorem A2_not_sum (e f x y z r : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) (hr1 : 1 ≤ r) (hr : r ≤ f - 1) :
    x * ta e f + y * tb e f + z * tc e f + ta e f ≠ r * tb e f ∧
    x * ta e f + y * tb e f + z * tc e f + tc e f ≠ r * tb e f := by
  unfold ta tb tc
  constructor <;> intro h
  · obtain ⟨h1, -, -⟩ := Erdos634.Draft.SideRunGArith.A1 he hef hco hr1 hr (x := x + 1) (y := y) (z := z)
      (by rw [add_mul, one_mul]; linarith)
    omega
  · obtain ⟨-, -, h3⟩ := Erdos634.Draft.SideRunGArith.A1 he hef hco hr1 hr (x := x) (y := y) (z := z + 1)
      (by rw [add_mul, one_mul]; linarith)
    omega

/-- **Negative control at `j = f`**: `f b = (f−e)(a+c)` is a second cover of `f b`, so (A1) (and (A2), the vertex exclusion of
Step B) fail at `r = f`. -/
theorem A_threshold_fails_at_f (e f : ℕ) (he : 1 ≤ e) (hef : e < f) :
    f * tb e f = (f - e) * ta e f + (f - e) * tc e f ∧
    ¬ (∀ x y z : ℕ, x * ta e f + y * tb e f + z * tc e f = f * tb e f → x = 0 ∧ y = f ∧ z = 0) :=
  ⟨LaczColumn.chord_second_cover e f hef, LaczColumn.chord_cover_fails_at_f e f he hef⟩

end Erdos634.LaczCol

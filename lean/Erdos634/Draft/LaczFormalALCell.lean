import Erdos634.Draft.LaczFormalALLat

/-!
# Standard cells of the exchanged (a-)lattice frame and their angles (Lemma A(j), general `j`)

Erdős #634, base-`β` row, thick analogue of `M(j)`.  Credit: AI assistant (Lemma A(k) proposal), Beeson–Roșu, Beeson,
Laczkovich, Paliy.  UNAUDITED.  Axiom-clean; no `sorry`.  Port of `LaczFormalMJCell` with `e0` of length `a` (along
the base) and `v` of length `c` (along the left leg).

`UpCell x y`: `β` at `(x,y)`, `γ` at `(x+1,y)`, `α` at `(x,y+1)` (the `aBG` cell); `DownCell x y`: `α` at `(x+1,y)`,
`γ` at `(x,y+1)`, `β` at `(x+1,y+1)`.
-/

namespace Erdos634.LaczAL

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Walk
  Erdos634.LaczJunction.Grammar Erdos634.LaczMJ

variable {N : ℕ}

namespace AF

variable {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
  (F : AF D e f α β γ p q r)

theorem dist_pt (x y x' y' : ℝ) :
    dist (F.pt x y) (F.pt x' y') = ‖(x - x') • F.e0 + (y - y') • F.v‖ := by
  rw [dist_eq_norm]; congr 1; simp only [pt]; module

theorem dist_pt_a (x y : ℝ) : dist (F.pt x y) (F.pt (x + 1) y) = (ta e f : ℝ) := by
  rw [F.dist_pt]
  have : (x - (x + 1)) • F.e0 + (y - y) • F.v = (-1 : ℝ) • F.e0 := by module
  rw [this, norm_smul, F.he0]; simp

theorem dist_pt_c (x y : ℝ) : dist (F.pt x y) (F.pt x (y + 1)) = (tc e f : ℝ) := by
  rw [F.dist_pt]
  have : (x - x) • F.e0 + (y - (y + 1)) • F.v = (-1 : ℝ) • F.v := by module
  rw [this, norm_smul, F.hv]; simp

theorem dist_pt_b (x y : ℝ) : dist (F.pt (x + 1) y) (F.pt x (y + 1)) = (tb e f : ℝ) := by
  rw [F.dist_pt]
  have : (x + 1 - x) • F.e0 + (y - (y + 1)) • F.v = -(F.v - F.e0) := by module
  rw [this, norm_neg, F.hu]

/-- A tile with the three vertices of the up cell. -/
def UpCell (x y : ℝ) : Prop := ∃ i : Fin N, TileVerts (D.tile i) (F.pt x y) (F.pt (x + 1) y) (F.pt x (y + 1))

def DownCell (x y : ℝ) : Prop :=
  ∃ i : Fin N, TileVerts (D.tile i) (F.pt (x + 1) y) (F.pt x (y + 1)) (F.pt (x + 1) (y + 1))

theorem up_angles {x y : ℝ} {i : Fin N}
    (hv : TileVerts (D.tile i) (F.pt x y) (F.pt (x + 1) y) (F.pt x (y + 1))) :
    (D.tile i).localAngle (F.pt x y) = β ∧ (D.tile i).localAngle (F.pt (x + 1) y) = γ ∧
      (D.tile i).localAngle (F.pt x (y + 1)) = α := by
  refine ⟨(LFrame.tileVerts_angle F.S hv).2.1 (F.dist_pt_b x y), ?_, ?_⟩
  · exact (LFrame.tileVerts_angle F.S hv.rot).2.2 (by rw [dist_comm]; exact F.dist_pt_c x y)
  · exact (LFrame.tileVerts_angle F.S hv.rot.rot).1 (F.dist_pt_a x y)

theorem down_angles {x y : ℝ} {i : Fin N}
    (hv : TileVerts (D.tile i) (F.pt (x + 1) y) (F.pt x (y + 1)) (F.pt (x + 1) (y + 1))) :
    (D.tile i).localAngle (F.pt (x + 1) y) = α ∧ (D.tile i).localAngle (F.pt x (y + 1)) = γ ∧
      (D.tile i).localAngle (F.pt (x + 1) (y + 1)) = β := by
  refine ⟨?_, ?_, ?_⟩
  · exact (LFrame.tileVerts_angle F.S hv).1 (F.dist_pt_a x (y + 1))
  · exact (LFrame.tileVerts_angle F.S hv.rot).2.2 (by
      have := F.dist_pt_c (x + 1) y; rw [dist_comm] at this; simpa using this)
  · exact (LFrame.tileVerts_angle F.S hv.rot.rot).2.1 (F.dist_pt_b x y)

end AF

end Erdos634.LaczAL

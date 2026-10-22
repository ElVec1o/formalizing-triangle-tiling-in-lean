import Erdos634.Draft.LaczFormalColumnLat

/-!
# Column Lemma, wall frame: copy of `LaczFormalMJCell` (LFrame blocks) for `WFrame`

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

theorem dist_pt (x y x' y' : ℝ) :
    dist (F.pt x y) (F.pt x' y') = ‖(x - x') • F.e0 + (y - y') • F.v‖ := by
  rw [dist_eq_norm]; congr 1; simp only [pt]; module

theorem dist_pt_c (x y : ℝ) : dist (F.pt x y) (F.pt (x + 1) y) = (tc e f : ℝ) := by
  rw [F.dist_pt]
  have : (x - (x + 1)) • F.e0 + (y - y) • F.v = (-1 : ℝ) • F.e0 := by module
  rw [this, norm_smul, F.he0]; simp

theorem dist_pt_a (x y : ℝ) : dist (F.pt x y) (F.pt x (y + 1)) = (ta e f : ℝ) := by
  rw [F.dist_pt]
  have : (x - x) • F.e0 + (y - (y + 1)) • F.v = (-1 : ℝ) • F.v := by module
  rw [this, norm_smul, F.hv]; simp

theorem dist_pt_b (x y : ℝ) : dist (F.pt (x + 1) y) (F.pt x (y + 1)) = (tb e f : ℝ) := by
  rw [F.dist_pt]
  have : (x + 1 - x) • F.e0 + (y - (y + 1)) • F.v = -(F.v - F.e0) := by module
  rw [this, norm_neg, F.hu]

/-- The three corner angles of a tile at its vertices `A, B, C`, from the opposite sides. -/
theorem tileVerts_angle (S : BandSetup D e f α β γ p q r) {i : Fin N} {A B C : Plane}
    (hv : TileVerts (D.tile i) A B C) :
    ((dist B C = (ta e f : ℝ) → (D.tile i).localAngle A = α) ∧
      (dist B C = (tb e f : ℝ) → (D.tile i).localAngle A = β) ∧
      (dist B C = (tc e f : ℝ) → (D.tile i).localAngle A = γ)) := by
  obtain ⟨hαβ, hβγ, hαγ, hab, hbc, hac⟩ := BandSetup.distinct S
  have F3 : ∀ j : Fin 3, j ≠ j + 1 ∧ j ≠ j + 2 ∧ j + 1 ≠ j + 2 := by decide
  obtain ⟨j, ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩⟩ := hv
  · have := angle_of_opp D α β γ S.hα' S.hβ' S.hγ' hab hbc hac i j (j + 1) (j + 2)
      (F3 j).1 (F3 j).2.1 (F3 j).2.2
    rw [h1, h2, h3, S.hsa, S.hsb, S.hsc] at this
    exact this
  · have := angle_of_opp D α β γ S.hα' S.hβ' S.hγ' hab hbc hac i j (j + 2) (j + 1)
      (F3 j).2.1 (F3 j).1 (F3 j).2.2.symm
    rw [h1, h2, h3, S.hsa, S.hsb, S.hsc] at this
    exact this

/-- A tile with three given vertices, at the lattice cells. -/
def UpCell (x y : ℝ) : Prop := ∃ i : Fin N, TileVerts (D.tile i) (F.pt x y) (F.pt (x + 1) y) (F.pt x (y + 1))

def DownCell (x y : ℝ) : Prop :=
  ∃ i : Fin N, TileVerts (D.tile i) (F.pt (x + 1) y) (F.pt x (y + 1)) (F.pt (x + 1) (y + 1))

theorem up_angles {x y : ℝ} {i : Fin N}
    (hv : TileVerts (D.tile i) (F.pt x y) (F.pt (x + 1) y) (F.pt x (y + 1))) :
    (D.tile i).localAngle (F.pt x y) = β ∧ (D.tile i).localAngle (F.pt (x + 1) y) = α ∧
      (D.tile i).localAngle (F.pt x (y + 1)) = γ := by
  refine ⟨(tileVerts_angle F.S hv).2.1 (F.dist_pt_b x y), ?_, ?_⟩
  · exact (tileVerts_angle F.S hv.rot).1 (by rw [dist_comm]; exact F.dist_pt_a x y)
  · exact (tileVerts_angle F.S hv.rot.rot).2.2 (F.dist_pt_c x y)

theorem down_angles {x y : ℝ} {i : Fin N}
    (hv : TileVerts (D.tile i) (F.pt (x + 1) y) (F.pt x (y + 1)) (F.pt (x + 1) (y + 1))) :
    (D.tile i).localAngle (F.pt (x + 1) y) = γ ∧ (D.tile i).localAngle (F.pt x (y + 1)) = α ∧
      (D.tile i).localAngle (F.pt (x + 1) (y + 1)) = β := by
  refine ⟨(tileVerts_angle F.S hv).2.2 (F.dist_pt_c x (y + 1)), ?_, ?_⟩
  · exact (tileVerts_angle F.S hv.rot).1 (by rw [dist_comm]; exact F.dist_pt_a (x + 1) y)
  · exact (tileVerts_angle F.S hv.rot.rot).2.1 (F.dist_pt_b x y)


end WFrame

end Erdos634.LaczCol

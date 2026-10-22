-- Draft/LaczFormalRGWalk.lean -- S3 of PLAN_THM21: walks of tiles along a line for a dissection of a REGION (port of the D-dependent generic part of
-- LaczFormalGraphWalk: `WalkT`, its progress/length lemmas, uniqueness of the fan sectors starting/ending along a line).
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 4), Beeson, Beeson-Zhang; port of the project's LaczFormalGraphWalk.
import Erdos634.Draft.LaczFormalRGExt

open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

/-- A chain of left steps along `d`, recorded as triples `(tile, tail, head)`. -/
inductive WalkT (D : RegionDissection N) (d : V2) : Plane → Plane → List (Fin N × Plane × Plane) → Prop
  | nil (X : Plane) : WalkT D d X X []
  | cons {i : Fin N} {X X' Y : Plane} {L : List (Fin N × Plane × Plane)} :
      TriStep (D.tile i) d X X' → WalkT D d X' Y L → WalkT D d X Y ((i, X, X') :: L)

theorem walkT_progress {D : RegionDissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkT D d X Y L) : ∃ T : ℝ, 0 ≤ T ∧ toV2 (Y - X) = (T * d.1, T * d.2) ∧ (L ≠ [] → 0 < T) := by
  induction W with
  | nil X => exact ⟨0, le_rfl, by unfold toV2; ext <;> simp, fun h => absurd rfl h⟩
  | @cons i X X' Y L hS W ih =>
    obtain ⟨-, -, -, -, -, -, -, -, hpar, -⟩ := hS
    obtain ⟨c, hc, hcw⟩ := hpar.smul
    obtain ⟨T, hT, hTe, -⟩ := ih
    refine ⟨c + T, by positivity, ?_, fun _ => by positivity⟩
    have : toV2 (Y - X) = ((toV2 (Y - X')).1 + (toV2 (X' - X)).1, (toV2 (Y - X')).2 + (toV2 (X' - X)).2) := by
      unfold toV2; ext <;> simp
    rw [this, hTe, hcw]
    ext <;> simp <;> ring

theorem walkT_dist_sum {D : RegionDissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkT D d X Y L) : (L.map fun e => dist e.2.1 e.2.2).sum = dist X Y := by
  induction W with
  | nil X => simp
  | @cons i X X' Y L hS W ih =>
    obtain ⟨-, -, -, -, -, -, -, -, hpar, -⟩ := id hS
    obtain ⟨c, hc, hcw⟩ := hpar.smul
    obtain ⟨T, hT, hTe, -⟩ := walkT_progress W
    have hXY : toV2 (Y - X) = ((c + T) * d.1, (c + T) * d.2) := by
      have : toV2 (Y - X) = ((toV2 (Y - X')).1 + (toV2 (X' - X)).1, (toV2 (Y - X')).2 + (toV2 (X' - X)).2) := by
        unfold toV2; ext <;> simp
      rw [this, hTe, hcw]; ext <;> simp <;> ring
    have d1 := dist_of_toV2 hc.le hcw
    have d2 := dist_of_toV2 hT hTe
    have d3 := dist_of_toV2 (by positivity : 0 ≤ c + T) hXY
    simp only [List.map_cons, List.sum_cons]
    rw [ih, dist_comm X X', d1, dist_comm X' Y, d2, dist_comm X Y, d3]
    ring

theorem walkT_mem_step {D : RegionDissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkT D d X Y L) : ∀ e ∈ L, TriStep (D.tile e.1) d e.2.1 e.2.2 := by
  induction W with
  | nil X => intro e he; exact absurd he (by simp)
  | @cons i X X' Y L hS W ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | h
    · exact hS
    · exact ih e h

/-- The type pair of a tile on a side `U -> U'`: types at the tail and at the head. -/
def PairIs (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (i : Fin N) (U U' : Plane) (ℓ : Fin 3 × Fin 3) : Prop :=
  ∀ k k', (D.tile i).pts k = U → (D.tile i).pts k' = U' → (idx i k, idx i k') = ℓ

end Erdos634.Draft.LaczFormal.RG

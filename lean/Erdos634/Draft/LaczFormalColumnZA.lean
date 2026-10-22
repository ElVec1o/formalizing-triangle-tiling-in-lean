import Erdos634.Draft.LaczFormalColumnZ

/-!
# Column Lemma, wall frame: copy of `LaczFormalMJZA` (LFrame blocks) for `WFrame`

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

/-- The up tile `N_{s'+1}` with top vertex `D_{s'+1}`: `γ` there, a vertex on the near side of `l`. -/
theorem stage_N {m lv s' : ℕ} (hStd : F.Std lv m s') (hs' : s' + 1 ≤ m + 1) :
    ∃ (iN : Fin N) (A B : Plane), TileVerts (D.tile iN) A B (F.pt ((m : ℝ) + 1 - ((s' : ℝ) + 1)) ((lv : ℝ) + ((s' : ℝ) + 1))) ∧
      B = F.pt ((m : ℝ) + 1 - (s' : ℝ)) ((lv : ℝ) + (s' : ℝ)) ∧
      (D.tile iN).localAngle (F.pt ((m : ℝ) + 1 - ((s' : ℝ) + 1)) ((lv : ℝ) + ((s' : ℝ) + 1))) = γ ∧
      cross (F.v - F.e0) (F.pt ((m : ℝ) + 1) (lv : ℝ)) < cross (F.v - F.e0) A ∧
      F.Below ((lv : ℝ) + ((s' : ℝ) + 1)) iN := by
  obtain ⟨hU, -⟩ := hStd s' le_rfl
  obtain ⟨iN, hiN⟩ := hU (m - s') (by omega)
  have hx : ((m - s' : ℕ) : ℝ) = (m : ℝ) - s' := by rw [Nat.cast_sub (by omega)]
  rw [hx] at hiN
  have hang := (F.up_angles hiN).2.2
  have hbel : F.Below ((lv : ℝ) + ((s' : ℝ) + 1)) iN :=
    F.below_of_verts hiN (by rw [F.ht_pt]; linarith) (by rw [F.ht_pt]; linarith) (by rw [F.ht_pt]; linarith)
  have pA : F.pt ((m : ℝ) - s') ((lv : ℝ) + s') =
      F.pt ((m : ℝ) + 1 - ((s' : ℝ) + 1)) ((lv : ℝ) + s') := by congr 1; ring
  have pB : F.pt ((m : ℝ) - s' + 1) ((lv : ℝ) + s') = F.pt ((m : ℝ) + 1 - (s' : ℝ)) ((lv : ℝ) + (s' : ℝ)) := by
    congr 1; ring
  have pC : F.pt ((m : ℝ) - s') ((lv : ℝ) + s' + 1) =
      F.pt ((m : ℝ) + 1 - ((s' : ℝ) + 1)) ((lv : ℝ) + ((s' : ℝ) + 1)) := by congr 1 <;> ring
  rw [pA, pB, pC] at hiN
  rw [pC] at hang
  refine ⟨iN, _, _, hiN, rfl, hang, ?_, ?_⟩
  · have e1 : F.pt ((m : ℝ) + 1 - ((s' : ℝ) + 1)) ((lv : ℝ) + s') - F.pt ((m : ℝ) + 1) (lv : ℝ) =
        (s' : ℝ) • (F.v - F.e0) - F.e0 := by
      rw [F.pt_sub]; module
    have : cross (F.v - F.e0) (F.pt ((m : ℝ) + 1 - ((s' : ℝ) + 1)) ((lv : ℝ) + s')) -
        cross (F.v - F.e0) (F.pt ((m : ℝ) + 1) (lv : ℝ)) = cross F.e0 F.v := by
      rw [← cross_sub_right, e1, cross_sub_right, cross_smul_right, Erdos634.Geometry.cross_self]
      simp only [cross, PiLp.sub_apply]; ring
    linarith [F.hcr]
  · exact hbel

/-- The down tile with top-right vertex `D_{s'+1}`: `β` there. -/
theorem stage_D {m lv s' : ℕ} (hStd : F.Std lv m s') (hs : s' + 1 ≤ m) :
    ∃ iD : Fin N, (D.tile iD).localAngle (F.pt ((m : ℝ) + 1 - ((s' : ℝ) + 1)) ((lv : ℝ) + ((s' : ℝ) + 1))) = β ∧
      F.Below ((lv : ℝ) + ((s' : ℝ) + 1)) iD := by
  obtain ⟨-, hD⟩ := hStd s' le_rfl
  obtain ⟨iD, hiD⟩ := hD (m - s' - 1) (by omega)
  have hx : ((m - s' - 1 : ℕ) : ℝ) = (m : ℝ) - s' - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  rw [hx] at hiD
  have hang := (F.down_angles hiD).2.2
  have hbel : F.Below ((lv : ℝ) + ((s' : ℝ) + 1)) iD :=
    F.below_of_verts hiD (by rw [F.ht_pt]; linarith) (by rw [F.ht_pt]; linarith) (by rw [F.ht_pt]; linarith)
  have pC : F.pt ((m : ℝ) - s' - 1 + 1) ((lv : ℝ) + s' + 1) =
      F.pt ((m : ℝ) + 1 - ((s' : ℝ) + 1)) ((lv : ℝ) + ((s' : ℝ) + 1)) := by congr 1 <;> ring
  rw [pC] at hang
  exact ⟨iD, hang, hbel⟩


end WFrame

end Erdos634.LaczCol

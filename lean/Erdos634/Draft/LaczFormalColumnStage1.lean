import Erdos634.Draft.LaczFormalColumnRow

/-!
# Column Lemma, wall frame: copy of `LaczFormalMJStage1` (LFrame blocks) for `WFrame`

Credit: AI assistant (Column Lemma proposal), Beeson–Roșu, Beeson, Laczkovich, Paliy.  UNAUDITED.  Generated from the audited
module by renaming `LFrame` to `WFrame`; the leg-specific facts are replaced as documented in `LaczFormalColumnLat`.
-/

namespace Erdos634.LaczCol

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Walk
  Erdos634.LaczJunction.Grammar Erdos634.Draft.TraceCovering Erdos634.LaczMJ Erdos634.LaczWall Set

variable {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}

namespace WFrame


variable (F : WFrame D e f α β γ p q r)

/-- Vertices of tiles of the far (upper) chain of `Λ_ρ` have height `≥ ρ`. -/
theorem chainH_ht {ρ : ℝ} {i : Fin N}
    (h : ∀ j, (crossL (-F.e0) : Plane →ₗ[ℝ] ℝ) ((D.tile i).pts j) ≤ cross (-F.e0) (F.pt 0 ρ)) :
    ∀ j, ρ ≤ F.ht ((D.tile i).pts j) := by
  intro j
  have h1 := h j
  simp only [crossL_apply] at h1
  have e1 : cross (-F.e0) ((D.tile i).pts j) - cross (-F.e0) (F.pt 0 ρ) = - cross F.e0 ((D.tile i).pts j - F.pt 0 ρ) := by
    simp only [cross, PiLp.sub_apply, PiLp.neg_apply]; ring
  have e2 : F.ht ((D.tile i).pts j) - ρ = cross F.e0 ((D.tile i).pts j - F.pt 0 ρ) / cross F.e0 F.v := by
    have := F.ht_sub ((D.tile i).pts j) (F.pt 0 ρ)
    rwa [F.ht_pt] at this
  have h3 : 0 ≤ cross F.e0 ((D.tile i).pts j - F.pt 0 ρ) := by linarith
  have : 0 ≤ F.ht ((D.tile i).pts j) - ρ := by rw [e2]; exact div_nonneg h3 F.hcr.le
  linarith

/-- The third vertex of a tile with the lattice edge `[(x,ρ),(x+1,ρ)]`, all of whose vertices have height `≥ ρ`,
is strictly above `Λ_ρ`. -/
theorem third_above {i : Fin N} {x ρ : ℝ} {Z : Plane}
    (hv : TileVerts (D.tile i) (F.pt x ρ) (F.pt (x + 1) ρ) Z)
    (hge : ∀ j, ρ ≤ F.ht ((D.tile i).pts j)) : 0 < cross F.e0 (Z - F.pt x ρ) := by
  have F3 : ∀ j : Fin 3, j ≠ j + 1 ∧ j ≠ j + 2 ∧ j + 1 ≠ j + 2 := by decide
  have e1 : F.pt (x + 1) ρ - F.pt x ρ = F.e0 := by rw [F.pt_sub]; module
  have e2 : F.ht Z - ρ = cross F.e0 (Z - F.pt x ρ) / cross F.e0 F.v := by
    have := F.ht_sub Z (F.pt x ρ)
    rwa [F.ht_pt] at this
  have key : cross F.e0 (Z - F.pt x ρ) ≠ 0 → 0 ≤ F.ht Z - ρ → 0 < cross F.e0 (Z - F.pt x ρ) := by
    intro hne hz
    rw [e2] at hz
    have : 0 ≤ cross F.e0 (Z - F.pt x ρ) :=
      (div_nonneg_iff.mp hz).elim (fun h => h.1) (fun h => absurd h.2 (not_le.mpr F.hcr))
    exact lt_of_le_of_ne this (Ne.symm hne)
  obtain ⟨j, ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩⟩ := hv
  · have hne := tile_cross_ne (D.tile i) j (j + 1) (j + 2) (F3 j).1 (F3 j).2.1 (F3 j).2.2
    rw [h1, h2, h3, e1] at hne
    have hz := hge (j + 2)
    rw [h3] at hz
    exact key hne (by linarith)
  · have hne := tile_cross_ne (D.tile i) j (j + 2) (j + 1) (F3 j).2.1 (F3 j).1 (F3 j).2.2.symm
    rw [h1, h3, h2, e1] at hne
    have hz := hge (j + 1)
    rw [h2] at hz
    exact key hne (by linarith)

/-- The two tiles below the wall point `(0, ρ+1)` present `γ` and `α` and are side tiles. -/
theorem ground_leg_side {ρ k : ℕ} (hG : F.Ground (ρ + 1) k) (hy : ((ρ : ℝ) + 1) < F.mu) :
    ∃ iγ iα : Fin N, (D.tile iγ).localAngle (F.pt 0 ((ρ : ℝ) + 1)) = γ ∧
      (D.tile iα).localAngle (F.pt 0 ((ρ : ℝ) + 1)) = α ∧
      F.Below (ρ + 1 : ℕ) iγ ∧ F.Below (ρ + 1 : ℕ) iα ∧
      iγ ∈ Side D.toDissection F.wg F.wc ∧ iα ∈ Side D.toDissection F.wg F.wc := by
  have h0 : (0 : ℝ) < (ρ : ℝ) + 1 := by positivity
  rcases hG with h | ⟨ρ', hρ, h⟩
  · omega
  · have hρ' : ρ' = ρ := by omega
    subst hρ'
    obtain ⟨hu, hd⟩ := h 0 (Nat.zero_le _)
    obtain ⟨iu, hiu, hbu⟩ := F.up_below hu
    obtain ⟨id1, hid1, hbd1⟩ := F.down_below hd
    refine ⟨iu, id1, ?_, ?_, by simpa using hbu, by simpa using hbd1, ?_, ?_⟩
    · have := (F.up_angles hiu).2.2
      simpa using this
    · have := (F.down_angles hid1).2.1
      simpa using this
    · refine F.tile_mem_Side h0 hy (x' := 1) (y' := (ρ' : ℝ)) one_pos ?_ ?_
      · simpa using hiu.vertex_C
      · simpa using hiu.vertex_B
    · refine F.tile_mem_Side h0 hy (x' := 1) (y' := (ρ' : ℝ)) one_pos ?_ ?_
      · simpa using hid1.vertex_B
      · simpa using hid1.vertex_A

/-- **The figure at a wall point above the ground**: exactly one side tile each presents `α`, `β`, `γ`, none `π`. -/
theorem leg_fig {ρ k : ℕ} (hG : F.Ground (ρ + 1) k) (hmu : ((ρ : ℝ) + 1) < F.mu) :
    scnt D.toDissection F.wg F.wc (F.pt 0 ((ρ : ℝ) + 1)) α = 1 ∧
      scnt D.toDissection F.wg F.wc (F.pt 0 ((ρ : ℝ) + 1)) β = 1 ∧
      scnt D.toDissection F.wg F.wc (F.pt 0 ((ρ : ℝ) + 1)) γ = 1 ∧
      scnt D.toDissection F.wg F.wc (F.pt 0 ((ρ : ℝ) + 1)) Real.pi = 0 := by
  obtain ⟨iγ, iα, hγ, hα, -, -, hsγ, hsα⟩ := F.ground_leg_side hG hmu
  have hρ : (0 : ℝ) < (ρ : ℝ) + 1 := by positivity
  exact F.wall_fig hρ hmu hsγ hsα hγ hα


end WFrame

end Erdos634.LaczCol

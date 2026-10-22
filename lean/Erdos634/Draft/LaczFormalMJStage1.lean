import Erdos634.Draft.LaczFormalMJRow

/-!
# Edge-type labels, tiles above a level, and the figure at a leg point (rule `M(j)`)

Erdős #634, base-`β` band, rule `M(j)`.  Credit: AI assistant (item 3, band program), Beeson–Roșu, Beeson,
Laczkovich, Paliy.  UNAUDITED.  Axiom-clean; no `sorry`.

* `tv_cedge`, `tv_bedge`, `tv_aedge`: a tile with vertices `X,Y,Z` and `|XY| = c` (resp. `b`, `a`) has the two
  labellings forced by the side lengths.
* `chainH_ht`: tiles of the far (upper) chain of `Λ_ρ` have all vertices of height `≥ ρ`.
* `third_above`: the third vertex of a tile with a lattice edge on `Λ_ρ` in the upper chain is strictly above.
* `leg_fig`: at the leg point `(0, ρ+1)` (ground below) exactly one tile each presents `α, β, γ`, none `π`.
-/

namespace Erdos634.LaczMJ

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Walk
  Erdos634.LaczJunction.Grammar Erdos634.Draft.TraceCovering Set

variable {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}

theorem tv_cedge (S : BandSetup D e f α β γ p q r) {i : Fin N} {X Y Z : Plane}
    (hv : TileVerts (D.tile i) X Y Z) (h : dist X Y = (tc e f : ℝ)) :
    ((D.tile i).localAngle X = α ∧ (D.tile i).localAngle Y = β ∧ (D.tile i).localAngle Z = γ ∧
      dist Y Z = (ta e f : ℝ) ∧ dist X Z = (tb e f : ℝ)) ∨
    ((D.tile i).localAngle X = β ∧ (D.tile i).localAngle Y = α ∧ (D.tile i).localAngle Z = γ ∧
      dist Y Z = (tb e f : ℝ) ∧ dist X Z = (ta e f : ℝ)) := by
  obtain ⟨hab, hbc, hac⟩ := BandSetup.dist3 S
  rcases tv_lab S hv with ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩ |
      ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩ |
      ⟨h1, h2, h3, h4, h5, h6⟩
  · exact Or.inl ⟨h1, h2, h3, h4, h5⟩
  · exact absurd (h6.symm.trans h) hbc
  · exact Or.inr ⟨h1, h2, h3, h4, h5⟩
  · exact absurd (h6.symm.trans h) hac
  · exact absurd (h6.symm.trans h) hbc
  · exact absurd (h6.symm.trans h) hac

theorem tv_bedge (S : BandSetup D e f α β γ p q r) {i : Fin N} {X Y Z : Plane}
    (hv : TileVerts (D.tile i) X Y Z) (h : dist X Y = (tb e f : ℝ)) :
    ((D.tile i).localAngle X = α ∧ (D.tile i).localAngle Y = γ ∧ (D.tile i).localAngle Z = β ∧
      dist Y Z = (ta e f : ℝ) ∧ dist X Z = (tc e f : ℝ)) ∨
    ((D.tile i).localAngle X = γ ∧ (D.tile i).localAngle Y = α ∧ (D.tile i).localAngle Z = β ∧
      dist Y Z = (tc e f : ℝ) ∧ dist X Z = (ta e f : ℝ)) := by
  obtain ⟨hab, hbc, hac⟩ := BandSetup.dist3 S
  rcases tv_lab S hv with ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩ |
      ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩ |
      ⟨h1, h2, h3, h4, h5, h6⟩
  · exact absurd (h6.symm.trans h) hbc.symm
  · exact Or.inl ⟨h1, h2, h3, h4, h5⟩
  · exact absurd (h6.symm.trans h) hbc.symm
  · exact absurd (h6.symm.trans h) hab
  · exact Or.inr ⟨h1, h2, h3, h4, h5⟩
  · exact absurd (h6.symm.trans h) hab

theorem tv_aedge (S : BandSetup D e f α β γ p q r) {i : Fin N} {X Y Z : Plane}
    (hv : TileVerts (D.tile i) X Y Z) (h : dist X Y = (ta e f : ℝ)) :
    ((D.tile i).localAngle X = β ∧ (D.tile i).localAngle Y = γ ∧ (D.tile i).localAngle Z = α ∧
      dist Y Z = (tb e f : ℝ) ∧ dist X Z = (tc e f : ℝ)) ∨
    ((D.tile i).localAngle X = γ ∧ (D.tile i).localAngle Y = β ∧ (D.tile i).localAngle Z = α ∧
      dist Y Z = (tc e f : ℝ) ∧ dist X Z = (tb e f : ℝ)) := by
  obtain ⟨hab, hbc, hac⟩ := BandSetup.dist3 S
  rcases tv_lab S hv with ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩ |
      ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩ |
      ⟨h1, h2, h3, h4, h5, h6⟩
  · exact absurd (h6.symm.trans h) hac.symm
  · exact absurd (h6.symm.trans h) hab.symm
  · exact absurd (h6.symm.trans h) hac.symm
  · exact Or.inl ⟨h1, h2, h3, h4, h5⟩
  · exact absurd (h6.symm.trans h) hab.symm
  · exact Or.inr ⟨h1, h2, h3, h4, h5⟩

namespace LFrame

variable (F : LFrame D e f α β γ p q r)

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

/-- Leg points are frontier points which are not target vertices. -/
theorem leg_front {y : ℝ} (h0 : 0 < y) (h1 : y < F.mu) :
    F.pt 0 y ∈ frontier D.target.carrier ∧ F.pt 0 y ∉ Set.range D.target.pts :=
  side_frontier D.target F.S.hpr F.S.hpq F.S.hqr.symm (F.pt_leg_mem h0 h1)

/-- Base points are frontier points which are not target vertices. -/
theorem base_front {x : ℝ} (h0 : 0 < x) (h1 : x < F.lam) :
    F.pt x 0 ∈ frontier D.target.carrier ∧ F.pt x 0 ∉ Set.range D.target.pts :=
  side_frontier D.target F.S.hpq F.S.hpr F.S.hqr (F.pt_base_mem h0 h1)

/-- **The figure at a leg point above level 0**: exactly one tile each presents `α`, `β`, `γ`, none `π`. -/
theorem leg_fig {ρ k : ℕ} (hG : F.Ground (ρ + 1) k) (hmu : ((ρ : ℝ) + 1) < F.mu) :
    cnt D.toDissection (F.pt 0 ((ρ : ℝ) + 1)) α = 1 ∧ cnt D.toDissection (F.pt 0 ((ρ : ℝ) + 1)) β = 1 ∧
      cnt D.toDissection (F.pt 0 ((ρ : ℝ) + 1)) γ = 1 ∧
      cnt D.toDissection (F.pt 0 ((ρ : ℝ) + 1)) Real.pi = 0 := by
  obtain ⟨iγ, iα, hγ, hα, -, -⟩ := F.ground_leg hG
  have hρ : (0 : ℝ) < (ρ : ℝ) + 1 := by positivity
  obtain ⟨hfr, hnv⟩ := F.leg_front hρ hmu
  have hfig := bfig F.S hfr hnv
  have h1 := cnt_ge_one hγ
  have h2 := cnt_ge_one hα
  omega

end LFrame

end Erdos634.LaczMJ

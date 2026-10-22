import Erdos634.Draft.LaczFormalMJFig

/-!
# Tile labels and third vertices at the lattice cells (rule `M(j)`)

Erdős #634, base-`β` band, rule `M(j)`.  Credit: AI assistant (item 3, band program), Beeson–Roșu, Beeson,
Laczkovich, Paliy.  UNAUDITED.  Axiom-clean; no `sorry`.

* `tv_ms`: for a tile with vertices `X,Y,Z` the three distances are `{c,b,a}`.
* `tv_lab`: the six labellings of `(X,Y,Z)` by `(α,β,γ)` with the matching opposite sides.
* `third_up`: a tile with a `c`-edge `[(x,ρ),(x+1,ρ)]`, `β` at `(x,ρ)` and third vertex above the line is the
  standard up tile (third vertex `(x,ρ+1)`).
* `third_down`: a tile with a `b`-edge `[(x+1,y),(x,y+1)]`, `γ` at `(x+1,y)` and third vertex to the right of
  the directed edge is the standard down tile (third vertex `(x+1,y+1)`).
-/

namespace Erdos634.LaczMJ

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Walk
  Erdos634.LaczJunction.Grammar

variable {N : ℕ}

theorem tv_ms {D : CongruentDissection N} {i : Fin N} {X Y Z : Plane} (hv : TileVerts (D.tile i) X Y Z) :
    ({dist X Y, dist X Z, dist Y Z} : Multiset ℝ) =
      {sideOpp D.model 2, sideOpp D.model 1, sideOpp D.model 0} := by
  have F3 : ∀ j : Fin 3, j ≠ j + 1 ∧ j ≠ j + 2 ∧ j + 1 ≠ j + 2 := by decide
  obtain ⟨j, ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩⟩ := hv
  · have := tri_ms D i j (j + 1) (j + 2) (F3 j).1 (F3 j).2.1 (F3 j).2.2
    rw [h1, h2, h3] at this
    exact this
  · have := tri_ms D i j (j + 2) (j + 1) (F3 j).2.1 (F3 j).1 (F3 j).2.2.symm
    rw [h1, h2, h3] at this
    exact this

variable {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}

/-- The six labellings of a tile's vertices `X, Y, Z` by `α, β, γ` (opposite sides `a, b, c`). -/
theorem tv_lab (S : BandSetup D e f α β γ p q r) {i : Fin N} {X Y Z : Plane}
    (hv : TileVerts (D.tile i) X Y Z) :
    let a := (ta e f : ℝ); let b := (tb e f : ℝ); let c := (tc e f : ℝ)
    ((D.tile i).localAngle X = α ∧ (D.tile i).localAngle Y = β ∧ (D.tile i).localAngle Z = γ ∧
        dist Y Z = a ∧ dist X Z = b ∧ dist X Y = c) ∨
    ((D.tile i).localAngle X = α ∧ (D.tile i).localAngle Y = γ ∧ (D.tile i).localAngle Z = β ∧
        dist Y Z = a ∧ dist X Z = c ∧ dist X Y = b) ∨
    ((D.tile i).localAngle X = β ∧ (D.tile i).localAngle Y = α ∧ (D.tile i).localAngle Z = γ ∧
        dist Y Z = b ∧ dist X Z = a ∧ dist X Y = c) ∨
    ((D.tile i).localAngle X = β ∧ (D.tile i).localAngle Y = γ ∧ (D.tile i).localAngle Z = α ∧
        dist Y Z = b ∧ dist X Z = c ∧ dist X Y = a) ∨
    ((D.tile i).localAngle X = γ ∧ (D.tile i).localAngle Y = α ∧ (D.tile i).localAngle Z = β ∧
        dist Y Z = c ∧ dist X Z = a ∧ dist X Y = b) ∨
    ((D.tile i).localAngle X = γ ∧ (D.tile i).localAngle Y = β ∧ (D.tile i).localAngle Z = α ∧
        dist Y Z = c ∧ dist X Z = b ∧ dist X Y = a) := by
  intro a b c
  obtain ⟨hαβ, hβγ, hαγ, hab, hbc, hac⟩ := BandSetup.distinct S
  have hm := tv_ms hv
  have hX := LFrame.tileVerts_angle S hv
  have hY := LFrame.tileVerts_angle S hv.rot
  have hZ := LFrame.tileVerts_angle S hv.rot.rot
  have hd1 : dist Z X = dist X Z := dist_comm _ _
  have hd2 : dist Y X = dist X Y := dist_comm _ _
  rw [S.hsa, S.hsb, S.hsc] at hm
  rcases perm3 hm (by rw [S.hsa, S.hsb] at hab; exact hab) (by rw [S.hsb, S.hsc] at hbc; exact hbc)
    (by rw [S.hsa, S.hsc] at hac; exact hac) with
    ⟨x1, x2, x3⟩ | ⟨x1, x2, x3⟩ | ⟨x1, x2, x3⟩ | ⟨x1, x2, x3⟩ | ⟨x1, x2, x3⟩ | ⟨x1, x2, x3⟩
  · exact Or.inl ⟨hX.1 x3, hY.2.1 ((dist_comm Z X).trans x2), hZ.2.2 x1, x3, x2, x1⟩
  · exact Or.inr (Or.inr (Or.inl ⟨hX.2.1 x3, hY.1 ((dist_comm Z X).trans x2), hZ.2.2 x1, x3, x2, x1⟩))
  · exact Or.inr (Or.inl ⟨hX.1 x3, hY.2.2 ((dist_comm Z X).trans x2), hZ.2.1 x1, x3, x2, x1⟩)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨hX.2.2 x3, hY.1 ((dist_comm Z X).trans x2), hZ.2.1 x1, x3, x2, x1⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hX.2.1 x3, hY.2.2 ((dist_comm Z X).trans x2), hZ.1 x1, x3, x2, x1⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨hX.2.2 x3, hY.2.1 ((dist_comm Z X).trans x2), hZ.1 x1, x3, x2, x1⟩))))


theorem BandSetup.dist3 (S : BandSetup D e f α β γ p q r) :
    (ta e f : ℝ) ≠ tb e f ∧ (tb e f : ℝ) ≠ tc e f ∧ (ta e f : ℝ) ≠ tc e f := by
  obtain ⟨-, -, -, hab, hbc, hac⟩ := BandSetup.distinct S
  rw [S.hsa, S.hsb] at hab
  rw [S.hsb, S.hsc] at hbc
  rw [S.hsa, S.hsc] at hac
  exact ⟨hab, hbc, hac⟩

namespace LFrame

variable (F : LFrame D e f α β γ p q r)

theorem pt_sub (x1 y1 x2 y2 : ℝ) :
    F.pt x1 y1 - F.pt x2 y2 = (x1 - x2) • F.e0 + (y1 - y2) • F.v := by
  simp only [pt]; module

theorem cross_e0_v_pos : 0 < cross F.e0 F.v := F.hcr

/-- A tile with the `c`-edge `[(x,ρ),(x+1,ρ)]`, `β` at `(x,ρ)` and third vertex above the line is the
standard up tile. -/
theorem third_up {i : Fin N} {x ρ : ℝ} {Z : Plane}
    (hv : TileVerts (D.tile i) (F.pt x ρ) (F.pt (x + 1) ρ) Z)
    (hβ : (D.tile i).localAngle (F.pt x ρ) = β)
    (hup : 0 < cross F.e0 (Z - F.pt x ρ)) : Z = F.pt x (ρ + 1) := by
  obtain ⟨hαβ, hβγ, hαγ, -, -, -⟩ := BandSetup.distinct F.S
  obtain ⟨hab, hbc, hac⟩ := BandSetup.dist3 F.S
  have hXY : dist (F.pt x ρ) (F.pt (x + 1) ρ) = (tc e f : ℝ) := F.dist_pt_c x ρ
  have key : dist (F.pt x ρ) Z = (ta e f : ℝ) ∧ dist (F.pt (x + 1) ρ) Z = (tb e f : ℝ) := by
    rcases tv_lab F.S hv with ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩ |
        ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩ |
        ⟨h1, h2, h3, h4, h5, h6⟩
    · exact absurd (h1.symm.trans hβ) hαβ
    · exact absurd (h1.symm.trans hβ) hαβ
    · exact ⟨h5, h4⟩
    · exact absurd (hXY.symm.trans h6) hac.symm
    · exact absurd (h1.symm.trans hβ) hβγ.symm
    · exact absurd (h1.symm.trans hβ) hβγ.symm
  have hAB : F.pt x ρ ≠ F.pt (x + 1) ρ := by
    intro h; rw [h, dist_self] at hXY
    have : (0 : ℝ) < tc e f := by
      have := b_lt_c e f F.S.he F.S.hef
      have := b_pos e f F.S.he F.S.hef
      exact_mod_cast (by omega : 0 < tc e f)
    linarith
  refine two_circles hAB ?_ ?_ ?_ |>.symm.symm
  · rw [key.1, F.dist_pt_a]
  · rw [key.2]; exact (F.dist_pt_b x ρ).symm
  · have e1 : F.pt (x + 1) ρ - F.pt x ρ = F.e0 := by rw [F.pt_sub]; module
    have e2 : F.pt x (ρ + 1) - F.pt x ρ = F.v := by rw [F.pt_sub]; module
    rw [e1, e2]
    exact mul_pos hup F.hcr

/-- A tile with the `b`-edge `[(x+1,y),(x,y+1)]`, `γ` at `(x+1,y)` and third vertex to the right of the directed
edge is the standard down tile. -/
theorem third_down {i : Fin N} {x y : ℝ} {Z : Plane}
    (hv : TileVerts (D.tile i) (F.pt (x + 1) y) (F.pt x (y + 1)) Z)
    (hγ : (D.tile i).localAngle (F.pt (x + 1) y) = γ)
    (hside : cross (F.pt x (y + 1) - F.pt (x + 1) y) (Z - F.pt (x + 1) y) < 0) :
    Z = F.pt (x + 1) (y + 1) := by
  obtain ⟨hαβ, hβγ, hαγ, -, -, -⟩ := BandSetup.distinct F.S
  obtain ⟨hab, hbc, hac⟩ := BandSetup.dist3 F.S
  have hXY : dist (F.pt (x + 1) y) (F.pt x (y + 1)) = (tb e f : ℝ) := F.dist_pt_b x y
  have key : dist (F.pt (x + 1) y) Z = (ta e f : ℝ) ∧ dist (F.pt x (y + 1)) Z = (tc e f : ℝ) := by
    rcases tv_lab F.S hv with ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩ |
        ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩ |
        ⟨h1, h2, h3, h4, h5, h6⟩
    · exact absurd (h1.symm.trans hγ) hαγ
    · exact absurd (h1.symm.trans hγ) hαγ
    · exact absurd (h1.symm.trans hγ) hβγ
    · exact absurd (h1.symm.trans hγ) hβγ
    · exact ⟨h5, h4⟩
    · exact absurd (hXY.symm.trans h6) hab.symm
  have hAB : F.pt (x + 1) y ≠ F.pt x (y + 1) := by
    intro h; rw [h, dist_self] at hXY
    have : (0 : ℝ) < tb e f := by exact_mod_cast b_pos e f F.S.he F.S.hef
    linarith
  refine two_circles hAB ?_ ?_ ?_
  · rw [key.1, F.dist_pt_a]
  · rw [key.2]; exact (F.dist_pt_c x (y + 1)).symm
  · have e1 : F.pt (x + 1) (y + 1) - F.pt (x + 1) y = F.v := by rw [F.pt_sub]; module
    have e2 : F.pt x (y + 1) - F.pt (x + 1) y = F.v - F.e0 := by rw [F.pt_sub]; module
    rw [e2] at hside
    rw [e1, e2]
    have : cross (F.v - F.e0) F.v < 0 := by
      have : cross (F.v - F.e0) F.v = - cross F.e0 F.v := by
        simp only [cross, PiLp.sub_apply]; ring
      rw [this]; linarith [F.hcr]
    exact mul_pos_of_neg_of_neg hside this

end LFrame

end Erdos634.LaczMJ

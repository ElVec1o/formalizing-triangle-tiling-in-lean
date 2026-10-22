import Erdos634.Draft.LaczFormalALChord

/-!
# Third vertices of the standard cells (a-lattice)

Erdős \#634, base-`β` row, thick analogue of `M(j)` (Lemma A(j)).  Credit: AI assistant (Lemma A(k) proposal), Beeson–Roșu,
Beeson, Laczkovich, Paliy.  UNAUDITED.  Axiom-clean; no `sorry`.  Port of `LaczFormalMJTile.lean` to the exchanged frame
`AF` (`e0` of length `a` along the base, `v` of length `c` along the left leg).
-/

namespace Erdos634.LaczAL

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Walk
  Erdos634.LaczJunction.Grammar Erdos634.Draft.TraceCovering Erdos634.LaczMJ Set

variable {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}

namespace AF

variable (F : AF D e f α β γ p q r)

theorem pt_sub (x1 y1 x2 y2 : ℝ) :
    F.pt x1 y1 - F.pt x2 y2 = (x1 - x2) • F.e0 + (y1 - y2) • F.v := by
  simp only [pt]; module

theorem cross_e0_v_pos : 0 < cross F.e0 F.v := F.hcr

/-- A tile with the `a`-edge `[(x,ρ),(x+1,ρ)]`, `β` at `(x,ρ)` and third vertex above the line is the
standard up tile. -/
theorem third_up {i : Fin N} {x ρ : ℝ} {Z : Plane}
    (hv : TileVerts (D.tile i) (F.pt x ρ) (F.pt (x + 1) ρ) Z)
    (hβ : (D.tile i).localAngle (F.pt x ρ) = β)
    (hup : 0 < cross F.e0 (Z - F.pt x ρ)) : Z = F.pt x (ρ + 1) := by
  obtain ⟨hαβ, hβγ, hαγ, -, -, -⟩ := BandSetup.distinct F.S
  obtain ⟨hab, hbc, hac⟩ := BandSetup.dist3 F.S
  have hXY : dist (F.pt x ρ) (F.pt (x + 1) ρ) = (ta e f : ℝ) := F.dist_pt_a x ρ
  have key : dist (F.pt x ρ) Z = (tc e f : ℝ) ∧ dist (F.pt (x + 1) ρ) Z = (tb e f : ℝ) := by
    rcases tv_lab F.S hv with ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩ |
        ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩ |
        ⟨h1, h2, h3, h4, h5, h6⟩
    · exact absurd (h1.symm.trans hβ) hαβ
    · exact absurd (h1.symm.trans hβ) hαβ
    · exact absurd (hXY.symm.trans h6) hac
    · exact ⟨h5, h4⟩
    · exact absurd (h1.symm.trans hβ) hβγ.symm
    · exact absurd (h1.symm.trans hβ) hβγ.symm
  have hAB : F.pt x ρ ≠ F.pt (x + 1) ρ := by
    intro h; rw [h, dist_self] at hXY
    have : (0 : ℝ) < ta e f := by
      have := F.S.he
      have := F.S.hef
      have : 0 < ta e f := by unfold ta; exact Nat.mul_pos (by omega) (by omega)
      exact_mod_cast this
    linarith
  refine two_circles hAB ?_ ?_ ?_
  · rw [key.1, F.dist_pt_c]
  · rw [key.2]; exact (F.dist_pt_b x ρ).symm
  · have e1 : F.pt (x + 1) ρ - F.pt x ρ = F.e0 := by rw [F.pt_sub]; module
    have e2 : F.pt x (ρ + 1) - F.pt x ρ = F.v := by rw [F.pt_sub]; module
    rw [e1, e2]
    exact mul_pos hup F.hcr

/-- A tile with the `b`-edge `[(x+1,y),(x,y+1)]`, `α` at `(x+1,y)` and third vertex to the right of the directed
edge is the standard down tile. -/
theorem third_down {i : Fin N} {x y : ℝ} {Z : Plane}
    (hv : TileVerts (D.tile i) (F.pt (x + 1) y) (F.pt x (y + 1)) Z)
    (hα : (D.tile i).localAngle (F.pt (x + 1) y) = α)
    (hside : cross (F.pt x (y + 1) - F.pt (x + 1) y) (Z - F.pt (x + 1) y) < 0) :
    Z = F.pt (x + 1) (y + 1) := by
  obtain ⟨hαβ, hβγ, hαγ, -, -, -⟩ := BandSetup.distinct F.S
  obtain ⟨hab, hbc, hac⟩ := BandSetup.dist3 F.S
  have hXY : dist (F.pt (x + 1) y) (F.pt x (y + 1)) = (tb e f : ℝ) := F.dist_pt_b x y
  have key : dist (F.pt (x + 1) y) Z = (tc e f : ℝ) ∧ dist (F.pt x (y + 1)) Z = (ta e f : ℝ) := by
    rcases tv_lab F.S hv with ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩ |
        ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩ |
        ⟨h1, h2, h3, h4, h5, h6⟩
    · exact absurd (hXY.symm.trans h6) hbc
    · exact ⟨h5, h4⟩
    · exact absurd (h1.symm.trans hα) hαβ.symm
    · exact absurd (h1.symm.trans hα) hαβ.symm
    · exact absurd (h1.symm.trans hα) hαγ.symm
    · exact absurd (h1.symm.trans hα) hαγ.symm
  have hAB : F.pt (x + 1) y ≠ F.pt x (y + 1) := by
    intro h; rw [h, dist_self] at hXY
    have : (0 : ℝ) < tb e f := by exact_mod_cast b_pos e f F.S.he F.S.hef
    linarith
  refine two_circles hAB ?_ ?_ ?_
  · rw [key.1, F.dist_pt_c]
  · rw [key.2]; exact (F.dist_pt_a x (y + 1)).symm
  · have e1 : F.pt (x + 1) (y + 1) - F.pt (x + 1) y = F.v := by rw [F.pt_sub]; module
    have e2 : F.pt x (y + 1) - F.pt (x + 1) y = F.v - F.e0 := by rw [F.pt_sub]; module
    rw [e2] at hside
    rw [e1, e2]
    have : cross (F.v - F.e0) F.v < 0 := by
      have : cross (F.v - F.e0) F.v = - cross F.e0 F.v := by
        simp only [cross, PiLp.sub_apply]; ring
      rw [this]; linarith [F.hcr]
    exact mul_pos_of_neg_of_neg hside this

end AF

end Erdos634.LaczAL

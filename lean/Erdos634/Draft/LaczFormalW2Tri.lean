import Erdos634.Draft.LaczFormalW2Fan

/-!
# Rule W2: sides adjacent to a tile angle; a corner angle is attained at a vertex

Erdős #634, band program, rule W2.  Credit: AI assistant (item 3, band program), Beeson–Roșu (the tile `(a,b,c)`),
Beeson, Laczkovich, Paliy.  UNAUDITED.

* `tile_adj_B / tile_adj_A / tile_adj_G`: at a vertex presenting `β` (resp. `α`, `γ`) the two adjacent sides are
  `{a, c}` (resp. `{b, c}`, `{a, b}`);
* `exists_vertex_of_angle`: a tile whose local angle at `V` is a corner angle `β ∉ {0, π, 2π}` has `V` as a vertex;
* `mem_of_angle_ne_zero`: nonzero local angle puts `V` in the carrier.
-/

namespace Erdos634.LaczJunction.Walk

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Grammar
open Erdos634.Draft.LaczFormal.Graph

variable {N : ℕ}

theorem tile_adj_B {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r) (i : Fin N) (k0 k1 k2 : Fin 3) (h01 : k0 ≠ k1) (h02 : k0 ≠ k2)
    (h12 : k1 ≠ k2) (hβ : (D.tile i).localAngle ((D.tile i).pts k0) = β) :
    (dist ((D.tile i).pts k0) ((D.tile i).pts k1) = sideOpp D.model 0 ∧
        dist ((D.tile i).pts k0) ((D.tile i).pts k2) = sideOpp D.model 2) ∨
      (dist ((D.tile i).pts k0) ((D.tile i).pts k1) = sideOpp D.model 2 ∧
        dist ((D.tile i).pts k0) ((D.tile i).pts k2) = sideOpp D.model 0) := by
  obtain ⟨hαβ, hβγ, hαγ, hab, hbc, hac⟩ := BandSetup.distinct S
  have hm := tri_ms D i k0 k1 k2 h01 h02 h12
  have hang := angle_of_opp D α β γ S.hα' S.hβ' S.hγ' hab hbc hac i k0 k1 k2 h01 h02 h12
  rcases perm3 hm hab hbc hac with ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ |
      ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩
  · exact absurd (hβ.symm.trans (hang.1 hz)) hαβ.symm
  · exact Or.inr ⟨hx, hy⟩
  · exact absurd (hβ.symm.trans (hang.1 hz)) hαβ.symm
  · exact absurd (hβ.symm.trans (hang.2.2 hz)) hβγ
  · exact Or.inl ⟨hx, hy⟩
  · exact absurd (hβ.symm.trans (hang.2.2 hz)) hβγ

theorem tile_adj_A {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r) (i : Fin N) (k0 k1 k2 : Fin 3) (h01 : k0 ≠ k1) (h02 : k0 ≠ k2)
    (h12 : k1 ≠ k2) (hα : (D.tile i).localAngle ((D.tile i).pts k0) = α) :
    (dist ((D.tile i).pts k0) ((D.tile i).pts k1) = sideOpp D.model 1 ∧
        dist ((D.tile i).pts k0) ((D.tile i).pts k2) = sideOpp D.model 2) ∨
      (dist ((D.tile i).pts k0) ((D.tile i).pts k1) = sideOpp D.model 2 ∧
        dist ((D.tile i).pts k0) ((D.tile i).pts k2) = sideOpp D.model 1) := by
  obtain ⟨hαβ, hβγ, hαγ, hab, hbc, hac⟩ := BandSetup.distinct S
  have hm := tri_ms D i k0 k1 k2 h01 h02 h12
  have hang := angle_of_opp D α β γ S.hα' S.hβ' S.hγ' hab hbc hac i k0 k1 k2 h01 h02 h12
  rcases perm3 hm hab hbc hac with ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ |
      ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩
  · exact Or.inr ⟨hx, hy⟩
  · exact absurd (hα.symm.trans (hang.2.1 hz)) hαβ
  · exact Or.inl ⟨hx, hy⟩
  · exact absurd (hα.symm.trans (hang.2.2 hz)) hαγ
  · exact absurd (hα.symm.trans (hang.2.1 hz)) hαβ
  · exact absurd (hα.symm.trans (hang.2.2 hz)) hαγ

theorem tile_adj_G {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r) (i : Fin N) (k0 k1 k2 : Fin 3) (h01 : k0 ≠ k1) (h02 : k0 ≠ k2)
    (h12 : k1 ≠ k2) (hγ : (D.tile i).localAngle ((D.tile i).pts k0) = γ) :
    (dist ((D.tile i).pts k0) ((D.tile i).pts k1) = sideOpp D.model 1 ∧
        dist ((D.tile i).pts k0) ((D.tile i).pts k2) = sideOpp D.model 0) ∨
      (dist ((D.tile i).pts k0) ((D.tile i).pts k1) = sideOpp D.model 0 ∧
        dist ((D.tile i).pts k0) ((D.tile i).pts k2) = sideOpp D.model 1) := by
  obtain ⟨hαβ, hβγ, hαγ, hab, hbc, hac⟩ := BandSetup.distinct S
  have hm := tri_ms D i k0 k1 k2 h01 h02 h12
  have hang := angle_of_opp D α β γ S.hα' S.hβ' S.hγ' hab hbc hac i k0 k1 k2 h01 h02 h12
  rcases perm3 hm hab hbc hac with ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ |
      ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩
  · exact absurd (hγ.symm.trans (hang.1 hz)) hαγ.symm
  · exact absurd (hγ.symm.trans (hang.2.1 hz)) hβγ.symm
  · exact absurd (hγ.symm.trans (hang.1 hz)) hαγ.symm
  · exact Or.inl ⟨hx, hy⟩
  · exact absurd (hγ.symm.trans (hang.2.1 hz)) hβγ.symm
  · exact Or.inr ⟨hx, hy⟩

/-- Nonzero local angle puts the point in the carrier. -/
theorem mem_of_angle_ne_zero (T : Tri) {V : Plane} (h : T.localAngle V ≠ 0) : V ∈ T.carrier := by
  by_contra hn
  exact h (Tri.localAngle_eq_zero_of_not_mem T hn)

/-- A corner angle (`≠ 0, π, 2π`) is attained at a vertex. -/
theorem exists_vertex_of_angle (T : Tri) {V : Plane} {x : ℝ} (hx : T.localAngle V = x) (h0 : x ≠ 0)
    (hπ : x ≠ Real.pi) (h2π : x ≠ 2 * Real.pi) : ∃ k, T.pts k = V := by
  classical
  by_contra hn
  push_neg at hn
  have hv : ¬ ∃ j, V = T.pts j := fun ⟨j, hj⟩ => hn j hj.symm
  rw [Tri.localAngle, dif_neg hv] at hx
  by_cases h1 : ∀ j, 0 < T.basis.coord j V
  · rw [if_pos h1] at hx; exact h2π hx.symm
  · rw [if_neg h1] at hx
    by_cases h2 : ∃ k, T.basis.coord k V = 0 ∧ ∀ j, j ≠ k → 0 < T.basis.coord j V
    · rw [if_pos h2] at hx; exact hπ hx.symm
    · rw [if_neg h2] at hx; exact h0 hx.symm

end Erdos634.LaczJunction.Walk

import Erdos634.Draft.LaczFormalW2Chords

/-!
# Rule W2: the junction `P₂` cannot present `γ` on a tile with a `b`-edge `[P₂, G₂]`

Erdős #634, band program, rule W2 (`PROOF_W2.md`).  Credit: AI assistant (item 3, band program), Beeson–Roșu, Beeson,
Laczkovich, Paliy.  UNAUDITED.

`w2_P2_clash`: with `T₁` presenting `α` at `P₂` and the third token `bAG`, `cAB` or `bGA` starting at `P₂`, no tile `W`
presents `γ` at `P₂` with `G₂` (off the base) another vertex at distance `b`.  Boundary figure at `P₂`
(`congruentDissection_boundary_figure_cases_at_vertex`, `congruentDissection_no_double_gamma`).
-/

namespace Erdos634.LaczJunction.Walk

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Grammar
open Erdos634.Geometry.Dissection

variable {N : ℕ}

theorem tile_adj_ne {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r) (i : Fin N) (k0 k1 k2 : Fin 3) (h01 : k0 ≠ k1) (h02 : k0 ≠ k2)
    (h12 : k1 ≠ k2) :
    dist ((D.tile i).pts k0) ((D.tile i).pts k1) ≠ dist ((D.tile i).pts k0) ((D.tile i).pts k2) := by
  obtain ⟨hαβ, hβγ, hαγ, hab, hbc, hac⟩ := BandSetup.distinct S
  have hm := tri_ms D i k0 k1 k2 h01 h02 h12
  intro hxy
  rcases perm3 hm hab hbc hac with ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ |
      ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩
  · exact hbc.symm (hx.symm.trans (hxy.trans hy))
  · exact hac.symm (hx.symm.trans (hxy.trans hy))
  · exact hbc (hx.symm.trans (hxy.trans hy))
  · exact hab.symm (hx.symm.trans (hxy.trans hy))
  · exact hac (hx.symm.trans (hxy.trans hy))
  · exact hab (hx.symm.trans (hxy.trans hy))

theorem w2_P2_clash {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r) {P2 G2 P3 Z3 : Plane} {i2 i3 iW : Fin N}
    (hP2seg : P2 ∈ openSegment ℝ (D.target.pts p) (D.target.pts q))
    (hα2 : (D.tile i2).localAngle P2 = α) (hne : i3 ≠ i2)
    (x3 : Side) (l3 r3 : Corner)
    (hlr : (x3 = .b ∧ l3 = .A) ∨ (x3 = .c ∧ l3 = .A) ∨ (x3 = .b ∧ l3 = .G ∧ r3 = .A))
    (t3 : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) x3 l3 r3 i3 P2 P3 Z3)
    (hW : (D.tile iW).localAngle P2 = γ) (k1 k2 : Fin 3) (hk12 : k1 ≠ k2)
    (hk1 : (D.tile iW).pts k1 = P2) (hk2 : (D.tile iW).pts k2 = G2)
    (hPG : dist P2 G2 = (tb e f : ℝ)) (hG2P3 : G2 ≠ P3) : False := by
  classical
  obtain ⟨hαβ, hβγ, hαγ, hab, hbc, hac⟩ := BandSetup.distinct S
  have hα0 := S.hα0
  have hβ0 := S.hβ0
  have hγdef := S.hγdef
  have hrel := S.hrel
  have hαπ : α ≠ Real.pi := by intro h; linarith
  have hβπ : β ≠ Real.pi := by intro h; linarith
  have hγπ : γ ≠ Real.pi := by intro h; rw [hγdef] at h; linarith
  have hγ0 : γ ≠ 0 := by rw [hγdef]; intro h; linarith
  obtain ⟨hfront, hnv⟩ := side_frontier D.target S.hpq S.hpr S.hqr hP2seg
  rcases hlr with ⟨-, hl⟩ | ⟨-, hl⟩ | ⟨hx, hl, -⟩
  · -- l3 = A
    have hα3 : (D.tile i3).localAngle P2 = α := by simpa [hl, angOf] using t3.left_angle
    have hfig := congruentDissection_boundary_figure_cases_at_vertex D α β γ hαβ hαγ hαπ hα0.ne' hβγ hβπ hβ0.ne'
      hγπ hγ0 Real.pi_ne_zero hγdef hrel S.hirr S.hα' S.hβ' S.hγ' hfront hnv iW (Or.inr (Or.inr hW))
    have hmemγ : iW ∈ ({i | (D.tile i).localAngle P2 = γ} : Finset (Fin N)) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hW
    have hm2 : i2 ∈ ({i | (D.tile i).localAngle P2 = α} : Finset (Fin N)) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hα2
    have hm3 : i3 ∈ ({i | (D.tile i).localAngle P2 = α} : Finset (Fin N)) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hα3
    rcases hfig with ⟨_, _, hg0⟩ | ⟨hαc, _, _⟩
    · rw [Finset.card_eq_zero.mp hg0] at hmemγ; simp at hmemγ
    · obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hαc
      rw [hy] at hm2 hm3
      simp at hm2 hm3
      exact hne (hm3.trans hm2.symm)
  · have hα3 : (D.tile i3).localAngle P2 = α := by simpa [hl, angOf] using t3.left_angle
    have hfig := congruentDissection_boundary_figure_cases_at_vertex D α β γ hαβ hαγ hαπ hα0.ne' hβγ hβπ hβ0.ne'
      hγπ hγ0 Real.pi_ne_zero hγdef hrel S.hirr S.hα' S.hβ' S.hγ' hfront hnv iW (Or.inr (Or.inr hW))
    have hmemγ : iW ∈ ({i | (D.tile i).localAngle P2 = γ} : Finset (Fin N)) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hW
    have hm2 : i2 ∈ ({i | (D.tile i).localAngle P2 = α} : Finset (Fin N)) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hα2
    have hm3 : i3 ∈ ({i | (D.tile i).localAngle P2 = α} : Finset (Fin N)) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hα3
    rcases hfig with ⟨_, _, hg0⟩ | ⟨hαc, _, _⟩
    · rw [Finset.card_eq_zero.mp hg0] at hmemγ; simp at hmemγ
    · obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hαc
      rw [hy] at hm2 hm3
      simp at hm2 hm3
      exact hne (hm3.trans hm2.symm)
  · -- l3 = G : tile i3 presents gamma at P2
    have hγ3 : (D.tile i3).localAngle P2 = γ := by simpa [hl, angOf] using t3.left_angle
    by_cases hWi : iW = i3
    · subst hWi
      have hlen : dist P2 P3 = (tb e f : ℝ) := by simpa [hx, lenOf] using t3.length
      obtain ⟨kk, k3, hkk, hk3, hkk3⟩ : ∃ kk k3 : Fin 3, (D.tile iW).pts kk = P2 ∧ (D.tile iW).pts k3 = P3 ∧ kk ≠ k3 := by
        obtain ⟨j, hj | hj⟩ := t3.verts
        · exact ⟨j, j + 1, hj.1, hj.2.1, (by decide : ∀ k : Fin 3, k ≠ k + 1) j⟩
        · exact ⟨j, j + 2, hj.1, hj.2.2, (by decide : ∀ k : Fin 3, k ≠ k + 2) j⟩
      have hk1kk : k1 = kk := (D.tile iW).indep.injective (hk1.trans hkk.symm)
      subst hk1kk
      have hn2 : k2 ≠ k3 := by
        intro h; apply hG2P3; rw [← hk2, h, hk3]
      have hne' := tile_adj_ne S iW k1 k2 k3 hk12 hkk3 hn2
      apply hne'
      rw [hk1, hk2, hk3, hPG, hlen]
    · exact congruentDissection_no_double_gamma D α β γ hαβ hαγ hαπ hα0.ne' hβγ hβπ hβ0.ne' hγπ hγ0
        Real.pi_ne_zero hγdef hrel S.hirr S.hα' S.hβ' S.hγ' hfront hnv iW i3 hWi hW hγ3

end Erdos634.LaczJunction.Walk

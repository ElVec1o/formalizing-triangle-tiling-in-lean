import Erdos634.Draft.LaczFormalFanFill
import Erdos634.Draft.LaczFormalW2Main

/-!
# Rule W2: tiles at a boundary point (`{α, β, γ}` figure), first wedge lemma

Erdős #634, band program, rule W2 (`PROOF_W2.md`).  Credit: AI assistant (item 3, band program), Laczkovich (DCG 48
(2012), Sect. 4), Beeson–Roșu, Beeson, Paliy.  UNAUDITED.
-/

namespace Erdos634.LaczJunction.Walk

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Grammar
open Erdos634.Draft.LaczFormal.Graph Erdos634.Geometry.Dissection Erdos634.VertexFigureReal

variable {N : ℕ}

/-- **The tiles through a boundary point presenting `γ` and `α`:** exactly three tiles, the third with angle `β`. -/
theorem boundary_three_tiles {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r) {v : Plane} (hv : v ∈ frontier D.target.carrier)
    (hnv : v ∉ Set.range D.target.pts) (i0 i1 : Fin N)
    (h0 : (D.tile i0).localAngle v = γ) (h1 : (D.tile i1).localAngle v = α) :
    ∃ iU : Fin N, (D.tile iU).localAngle v = β ∧ iU ≠ i0 ∧ iU ≠ i1 ∧ i0 ≠ i1 ∧
      ∀ j, v ∈ (D.tile j).carrier → j = i0 ∨ j = i1 ∨ j = iU := by
  classical
  obtain ⟨hαβ, hβγ, hαγ, -, -, -⟩ := BandSetup.distinct S
  have hα0 := S.hα0
  have hβ0 := S.hβ0
  have hγdef := S.hγdef
  have hrel := S.hrel
  have hαπ : α ≠ Real.pi := by intro h; linarith
  have hβπ : β ≠ Real.pi := by intro h; linarith
  have hγπ : γ ≠ Real.pi := by intro h; rw [hγdef] at h; linarith
  have hfig := congruentDissection_boundary_figure_cases_at_vertex D α β γ hαβ hαγ hαπ hα0.ne' hβγ hβπ hβ0.ne'
    hγπ (by rw [hγdef]; intro h; linarith) Real.pi_ne_zero hγdef hrel S.hirr S.hα' S.hβ' S.hγ' hv hnv i0
    (Or.inr (Or.inr h0))
  have hmem : ∀ (x : ℝ) (i : Fin N), (D.tile i).localAngle v = x →
      i ∈ ({i | (D.tile i).localAngle v = x} : Finset (Fin N)) := by
    intro x i h; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h
  have hc : ({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card = 1 ∧
      ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card = 1 ∧
      ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card = 1 := by
    rcases hfig with ⟨_, _, hg0⟩ | h
    · have := hmem γ i0 h0
      rw [Finset.card_eq_zero.mp hg0] at this; simp at this
    · exact h
  obtain ⟨hca, hcb, hcg⟩ := hc
  obtain ⟨ia, hia⟩ := Finset.card_eq_one.mp hca
  obtain ⟨ib, hib⟩ := Finset.card_eq_one.mp hcb
  obtain ⟨ig, hig⟩ := Finset.card_eq_one.mp hcg
  have e1 : i1 = ia := by have := hmem α i1 h1; rw [hia] at this; simpa using this
  have e0 : i0 = ig := by have := hmem γ i0 h0; rw [hig] at this; simpa using this
  have hbm : ib ∈ ({i | (D.tile i).localAngle v = β} : Finset (Fin N)) := by rw [hib]; simp
  have hbang : (D.tile ib).localAngle v = β := by simpa using hbm
  have hne01 : i0 ≠ i1 := by
    intro h
    have : (D.tile i0).localAngle v = α := h ▸ h1
    rw [h0] at this; exact hαγ this.symm
  have hnb0 : ib ≠ i0 := by
    intro h; have : (D.tile i0).localAngle v = β := h ▸ hbang
    rw [h0] at this; exact hβγ this.symm
  have hnb1 : ib ≠ i1 := by
    intro h; have : (D.tile i1).localAngle v = β := h ▸ hbang
    rw [h1] at this; exact hαβ this
  refine ⟨ib, hbang, hnb0, hnb1, hne01, ?_⟩
  intro j hj
  -- the angle sum excludes a straight tile
  have hvals := congruentDissection_localAngle_mem_boundary D α β γ S.hα' S.hβ' S.hγ' hv hnv j
  have hmult := boundary_multiplicities_cards D.toDissection α β γ hαβ hαγ hαπ hα0.ne' hβγ hβπ hβ0.ne'
    hγπ (by rw [hγdef]; intro h; linarith) Real.pi_ne_zero hv hnv
    (fun i => congruentDissection_localAngle_mem_boundary D α β γ S.hα' S.hβ' S.hγ' hv hnv i)
  rw [hca, hcb, hcg] at hmult
  have hnz := Erdos634.MarchFlank.localAngle_ne_zero_of_mem (D.tile j) hj
  simp only [Finset.mem_insert, Finset.mem_singleton] at hvals
  rcases hvals with h | h | h | h | h
  · right; left
    have := hmem α j h; rw [hia] at this
    rw [e1]; simpa using this
  · right; right
    have := hmem β j h; rw [hib] at this; simpa using this
  · left
    have := hmem γ j h; rw [hig] at this
    rw [e0]; simpa using this
  · exfalso
    have hpc : ({i | (D.tile i).localAngle v = Real.pi} : Finset (Fin N)).card ≠ 0 := by
      have := hmem Real.pi j h
      intro h0'; rw [Finset.card_eq_zero.mp h0'] at this; simp at this
    have hpc1 : (1 : ℝ) ≤ (({i | (D.tile i).localAngle v = Real.pi} : Finset (Fin N)).card : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hpc
    push_cast at hmult
    nlinarith [Real.pi_pos]
  · exact absurd h hnz

end Erdos634.LaczJunction.Walk

import Erdos634.Draft.LaczFormalMJChord

/-!
# Vertex figures by counting (interior and boundary points), for the induction `M(j)`

Erdős #634, base-`β` band, rule `M(j)`.  Credit: AI assistant (item 3, band program), Beeson–Roșu (vertex figures,
Lemma 28), Beeson, Laczkovich, Paliy.  UNAUDITED.  Axiom-clean; no `sorry`.

`cnt D v θ` is the number of tiles whose local angle at `v` is `θ`.
* `ifig`: at an interior point of the target the counts `(α, β, γ, π, 2π)` form one of the figures
  `{6α,4β}, {4α,3β,γ}, {2α,2β,2γ}, {β,3γ}`, `π + {3α,2β}`, `π + {α,β,γ}`, `π + π`, `2π`.
* `bfig`: at a frontier point which is not a target vertex: `π`, or `{3α,2β}`, or `{α,β,γ}`.
* `cnt_ge_one`, `cnt_ge_two`, `cnt_ge_three`: lower bounds from explicit distinct tiles.
-/

namespace Erdos634.LaczMJ

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Walk
  Erdos634.LaczJunction.Grammar Erdos634.VertexFigureReal Erdos634.Geometry.Dissection

variable {N : ℕ}

/-- The number of tiles whose local angle at `v` equals `θ`. -/
noncomputable def cnt (D : Dissection N) (v : Plane) (θ : ℝ) : ℕ :=
  open Classical in ({i | (D.tile i).localAngle v = θ} : Finset (Fin N)).card

theorem cnt_ge_one {D : Dissection N} {v : Plane} {θ : ℝ} {i : Fin N} (h : (D.tile i).localAngle v = θ) :
    1 ≤ cnt D v θ := by
  classical
  unfold cnt
  exact Finset.card_pos.mpr ⟨i, by simp [h]⟩

theorem cnt_ge_two {D : Dissection N} {v : Plane} {θ : ℝ} {i j : Fin N} (hij : i ≠ j)
    (hi : (D.tile i).localAngle v = θ) (hj : (D.tile j).localAngle v = θ) : 2 ≤ cnt D v θ := by
  classical
  unfold cnt
  exact Finset.one_lt_card.mpr ⟨i, by simp [hi], j, by simp [hj], hij⟩

theorem cnt_ge_three {D : Dissection N} {v : Plane} {θ : ℝ} {i j k : Fin N} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (hi : (D.tile i).localAngle v = θ) (hj : (D.tile j).localAngle v = θ)
    (hk : (D.tile k).localAngle v = θ) : 3 ≤ cnt D v θ := by
  classical
  unfold cnt
  have : ({i, j, k} : Finset (Fin N)) ⊆ ({i | (D.tile i).localAngle v = θ} : Finset (Fin N)) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl <;> assumption
  have h3 : ({i, j, k} : Finset (Fin N)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hij, hik]), Finset.card_insert_of_notMem (by simp [hjk]),
      Finset.card_singleton]
  calc 3 = ({i, j, k} : Finset (Fin N)).card := h3.symm
    _ ≤ _ := Finset.card_le_card this

variable {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}

/-- Inequalities between the angles and `π`, `2π`, `0`. -/
theorem cnt_eq_of_one {D : Dissection N} {v : Plane} {θ : ℝ} (h : cnt D v θ = 1) {i j : Fin N}
    (hi : (D.tile i).localAngle v = θ) (hj : (D.tile j).localAngle v = θ) : i = j := by
  classical
  unfold cnt at h
  have := Finset.card_le_one.mp h.le i (by simp [hi]) j (by simp [hj])
  exact this

theorem ang_ne (S : BandSetup D e f α β γ p q r) :
    α ≠ Real.pi ∧ β ≠ Real.pi ∧ γ ≠ Real.pi ∧ α ≠ 2 * Real.pi ∧ β ≠ 2 * Real.pi ∧ γ ≠ 2 * Real.pi ∧
      α ≠ 0 ∧ β ≠ 0 ∧ γ ≠ 0 := by
  have h1 := S.hα0
  have h2 := S.hβ0
  have h3 := S.hγdef
  have h4 := S.hrel
  have hpi := Real.pi_pos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, h1.ne', h2.ne', ?_⟩ <;> intro h <;> nlinarith

set_option maxHeartbeats 1000000 in
/-- **Interior vertex figures.** -/
theorem ifig (S : BandSetup D e f α β γ p q r) {v : Plane} (hv : v ∈ interior D.target.carrier) :
    (cnt D.toDissection v Real.pi = 0 ∧ cnt D.toDissection v (2 * Real.pi) = 0 ∧
      ((cnt D.toDissection v α = 6 ∧ cnt D.toDissection v β = 4 ∧ cnt D.toDissection v γ = 0) ∨
       (cnt D.toDissection v α = 4 ∧ cnt D.toDissection v β = 3 ∧ cnt D.toDissection v γ = 1) ∨
       (cnt D.toDissection v α = 2 ∧ cnt D.toDissection v β = 2 ∧ cnt D.toDissection v γ = 2) ∨
       (cnt D.toDissection v α = 0 ∧ cnt D.toDissection v β = 1 ∧ cnt D.toDissection v γ = 3))) ∨
    (cnt D.toDissection v Real.pi = 1 ∧ cnt D.toDissection v (2 * Real.pi) = 0 ∧
      ((cnt D.toDissection v α = 3 ∧ cnt D.toDissection v β = 2 ∧ cnt D.toDissection v γ = 0) ∨
       (cnt D.toDissection v α = 1 ∧ cnt D.toDissection v β = 1 ∧ cnt D.toDissection v γ = 1))) ∨
    (cnt D.toDissection v Real.pi = 2 ∧ cnt D.toDissection v (2 * Real.pi) = 0 ∧
      cnt D.toDissection v α = 0 ∧ cnt D.toDissection v β = 0 ∧ cnt D.toDissection v γ = 0) ∨
    (cnt D.toDissection v (2 * Real.pi) = 1 ∧ cnt D.toDissection v Real.pi = 0 ∧
      cnt D.toDissection v α = 0 ∧ cnt D.toDissection v β = 0 ∧ cnt D.toDissection v γ = 0) := by
  classical
  obtain ⟨hapi, hbpi, hgpi, ha2, hb2, hg2, ha0, hb0, hg0⟩ := ang_ne S
  obtain ⟨hαβ, hβγ, hαγ, -, -, -⟩ := BandSetup.distinct S
  have hpi := Real.pi_pos
  have hvals := fun i => interior_localAngle_mem D.toDissection α β γ
    (congruentDissection_hcorners D α β γ S.hα' S.hβ' S.hγ') v i
  have hsum := interior_multiplicities_cards D.toDissection α β γ hαβ hαγ hapi ha2 ha0 hβγ hbpi hb2 hb0
    hgpi hg2 hg0 (by intro h; linarith) hpi.ne' (by positivity) hv hvals
  have := interior_figure_cases_gen S.hγdef S.hrel S.hirr _ _ _ _ _ hsum
  unfold cnt
  rcases this with ⟨hu, hp, hq, hr, hs⟩ | ⟨hu, hs, hp, hq, hr⟩ | ⟨hu, hs, hc⟩ | ⟨hu, hs, hc⟩
  · exact Or.inr (Or.inr (Or.inr ⟨hu, hs, hp, hq, hr⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨hs, hu, hp, hq, hr⟩))
  · exact Or.inr (Or.inl ⟨hs, hu, hc⟩)
  · exact Or.inl ⟨hs, hu, hc⟩


/-- **Boundary vertex figures** (frontier points that are not target vertices). -/
theorem bfig (S : BandSetup D e f α β γ p q r) {v : Plane} (hv : v ∈ frontier D.target.carrier)
    (hnv : v ∉ Set.range D.target.pts) :
    (cnt D.toDissection v Real.pi = 1 ∧ cnt D.toDissection v α = 0 ∧ cnt D.toDissection v β = 0 ∧
        cnt D.toDissection v γ = 0) ∨
    (cnt D.toDissection v Real.pi = 0 ∧ cnt D.toDissection v α = 3 ∧ cnt D.toDissection v β = 2 ∧
        cnt D.toDissection v γ = 0) ∨
    (cnt D.toDissection v Real.pi = 0 ∧ cnt D.toDissection v α = 1 ∧ cnt D.toDissection v β = 1 ∧
        cnt D.toDissection v γ = 1) := by
  classical
  obtain ⟨hapi, hbpi, hgpi, ha2, hb2, hg2, ha0, hb0, hg0⟩ := ang_ne S
  obtain ⟨hαβ, hβγ, hαγ, -, -, -⟩ := BandSetup.distinct S
  have hpi := Real.pi_pos
  have hvals := fun i => localAngle_mem D.toDissection α β γ hv hnv
    (congruentDissection_hcorners D α β γ S.hα' S.hβ' S.hγ') i
  have hsum := boundary_multiplicities_cards D.toDissection α β γ hαβ hαγ hapi ha0 hβγ hbpi hb0
    hgpi hg0 hpi.ne' hv hnv hvals
  have := boundary_figure_cases S.hγdef S.hrel S.hirr _ _ _ _ hsum
  unfold cnt
  rcases this with ⟨hs, hp, hq, hr⟩ | ⟨hs, hc⟩
  · exact Or.inl ⟨hs, hp, hq, hr⟩
  · rcases hc with ⟨hp, hq, hr⟩ | ⟨hp, hq, hr⟩
    · exact Or.inr (Or.inl ⟨hs, hp, hq, hr⟩)
    · exact Or.inr (Or.inr ⟨hs, hp, hq, hr⟩)

end Erdos634.LaczMJ

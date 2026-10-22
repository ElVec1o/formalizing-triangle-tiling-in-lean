-- Draft/LaczFormalRG4Comb.lean -- Case IV: the purely combinatorial core of Subcase IVa.  Data: for each edge `i` of the polygon the types (tail, head) of the first tile of the walk
-- along the edge (`ft i`, `fh i`) and of the last tile (`lt i`, `lh i`); the four rules R1, R1', R2, R3 along an edge; the classification of each vertex (shapes S1a, S1b, S2a, S2b, S2c).
-- Conclusion: three consecutive vertices with angles `pi/3, 2 pi/3, pi/3` (shape pattern (S1a, S2a, S1a) or (S1b, S2b, S1b)).  This is the finite case analysis of Sect. 8.1.
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 8.1), Beeson, Beeson-Zhang.
import Mathlib.Tactic

namespace Erdos634.Draft.LaczFormal.RG

theorem fin_e12 (M : ℕ) [NeZero M] (e : Fin M) : e + 1 + 1 = e + 2 := by simp [add_assoc, Fin.ext_iff, Fin.val_add]
theorem fin_e23 (M : ℕ) [NeZero M] (e : Fin M) : e + 2 + 1 = e + 3 := by simp [add_assoc, Fin.ext_iff, Fin.val_add]

section Comb

variable {M : ℕ} [NeZero M]

/-- Vertex `e+1`, one `γ` tile, out-arm `a`: out `(γ,β)`, in tile `(α,γ)`. -/
def S1a (ft fh lt lh : Fin M → Fin 3) (e : Fin M) : Prop := ft (e + 1) = 2 ∧ fh (e + 1) = 1 ∧ lh e = 2 ∧ lt e = 0
/-- Vertex `e+1`, one `γ` tile, in-arm `a`: out `(γ,α)`, in `(β,γ)`. -/
def S1b (ft fh lt lh : Fin M → Fin 3) (e : Fin M) : Prop := ft (e + 1) = 2 ∧ fh (e + 1) = 0 ∧ lh e = 2 ∧ lt e = 1
/-- Vertex `e+1`, tiles `α` (out) and `β` (in, `(γ,β)` on the line). -/
def S2a (ft fh lt lh : Fin M → Fin 3) (e : Fin M) : Prop := ft (e + 1) = 0 ∧ lh e = 1 ∧ lt e = 2
/-- Vertex `e+1`, tiles `β` (out, `(β,γ)`) and `α` (in). -/
def S2b (ft fh lt lh : Fin M → Fin 3) (e : Fin M) : Prop := ft (e + 1) = 1 ∧ fh (e + 1) = 2 ∧ lh e = 0
/-- Vertex `e+1`, tiles `γ, γ` with both outer arms `a`. -/
def S2c (ft fh lt lh : Fin M → Fin 3) (e : Fin M) : Prop := ft (e + 1) = 2 ∧ fh (e + 1) = 1 ∧ lh e = 2 ∧ lt e = 1

structure CombHyp (ft fh lt lh : Fin M → Fin 3) (ang : Fin M → ℝ) : Prop where
  hne1 : ∀ i, ft i ≠ fh i
  hne2 : ∀ i, lt i ≠ lh i
  R1 : ∀ i, ((ft i = 1 ∧ fh i = 2) ∨ (ft i = 2 ∧ fh i = 1)) → lt i = ft i ∧ lh i = fh i
  R1' : ∀ i, ((lt i = 1 ∧ lh i = 2) ∨ (lt i = 2 ∧ lh i = 1)) → ft i = lt i ∧ fh i = lh i
  R2 : ∀ i, ft i = 0 → lt i = 0
  R3 : ∀ i, lh i = 0 → fh i = 0
  VC : ∀ e, (S1a ft fh lt lh e ∧ ang e = Real.pi / 3) ∨ (S1b ft fh lt lh e ∧ ang e = Real.pi / 3) ∨
    (S2a ft fh lt lh e ∧ ang e = 2 * Real.pi / 3) ∨ (S2b ft fh lt lh e ∧ ang e = 2 * Real.pi / 3) ∨ (S2c ft fh lt lh e ∧ ang e = 2 * Real.pi / 3)

variable {ft fh lt lh : Fin M → Fin 3} {ang : Fin M → ℝ}

theorem CombHyp.lt0 (H : CombHyp ft fh lt lh ang) {e : Fin M} (h : lt e = 0) : S1a ft fh lt lh e := by
  have hn := H.hne2 e
  rcases H.VC e with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
  · exact h1
  · exfalso; obtain ⟨-, -, -, h4⟩ := h1; rw [h] at h4; exact absurd h4 (by decide)
  · exfalso; obtain ⟨-, -, h4⟩ := h1; rw [h] at h4; exact absurd h4 (by decide)
  · exfalso; obtain ⟨-, -, h4⟩ := h1; exact hn (by rw [h, h4])
  · exfalso; obtain ⟨-, -, -, h4⟩ := h1; rw [h] at h4; exact absurd h4 (by decide)

theorem CombHyp.lh1 (H : CombHyp ft fh lt lh ang) {e : Fin M} (h : lh e = 1) : S2a ft fh lt lh e := by
  rcases H.VC e with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
  · exfalso; obtain ⟨-, -, h3, -⟩ := h1; rw [h] at h3; exact absurd h3 (by decide)
  · exfalso; obtain ⟨-, -, h3, -⟩ := h1; rw [h] at h3; exact absurd h3 (by decide)
  · exact h1
  · exfalso; obtain ⟨-, -, h3⟩ := h1; rw [h] at h3; exact absurd h3 (by decide)
  · exfalso; obtain ⟨-, -, h3, -⟩ := h1; rw [h] at h3; exact absurd h3 (by decide)

theorem CombHyp.ft1 (H : CombHyp ft fh lt lh ang) {e : Fin M} (h : ft (e + 1) = 1) : S2b ft fh lt lh e := by
  rcases H.VC e with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
  · exfalso; obtain ⟨h2, -⟩ := h1; rw [h] at h2; exact absurd h2 (by decide)
  · exfalso; obtain ⟨h2, -⟩ := h1; rw [h] at h2; exact absurd h2 (by decide)
  · exfalso; obtain ⟨h2, -⟩ := h1; rw [h] at h2; exact absurd h2 (by decide)
  · exact h1
  · exfalso; obtain ⟨h2, -⟩ := h1; rw [h] at h2; exact absurd h2 (by decide)

theorem CombHyp.fh0 (H : CombHyp ft fh lt lh ang) {e : Fin M} (h : fh (e + 1) = 0) : S1b ft fh lt lh e := by
  have hn := H.hne1 (e + 1)
  rcases H.VC e with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
  · exfalso; obtain ⟨-, h2, -⟩ := h1; rw [h] at h2; exact absurd h2 (by decide)
  · exact h1
  · exfalso; obtain ⟨h2, -⟩ := h1; exact hn (by rw [h, h2])
  · exfalso; obtain ⟨-, h2, -⟩ := h1; rw [h] at h2; exact absurd h2 (by decide)
  · exfalso; obtain ⟨-, h2, -⟩ := h1; rw [h] at h2; exact absurd h2 (by decide)

/-- From `S1a e`: `S2a (e+1)` and `S1a (e+2)`. -/
theorem CombHyp.step_a (H : CombHyp ft fh lt lh ang) {e : Fin M} (h : S1a ft fh lt lh e) :
    S2a ft fh lt lh (e + 1) ∧ S1a ft fh lt lh (e + 2) := by
  obtain ⟨h1, h2, -, -⟩ := h
  have r1 := H.R1 (e + 1) (Or.inr ⟨h1, h2⟩)
  have s2 := H.lh1 (e := e + 1) (by rw [r1.2, h2])
  have e12 : e + 1 + 1 = e + 2 := fin_e12 M e
  have r2 := H.R2 (e + 2) (by rw [← e12]; exact s2.1)
  exact ⟨s2, H.lt0 r2⟩

/-- From `S1b (e+2)`: `S2b (e+1)` and `S1b e`. -/
theorem CombHyp.step_b (H : CombHyp ft fh lt lh ang) {e : Fin M} (h : S1b ft fh lt lh (e + 2)) :
    S2b ft fh lt lh (e + 1) ∧ S1b ft fh lt lh e := by
  obtain ⟨-, -, h3, h4⟩ := h
  have e12 : e + 1 + 1 = e + 2 := fin_e12 M e
  have r1 := H.R1' (e + 2) (Or.inl ⟨h4, h3⟩)
  have s2 := H.ft1 (e := e + 1) (by rw [e12, r1.1, h4])
  have r3 := H.R3 (e + 1) s2.2.2
  exact ⟨s2, H.fh0 r3⟩

/-- There is a vertex of shape S1a or S1b. -/
theorem CombHyp.exists_E1 (H : CombHyp ft fh lt lh ang) : ∃ e, S1a ft fh lt lh e ∨ S1b ft fh lt lh e := by
  have e12 : ∀ e : Fin M, e + 1 + 1 = e + 2 := fun e => fin_e12 M e
  have e13 : ∀ e : Fin M, e + 2 + 1 = e + 3 := fun e => fin_e23 M e
  -- the case S2a e0 gives S1a (e0 + 1)
  have fromS2a : ∀ e : Fin M, S2a ft fh lt lh e → ∃ e', S1a ft fh lt lh e' ∨ S1b ft fh lt lh e' := by
    intro e hs
    have r2 := H.R2 (e + 1) hs.1
    exact ⟨e + 1, Or.inl (H.lt0 r2)⟩
  have fromS2c : ∀ e : Fin M, S2c ft fh lt lh e → ∃ e', S1a ft fh lt lh e' ∨ S1b ft fh lt lh e' := by
    intro e hs
    obtain ⟨h1, h2, -, -⟩ := hs
    have r1 := H.R1 (e + 1) (Or.inr ⟨h1, h2⟩)
    exact fromS2a (e + 1) (H.lh1 (by rw [r1.2, h2]))
  rcases H.VC 0 with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
  · exact ⟨0, Or.inl h1⟩
  · exact ⟨0, Or.inr h1⟩
  · exact fromS2a 0 h1
  · obtain ⟨h2, h3, -⟩ := h1
    have r1 := H.R1 (0 + 1) (Or.inl ⟨h2, h3⟩)
    rcases H.VC (0 + 1) with ⟨g, -⟩ | ⟨g, -⟩ | ⟨g, -⟩ | ⟨g, -⟩ | ⟨g, -⟩
    · exfalso; obtain ⟨-, -, -, g4⟩ := g; rw [r1.1, h2] at g4; exact absurd g4 (by decide)
    · exact ⟨0 + 1, Or.inr g⟩
    · exfalso; obtain ⟨-, -, g3⟩ := g; rw [r1.1, h2] at g3; exact absurd g3 (by decide)
    · exfalso; obtain ⟨-, -, g3⟩ := g; rw [r1.2, h3] at g3; exact absurd g3 (by decide)
    · exact fromS2c _ g
  · exact fromS2c 0 h1

/-- **The combinatorial core of Subcase IVa.** -/
theorem CombHyp.triple (H : CombHyp ft fh lt lh ang) :
    ∃ e, (S1a ft fh lt lh e ∧ S2a ft fh lt lh (e + 1) ∧ S1a ft fh lt lh (e + 2)) ∨
      (S1b ft fh lt lh e ∧ S2b ft fh lt lh (e + 1) ∧ S1b ft fh lt lh (e + 2)) := by
  obtain ⟨e, h | h⟩ := H.exists_E1
  · exact ⟨e, Or.inl ⟨h, H.step_a h⟩⟩
  · refine ⟨e - 2, Or.inr ?_⟩
    have he : e - 2 + 2 = e := by rw [sub_add_cancel]
    rw [he]
    have := H.step_b (e := e - 2) (by rw [he]; exact h)
    exact ⟨this.2, this.1, h⟩

/-- A vertex of shape S1a or S1b has angle `π/3`; S2a, S2b, S2c have angle `2π/3`. -/
theorem CombHyp.ang_E1 (H : CombHyp ft fh lt lh ang) {e : Fin M} (h : S1a ft fh lt lh e ∨ S1b ft fh lt lh e) : ang e = Real.pi / 3 := by
  rcases H.VC e with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact h2
  · exact h2
  · exfalso; obtain ⟨a1, -, -⟩ := h1
    rcases h with ⟨b1, -⟩ | ⟨b1, -⟩ <;> (rw [b1] at a1; exact absurd a1 (by decide))
  · exfalso; obtain ⟨a1, -⟩ := h1
    rcases h with ⟨b1, -⟩ | ⟨b1, -⟩ <;> (rw [b1] at a1; exact absurd a1 (by decide))
  · exfalso; obtain ⟨-, a2, -, a4⟩ := h1
    rcases h with ⟨-, -, -, b4⟩ | ⟨-, b2, -, -⟩
    · rw [b4] at a4; exact absurd a4 (by decide)
    · rw [b2] at a2; exact absurd a2 (by decide)

theorem CombHyp.ang_S2a (H : CombHyp ft fh lt lh ang) {e : Fin M} (h : S2a ft fh lt lh e) : ang e = 2 * Real.pi / 3 := by
  rcases H.VC e with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exfalso; obtain ⟨a1, -⟩ := h; obtain ⟨b1, -⟩ := h1; rw [b1] at a1; exact absurd a1 (by decide)
  · exfalso; obtain ⟨a1, -⟩ := h; obtain ⟨b1, -⟩ := h1; rw [b1] at a1; exact absurd a1 (by decide)
  · exact h2
  · exfalso; obtain ⟨a1, -⟩ := h; obtain ⟨b1, -⟩ := h1; rw [b1] at a1; exact absurd a1 (by decide)
  · exfalso; obtain ⟨a1, -⟩ := h; obtain ⟨b1, -⟩ := h1; rw [b1] at a1; exact absurd a1 (by decide)

theorem CombHyp.ang_S2b (H : CombHyp ft fh lt lh ang) {e : Fin M} (h : S2b ft fh lt lh e) : ang e = 2 * Real.pi / 3 := by
  rcases H.VC e with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exfalso; obtain ⟨a1, -⟩ := h; obtain ⟨b1, -⟩ := h1; rw [b1] at a1; exact absurd a1 (by decide)
  · exfalso; obtain ⟨a1, -⟩ := h; obtain ⟨b1, -⟩ := h1; rw [b1] at a1; exact absurd a1 (by decide)
  · exfalso; obtain ⟨a1, -⟩ := h; obtain ⟨b1, -⟩ := h1; rw [b1] at a1; exact absurd a1 (by decide)
  · exact h2
  · exfalso; obtain ⟨a1, -⟩ := h; obtain ⟨b1, -⟩ := h1; rw [b1] at a1; exact absurd a1 (by decide)

end Comb

end Erdos634.Draft.LaczFormal.RG

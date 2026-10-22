/-
Draft/SideRunGCornerWords.lean -- written 14 October 2026.  UNAUDITED.  In `AllThreshold`.  Module R1 (word part) of the plan for
`thm:cornerrun` (M1-M4: `Draft/SideRunGMirror.lean` ... `Draft/SideRunGMo.lean`; the geometry of the rules is in `Draft/SideRunGCornerRules.lean`).

**The word theorem for a side that starts at a corner `A'` of angle `2α` or `3α`.**  Paper: Theorem `thm:cornerrun`, proof, steps (1) and (2):
"(1) *There is no tile of type `R` on `s`* ... So in every case a later tile of type `R` exists, which is absurd on a finite side.  (2) So the first tile is `C_1`.  Let `C_1^k` be the maximal run at `A'`, on `[A', R]`; `k ≤ f − 1`.
After it comes `Q'`, `A_2`, `B_2` or `C_2`."

`Draft/SideRunWords.lean` (`SideRules`, `side_word`) is NOT reused as it stands: its rules `ra`, `rb`, `rc` are required also for the runs that START the side (`i = 0`), which is the alternative (ii) of the theorem here (a maximal
run `C1^k` from `A'` followed by `Q'`, `A2`, `B2` or `C2` is allowed), its `rQ` says only that the first tile is not `A2`, `B2` (here: it is `B1` or `C1`, `first_tile_alpha`), and its `rB` says that the last tile is `A2` or `C1` (here the
right corner may be `α + β` and the last tile may be `B2`, `C2`).  `SideRulesA` is the rule set of the side from `A'`: the runs are only those that FOLLOW a tile of type `R` (a tile showing `γ` at its right end: `A1`, `B1`), and a run
of `C2` that follows such a tile may not end the side (that is `(i')` at a right corner `α + β`).  `run_max`, `ty_cases`, `b1_gR` of `SideRunWords.lean` are reused.

CONTENTS.
* `SideRulesA n m τ`: the rules.  `rQ`: the first tile is `B1` or `C1`.  `rB`: the last tile does not show `γ` at its right end.  `rGG`: two `γ` never meet.  `ra`, `rb`, `rc`: the rules (a), (b), (c) of the paper for the runs that follow a tile of
  type `R`; in `rb` the run is followed by a tile (the side does not end with it) that does not show `γ` at its left end.
* `no_R_tile`: **step (1)**: if every run of `C1` and of `C2` is shorter than `n`, no tile of the word is of type `R`.
* `corner_word`: **steps (1) and (2)**: the word has `n` consecutive equal `c`-tiles (alternative (i)), or it begins with a maximal run `C1^k`, `1 ≤ k ≤ n − 1`, followed by the end of the word or by `A2`, `B2` or `C2`
  (alternative (ii)); `corner_word_succ`: the form `k = m ∨ (k < m ∧ τ k ≠ B1 ∧ τ k ≠ C1)` that `corner_run_mirror` consumes.

ON "B1 FIRST".  The tilings of `W_4(2,3)` have a side `AB` that starts with `B1^9` ((private working notes, not included)).  That is no counterexample: `B1` is of type `R`, and such a side carries a run of `n = 3` equal `c`-tiles (`C1^7`),
which is alternative (i).  The step "so the first tile is `C_1`" is made under the hypothesis that every run is shorter than `f`, and `no_R_tile` has that hypothesis.

WITNESSES.  `SideRulesA` is satisfiable: `exRulesA` (the word `C1^n`, `m = n`).

No sorry, no native_decide.
-/
import Erdos634.Draft.SideRunWords

open scoped Classical
set_option linter.unusedVariables false

namespace Erdos634.Draft.SideRunGA

open Erdos634.Draft.W2E1 Erdos634.Draft.W2E1.Ty Erdos634.Draft.SideRun

/-- **THE RULES OF THE SIDE FROM A CORNER `A'` OF ANGLE `2α` OR `3α`**, for a typed word `τ 0, …, τ (m − 1)`, `0 < m`, with the run bound `n`. -/
structure SideRulesA (n m : ℕ) (τ : ℕ → Ty) : Prop where
  rQ : τ 0 = B1 ∨ τ 0 = C1
  rB : ¬ (τ (m - 1)).gR
  rGG : ∀ k, k + 1 < m → (τ k).gR → ¬ (τ (k + 1)).gL
  ra : ∀ i k, 1 ≤ i → 1 ≤ k → k < n → i + k ≤ m → (∀ j, j < k → τ (i + j) = C1) → (τ (i - 1)).gR →
    i + k < m ∧ (τ (i + k) = B1 ∨ τ (i + k) = C1)
  rb : ∀ i k, 1 ≤ i → 1 ≤ k → k < n → i + k ≤ m → (∀ j, j < k → τ (i + j) = C2) → (τ (i - 1)).gR →
    i + k < m ∧ ¬ (τ (i + k)).gL
  rc : ∀ i s r, 1 ≤ i → 1 ≤ s → s < n → 1 ≤ r → r < n → i + s + r ≤ m → (∀ j, j < s → τ (i + j) = C2) →
    (∀ j, j < r → τ (i + s + j) = C1) → (τ (i - 1)).gR →
    i + s + r < m ∧ (τ (i + s + r) = B1 ∨ τ (i + s + r) = C1)

/-- **STEP (1) OF THE PROOF OF `thm:cornerrun`**: if no run of `n` equal `c`-tiles occurs, no tile of the word is of type `R` (after every tile of type `R` there is a later one: the next tile `Y` is not of type `L`; if `Y = C1` its
run is followed by `B1`; if `Y = C2` its run is followed by a tile that is not of type `L`, and by `B1` after a run of `C1`; the word is finite). -/
theorem no_R_tile (n m : ℕ) (τ : ℕ → Ty) (hm : 0 < m) (hr : SideRulesA n m τ)
    (hshort1 : ∀ p k, p + k ≤ m → (∀ j, j < k → τ (p + j) = C1) → k < n)
    (hshort2 : ∀ p k, p + k ≤ m → (∀ j, j < k → τ (p + j) = C2) → k < n) :
    ∀ i, i < m → ¬ (τ i).gR := by
  -- after every tile showing `γ` on the right there is a later such tile
  have step : ∀ p, 1 ≤ p → p ≤ m → (τ (p - 1)).gR → ∃ p', p < p' ∧ p' ≤ m ∧ (τ (p' - 1)).gR := by
    intro p hp1 hpm hp
    have hplt : p < m := by
      rcases Nat.lt_or_ge p m with h | h
      · exact h
      · exfalso
        have hpe : p = m := by omega
        rw [hpe] at hp
        exact hr.rB hp
    have hnotL : ¬ (τ p).gL := by
      have := hr.rGG (p - 1) (by omega) hp
      rwa [Nat.sub_add_cancel hp1] at this
    rcases ty_cases (τ p) with hR | hL | hC1 | hC2
    · exact ⟨p + 1, by omega, by omega, by rwa [Nat.add_sub_cancel]⟩
    · exact absurd hL hnotL
    · obtain ⟨k, hk1, hkm, hrun, hend⟩ := run_max τ C1 p m hplt hC1
      have hkn := hshort1 p k hkm hrun
      obtain ⟨hlt, hnext⟩ := hr.ra p k hp1 hk1 hkn hkm hrun hp
      have hB : τ (p + k) = B1 := by
        rcases hnext with h | h
        · exact h
        · rcases hend with h' | h'
          · omega
          · exact absurd h h'
      refine ⟨p + k + 1, by omega, by omega, ?_⟩
      rw [Nat.add_sub_cancel, hB]; exact b1_gR
    · obtain ⟨s, hs1, hsm, hrun, hend⟩ := run_max τ C2 p m hplt hC2
      have hsn := hshort2 p s hsm hrun
      obtain ⟨hslt, hZnotL⟩ := hr.rb p s hp1 hs1 hsn hsm hrun hp
      have hZne : τ (p + s) ≠ C2 := by
        rcases hend with h | h
        · omega
        · exact h
      rcases ty_cases (τ (p + s)) with hR | hL | hC1 | hC2'
      · exact ⟨p + s + 1, by omega, by omega, by rwa [Nat.add_sub_cancel]⟩
      · exact absurd hL hZnotL
      · obtain ⟨r, hr1, hrm, hrun', hend'⟩ := run_max τ C1 (p + s) m hslt hC1
        have hrn := hshort1 (p + s) r hrm hrun'
        obtain ⟨hlt, hnext⟩ := hr.rc p s r hp1 hs1 hsn hr1 hrn hrm hrun hrun' hp
        have hB : τ (p + s + r) = B1 := by
          rcases hnext with h | h
          · exact h
          · rcases hend' with h' | h'
            · omega
            · exact absurd h h'
        refine ⟨p + s + r + 1, by omega, by omega, ?_⟩
        rw [Nat.add_sub_cancel, hB]; exact b1_gR
      · exact absurd hC2' hZne
  have hall : ∀ K : ℕ, ∀ p0, 1 ≤ p0 → p0 ≤ m → (τ (p0 - 1)).gR → ∃ p, p0 + K ≤ p ∧ p ≤ m := by
    intro K
    induction K with
    | zero => intro p0 _ hpm _; exact ⟨p0, by omega, hpm⟩
    | succ K ih =>
      intro p0 hp1 hpm hg
      obtain ⟨p', hpp', hp'm, hg'⟩ := step p0 hp1 hpm hg
      obtain ⟨p, hKp, hpm'⟩ := ih p' (by omega) hp'm hg'
      exact ⟨p, by omega, hpm'⟩
  intro i hi hg
  obtain ⟨p, hp1, hp2⟩ := hall (m + 1) (i + 1) (by omega) (by omega) (by rwa [Nat.add_sub_cancel])
  omega

/-- **THE WORD THEOREM FOR THE SIDE FROM `A'`** (steps (1) and (2) of the proof of `thm:cornerrun`): either `n` consecutive tiles of type `C1` or `n` consecutive tiles of type `C2` (alternative (i), `n = f`), or the word begins with
a maximal run `C1^k`, `1 ≤ k ≤ n − 1`, followed by the end of the word or by `A2`, `B2` or `C2` (alternative (ii); `k ≥ e + 1` and the mirror image are the run lemma, `corner_run_mirror`). -/
theorem corner_word (n m : ℕ) (τ : ℕ → Ty) (hm : 0 < m) (hr : SideRulesA n m τ) :
    (∃ i, i + n ≤ m ∧ ((∀ j, j < n → τ (i + j) = C1) ∨ (∀ j, j < n → τ (i + j) = C2))) ∨
    (∃ k, 1 ≤ k ∧ k < n ∧ k ≤ m ∧ (∀ j, j < k → τ j = C1) ∧
      (k = m ∨ (k < m ∧ (τ k = A2 ∨ τ k = B2 ∨ τ k = C2)))) := by
  by_cases hrun : ∃ i, i + n ≤ m ∧ ((∀ j, j < n → τ (i + j) = C1) ∨ (∀ j, j < n → τ (i + j) = C2))
  · exact Or.inl hrun
  right
  push Not at hrun
  have hshort1 : ∀ p k, p + k ≤ m → (∀ j, j < k → τ (p + j) = C1) → k < n := by
    intro p k hpk hrunk
    by_contra hc
    push Not at hc
    obtain ⟨j, hj, hne⟩ := (hrun p (by omega)).1
    exact hne (hrunk j (by omega))
  have hshort2 : ∀ p k, p + k ≤ m → (∀ j, j < k → τ (p + j) = C2) → k < n := by
    intro p k hpk hrunk
    by_contra hc
    push Not at hc
    obtain ⟨j, hj, hne⟩ := (hrun p (by omega)).2
    exact hne (hrunk j (by omega))
  have hnoR := no_R_tile n m τ hm hr hshort1 hshort2
  -- the first tile is `C1`
  have hτ0 : τ 0 = C1 := by
    rcases hr.rQ with h | h
    · exact absurd (by rw [h]; exact b1_gR) (hnoR 0 hm)
    · exact h
  obtain ⟨k, hk1, hkm, hrunk, hend⟩ := run_max τ C1 0 m hm hτ0
  have hkn := hshort1 0 k (by omega) (by simpa using hrunk)
  refine ⟨k, hk1, hkn, by omega, by simpa using hrunk, ?_⟩
  by_cases hkm' : k = m
  · exact Or.inl hkm'
  · right
    have hlt : k < m := by omega
    refine ⟨hlt, ?_⟩
    have hk' : τ k ≠ C1 := by
      rcases hend with h | h
      · omega
      · simpa using h
    have hg := hnoR k hlt
    have key : ∀ t : Ty, t ≠ C1 → ¬ t.gR → (t = A2 ∨ t = B2 ∨ t = C2) := by
      intro t; cases t <;> decide
    exact key _ hk' hg

/-- the form of the end condition that `corner_run_mirror` and `K3G_run_end` consume -/
theorem corner_word_succ {m k : ℕ} {τ : ℕ → Ty}
    (h : k = m ∨ (k < m ∧ (τ k = A2 ∨ τ k = B2 ∨ τ k = C2))) :
    k = m ∨ (k < m ∧ τ k ≠ B1 ∧ τ k ≠ C1) := by
  rcases h with h | ⟨hlt, h⟩
  · exact Or.inl h
  · refine Or.inr ⟨hlt, ?_, ?_⟩ <;> rcases h with h | h | h <;> rw [h] <;> decide

/-- **The hypotheses of `corner_word` are satisfiable**: the word `C1^n` satisfies the rules (`m = n`, `n ≥ 1`): the run rules ask nothing of a word without a tile of type `R`. -/
theorem exRulesA (n : ℕ) (hn : 1 ≤ n) : SideRulesA n n (fun _ => C1) := by
  have hgR : ¬ (C1 : Ty).gR := by decide
  refine ⟨Or.inr rfl, hgR, ?_, ?_, ?_, ?_⟩
  · intro k _ hg
    exact absurd hg hgR
  · intro i k _ _ _ _ _ hp
    exact absurd hp hgR
  · intro i k _ _ _ _ _ hp
    exact absurd hp hgR
  · intro i s r _ _ _ _ _ _ _ _ hp
    exact absurd hp hgR

end Erdos634.Draft.SideRunGA

#print axioms Erdos634.Draft.SideRunGA.no_R_tile
#print axioms Erdos634.Draft.SideRunGA.corner_word
#print axioms Erdos634.Draft.SideRunGA.corner_word_succ
#print axioms Erdos634.Draft.SideRunGA.exRulesA

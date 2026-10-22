import Erdos634.Draft.LaczFormalALWalk
import Erdos634.Draft.LaczFormalBand

/-!
# Lemma A(j): the thick analogue of `M(j)`, as a theorem about base words of real dissections

Erdős #634, base-`β` row.  Credit: AI assistant (Lemma A(k) proposal, the `aBG^j` run rule, the threshold `j = f`),
Beeson–Roșu (the tile, Lemmas 28–37, the vertex figures), Beeson, Laczkovich (fan and chord covers), Paliy, Zhang.
UNAUDITED (a fresh-context audit must follow any claim).  Axiom-clean; no `sorry`.

`AARule_holds e f` (this file): for coprime `1 ≤ e < f`, every `CongruentDissection` of a target with `β`-corners at
`A_p, A_q` and base `[p,q]` of length `M e (3f²−e²)`, legs `M f³` (`M ≥ 2`, in fact `M ≥ 1` suffices), every base walk
with its step data, every `1 ≤ j ≤ f − 1`: the token word does NOT begin `aBG^j X` with `X ∈ {bAG, bGA, cAB, aGB}`
(left angle `α` or `γ`), and does NOT end `X aGB^j` with `X ∈ {bAG, bGA, cBA, aBG}` (the mirror at the right corner).
Proof: `AL_main` (`LaczFormalALMain`, the lattice rules `T(m)`, `A(m)` by strong induction) through the token bridge
`walk_noA`, `walk_noAm`.  The hand-proof hypothesis H4 (the chord triangle `L J D_j` lies in the target) is
discharged here by two facts: the target is a triangle (so it is convex) and the length condition `Bnd (m+1)`:
base `> j a`, left leg `> j c` (`base_gt_ja`, `leg_gt_jc`).  This is a derivation, not an assumption.

Negative control: `A_threshold_fails_at_f` (`LaczFormalAFrame`): `f b = (f−e)(a+c)`, so the arithmetic of the last
step of the induction fails at `j = f`.  (This is an arithmetic control for one step of the proof; the theorem itself
simply stops at `j ≤ f − 1` and does not assert failure at `j = f`.  That the thick witnesses realise `aBG^{Mf}` is an
observation of the scratch scripts (PROOF_A_v2 §4), not a Lean result.)
-/

namespace Erdos634.LaczAL

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Walk
  Erdos634.LaczJunction.Grammar Erdos634.Draft.LaczFormal.Graph Erdos634.LaczMJ

/-- The base is longer than `j` steps of length `a`, `j ≤ f − 1`. -/
theorem base_gt_ja (e f M j : ℕ) (he : 1 ≤ e) (hef : e < f) (hM : 1 ≤ M) (hj : j ≤ f - 1) :
    (j : ℝ) * ta e f < ((M * e * (3 * f ^ 2 - e ^ 2) : ℕ) : ℝ) := by
  have hB : e ^ 2 < f ^ 2 := Nat.pow_lt_pow_left hef (by norm_num)
  obtain ⟨A, hA⟩ : ∃ A, A = f ^ 2 := ⟨_, rfl⟩
  obtain ⟨B, hB'⟩ : ∃ B, B = e ^ 2 := ⟨_, rfl⟩
  rw [← hA, ← hB'] at hB ⊢
  have h1 : j * (e * f) < e * A := by
    have : j < f := by omega
    have h2 : j * (e * f) < f * (e * f) := Nat.mul_lt_mul_of_pos_right this (Nat.mul_pos (by omega) (by omega))
    calc j * (e * f) < f * (e * f) := h2
      _ = e * A := by rw [hA]; ring
  have h3 : e * A ≤ e * (3 * A - B) := Nat.mul_le_mul_left _ (by omega)
  have h4 : e * (3 * A - B) ≤ M * (e * (3 * A - B)) := Nat.le_mul_of_pos_left _ (by omega)
  have : j * (e * f) < M * e * (3 * A - B) := by
    calc j * (e * f) < e * A := h1
      _ ≤ e * (3 * A - B) := h3
      _ ≤ M * (e * (3 * A - B)) := h4
      _ = M * e * (3 * A - B) := by ring
  have hta : (ta e f : ℝ) = ((e * f : ℕ) : ℝ) := by simp [ta]
  rw [hta, ← Nat.cast_mul]
  exact_mod_cast this

/-- The legs are longer than `j` steps of length `c`, `j ≤ f − 1`. -/
theorem leg_gt_jc (e f M j : ℕ) (hM : 1 ≤ M) (hj : j ≤ f - 1) (hf : 1 ≤ f) :
    (j : ℝ) * tc e f < ((M * f ^ 3 : ℕ) : ℝ) := by
  have h1 : j * f ^ 2 < f * f ^ 2 := Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
  have h2 : f * f ^ 2 ≤ M * f ^ 3 := by
    calc f * f ^ 2 = 1 * f ^ 3 := by ring
      _ ≤ M * f ^ 3 := Nat.mul_le_mul_right _ hM
  have : j * f ^ 2 < M * f ^ 3 := lt_of_lt_of_le h1 h2
  have htc : (tc e f : ℝ) = ((f ^ 2 : ℕ) : ℝ) := by simp [tc]
  rw [htc, ← Nat.cast_mul]
  exact_mod_cast this

/-- **Lemma A(j), hand statement** (`PROOF_A_v2.md` §0): in the setting of a base-`β` target `T_M(e,f)`, the base walk of a
dissection does not begin `aBG^j X` (`X` with left angle `α`/`γ`) and does not end `X aGB^j`, `1 ≤ j ≤ f − 1`. -/
def AARule (e f : ℕ) : Prop :=
  1 ≤ e → e < f → Nat.Coprime e f → ∀ (N : ℕ) (D : CongruentDissection N) (α β γ : ℝ) (p q r : Fin 3),
    BandSetup D e f α β γ p q r →
    ∀ M : ℕ, 1 ≤ M →
    dist (D.target.pts p) (D.target.pts q) = ((M * e * (3 * f ^ 2 - e ^ 2) : ℕ) : ℝ) →
    dist (D.target.pts p) (D.target.pts r) = ((M * f ^ 3 : ℕ) : ℝ) →
    dist (D.target.pts q) (D.target.pts r) = ((M * f ^ 3 : ℕ) : ℝ) →
    ∀ (L : List (Fin N × Plane × Plane)),
      WalkT D.toDissection (toV2 (D.target.pts q - D.target.pts p)) (D.target.pts p)
        (D.target.pts q) L →
      (∀ x ∈ L, StepData D e f α β γ p q x) →
      ∀ j : ℕ, 1 ≤ j → j ≤ f - 1 →
        ¬ winA j (L.map (elemTok D α β)) ∧ ¬ winAm j (L.map (elemTok D α β))

/-- **Lemma A(j) is a theorem.** -/
theorem AARule_holds (e f : ℕ) : AARule e f := by
  intro he hef hcop N D α β γ p q r S M hM hbase hlegL hlegR L hL hstep j hj1 hjf
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  have hb : ((m + 1 : ℕ) : ℝ) * ta e f < dist (D.target.pts p) (D.target.pts q) := by
    rw [hbase]; exact base_gt_ja e f M (m + 1) he hef hM hjf
  have hlL : ((m + 1 : ℕ) : ℝ) * tc e f < dist (D.target.pts p) (D.target.pts r) := by
    rw [hlegL]; exact leg_gt_jc e f M (m + 1) hM hjf (by omega)
  have hlR : ((m + 1 : ℕ) : ℝ) * tc e f < dist (D.target.pts q) (D.target.pts r) := by
    rw [hlegR]; exact leg_gt_jc e f M (m + 1) hM hjf (by omega)
  exact ⟨walk_noA S hjf hb hlL hL hstep, walk_noAm S hjf hb hlR hL hstep⟩

#print axioms AARule_holds

/-- **Negative control at `j = f`.**  The arithmetic hypothesis of the hypotenuse cover (`far_positions` for the chord
`J D_s`, `l_cover`) is false at `s = f`: `f b = (f−e)(a+c)` is a second cover of `f b`. -/
theorem cover_hypothesis_fails_at_f (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f) :
    ¬ (∀ x y z : ℕ, x * ta e f + y * tb e f + z * tc e f = f * tb e f →
      (ta e f = tb e f ∨ x = 0) ∧ (tb e f = tb e f ∨ y = 0) ∧ (tc e f = tb e f ∨ z = 0)) := by
  intro H
  have h := LaczColumn.chord_second_cover e f hef
  have h3 := (H (f - e) 0 (f - e) (by rw [zero_mul, add_zero]; linarith [h])).2.2
  rcases h3 with h3 | h3
  · have hb : tb e f < tc e f := by
      unfold tb tc
      have : e ^ 2 ≥ 1 := Nat.one_le_pow _ _ he
      have : e ^ 2 < f ^ 2 := Nat.pow_lt_pow_left hef (by norm_num)
      omega
    omega
  · omega

end Erdos634.LaczAL

import Erdos634.Draft.LaczFormalMJWalk
import Erdos634.Draft.LaczFormalBand

/-!
# The band theorem, unconditional: `MRule e f` is a theorem

Erdős #634, base-`β` band.  Credit: AI assistant (item 3, band program: Band Lemma, Proposition B1, the induction `M(j)`,
Claims Z and A), Beeson–Roșu (the tile, Lemmas 28–37, the vertex figures), Beeson, Laczkovich (fans and chord covers),
Paliy, Zhang.  UNAUDITED (a fresh-context audit follows any unconditional claim).  Axiom-clean; no `sorry`.

`MRule_holds e f : MRule e f` — the hand rule `M(j)` of `PROOF_BAND.md` §3 (`1 ≤ j ≤ e`: the base word does not begin
`cBA^j X`, nor end `X cAB^j`, `X` a token with an `α`/`γ` left end) — proved from `MJ_main`
(`LaczFormalMJMain`: the lattice rules `T(m)`, `A(m)` at all levels, by strong induction on `m`) through the token
bridge `walk_noMJ`, `walk_noMJm`.  Hence `band_theorem_free`: for `e ≥ 2`, `M ≥ 2`, `f ≤ 2Me < f + e`
(coprime `e < f`) there is no `CongruentDissection` of `T_M(e,f)` by the tile `(ef, f²−e², f²)`.
-/

namespace Erdos634.LaczJunction.Walk

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Grammar
open Erdos634.Draft.LaczFormal.Graph Erdos634.LaczMJ

/-- The base is longer than `j` steps of length `c`. -/
theorem base_gt_jc (e f M j : ℕ) (he : 1 ≤ e) (hef : e < f) (hM : 2 ≤ M) (hj : j ≤ e) :
    (j : ℝ) * tc e f < ((M * e * (3 * f ^ 2 - e ^ 2) : ℕ) : ℝ) := by
  have hB : e ^ 2 < f ^ 2 := Nat.pow_lt_pow_left hef (by norm_num)
  obtain ⟨A, hA⟩ : ∃ A, A = f ^ 2 := ⟨_, rfl⟩
  obtain ⟨B, hB'⟩ : ∃ B, B = e ^ 2 := ⟨_, rfl⟩
  rw [← hA, ← hB'] at hB ⊢
  have h2 : 2 * A + 1 ≤ 3 * A - B := by omega
  have h1 : j * A ≤ e * A := Nat.mul_le_mul_right _ hj
  have h3 : e * (2 * A + 1) ≤ e * (3 * A - B) := Nat.mul_le_mul_left _ h2
  have h4 : 2 * (e * (3 * A - B)) ≤ M * (e * (3 * A - B)) := Nat.mul_le_mul_right _ hM
  have h5 : e * A < e * (2 * A + 1) := by nlinarith
  have hfin : j * A < M * e * (3 * A - B) := by
    calc j * A ≤ e * A := h1
      _ < e * (2 * A + 1) := h5
      _ ≤ e * (3 * A - B) := h3
      _ ≤ 2 * (e * (3 * A - B)) := by omega
      _ ≤ M * (e * (3 * A - B)) := h4
      _ = M * e * (3 * A - B) := by ring
  have : (tc e f : ℝ) = (A : ℝ) := by rw [hA]; simp [tc]
  rw [this]
  exact_mod_cast hfin

/-- **`M(j)` is a theorem** (`PROOF_BAND.md` §3). -/
theorem MRule_holds (e f : ℕ) : MRule e f := by
  intro he2 hab N D α β γ p q r S M hM2 hlo hhi hbase hlegL hlegR hori L hL hstep hno j hj1 hje hlj hrj
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  have hb : ((m + 1 : ℕ) : ℝ) * tc e f < dist (D.target.pts p) (D.target.pts q) := by
    rw [hbase]
    exact base_gt_jc e f M (m + 1) (by omega) S.hef hM2 hje
  exact ⟨walk_noMJ S hje hb hlj hL hstep, walk_noMJm S hje hb hrj hL hstep⟩

#print axioms MRule_holds

/-- **Negative control at `j = e + 1`.**  The one place where the bound `j ≤ e` enters the induction is the arithmetic
hypothesis of `far_positions` for the horizontal cover of length `n'·c` with `n' < e` (`h_cover`, from
`MJ_jc_unique`) and for the hypotenuse cover of length `s·b`, `s < f` (`l_cover`, from `MJ_jb_unique`).  For
`n' = e` this hypothesis is false: `e·c = f·a`, so a row of `e` `c`-edges can be replaced by `f` `a`-edges.  Hence the
proof of `M(j)` does not extend to `j = e + 1` (the engine's region mode agrees: `REGION_ALIVE` at `i = e + 1`). -/
theorem cover_hypothesis_fails_at_e (e f : ℕ) (he : 1 ≤ e) (hef : e < f) :
    ¬ (∀ x y z : ℕ, x * ta e f + y * tb e f + z * tc e f = e * tc e f →
      (ta e f = tc e f ∨ x = 0) ∧ (tb e f = tc e f ∨ y = 0) ∧ (tc e f = tc e f ∨ z = 0)) := by
  intro H
  have h := (H f 0 0 (by rw [MJ_ec_eq_fa]; ring)).1
  have hac : ta e f < tc e f := by unfold ta tc; nlinarith
  rcases h with h | h
  · omega
  · omega

#print axioms cover_hypothesis_fails_at_e

/-- **The band theorem, unconditional.**  For `e ≥ 2`, `M ≥ 2`, `f ≤ 2Me < f + e` (coprime `e < f`) there is no
`CongruentDissection` of `T_M(e,f)` (base `[p,q]` of length `M e (3f²−e²)`, legs `M f³`) by copies of
`(ef, f²−e², f²)`. -/
theorem band_theorem_free {N : ℕ} (D : CongruentDissection N) (e f M : ℕ) (he : 2 ≤ e)
    (hef : e < f) (hcop : Nat.Coprime e f) (hM2 : 2 ≤ M)
    (hsa : sideOpp D.model 0 = (ta e f : ℝ)) (hsb : sideOpp D.model 1 = (tb e f : ℝ))
    (hsc : sideOpp D.model 2 = (tc e f : ℝ))
    {p q r : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hbase : dist (D.target.pts p) (D.target.pts q) = ((M * e * (3 * f ^ 2 - e ^ 2) : ℕ) : ℝ))
    (hlegL : dist (D.target.pts p) (D.target.pts r) = ((M * f ^ 3 : ℕ) : ℝ))
    (hlegR : dist (D.target.pts q) (D.target.pts r) = ((M * f ^ 3 : ℕ) : ℝ))
    (hlo : f ≤ 2 * M * e) (hhi : 2 * M * e < f + e) : False :=
  band_theorem D e f M (MRule_holds e f) he hef hcop hM2 hsa hsb hsc hpq hpr hqr hbase hlegL hlegR hlo hhi

#print axioms band_theorem_free

end Erdos634.LaczJunction.Walk

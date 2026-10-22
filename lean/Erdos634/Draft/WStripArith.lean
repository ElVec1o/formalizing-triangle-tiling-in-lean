/-
Draft/WStripArith.lean -- written 14 October 2026.  UNAUDITED.  In `AllThreshold`.

Paper: Proposition `prop:wstrip` (b), (c): the ARITHMETIC of the strip along the side `AQ` of `W_M(e, f)`; no geometry.
Coprime `1 ≤ e < f`, tile `(a, b, c) = (e f, f^2 - e^2, f^2)`.

(i)   `strip_z_exists_iff`: an integer `z ≡ M f (mod e)` with `f ≤ z` and `z f ≤ M b` exists iff `f ≤ M (f - e)`
      (the paper's part (b); the proof of the converse is the count `x e + z f = M b`, `x ≡ M (f - e) (mod f)`, packaged as
      `count_no_b_int`, which is also the count behind `cor:thickw`(a));
(ii)  `strip_chain`: `e + 1 ≤ M (f - e)` gives `f + 1 ≤ (M + 1) (f - e)` (the step of part (c));
(iii) `no_w_below_iff_top`: the logic of part (c), for an abstract predicate `P` ("`W_M` has a tiling") with the two
      geometric inputs as hypotheses: `hstep` (the strip, part (a), at the scales with `f ≤ M (f - e)`) and `hexcl`
      (`cor:thickw`(a), at the scales with `M (f - e) ≤ e`):
      `(∀ M, 1 ≤ M → M < f → ¬ P M) ↔ ¬ P (f - 1)`.

Test of the statement of (i) before proving (outside Lean, exhaustive for `f ≤ 12` and `M ≤ 2 f + 1`, and the six cases named
in the task): no counterexample.  No sorry, no native_decide.  `#print axioms` at the foot.
-/
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.WStripArith

/-! ## Helpers (shared with `SideRunGArith`) -/

/-- `f ∣ e w` and `gcd (e, f) = 1` give `f ∣ w` (in `ℤ`). -/
theorem dvd_of_coprime_mul {e f : ℕ} (hco : Nat.Coprime e f) {w : ℤ}
    (h : (f : ℤ) ∣ (e : ℤ) * w) : (f : ℤ) ∣ w :=
  (Nat.isCoprime_iff_coprime.mpr hco.symm).dvd_of_dvd_mul_left h

/-- `f ∣ e^2 w` and `gcd (e, f) = 1` give `f ∣ w` (in `ℤ`). -/
theorem dvd_of_coprime_mul_sq {e f : ℕ} (hco : Nat.Coprime e f) {w : ℤ}
    (h : (f : ℤ) ∣ (e : ℤ) ^ 2 * w) : (f : ℤ) ∣ w := by
  apply dvd_of_coprime_mul hco
  apply dvd_of_coprime_mul hco
  have e2 : (e : ℤ) ^ 2 * w = (e : ℤ) * ((e : ℤ) * w) := by ring
  rwa [e2] at h

/-- a multiple of `f` strictly between `-f` and `f` is `0` -/
theorem dvd_eq_zero_of_lt {f w : ℤ} (hf : 0 < f) (h : f ∣ w) (h1 : -f < w) (h2 : w < f) : w = 0 := by
  obtain ⟨k, rfl⟩ := h
  have hk1 : k < 1 := by
    by_contra hc
    push_neg at hc
    nlinarith [mul_nonneg hf.le (sub_nonneg.2 hc)]
  have hk2 : -1 < k := by
    by_contra hc
    push_neg at hc
    nlinarith [mul_nonneg hf.le (show (0 : ℤ) ≤ -1 - k by linarith)]
  have hk : k = 0 := by omega
  rw [hk, mul_zero]

/-- `b = f^2 - e^2` (natural subtraction, `e < f`) as a natural number with its integer value -/
theorem exists_b {e f : ℕ} (hef : e < f) :
    ∃ b : ℕ, f ^ 2 - e ^ 2 = b ∧ (b : ℤ) = (f : ℤ) ^ 2 - (e : ℤ) ^ 2 :=
  ⟨f ^ 2 - e ^ 2, rfl, by
    rw [Nat.cast_sub (Nat.pow_le_pow_left hef.le 2), Nat.cast_pow, Nat.cast_pow]⟩

/-! ## The count without an edge `b` -/

/-- **The count on a side with no edge `b`**: if `X e + Z f = N (f^2 - e^2)` with `X ≥ 0` and `N (f - e) < f`, then
`N (f - e) ≤ X` and `Z ≤ N (f - e)`.  (Modulo `f` the equation gives `X ≡ -N e ≡ N (f - e)`; `X` is the number of edges `a`,
`Z` the number of edges `c`.) -/
theorem count_no_b_int {e f : ℕ} {N X Z : ℤ} (hef : e < f) (hco : Nat.Coprime e f)
    (hX : 0 ≤ X) (hN : N * ((f : ℤ) - e) < f)
    (h : X * e + Z * f = N * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2)) :
    N * ((f : ℤ) - e) ≤ X ∧ Z ≤ N * ((f : ℤ) - e) := by
  have hF : (0 : ℤ) < f := by omega
  have hE : (0 : ℤ) ≤ e := by omega
  have h1 : (f : ℤ) ∣ (e : ℤ) * (X + N * e) := ⟨N * f - Z, by linear_combination h⟩
  obtain ⟨t, ht⟩ := dvd_of_coprime_mul hco h1
  have ht1 : N ≤ t := by
    by_contra hlt
    push_neg at hlt
    have h3 : t ≤ N - 1 := by omega
    have h4 := mul_le_mul_of_nonneg_left h3 hF.le
    nlinarith
  have h5 := mul_le_mul_of_nonneg_left ht1 hF.le
  have hx : N * ((f : ℤ) - e) ≤ X := by nlinarith
  refine ⟨hx, ?_⟩
  have h6 := mul_le_mul_of_nonneg_right hx hE
  have h7 : Z * f ≤ (N * ((f : ℤ) - e)) * f := by nlinarith
  exact le_of_mul_le_mul_right h7 hF

/-! ## (i) the strip exists iff `M (f - e) ≥ f` -/

/-- **(i)** (paper, `prop:wstrip`(b)) An integer `z` with `z ≡ M f (mod e)`, `f ≤ z`, `z f ≤ M b` exists if and only if
`M (f - e) ≥ f`.  The statement as proposed in the task is true as written (exhaustively checked for `f ≤ 12`); the
hypothesis `2 ≤ M` is implied by `f ≤ M (f - e)`. -/
theorem strip_z_exists_iff (e f M : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) (hM : 2 ≤ M) :
    (∃ z : ℕ, z % e = (M * f) % e ∧ f ≤ z ∧ z * f ≤ M * (f ^ 2 - e ^ 2)) ↔ f ≤ M * (f - e) := by
  obtain ⟨b, hbN, hbZ⟩ := exists_b hef
  rw [hbN]
  constructor
  · rintro ⟨z, hz, hzf, hzb⟩
    by_contra hcon
    have hcon' : M * (f - e) < f := by omega
    have hz' : z ≡ M * f [MOD e] := hz
    obtain ⟨k, hk⟩ := Nat.modEq_iff_dvd.mp hz'
    push_cast at hk
    have he0 : (0 : ℤ) < e := by omega
    have hXe : (e : ℤ) * ((f : ℤ) * k - M * e) = M * b - z * f := by
      linear_combination (-(f : ℤ)) * hk - (M : ℤ) * hbZ
    have hX0 : 0 ≤ (f : ℤ) * k - M * e := by
      by_contra hneg
      push_neg at hneg
      have h1 : (e : ℤ) * ((f : ℤ) * k - M * e) < 0 := mul_neg_of_pos_of_neg he0 hneg
      have h2 : (z : ℤ) * f ≤ M * b := by exact_mod_cast hzb
      linarith
    have key : ((f : ℤ) * k - M * e) * e + (z : ℤ) * f = M * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) := by
      rw [← hbZ]
      linear_combination hXe
    have hN : (M : ℤ) * ((f : ℤ) - e) < f := by
      have hcast : ((M * (f - e) : ℕ) : ℤ) = (M : ℤ) * ((f : ℤ) - e) := by
        rw [Nat.cast_mul, Nat.cast_sub hef.le]
      rw [← hcast]
      exact_mod_cast hcon'
    obtain ⟨-, hz1⟩ := count_no_b_int (N := (M : ℤ)) (X := (f : ℤ) * k - M * e) (Z := (z : ℤ))
      hef hco hX0 hN key
    have hzf' : (f : ℤ) ≤ z := by exact_mod_cast hzf
    linarith
  · intro hMf
    obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
    obtain ⟨d, hdN⟩ : ∃ d, f - e = d := ⟨_, rfl⟩
    have hd : d + e = f := by omega
    rw [hdN] at hMf
    have hbd : b = d * (f + e) := by
      have hb : b + e ^ 2 = f ^ 2 := by
        have := Nat.pow_le_pow_left hef.le 2
        omega
      have hf2 : f ^ 2 = (d + e) ^ 2 := by rw [hd]
      have hfe : f + e = d + 2 * e := by omega
      rw [hfe]
      nlinarith [hb, hf2]
    refine ⟨f + (M' * f) % e, ?_, by omega, ?_⟩
    · have h1 : (f + M' * f % e) ≡ f + M' * f [MOD e] := Nat.ModEq.add_left f (Nat.mod_modEq _ _)
      have h2 : f + M' * f = (M' + 1) * f := by ring
      rw [h2] at h1
      exact h1
    · have hr : M' * f % e < e := Nat.mod_lt _ he
      calc (f + M' * f % e) * f ≤ (f + e) * f := Nat.mul_le_mul_right f (by omega)
        _ = f * (f + e) := by ring
        _ ≤ ((M' + 1) * d) * (f + e) := Nat.mul_le_mul_right _ hMf
        _ = (M' + 1) * (d * (f + e)) := by ring
        _ = (M' + 1) * b := by rw [hbd]

/-! ## (ii) the chain step -/

/-- **(ii)** (paper, `prop:wstrip`(c)) a scale not excluded by `M (f - e) ≤ e` admits the strip at the next scale -/
theorem strip_chain (e f M : ℕ) (he : 1 ≤ e) (hef : e < f) (h : e + 1 ≤ M * (f - e)) :
    f + 1 ≤ (M + 1) * (f - e) := by
  have h1 : (M + 1) * (f - e) = M * (f - e) + (f - e) := by rw [Nat.add_mul, Nat.one_mul]
  omega

/-! ## (iii) the logic of `prop:wstrip`(c) -/

/-- **(iii)** (paper, `prop:wstrip`(c), second statement) Let `P M` mean "`W_M(e, f)` has a tiling".  Suppose
`hstep`: for `M ≥ 2` with `f ≤ M (f - e)`, `P (M - 1)` gives `P M` (the strip of (a) with (b)), and `hexcl`: for `M ≥ 1`
with `M (f - e) ≤ e`, `¬ P M` (`cor:thickw`(a)).  Then `W_M` has no tiling at any scale `M < f` if and only if `W_{f-1}`
has none.  The hypotheses are `1 ≤ e < f` only: the edge cases `e = f - 1` (where `hexcl` already excludes every `M ≤ f - 1`)
and `f = 2` need no separate treatment. -/
theorem no_w_below_iff_top (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (P : ℕ → Prop)
    (hstep : ∀ M, 2 ≤ M → f ≤ M * (f - e) → P (M - 1) → P M)
    (hexcl : ∀ M, 1 ≤ M → M * (f - e) ≤ e → ¬ P M) :
    (∀ M, 1 ≤ M → M < f → ¬ P M) ↔ ¬ P (f - 1) := by
  constructor
  · intro h
    exact h (f - 1) (by omega) (by omega)
  · intro hnot M hM1 hMf hPM
    by_cases hlast : M = f - 1
    · subst hlast
      exact hnot hPM
    · have hbig : e + 1 ≤ M * (f - e) := by
        by_contra hc
        push_neg at hc
        exact hexcl M hM1 (by omega) hPM
      have hind : ∀ k, M + k ≤ f - 1 → P (M + k) := by
        intro k
        induction k with
        | zero => intro _; exact hPM
        | succ k ih =>
          intro hk
          have hPk : P (M + k) := ih (by omega)
          have hmul : (M + (k + 1)) * (f - e) = M * (f - e) + (k + 1) * (f - e) := Nat.add_mul _ _ _
          have hpos : f - e ≤ (k + 1) * (f - e) := Nat.le_mul_of_pos_left _ (Nat.succ_pos k)
          have hcond : f ≤ (M + (k + 1)) * (f - e) := by omega
          have e1 : M + (k + 1) - 1 = M + k := by omega
          exact hstep (M + (k + 1)) (by omega) hcond (by rw [e1]; exact hPk)
      have h := hind (f - 1 - M) (by omega)
      rw [show M + (f - 1 - M) = f - 1 from by omega] at h
      exact hnot h

/-! ## Instances: the six cases of the task, and the hypotheses of every statement are satisfied -/

example : ∃ z : ℕ, z % 2 = (2 * 5) % 2 ∧ 5 ≤ z ∧ z * 5 ≤ 2 * (5 ^ 2 - 2 ^ 2) := ⟨6, by norm_num⟩
example : ∃ z : ℕ, z % 2 = (3 * 5) % 2 ∧ 5 ≤ z ∧ z * 5 ≤ 3 * (5 ^ 2 - 2 ^ 2) := ⟨5, by norm_num⟩
example : ∃ z : ℕ, z % 1 = (2 * 4) % 1 ∧ 4 ≤ z ∧ z * 4 ≤ 2 * (4 ^ 2 - 1 ^ 2) := ⟨4, by norm_num⟩
example : ∃ z : ℕ, z % 3 = (4 * 4) % 3 ∧ 4 ≤ z ∧ z * 4 ≤ 4 * (4 ^ 2 - 3 ^ 2) := ⟨4, by norm_num⟩
/-- `(e, f, M) = (3, 5, 2)`: no `z`, by exhaustion (independent of the theorem) -/
example : ∀ z : Fin 9, ¬ (z.val % 3 = (2 * 5) % 3 ∧ 5 ≤ z.val ∧ z.val * 5 ≤ 2 * (5 ^ 2 - 3 ^ 2)) := by decide
/-- `(e, f, M) = (3, 4, 3)`: no `z`, by exhaustion (independent of the theorem) -/
example : ∀ z : Fin 9, ¬ (z.val % 3 = (3 * 4) % 3 ∧ 4 ≤ z.val ∧ z.val * 4 ≤ 3 * (4 ^ 2 - 3 ^ 2)) := by decide
example : (∃ z : ℕ, z % 2 = (2 * 5) % 2 ∧ 5 ≤ z ∧ z * 5 ≤ 2 * (5 ^ 2 - 2 ^ 2)) ↔ 5 ≤ 2 * (5 - 2) :=
  strip_z_exists_iff 2 5 2 (by norm_num) (by norm_num) (by first | decide | norm_num) (by norm_num)
example : ¬ (5 ≤ 2 * (5 - 3)) := by norm_num
example : ¬ ∃ z : ℕ, z % 3 = (2 * 5) % 3 ∧ 5 ≤ z ∧ z * 5 ≤ 2 * (5 ^ 2 - 3 ^ 2) :=
  fun h => absurd ((strip_z_exists_iff 3 5 2 (by norm_num) (by norm_num) (by first | decide | norm_num) (by norm_num)).mp h)
    (by norm_num)
example : 5 + 1 ≤ (3 + 1) * (5 - 2) := strip_chain 2 5 3 (by norm_num) (by norm_num) (by norm_num)

/-- the hypotheses of the abstract statement are satisfiable (and the statement holds): `(e, f) = (1, 3)`,
`P M := 3 ≤ M` -/
example : (∀ M : ℕ, 1 ≤ M → M < 3 → ¬ 3 ≤ M) ↔ ¬ 3 ≤ 3 - 1 :=
  no_w_below_iff_top 1 3 (by norm_num) (by norm_num) (fun M => 3 ≤ M)
    (by
      intro M h2 h3 h4
      have h5 : 3 ≤ M - 1 := h4
      show 3 ≤ M
      omega)
    (by
      intro M h1 h2 h3
      have h4 : M * 2 ≤ 1 := h2
      have h5 : 3 ≤ M := h3
      omega)

end Erdos634.Draft.WStripArith

#print axioms Erdos634.Draft.WStripArith.count_no_b_int
#print axioms Erdos634.Draft.WStripArith.strip_z_exists_iff
#print axioms Erdos634.Draft.WStripArith.strip_chain
#print axioms Erdos634.Draft.WStripArith.no_w_below_iff_top

/-
Draft/SideRunWords.lean -- Stage 0 of the formalization of the side theorem of room GAP3
((private working notes, not included)): tile `(a, b, c) = (f, f²−1, f²)`, `f ≥ 2`.

Pure arithmetic and combinatorics, no geometry.

(a) representations by the three sides (`y ≡ −T (mod f)`):
    `rep_jb`  (A1): `j·b`, `j < f`, is represented only by `b^j`;
    `rep_qc`  (A5): a representation of `q·c`, `q < f`, contains no `b`;
    `first_len_jb`, `first_len_qc`: the real forms used with the run partition (first edge + the rest);
    `rep_side`: if `x a + y b + z c = M (κ f² − 1)` and `M < f`, then `z ≤ (κ − 1) M`
    (`κ = 3`: the base of `T_M(1,f)`, `z ≤ 2M`; `κ = 2`: the side `QB` of `W_M(1,f)`, `z ≤ M`).
(b) the word theorem behind the side theorem (`side_word`): a typed side word (six types of `W2E1Words`) that
    satisfies the corner rules, "no `γ γ`", and the run rules (a), (b), (c) for runs shorter than `n` contains `n`
    consecutive `C1` or `n` consecutive `C2`.
(c) `no_side_word`: such a word cannot have total length `M (κ n² − 1)` with `(κ − 1) M < n`.

The rules are hypotheses here (`SideRules`); the geometry proves each field.  Non-vacuity: `exRules`.

Composite-N work (base-beta threshold program); not prime-case work.  No sorry, no native_decide.
-/
import Mathlib.Tactic
import Erdos634.Draft.W2E1Words

namespace Erdos634.Draft.SideRun

open Erdos634.Draft.W2E1 Erdos634.Draft.W2E1.Ty

/-! ## (a) arithmetic -/

theorem dvd_abs_lt {n m : ℤ} (hn : 0 < n) (h : n ∣ m) (h1 : -n < m) (h2 : m < n) : m = 0 := by
  obtain ⟨k, rfl⟩ := h
  have hk : k = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hk | hk
    · have hk' : k ≤ -1 := by omega
      have h3 := mul_nonneg hn.le (show (0:ℤ) ≤ -1 - k by linarith)
      nlinarith
    · have hk' : 1 ≤ k := by omega
      have h3 := mul_nonneg hn.le (show (0:ℤ) ≤ k - 1 by linarith)
      nlinarith
  rw [hk, mul_zero]

theorem b_pos_int {n : ℕ} (hn : 2 ≤ n) : (0:ℤ) < (n:ℤ) ^ 2 - 1 := by
  have hn' : (2:ℤ) ≤ n := by exact_mod_cast hn
  nlinarith

/-- (A1) `j·b`, `j < f`, is represented only by `b^j`. -/
theorem rep_jb {n x y z j : ℕ} (hn : 2 ≤ n) (hj : j < n)
    (h : (x:ℤ) * n + y * ((n:ℤ) ^ 2 - 1) + z * (n:ℤ) ^ 2 = j * ((n:ℤ) ^ 2 - 1)) :
    x = 0 ∧ y = j ∧ z = 0 := by
  have hn' : (2:ℤ) ≤ n := by exact_mod_cast hn
  have hj' : (j:ℤ) < n := by exact_mod_cast hj
  have hb := b_pos_int hn
  have hx0 : (0:ℤ) ≤ x := by positivity
  have hy0 : (0:ℤ) ≤ y := by positivity
  have hz0 : (0:ℤ) ≤ z := by positivity
  have hj0 : (0:ℤ) ≤ j := by positivity
  have hle := rep_y_le h
  have hyj : (y:ℤ) ≤ j := by
    by_contra hc
    push Not at hc
    have h1 : (j:ℤ) + 1 ≤ y := by omega
    have h2 := mul_le_mul_of_nonneg_right h1 hb.le
    nlinarith
  have hd := rep_dvd h
  have hd' : (n:ℤ) ∣ (y:ℤ) - j := by
    have e : (y:ℤ) - j = ((y:ℤ) + j * ((n:ℤ) ^ 2 - 1)) - (n:ℤ) * (j * n) := by ring
    rw [e]; exact dvd_sub hd (dvd_mul_right _ _)
  have hy : (y:ℤ) = j := by
    have := dvd_abs_lt (by linarith) hd' (by linarith) (by linarith)
    linarith
  rw [hy] at h
  have h3 : (x:ℤ) * n + z * (n:ℤ) ^ 2 = 0 := by linarith
  have hxn : (0:ℤ) ≤ (x:ℤ) * n := by positivity
  have hzn : (0:ℤ) ≤ (z:ℤ) * (n:ℤ) ^ 2 := by positivity
  refine ⟨nat_zero_of_mul (by linarith : (0:ℤ) < n) (by linarith), by exact_mod_cast hy,
    nat_zero_of_mul (by nlinarith : (0:ℤ) < (n:ℤ) ^ 2) (by linarith)⟩

/-- (A5) a representation of `q·c`, `q < f`, contains no `b`. -/
theorem rep_qc {n x y z q : ℕ} (hn : 2 ≤ n) (hq : q < n)
    (h : (x:ℤ) * n + y * ((n:ℤ) ^ 2 - 1) + z * (n:ℤ) ^ 2 = q * (n:ℤ) ^ 2) : y = 0 := by
  have hn' : (2:ℤ) ≤ n := by exact_mod_cast hn
  have hq' : (q:ℤ) + 1 ≤ n := by exact_mod_cast hq
  have hb := b_pos_int hn
  have hy0 : (0:ℤ) ≤ y := by positivity
  have hq0 : (0:ℤ) ≤ q := by positivity
  have hle := rep_y_le h
  have hyn : (y:ℤ) < n := by
    by_contra hc
    push Not at hc
    have h2 := mul_le_mul_of_nonneg_right hc hb.le
    have h3 := mul_le_mul_of_nonneg_right hq' (by nlinarith : (0:ℤ) ≤ (n:ℤ) ^ 2)
    nlinarith
  have hd := rep_dvd h
  have hd' : (n:ℤ) ∣ (y:ℤ) := by
    have e : (y:ℤ) = ((y:ℤ) + q * (n:ℤ) ^ 2) - (n:ℤ) * (q * n) := by ring
    rw [e]; exact dvd_sub hd (dvd_mul_right _ _)
  have := dvd_abs_lt (by linarith) hd' (by linarith) hyn
  exact_mod_cast this

theorem cast_rep' {n x y z : ℕ} {T : ℤ}
    (h : (x:ℝ) * n + y * ((n:ℝ) ^ 2 - 1) + z * (n:ℝ) ^ 2 = (T:ℝ)) :
    (x:ℤ) * n + y * ((n:ℤ) ^ 2 - 1) + z * (n:ℤ) ^ 2 = T := by
  exact_mod_cast h

/-- **The first edge of a clamped run of length `j·b`, `1 ≤ j < f`, is a `b`-edge.** -/
theorem first_len_jb {n : ℕ} (hn : 2 ≤ n) {j : ℕ} (hj : j < n) {ℓ : ℝ} {x y z : ℕ}
    (hℓ : ℓ = (n:ℝ) ∨ ℓ = (n:ℝ) ^ 2 - 1 ∨ ℓ = (n:ℝ) ^ 2)
    (h : ℓ + ((x:ℝ) * n + y * ((n:ℝ) ^ 2 - 1) + z * (n:ℝ) ^ 2) = (j:ℝ) * ((n:ℝ) ^ 2 - 1)) :
    ℓ = (n:ℝ) ^ 2 - 1 := by
  rcases hℓ with h1 | h1 | h1
  · exfalso
    have := (rep_jb hn hj (cast_rep' (x := x + 1) (y := y) (z := z) (T := (j:ℤ) * ((n:ℤ) ^ 2 - 1))
      (by push_cast; linarith))).1
    omega
  · exact h1
  · exfalso
    have := (rep_jb hn hj (cast_rep' (x := x) (y := y) (z := z + 1) (T := (j:ℤ) * ((n:ℤ) ^ 2 - 1))
      (by push_cast; linarith))).2.2
    omega

/-- **An edge of a clamped run of length `q·c`, `q < f`, is not a `b`-edge.** -/
theorem first_len_qc {n : ℕ} (hn : 2 ≤ n) {q : ℕ} (hq : q < n) {ℓ : ℝ} {x y z : ℕ}
    (h : ℓ + ((x:ℝ) * n + y * ((n:ℝ) ^ 2 - 1) + z * (n:ℝ) ^ 2) = (q:ℝ) * (n:ℝ) ^ 2) :
    ℓ ≠ (n:ℝ) ^ 2 - 1 := by
  intro h1
  have := rep_qc hn hq (cast_rep' (x := x) (y := y + 1) (z := z) (T := (q:ℤ) * (n:ℤ) ^ 2)
    (by push_cast; linarith))
  omega

/-- **The letters of a side of length `M (κ f² − 1)`, `M < f`**: at least `M` letters `b`, hence at most
`(κ − 1) M` letters `c`. -/
theorem rep_side {n x y z M κ : ℕ} (hn : 2 ≤ n) (hM : M < n)
    (h : (x:ℤ) * n + y * ((n:ℤ) ^ 2 - 1) + z * (n:ℤ) ^ 2 = M * (κ * (n:ℤ) ^ 2 - 1)) :
    (z:ℤ) + M ≤ κ * M := by
  have hn' : (2:ℤ) ≤ n := by exact_mod_cast hn
  have hM' : (M:ℤ) < n := by exact_mod_cast hM
  have hb := b_pos_int hn
  have hx0 : (0:ℤ) ≤ x := by positivity
  have hy0 : (0:ℤ) ≤ y := by positivity
  have hz0 : (0:ℤ) ≤ z := by positivity
  have hM0 : (0:ℤ) ≤ M := by positivity
  have hd := rep_dvd h
  have hd' : (n:ℤ) ∣ (y:ℤ) - M := by
    have e : (y:ℤ) - M = ((y:ℤ) + M * (κ * (n:ℤ) ^ 2 - 1)) - (n:ℤ) * (M * κ * n) := by ring
    rw [e]; exact dvd_sub hd (dvd_mul_right _ _)
  have hyM : (M:ℤ) ≤ y := by
    by_contra hc
    push Not at hc
    have := dvd_abs_lt (by linarith) hd' (by linarith) (by linarith)
    linarith
  have hxn : (0:ℤ) ≤ (x:ℤ) * n := by positivity
  have h2 := mul_le_mul_of_nonneg_right hyM hb.le
  have h3 : (z:ℤ) * (n:ℤ) ^ 2 ≤ (κ * M - M) * (n:ℤ) ^ 2 := by nlinarith
  have hn2 : (0:ℤ) < (n:ℤ) ^ 2 := by nlinarith
  have := le_of_mul_le_mul_right h3 hn2
  linarith

/-! ## (b) the word theorem -/

/-- **The rules of the side theorem**, for a word `τ 0, …, τ (m−1)` given as a function on indices, `0 < m`.
`rQ`: the first tile does not show `γ` at the left end.  `rB`: the last tile shows `β` at the right end.
`rGG`: two `γ` never meet.  `ra`: a run `C1^k`, `k < n`, that is first or follows a tile showing `γ` is followed by
`B1` or `C1`.  `rb`: a run `C2^k`, `k < n`, that is first or follows a tile showing `γ` is not followed by a tile
showing `γ`.  `rc`: runs `C2^s C1^r`, `s, r < n`, the first being first or following a tile showing `γ`, are
followed by `B1` or `C1`. -/
structure SideRules (n m : ℕ) (τ : ℕ → Ty) : Prop where
  rQ : τ 0 ≠ A2 ∧ τ 0 ≠ B2
  rB : τ (m - 1) = A2 ∨ τ (m - 1) = C1
  rGG : ∀ k, k + 1 < m → (τ k).gR → ¬ (τ (k + 1)).gL
  ra : ∀ i k, 1 ≤ k → k < n → i + k ≤ m → (∀ j, j < k → τ (i + j) = C1) →
    (i = 0 ∨ (τ (i - 1)).gR) → i + k < m ∧ (τ (i + k) = B1 ∨ τ (i + k) = C1)
  rb : ∀ i k, 1 ≤ k → k < n → i + k < m → (∀ j, j < k → τ (i + j) = C2) →
    (i = 0 ∨ (τ (i - 1)).gR) → ¬ (τ (i + k)).gL
  rc : ∀ i s r, 1 ≤ s → s < n → 1 ≤ r → r < n → i + s + r ≤ m → (∀ j, j < s → τ (i + j) = C2) →
    (∀ j, j < r → τ (i + s + j) = C1) → (i = 0 ∨ (τ (i - 1)).gR) →
    i + s + r < m ∧ (τ (i + s + r) = B1 ∨ τ (i + s + r) = C1)

/-- the maximal run of the type `X` that starts at `p` -/
theorem run_max (τ : ℕ → Ty) (X : Ty) (p m : ℕ) (hp : p < m) (h0 : τ p = X) :
    ∃ k, 1 ≤ k ∧ p + k ≤ m ∧ (∀ j, j < k → τ (p + j) = X) ∧ (p + k = m ∨ τ (p + k) ≠ X) := by
  classical
  have hex : ∃ k, p + k = m ∨ τ (p + k) ≠ X := ⟨m - p, Or.inl (by omega)⟩
  refine ⟨Nat.find hex, ?_, ?_, ?_, Nat.find_spec hex⟩
  · rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · exfalso
      have hs := Nat.find_spec hex
      rw [h] at hs
      rcases hs with hs | hs
      · omega
      · exact hs h0
    · exact h
  · have := Nat.find_min' hex (show p + (m - p) = m ∨ τ (p + (m - p)) ≠ X from Or.inl (by omega))
    omega
  · intro j hj
    have hmin := Nat.find_min hex hj
    by_contra hne
    exact hmin (Or.inr hne)

theorem ty_cases (t : Ty) : t.gR ∨ t.gL ∨ t = C1 ∨ t = C2 := by
  cases t
  · exact Or.inl (Or.inl rfl)
  · exact Or.inr (Or.inl (Or.inl rfl))
  · exact Or.inl (Or.inr rfl)
  · exact Or.inr (Or.inl (Or.inr rfl))
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

theorem gR_not_last : ∀ t : Ty, t.gR → ¬ (t = A2 ∨ t = C1) := by
  intro t; cases t <;> decide

theorem b1_gR : (B1 : Ty).gR := Or.inr rfl

/-- **THE WORD THEOREM OF THE SIDE THEOREM**: a typed word that satisfies the rules contains `n` consecutive
`C1` or `n` consecutive `C2`. -/
theorem side_word (n m : ℕ) (τ : ℕ → Ty) (hm : 0 < m) (hr : SideRules n m τ) :
    ∃ i, i + n ≤ m ∧ ((∀ j, j < n → τ (i + j) = C1) ∨ (∀ j, j < n → τ (i + j) = C2)) := by
  by_contra hno
  push Not at hno
  -- a run that is not shorter than `n` contains `n` equal tiles
  have hshort1 : ∀ p k, p + k ≤ m → (∀ j, j < k → τ (p + j) = C1) → k < n := by
    intro p k hpk hrun
    by_contra hc
    push Not at hc
    obtain ⟨j, hj, hne⟩ := (hno p (by omega)).1
    exact hne (hrun j (by omega))
  have hshort2 : ∀ p k, p + k ≤ m → (∀ j, j < k → τ (p + j) = C2) → k < n := by
    intro p k hpk hrun
    by_contra hc
    push Not at hc
    obtain ⟨j, hj, hne⟩ := (hno p (by omega)).2
    exact hne (hrun j (by omega))
  -- after START and after every tile showing `γ` on the right there is a later such tile
  have step : ∀ p, p ≤ m → (p = 0 ∨ (τ (p - 1)).gR) →
      ∃ p', p < p' ∧ p' ≤ m ∧ (τ (p' - 1)).gR := by
    intro p hpm hp
    have hplt : p < m := by
      rcases Nat.lt_or_ge p m with h | h
      · exact h
      · exfalso
        have hpe : p = m := by omega
        rcases hp with h0 | hg
        · omega
        · rw [hpe] at hg
          exact gR_not_last _ hg hr.rB
    have hnotL : ¬ (τ p).gL := by
      rcases Nat.eq_zero_or_pos p with h0 | h0
      · rw [h0]
        intro hL
        rcases hL with h | h
        · exact hr.rQ.1 h
        · exact hr.rQ.2 h
      · rcases hp with h | hg
        · omega
        · have := hr.rGG (p - 1) (by omega) hg
          rwa [Nat.sub_add_cancel h0] at this
    rcases ty_cases (τ p) with hR | hL | hC1 | hC2
    · exact ⟨p + 1, by omega, by omega, by rwa [Nat.add_sub_cancel]⟩
    · exact absurd hL hnotL
    · obtain ⟨k, hk1, hkm, hrun, hend⟩ := run_max τ C1 p m hplt hC1
      have hkn := hshort1 p k hkm hrun
      obtain ⟨hlt, hnext⟩ := hr.ra p k hk1 hkn hkm hrun hp
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
      have hslt : p + s < m := by
        rcases Nat.lt_or_ge (p + s) m with h | h
        · exact h
        · exfalso
          have hpe : p + s = m := by omega
          have hlast := hrun (s - 1) (by omega)
          have e : p + (s - 1) = m - 1 := by omega
          rw [e] at hlast
          rcases hr.rB with h | h
          · rw [hlast] at h; exact absurd h (by decide)
          · rw [hlast] at h; exact absurd h (by decide)
      have hZne : τ (p + s) ≠ C2 := by
        rcases hend with h | h
        · omega
        · exact h
      have hZnotL := hr.rb p s hs1 hsn hslt hrun hp
      rcases ty_cases (τ (p + s)) with hR | hL | hC1 | hC2'
      · exact ⟨p + s + 1, by omega, by omega, by rwa [Nat.add_sub_cancel]⟩
      · exact absurd hL hZnotL
      · obtain ⟨r, hr1, hrm, hrun', hend'⟩ := run_max τ C1 (p + s) m hslt hC1
        have hrn := hshort1 (p + s) r hrm hrun'
        obtain ⟨hlt, hnext⟩ := hr.rc p s r hs1 hsn hr1 hrn hrm hrun hrun' hp
        have hB : τ (p + s + r) = B1 := by
          rcases hnext with h | h
          · exact h
          · rcases hend' with h' | h'
            · omega
            · exact absurd h h'
        refine ⟨p + s + r + 1, by omega, by omega, ?_⟩
        rw [Nat.add_sub_cancel, hB]; exact b1_gR
      · exact absurd hC2' hZne
  have hall : ∀ K : ℕ, ∃ p, K ≤ p ∧ p ≤ m ∧ (p = 0 ∨ (τ (p - 1)).gR) := by
    intro K
    induction K with
    | zero => exact ⟨0, le_refl _, Nat.zero_le _, Or.inl rfl⟩
    | succ K ih =>
      obtain ⟨p, hKp, hpm, hp⟩ := ih
      obtain ⟨p', hpp', hp'm, hg⟩ := step p hpm hp
      exact ⟨p', by omega, hp'm, Or.inr hg⟩
  obtain ⟨p, hp1, hp2, -⟩ := hall (m + 1)
  omega

/-! ## (c) the count of `c`-tiles -/

theorem cC_run (τ : ℕ → Ty) (i n m : ℕ) (him : i + n ≤ m)
    (h : (∀ j, j < n → τ (i + j) = C1) ∨ (∀ j, j < n → τ (i + j) = C2)) :
    n ≤ ∑ k ∈ Finset.range m, (τ k).cC := by
  have h1 : ∀ k ∈ Finset.Ico i (i + n), (τ k).cC = 1 := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_Ico.mp hk
    have e : i + (k - i) = k := by omega
    rcases h with h | h
    · have := h (k - i) (by omega)
      rw [e] at this
      rw [this]; rfl
    · have := h (k - i) (by omega)
      rw [e] at this
      rw [this]; rfl
  have h2 : ∑ k ∈ Finset.Ico i (i + n), (τ k).cC = n := by
    rw [Finset.sum_congr rfl h1, Finset.sum_const, Nat.card_Ico, smul_eq_mul, mul_one,
      Nat.add_sub_cancel_left]
  have h3 : ∑ k ∈ Finset.Ico i (i + n), (τ k).cC ≤ ∑ k ∈ Finset.range m, (τ k).cC := by
    refine Finset.sum_le_sum_of_subset ?_
    intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_Ico.mp hk
    exact Finset.mem_range.mpr (by omega)
  omega

/-- **No typed side word of total length `M (κ n² − 1)` with `(κ − 1) M < n` satisfies the rules.**
(`κ = 3`: the base of `T_M(1,n)`, `2M < n`; `κ = 2`: the side `QB` of `W_M(1,n)`, `M < n`.) -/
theorem no_side_word {n m M κ : ℕ} (hn : 2 ≤ n) (hκ : 2 ≤ κ) (hκM : (κ - 1) * M < n) (hm : 0 < m)
    (τ : ℕ → Ty)
    (hsum : ((∑ k ∈ Finset.range m, (τ k).len n : ℕ) : ℝ) = (M:ℝ) * (κ * (n:ℝ) ^ 2 - 1))
    (hr : SideRules n m τ) : False := by
  obtain ⟨i, him, hrun⟩ := side_word n m τ hm hr
  have hz := cC_run τ i n m him hrun
  obtain ⟨x, hx⟩ : ∃ x, x = ∑ k ∈ Finset.range m, (τ k).cA := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = ∑ k ∈ Finset.range m, (τ k).cB := ⟨_, rfl⟩
  obtain ⟨z, hzdef⟩ : ∃ z, z = ∑ k ∈ Finset.range m, (τ k).cC := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S, S = ∑ k ∈ Finset.range m, (τ k).len n := ⟨_, rfl⟩
  have hrep : x * n + y * (n * n - 1) + z * (n * n) = S := by
    rw [hS, Finset.sum_congr rfl (fun k _ => len_eq n (τ k)), Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul, ← hx, ← hy, ← hzdef]
  rw [← hS] at hsum
  have h1 := toInt (by omega : 1 ≤ n) hrep
  have hZ : (S:ℤ) = (M:ℤ) * ((κ:ℤ) * (n:ℤ) ^ 2 - 1) := by
    have h' : (((S:ℤ)) : ℝ) = (((M:ℤ) * ((κ:ℤ) * (n:ℤ) ^ 2 - 1) : ℤ) : ℝ) := by
      push_cast; exact hsum
    exact Int.cast_injective h'
  rw [hZ] at h1
  have hM1 : M ≤ (κ - 1) * M := Nat.le_mul_of_pos_left M (by omega)
  have h2 := rep_side hn (by omega : M < n) h1
  have h4 : z + M ≤ κ * M := by exact_mod_cast h2
  rw [← hzdef] at hz
  obtain ⟨c, hc⟩ : ∃ c, κ = c + 1 := ⟨κ - 1, by omega⟩
  subst hc
  rw [Nat.add_sub_cancel] at hκM
  have h5 : (c + 1) * M = c * M + M := by ring
  omega

/-! ## Non-vacuity of the rules -/

/-- the word `C1^n` followed by nothing: with `n` tiles `C1` -/
def exW (_ : ℕ) : Ty := C1

/-- **The hypotheses of `side_word` are satisfiable**: for every `n ≥ 1` the word `C1^n` satisfies all the rules
(with `m = n`): the run rules ask nothing of a run of length `n`.  (In a real tiling of `W_n(1,n)` the side `QB`
carries such runs.) -/
theorem exRules (n : ℕ) (hn : 1 ≤ n) : SideRules n n exW := by
  have hC2 : (C1 : Ty) ≠ C2 := by decide
  have hgR : ¬ (C1 : Ty).gR := by decide
  refine ⟨by decide, Or.inr rfl, ?_, ?_, ?_, ?_⟩
  · intro k _ hg
    exact absurd hg hgR
  · intro i k hk1 hkn hik _ hp
    rcases hp with h | h
    · exact ⟨by omega, Or.inr rfl⟩
    · exact absurd h hgR
  · intro i k hk1 _ _ hrun _
    exact absurd (hrun 0 (by omega)) hC2
  · intro i s r hs1 _ _ _ _ hrun _ _
    exact absurd (hrun 0 (by omega)) hC2

end Erdos634.Draft.SideRun

#print axioms Erdos634.Draft.SideRun.rep_jb
#print axioms Erdos634.Draft.SideRun.rep_qc
#print axioms Erdos634.Draft.SideRun.rep_side
#print axioms Erdos634.Draft.SideRun.side_word
#print axioms Erdos634.Draft.SideRun.no_side_word
#print axioms Erdos634.Draft.SideRun.exRules

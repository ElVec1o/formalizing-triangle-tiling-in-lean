/-
Draft/W2E1Words.lean -- Stage 0 of the formalization of `prop:w2e1` (paper/erdos-634.tex): the triangle `W_2(1,f)`
with sides `2f(f²−1)`, `2(2f²−1)`, `2f³` has no tiling by the tile `(f, f²−1, f²)`, `f ≥ 3`.

Pure arithmetic and combinatorics, no geometry.

(a) representations by the three sides `a = f`, `b = f²−1`, `c = f²` (`f ≥ 3`):
    `L = 4f²−2` only as `a^{2f} b²`, `a^f b² c`, `b² c²` (`letters_L`); `b` only as `b`, `2b` only as `b + b`
    (`OrderForcing.partition_jb`, restated as `letters_b`, `letters_2b`); integer forms `rep_*` for the geometry.
(b) the word theorem: a typed side word (six types `A1 A2 B1 B2 C1 C2`: letter and the angles at the two ends) of
    total length `L` cannot satisfy the rules R-Q, R-B, R-GG, R-H2, R-H1, R-C, R-CH of the proof
    (`no_word_fn` for a word given as a function on indices, `no_word` for a list).

The rules are hypotheses here; Stages 1-3 prove them for the side word of a dissection.  Non-vacuity: the word
`B1 B1 C1 C1` has the length `L` for every `f` and satisfies every rule except R-CH (`exW_rules`).

Composite-N work (base-beta threshold program); not prime-case work.  No sorry, no native_decide.
-/
import Mathlib.Tactic
import Erdos634.OrderForcing

namespace Erdos634.Draft.W2E1

/-! ## (a) arithmetic -/

theorem dvd_small {n m : ℤ} (hn : 3 ≤ n) (h : n ∣ m) (h1 : -2 ≤ m) (h2 : m ≤ 2) : m = 0 := by
  obtain ⟨k, rfl⟩ := h
  have hk : k = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hk | hk
    · have hk' : k ≤ -1 := by omega
      nlinarith [mul_nonneg (sub_nonneg.mpr hn) (show (0:ℤ) ≤ -1 - k by linarith)]
    · have hk' : 1 ≤ k := by omega
      nlinarith [mul_nonneg (sub_nonneg.mpr hn) (show (0:ℤ) ≤ k - 1 by linarith)]
  rw [hk, mul_zero]

/-- the congruence behind every representation: `y ≡ −T (mod n)` -/
theorem rep_dvd {n x y z : ℕ} {T : ℤ}
    (h : (x:ℤ) * n + y * ((n:ℤ) ^ 2 - 1) + z * (n:ℤ) ^ 2 = T) : (n:ℤ) ∣ (y:ℤ) + T :=
  ⟨(x:ℤ) + y * n + z * n, by rw [← h]; ring⟩

theorem rep_y_le {n x y z : ℕ} {T : ℤ}
    (h : (x:ℤ) * n + y * ((n:ℤ) ^ 2 - 1) + z * (n:ℤ) ^ 2 = T) : (y:ℤ) * ((n:ℤ) ^ 2 - 1) ≤ T := by
  have hx : (0:ℤ) ≤ (x:ℤ) * n := by positivity
  have hz : (0:ℤ) ≤ (z:ℤ) * (n:ℤ) ^ 2 := by positivity
  linarith

theorem rep_y_bound {n x y z : ℕ} {T : ℤ} (hn : 3 ≤ n) (K : ℤ)
    (h : (x:ℤ) * n + y * ((n:ℤ) ^ 2 - 1) + z * (n:ℤ) ^ 2 = T)
    (hT : T < (K + 1) * ((n:ℤ) ^ 2 - 1)) : (y:ℤ) ≤ K := by
  have hn' : (3:ℤ) ≤ n := by exact_mod_cast hn
  have hb : (0:ℤ) ≤ (n:ℤ) ^ 2 - 1 := by nlinarith
  have hle := rep_y_le h
  by_contra hc
  push Not at hc
  have h1 : K + 1 ≤ (y:ℤ) := by omega
  have h2 := mul_le_mul_of_nonneg_right h1 hb
  linarith

theorem rep_y_eq {n x y z : ℕ} {T : ℤ} (hn : 3 ≤ n) (y₀ : ℤ)
    (h : (x:ℤ) * n + y * ((n:ℤ) ^ 2 - 1) + z * (n:ℤ) ^ 2 = T)
    (hT : (n:ℤ) ∣ T + y₀) (hlo : y₀ - 2 ≤ (y:ℤ)) (hhi : (y:ℤ) ≤ y₀ + 2) : (y:ℤ) = y₀ := by
  have hd := rep_dvd h
  have hd' : (n:ℤ) ∣ (y:ℤ) - y₀ := by
    have e : (y:ℤ) - y₀ = ((y:ℤ) + T) - (T + y₀) := by ring
    rw [e]; exact dvd_sub hd hT
  have := dvd_small (by exact_mod_cast hn) hd' (by linarith) (by linarith)
  linarith

theorem nat_zero_of_mul {x : ℕ} {m : ℤ} (hm : 0 < m) (h : (x:ℤ) * m = 0) : x = 0 := by
  rcases mul_eq_zero.mp h with h0 | h0
  · exact_mod_cast h0
  · exact absurd h0 hm.ne'

/-- `b` is represented only by one `b`. -/
theorem rep_b {n x y z : ℕ} (hn : 3 ≤ n)
    (h : (x:ℤ) * n + y * ((n:ℤ) ^ 2 - 1) + z * (n:ℤ) ^ 2 = (n:ℤ) ^ 2 - 1) :
    x = 0 ∧ y = 1 ∧ z = 0 := by
  have hn' : (3:ℤ) ≤ n := by exact_mod_cast hn
  have hb : (8:ℤ) ≤ (n:ℤ) ^ 2 - 1 := by nlinarith
  have hy0 : (0:ℤ) ≤ y := by positivity
  have hy2 : (y:ℤ) ≤ 1 := rep_y_bound hn 1 h (by nlinarith)
  have hy : (y:ℤ) = 1 := rep_y_eq hn 1 h ⟨n, by ring⟩ (by linarith) (by linarith)
  rw [hy] at h
  have hx : (0:ℤ) ≤ (x:ℤ) * n := by positivity
  have hz : (0:ℤ) ≤ (z:ℤ) * (n:ℤ) ^ 2 := by positivity
  refine ⟨nat_zero_of_mul (by linarith : (0:ℤ) < n) (by linarith), by exact_mod_cast hy,
    nat_zero_of_mul (by nlinarith : (0:ℤ) < (n:ℤ) ^ 2) (by linarith)⟩

/-- `2b` is represented only by `b + b`. -/
theorem rep_2b {n x y z : ℕ} (hn : 3 ≤ n)
    (h : (x:ℤ) * n + y * ((n:ℤ) ^ 2 - 1) + z * (n:ℤ) ^ 2 = 2 * ((n:ℤ) ^ 2 - 1)) :
    x = 0 ∧ y = 2 ∧ z = 0 := by
  have hn' : (3:ℤ) ≤ n := by exact_mod_cast hn
  have hb : (8:ℤ) ≤ (n:ℤ) ^ 2 - 1 := by nlinarith
  have hy0 : (0:ℤ) ≤ y := by positivity
  have hy2 : (y:ℤ) ≤ 2 := rep_y_bound hn 2 h (by nlinarith)
  have hy : (y:ℤ) = 2 := rep_y_eq hn 2 h ⟨2 * n, by ring⟩ (by linarith) (by linarith)
  rw [hy] at h
  have hx : (0:ℤ) ≤ (x:ℤ) * n := by positivity
  have hz : (0:ℤ) ≤ (z:ℤ) * (n:ℤ) ^ 2 := by positivity
  refine ⟨nat_zero_of_mul (by linarith : (0:ℤ) < n) (by linarith), by exact_mod_cast hy,
    nat_zero_of_mul (by nlinarith : (0:ℤ) < (n:ℤ) ^ 2) (by linarith)⟩

/-- `a` is represented only by one `a`. -/
theorem rep_a {n x y z : ℕ} (hn : 3 ≤ n)
    (h : (x:ℤ) * n + y * ((n:ℤ) ^ 2 - 1) + z * (n:ℤ) ^ 2 = (n:ℤ)) :
    x = 1 ∧ y = 0 ∧ z = 0 := by
  have hn' : (3:ℤ) ≤ n := by exact_mod_cast hn
  have hb : (8:ℤ) ≤ (n:ℤ) ^ 2 - 1 := by nlinarith
  have hy0 : (0:ℤ) ≤ y := by positivity
  have hy2 : (y:ℤ) ≤ 0 := rep_y_bound hn 0 h (by nlinarith)
  have hy : (y:ℤ) = 0 := by linarith
  rw [hy] at h
  have hx0 : (0:ℤ) ≤ x := by positivity
  have hz0 : (0:ℤ) ≤ z := by positivity
  have hz : (z:ℤ) = 0 := by
    by_contra hne
    have h1 : (1:ℤ) ≤ z := by omega
    have h2 : (0:ℤ) ≤ (x:ℤ) * n := by positivity
    nlinarith [mul_le_mul_of_nonneg_right h1 (by nlinarith : (0:ℤ) ≤ (n:ℤ) ^ 2)]
  rw [hz] at h
  have hx : (x:ℤ) = 1 := by
    have h3 : ((x:ℤ) - 1) * n = 0 := by linarith
    rcases mul_eq_zero.mp h3 with h0 | h0
    · linarith
    · linarith
  exact ⟨by exact_mod_cast hx, by exact_mod_cast hy, by exact_mod_cast hz⟩

/-- a representation of `c` contains no `b`. -/
theorem rep_c {n x y z : ℕ} (hn : 3 ≤ n)
    (h : (x:ℤ) * n + y * ((n:ℤ) ^ 2 - 1) + z * (n:ℤ) ^ 2 = (n:ℤ) ^ 2) : y = 0 := by
  have hn' : (3:ℤ) ≤ n := by exact_mod_cast hn
  have hb : (8:ℤ) ≤ (n:ℤ) ^ 2 - 1 := by nlinarith
  have hy0 : (0:ℤ) ≤ y := by positivity
  have hy2 : (y:ℤ) ≤ 1 := rep_y_bound hn 1 h (by nlinarith)
  have hy : (y:ℤ) = 0 := rep_y_eq hn 0 h ⟨n, by ring⟩ (by linarith) (by linarith)
  exact_mod_cast hy

/-- **The letters of the side `L = 4f²−2`**: `a^{2f} b²`, `a^f b² c` or `b² c²`. -/
theorem rep_L {n x y z : ℕ} (hn : 3 ≤ n)
    (h : (x:ℤ) * n + y * ((n:ℤ) ^ 2 - 1) + z * (n:ℤ) ^ 2 = 4 * (n:ℤ) ^ 2 - 2) :
    (x = 2 * n ∧ y = 2 ∧ z = 0) ∨ (x = n ∧ y = 2 ∧ z = 1) ∨ (x = 0 ∧ y = 2 ∧ z = 2) := by
  have hn' : (3:ℤ) ≤ n := by exact_mod_cast hn
  have hb : (8:ℤ) ≤ (n:ℤ) ^ 2 - 1 := by nlinarith
  have hy0 : (0:ℤ) ≤ y := by positivity
  have hy4 : (y:ℤ) ≤ 4 := rep_y_bound hn 4 h (by nlinarith)
  have hy : (y:ℤ) = 2 := rep_y_eq hn 2 h ⟨4 * n, by ring⟩ (by linarith) (by linarith)
  rw [hy] at h
  have hx0 : (0:ℤ) ≤ x := by positivity
  have hz0 : (0:ℤ) ≤ z := by positivity
  have h3 : ((x:ℤ) + z * n - 2 * n) * n = 0 := by linarith
  have h4 : (x:ℤ) + z * n = 2 * n := by
    rcases mul_eq_zero.mp h3 with h0 | h0
    · linarith
    · linarith
  have hz2 : (z:ℤ) ≤ 2 := by
    by_contra hc
    push Not at hc
    have h1 : (3:ℤ) ≤ z := by omega
    nlinarith [mul_le_mul_of_nonneg_right h1 (by linarith : (0:ℤ) ≤ (n:ℤ))]
  have hy' : y = 2 := by exact_mod_cast hy
  have hz2' : z ≤ 2 := by exact_mod_cast hz2
  interval_cases z
  · left
    refine ⟨?_, hy', rfl⟩
    have : (x:ℤ) = 2 * n := by push_cast at h4; linarith
    exact_mod_cast this
  · right; left
    refine ⟨?_, hy', rfl⟩
    have : (x:ℤ) = n := by push_cast at h4; linarith
    exact_mod_cast this
  · right; right
    refine ⟨?_, hy', rfl⟩
    have : (x:ℤ) = 0 := by push_cast at h4; linarith
    exact_mod_cast this

/-- from a natural-number equation with the truncated subtraction `f * f - 1` to the integer form -/
theorem toInt {f x y z T : ℕ} (hf : 1 ≤ f) (h : x * f + y * (f * f - 1) + z * (f * f) = T) :
    (x:ℤ) * f + y * ((f:ℤ) ^ 2 - 1) + z * (f:ℤ) ^ 2 = T := by
  obtain ⟨B, hB⟩ : ∃ B, f * f = B + 1 := ⟨f * f - 1, by have : 1 ≤ f * f := Nat.mul_pos hf hf; omega⟩
  rw [hB, Nat.add_sub_cancel] at h
  have hz : (x:ℤ) * f + y * B + z * ((B:ℤ) + 1) = T := by exact_mod_cast h
  have hBz : (f:ℤ) ^ 2 = B + 1 := by
    have : (f:ℤ) * f = B + 1 := by exact_mod_cast hB
    rw [sq]; exact this
  rw [hBz]
  linarith

/-- **The letters of `L = 4f²−2`** (natural-number form). -/
theorem letters_L {f x y z : ℕ} (hf : 3 ≤ f)
    (h : x * f + y * (f * f - 1) + z * (f * f) = 4 * (f * f) - 2) :
    (x = 2 * f ∧ y = 2 ∧ z = 0) ∨ (x = f ∧ y = 2 ∧ z = 1) ∨ (x = 0 ∧ y = 2 ∧ z = 2) := by
  have hff : 9 ≤ f * f := by nlinarith
  have h1 := toInt (by omega) h
  have h2 : ((4 * (f * f) - 2 : ℕ) : ℤ) = 4 * (f:ℤ) ^ 2 - 2 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [h2] at h1
  exact rep_L hf h1

/-- `b` only as `(0,1,0)`. -/
theorem letters_b {f x y z : ℕ} (hf : 3 ≤ f)
    (h : x * f + y * (f * f - 1) + z * (f * f) = f * f - 1) : x = 0 ∧ y = 1 ∧ z = 0 := by
  have h' : x * f + y * (f * f - 1) + z * (f * f) = 1 * (f * f - 1) := by rw [Nat.one_mul]; exact h
  exact Erdos634.OrderForcing.partition_jb (j := 1) (x := x) (y := y) (z := z) hf le_rfl (by omega) h'

/-- `2b` only as `(0,2,0)`. -/
theorem letters_2b {f x y z : ℕ} (hf : 3 ≤ f)
    (h : x * f + y * (f * f - 1) + z * (f * f) = 2 * (f * f - 1)) : x = 0 ∧ y = 2 ∧ z = 0 :=
  Erdos634.OrderForcing.partition_jb (j := 2) hf (by omega) (by omega) h

/-! ## (b) the typed side word -/

/-- The six types of a tile with an edge on the side `QB`: the letter and the angles at its left and right ends.
`A1 = (a; β, γ)`, `A2 = (a; γ, β)`, `B1 = (b; α, γ)`, `B2 = (b; γ, α)`, `C1 = (c; α, β)`, `C2 = (c; β, α)`. -/
inductive Ty
  | A1 | A2 | B1 | B2 | C1 | C2
  deriving DecidableEq

namespace Ty

/-- the length of the letter -/
def len (f : ℕ) : Ty → ℕ
  | A1 => f | A2 => f | B1 => f * f - 1 | B2 => f * f - 1 | C1 => f * f | C2 => f * f

/-- the tile shows `γ` at its right end -/
abbrev gR (t : Ty) : Prop := t = A1 ∨ t = B1
/-- the tile shows `γ` at its left end -/
abbrev gL (t : Ty) : Prop := t = A2 ∨ t = B2

def cA : Ty → ℕ | A1 => 1 | A2 => 1 | _ => 0
def cB : Ty → ℕ | B1 => 1 | B2 => 1 | _ => 0
def cC : Ty → ℕ | C1 => 1 | C2 => 1 | _ => 0

theorem len_eq (f : ℕ) (t : Ty) : t.len f = t.cA * f + t.cB * (f * f - 1) + t.cC * (f * f) := by
  cases t <;> simp [len, cA, cB, cC]

theorem count_one (t : Ty) : t.cA + t.cB + t.cC = 1 := by cases t <;> rfl
theorem cC_le (t : Ty) : t.cC ≤ 1 := by cases t <;> decide
theorem cC_zero : ∀ t : Ty, t.cC = 0 → t ≠ C1 ∧ t ≠ C2 := by intro t; cases t <;> decide
theorem cC_one : ∀ t : Ty, t.cC = 1 → t = C1 ∨ t = C2 := by intro t; cases t <;> decide
theorem cA_zero : ∀ t : Ty, t.cA = 0 → t ≠ A1 ∧ t ≠ A2 := by intro t; cases t <;> decide

theorem gR_of_first : ∀ t : Ty, t ≠ A2 → t ≠ B2 → t ≠ C1 → t ≠ C2 → t.gR := by
  intro t; cases t <;> decide
theorem gR_of_not_gL : ∀ t : Ty, ¬ t.gL → t ≠ C1 → t ≠ C2 → t.gR := by
  intro t; cases t <;> decide
theorem gL_of_not_gR : ∀ t : Ty, ¬ t.gR → t ≠ C1 → t ≠ C2 → t.gL := by
  intro t; cases t <;> decide
theorem gR_ne : ∀ t : Ty, t.gR → t ≠ A2 ∧ t ≠ C1 ∧ t ≠ B2 ∧ t ≠ C2 := by
  intro t; cases t <;> decide
theorem gL_ne : ∀ t : Ty, t.gL → t ≠ A1 ∧ t ≠ C2 ∧ t ≠ B1 ∧ t ≠ C1 := by
  intro t; cases t <;> decide
theorem gL_of_last : ∀ t : Ty, (t = A2 ∨ t = C1) → t ≠ C1 → t.gL := by
  intro t; cases t <;> decide
theorem b_cases : ∀ t : Ty, t ≠ A1 → t ≠ A2 → t ≠ C1 → t ≠ C2 → t = B1 ∨ t = B2 := by
  intro t; cases t <;> decide

end Ty

open Ty

/-- **The rules of the proof**, for a word `τ 0, …, τ (n−1)` given as a function on indices.
R-Q: the first tile does not show `γ` at `Q`.  R-B: the last tile shows `β` at `B`.  R-GG: two `γ` never meet.
R-H2 (half-turn lemma): a `C2` that is first or follows `A1`/`B1` is not last and is followed by `A1` or `C2`.
R-H1 (half-turn lemma): a `C1` followed by `A2`/`B2` is not first and is preceded by `A2` or `C1`.
R-C (corner lemma): a last `C1` is preceded by `A2` or `C1`.
R-CH: the word does not end `(A1 or B1) C1 C1`. -/
structure RulesFn (n : ℕ) (τ : ℕ → Ty) : Prop where
  rQ : 0 < n → τ 0 ≠ A2 ∧ τ 0 ≠ B2
  rB : 0 < n → τ (n - 1) = A2 ∨ τ (n - 1) = C1
  rGG : ∀ m, m + 1 < n → (τ m).gR → ¬ (τ (m + 1)).gL
  rH2 : ∀ m, m < n → τ m = C2 → (m = 0 ∨ (τ (m - 1)).gR) →
    m + 1 < n ∧ (τ (m + 1) = A1 ∨ τ (m + 1) = C2)
  rH1 : ∀ m, m + 1 < n → τ m = C1 → (τ (m + 1)).gL →
    0 < m ∧ (τ (m - 1) = A2 ∨ τ (m - 1) = C1)
  rC : 0 < n → τ (n - 1) = C1 → 1 < n ∧ (τ (n - 2) = A2 ∨ τ (n - 2) = C1)
  rCH : 3 ≤ n → τ (n - 1) = C1 → τ (n - 2) = C1 → ¬ (τ (n - 3)).gR

/-- a `0/1` sequence with sum one has exactly one `1` -/
theorem exists_unique_of_sum_one (n : ℕ) (g : ℕ → ℕ) (hg : ∀ m, g m ≤ 1)
    (h : ∑ m ∈ Finset.range n, g m = 1) :
    ∃ k, k < n ∧ g k = 1 ∧ ∀ m, m < n → m ≠ k → g m = 0 := by
  have hex : ∃ k ∈ Finset.range n, g k ≠ 0 := by
    by_contra hne
    push Not at hne
    have := Finset.sum_eq_zero hne
    omega
  obtain ⟨k, hk, hgk⟩ := hex
  have hk1 : g k = 1 := by have := hg k; omega
  have hsplit := Finset.add_sum_erase (Finset.range n) g hk
  have hrest : ∑ m ∈ (Finset.range n).erase k, g m = 0 := by omega
  rw [Finset.sum_eq_zero_iff] at hrest
  refine ⟨k, Finset.mem_range.mp hk, hk1, fun m hm hmk => ?_⟩
  exact hrest m (Finset.mem_erase.mpr ⟨hmk, Finset.mem_range.mpr hm⟩)

/-- **THE WORD THEOREM** (index form): no typed word of total length `4f²−2` satisfies the rules. -/
theorem no_word_fn (f : ℕ) (hf : 3 ≤ f) (n : ℕ) (τ : ℕ → Ty)
    (hsum : ∑ m ∈ Finset.range n, (τ m).len f = 4 * (f * f) - 2) (hr : RulesFn n τ) : False := by
  have hff : 9 ≤ f * f := by nlinarith
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      rw [Finset.range_zero, Finset.sum_empty] at hsum
      omega
    · exact h0
  obtain ⟨x, hx⟩ : ∃ x, x = ∑ m ∈ Finset.range n, (τ m).cA := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = ∑ m ∈ Finset.range n, (τ m).cB := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z, z = ∑ m ∈ Finset.range n, (τ m).cC := ⟨_, rfl⟩
  have hxyz : x + y + z = n := by
    rw [hx, hy, hz, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl (fun m _ => count_one (τ m))]
    simp
  have hrep : x * f + y * (f * f - 1) + z * (f * f) = 4 * (f * f) - 2 := by
    rw [← hsum, Finset.sum_congr rfl (fun m _ => len_eq f (τ m)), Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul, ← hx, ← hy, ← hz]
  rcases letters_L hf hrep with ⟨-, -, hz0⟩ | ⟨-, -, hz1⟩ | ⟨hx0, hy2, hz2⟩
  · -- K1: no `c`
    have hnoC : ∀ m, m < n → τ m ≠ C1 ∧ τ m ≠ C2 := by
      intro m hm
      have h0 : ∑ m ∈ Finset.range n, (τ m).cC = 0 := by rw [← hz]; exact hz0
      rw [Finset.sum_eq_zero_iff] at h0
      exact cC_zero _ (h0 m (Finset.mem_range.mpr hm))
    have hall : ∀ m, m < n → (τ m).gR := by
      intro m
      induction m with
      | zero =>
        intro h0
        exact gR_of_first _ (hr.rQ hn0).1 (hr.rQ hn0).2 (hnoC 0 h0).1 (hnoC 0 h0).2
      | succ m ih =>
        intro hm
        exact gR_of_not_gL _ (hr.rGG m hm (ih (by omega))) (hnoC _ hm).1 (hnoC _ hm).2
    have hlast := hall (n - 1) (by omega)
    obtain ⟨h1, h2, -, -⟩ := gR_ne _ hlast
    rcases hr.rB hn0 with h | h
    · exact h1 h
    · exact h2 h
  · -- K2: one `c`
    have h1 : ∑ m ∈ Finset.range n, (τ m).cC = 1 := by rw [← hz]; exact hz1
    obtain ⟨k, hkn, hk1, hkother⟩ := exists_unique_of_sum_one n (fun m => (τ m).cC) (fun m => cC_le _) h1
    have hnoC : ∀ m, m < n → m ≠ k → τ m ≠ C1 ∧ τ m ≠ C2 := fun m hm hmk =>
      cC_zero _ (hkother m hm hmk)
    -- before `k`: `γ` on the right
    have hfwd : ∀ m, m < k → (τ m).gR := by
      intro m
      induction m with
      | zero =>
        intro h0
        have hc := hnoC 0 hn0 (by omega)
        exact gR_of_first _ (hr.rQ hn0).1 (hr.rQ hn0).2 hc.1 hc.2
      | succ m ih =>
        intro hm
        have hc := hnoC (m + 1) (by omega) (by omega)
        exact gR_of_not_gL _ (hr.rGG m (by omega) (ih (by omega))) hc.1 hc.2
    -- after `k`: `γ` on the left
    have hbwd : ∀ d m, k < m → m < n → n - 1 - m = d → (τ m).gL := by
      intro d
      induction d with
      | zero =>
        intro m hkm hmn hd
        have hm : m = n - 1 := by omega
        subst hm
        have hc := hnoC (n - 1) hmn (by omega)
        exact gL_of_last _ (hr.rB hn0) hc.1
      | succ d ih =>
        intro m hkm hmn hd
        have hnext := ih (m + 1) (by omega) (by omega) (by omega)
        have hc := hnoC m hmn (by omega)
        refine gL_of_not_gR _ (fun hg => ?_) hc.1 hc.2
        exact hr.rGG m (by omega) hg hnext
    rcases cC_one _ hk1 with hC1 | hC2
    · -- `τ k = C1`
      by_cases hk : k + 1 < n
      · have hnext := hbwd (n - 1 - (k + 1)) (k + 1) (by omega) hk rfl
        obtain ⟨hk0, hprev⟩ := hr.rH1 k hk hC1 hnext
        obtain ⟨h1', h2', -, -⟩ := gR_ne _ (hfwd (k - 1) (by omega))
        rcases hprev with h | h
        · exact h1' h
        · exact h2' h
      · have hkl : k = n - 1 := by omega
        rw [hkl] at hC1
        obtain ⟨hn1, hprev⟩ := hr.rC hn0 hC1
        obtain ⟨h1', h2', -, -⟩ := gR_ne _ (hfwd (n - 2) (by omega))
        rcases hprev with h | h
        · exact h1' h
        · exact h2' h
    · -- `τ k = C2`
      have hhyp : k = 0 ∨ (τ (k - 1)).gR := by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · exact Or.inl h0
        · exact Or.inr (hfwd (k - 1) (by omega))
      obtain ⟨hk, hnextv⟩ := hr.rH2 k hkn hC2 hhyp
      have hnext := hbwd (n - 1 - (k + 1)) (k + 1) (by omega) hk rfl
      obtain ⟨h1', h2', -, -⟩ := gL_ne _ hnext
      rcases hnextv with h | h
      · exact h1' h
      · exact h2' h
  · -- K3: `b² c²`
    have hn4 : n = 4 := by omega
    subst hn4
    have hnoA : ∀ m, m < 4 → τ m ≠ A1 ∧ τ m ≠ A2 := by
      intro m hm
      have h0 : ∑ m ∈ Finset.range 4, (τ m).cA = 0 := by rw [← hx]; exact hx0
      rw [Finset.sum_eq_zero_iff] at h0
      exact cA_zero _ (h0 m (Finset.mem_range.mpr hm))
    have h3 : τ 3 = C1 := by
      rcases hr.rB (by norm_num) with h | h
      · exact absurd h (hnoA 3 (by norm_num)).2
      · exact h
    have h2 : τ 2 = C1 := by
      rcases (hr.rC (by norm_num) h3).2 with h | h
      · exact absurd h (hnoA 2 (by norm_num)).2
      · exact h
    have hzsum : (τ 0).cC + (τ 1).cC + (τ 2).cC + (τ 3).cC = 2 := by
      have := hz
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one] at this
      omega
    have hc2 : (τ 2).cC = 1 := by rw [h2]; rfl
    have hc3 : (τ 3).cC = 1 := by rw [h3]; rfl
    have h0C := cC_zero (τ 0) (by omega)
    have h1C := cC_zero (τ 1) (by omega)
    have h1B := b_cases (τ 1) (hnoA 1 (by norm_num)).1 (hnoA 1 (by norm_num)).2 h1C.1 h1C.2
    have h0B := b_cases (τ 0) (hnoA 0 (by norm_num)).1 (hnoA 0 (by norm_num)).2 h0C.1 h0C.2
    have hCH := hr.rCH (by norm_num) h3 h2
    have h1 : τ 1 = B2 := by
      rcases h1B with h | h
      · exact absurd (Or.inr h) hCH
      · exact h
    have h0 : τ 0 = B1 := by
      rcases h0B with h | h
      · exact h
      · exact absurd h (hr.rQ (by norm_num)).2
    exact hr.rGG 0 (by norm_num) (Or.inr h0) (Or.inr h1)

/-! ### The list form -/

/-- **The rules of the proof for a word given as a list** (`w[m]?` is the `m`-th tile from `Q`). -/
structure Rules (w : List Ty) : Prop where
  rQ : ∀ X, w[0]? = some X → X ≠ A2 ∧ X ≠ B2
  rB : ∀ X, w[w.length - 1]? = some X → X = A2 ∨ X = C1
  rGG : ∀ m X Y, w[m]? = some X → w[m + 1]? = some Y → X.gR → ¬ Y.gL
  rH2 : ∀ m, w[m]? = some C2 → (m = 0 ∨ ∃ X, w[m - 1]? = some X ∧ X.gR) →
    ∃ Y, w[m + 1]? = some Y ∧ (Y = A1 ∨ Y = C2)
  rH1 : ∀ m Y, w[m]? = some C1 → w[m + 1]? = some Y → Y.gL →
    0 < m ∧ ∃ X, w[m - 1]? = some X ∧ (X = A2 ∨ X = C1)
  rC : w[w.length - 1]? = some C1 →
    1 < w.length ∧ ∃ X, w[w.length - 2]? = some X ∧ (X = A2 ∨ X = C1)
  rCH : ∀ X, 3 ≤ w.length → w[w.length - 1]? = some C1 → w[w.length - 2]? = some C1 →
    w[w.length - 3]? = some X → ¬ X.gR

theorem sum_map_eq_sum_range {α : Type*} (g : α → ℕ) (d : α) :
    ∀ w : List α, (w.map g).sum = ∑ m ∈ Finset.range w.length, g (w.getD m d)
  | [] => by simp
  | x :: t => by
    rw [List.map_cons, List.sum_cons, sum_map_eq_sum_range g d t, List.length_cons,
      Finset.sum_range_succ']
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    ring

theorem getElem?_getD (w : List Ty) {m : ℕ} (h : m < w.length) : w[m]? = some (w.getD m A1) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

theorem lt_of_getElem? {w : List Ty} {m : ℕ} {X : Ty} (h : w[m]? = some X) :
    m < w.length ∧ w.getD m A1 = X := by
  obtain ⟨hm, hX⟩ := List.getElem?_eq_some_iff.mp h
  refine ⟨hm, ?_⟩
  have := getElem?_getD w hm
  rw [h] at this
  exact (Option.some.inj this).symm

/-- **THE WORD THEOREM** (list form): no typed word whose letters have total length `4f²−2` satisfies the rules. -/
theorem no_word (f : ℕ) (hf : 3 ≤ f) (w : List Ty) (hsum : (w.map (Ty.len f)).sum = 4 * (f * f) - 2)
    (hr : Rules w) : False := by
  refine no_word_fn f hf w.length (fun m => w.getD m A1) ?_ ?_
  · rw [← hsum, sum_map_eq_sum_range (Ty.len f) A1 w]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro hn
      exact hr.rQ _ (getElem?_getD w hn)
    · intro hn
      exact hr.rB _ (getElem?_getD w (by omega))
    · intro m hm hg
      exact hr.rGG m _ _ (getElem?_getD w (by omega)) (getElem?_getD w hm) hg
    · intro m hm hC hyp
      have hC' : w[m]? = some C2 := by rw [getElem?_getD w hm]; exact congrArg some hC
      have hyp' : m = 0 ∨ ∃ X, w[m - 1]? = some X ∧ X.gR := by
        rcases hyp with h | h
        · exact Or.inl h
        · rcases Nat.eq_zero_or_pos m with h0 | h0
          · exact Or.inl h0
          · exact Or.inr ⟨_, getElem?_getD w (by omega), h⟩
      obtain ⟨Y, hY, hYv⟩ := hr.rH2 m hC' hyp'
      obtain ⟨hlt, hYe⟩ := lt_of_getElem? hY
      refine ⟨hlt, ?_⟩
      show w.getD (m + 1) A1 = A1 ∨ w.getD (m + 1) A1 = C2
      rw [hYe]; exact hYv
    · intro m hm hC hg
      have hC' : w[m]? = some C1 := by rw [getElem?_getD w (by omega)]; exact congrArg some hC
      obtain ⟨h0, X, hX, hXv⟩ := hr.rH1 m _ hC' (getElem?_getD w hm) hg
      obtain ⟨-, hXe⟩ := lt_of_getElem? hX
      refine ⟨h0, ?_⟩
      show w.getD (m - 1) A1 = A2 ∨ w.getD (m - 1) A1 = C1
      rw [hXe]; exact hXv
    · intro hn hC
      have hC' : w[w.length - 1]? = some C1 := by
        rw [getElem?_getD w (by omega)]; exact congrArg some hC
      obtain ⟨h1, X, hX, hXv⟩ := hr.rC hC'
      obtain ⟨-, hXe⟩ := lt_of_getElem? hX
      refine ⟨h1, ?_⟩
      show w.getD (w.length - 2) A1 = A2 ∨ w.getD (w.length - 2) A1 = C1
      rw [hXe]; exact hXv
    · intro hn hC hC2
      have hC' : w[w.length - 1]? = some C1 := by
        rw [getElem?_getD w (by omega)]; exact congrArg some hC
      have hC2' : w[w.length - 2]? = some C1 := by
        rw [getElem?_getD w (by omega)]; exact congrArg some hC2
      exact hr.rCH _ hn hC' hC2' (getElem?_getD w (by omega))

/-! ### Non-vacuity: the word `B1 B1 C1 C1` -/

/-- the word `B1 B1 C1 C1` -/
def exW : ℕ → Ty
  | 0 => B1
  | 1 => B1
  | _ => C1

/-- **The hypotheses of `no_word_fn` without R-CH are satisfiable**: for every `f ≥ 1` the word `B1 B1 C1 C1`
has total length `4f²−2` and satisfies R-Q, R-B, R-GG, R-H2, R-H1 and R-C.  (R-CH is the rule it violates.) -/
theorem exW_rules (f : ℕ) (hf : 1 ≤ f) :
    ∑ m ∈ Finset.range 4, (exW m).len f = 4 * (f * f) - 2 ∧
    (exW 0 ≠ A2 ∧ exW 0 ≠ B2) ∧ (exW 3 = A2 ∨ exW 3 = C1) ∧
    (∀ m, m + 1 < 4 → (exW m).gR → ¬ (exW (m + 1)).gL) ∧
    (∀ m, m < 4 → exW m = C2 → (m = 0 ∨ (exW (m - 1)).gR) →
      m + 1 < 4 ∧ (exW (m + 1) = A1 ∨ exW (m + 1) = C2)) ∧
    (∀ m, m + 1 < 4 → exW m = C1 → (exW (m + 1)).gL → 0 < m ∧ (exW (m - 1) = A2 ∨ exW (m - 1) = C1)) ∧
    (exW 3 = C1 → exW 2 = A2 ∨ exW 2 = C1) ∧
    ¬ ¬ (exW 1).gR := by
  have hff : 1 ≤ f * f := Nat.mul_pos hf hf
  refine ⟨?_, by decide, by decide, ?_, ?_, ?_, by decide, by decide⟩
  · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    show f * f - 1 + (f * f - 1) + f * f + f * f = 4 * (f * f) - 2
    omega
  · intro m hm
    have hm' : m < 3 := by omega
    interval_cases m <;> decide
  · intro m hm
    interval_cases m <;> decide
  · intro m hm
    have hm' : m < 3 := by omega
    interval_cases m <;> decide

end Erdos634.Draft.W2E1

#print axioms Erdos634.Draft.W2E1.letters_L
#print axioms Erdos634.Draft.W2E1.no_word_fn
#print axioms Erdos634.Draft.W2E1.no_word
#print axioms Erdos634.Draft.W2E1.exW_rules

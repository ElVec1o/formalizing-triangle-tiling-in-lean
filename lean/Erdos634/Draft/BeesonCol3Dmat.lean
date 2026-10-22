import Mathlib

/-!
# Beeson (arXiv 1206.2229 v4) Lemmas 36, 37, Corollary 3 and the arithmetic half of Lemma 40 (d-matrix rows)

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Lemmas 34, 36, 37, 40, Corollary 3), Beeson-Rosu, Laczkovich.
Formalization debt, not progress on the /goal outcomes.  Pure integer arithmetic: the geometric inputs (the rows of the d matrix
`Y = g a + n b + f c`, `Z = g' a + l b + f' c`, `X = e a + d b + f'' c`, `X = M(b+c)`, `Y = K b`, `Z = K c`) are NAMED HYPOTHESES.
No H1 is used; no tiling is constructed.

* `l36_split`: Lemma 36 first half: `M k = K m`, `gcd(m,k)=1` gives `M = j m`, `K = j k`, and then `N = 2K^2-M^2 = j^2 (2k^2-m^2)`.
* `l37`: Lemma 37: `k | n`, `k | l`, `d = j m (mod k)`.
* `cor3`: Corollary 3: `n = k t`, `0 <= t < j`; for `j = 1`, `n = 0`.
* `l40_arith`: the arithmetic part of Lemma 40 (`N = 17`): the only solution of `M^2+17 = 2K^2`, `0<M<K` is `(1,3)`; tile `(3,8,9)`;
  `Y = 24` forces `(g,n,f)` among `(8,0,0),(5,0,1),(2,0,2)`.
GAP (quoted exactly, not attempted): "Neither of a = 3, b = 8 is a multiple of the other, so Lemma 38 gives f >= 2 ... We have
|AB| = Kc = 27, so its edge decomposition ... (6, 0, 1): then there would be 7 tiles with an edge on AB, and at least six
'in-betweens' ... making 18" and the rest (boundary-vertex type counting, Tiles 1-7, rays parallel to AB, AC).  Needs edge-level
tile placement and boundary vertex counting; not available.
-/

namespace Erdos634.BeesonCol3Dmat

theorem l36_split {m k M K : ℤ} (hcop : IsCoprime m k) (hm : 0 < m) (h : M * k = K * m) :
    ∃ j : ℤ, M = j * m ∧ K = j * k := by
  have h1 : m ∣ M * k := ⟨K, by linarith⟩
  have h2 : m ∣ M := hcop.dvd_of_dvd_mul_right h1
  obtain ⟨j, hj⟩ := h2
  refine ⟨j, by linarith, ?_⟩
  subst hj
  have : m * (j * k) = m * K := by linarith
  exact (mul_left_cancel₀ hm.ne' this).symm

theorem l36_N {m k j M K N : ℤ} (hM : M = j * m) (hK : K = j * k) (hN : M ^ 2 + N = 2 * K ^ 2) :
    N = j ^ 2 * (2 * k ^ 2 - m ^ 2) := by
  subst hM hK; linarith [hN]

theorem l36_sides {m k j : ℤ} :
    (j * m) * ((k ^ 2 - m ^ 2) + k ^ 2) = j * m * (2 * k ^ 2 - m ^ 2) := by ring

/-- Lemma 37. -/
theorem l37 {m k j a b c X Y Z g f n g' f' l e d f'' : ℤ} (hcop : IsCoprime m k)
    (ha : a = k * m) (hb : b = k ^ 2 - m ^ 2) (hc : c = k ^ 2)
    (hX : X = j * m * (b + c)) (hY : Y = j * k * b) (hZ : Z = j * k * c)
    (h2 : Y = g * a + n * b + f * c) (h3 : Z = g' * a + l * b + f' * c)
    (h1 : X = e * a + d * b + f'' * c) :
    k ∣ n ∧ k ∣ l ∧ d ≡ j * m [ZMOD k] := by
  have hk2 : IsCoprime k (m ^ 2) := (hcop.symm).pow_right
  subst ha hb hc hX hY hZ
  refine ⟨?_, ?_, ?_⟩
  · have : k ∣ n * m ^ 2 := ⟨n * k - j * (k ^ 2 - m ^ 2) + g * m + f * k, by linear_combination h2⟩
    exact hk2.dvd_of_dvd_mul_right this
  · have : k ∣ l * m ^ 2 := ⟨l * k - j * k ^ 2 + g' * m + f' * k, by linear_combination h3⟩
    exact hk2.dvd_of_dvd_mul_right this
  · have key : k ∣ (d - j * m) * m ^ 2 :=
      ⟨d * k + e * m + f'' * k - 2 * j * m * k, by linear_combination h1⟩
    have : k ∣ d - j * m := hk2.dvd_of_dvd_mul_right key
    exact (Int.modEq_iff_dvd.mpr (by simpa using this)).symm

/-- Corollary 3 (from Lemma 34 `n < K`). -/
theorem cor3 {k j n : ℤ} (hk : 0 < k) (hkn : k ∣ n) (hn0 : 0 ≤ n) (hlt : n < j * k) :
    ∃ t : ℤ, n = k * t ∧ 0 ≤ t ∧ t < j ∧ (j = 1 → n = 0) := by
  obtain ⟨t, rfl⟩ := hkn
  have ht0 : 0 ≤ t := by by_contra h; rw [not_le] at h; nlinarith
  have htj : t < j := by by_contra h; rw [not_lt] at h; nlinarith
  refine ⟨t, rfl, ht0, htj, fun hj => ?_⟩
  subst hj; have : t = 0 := by omega
  simp [this]

/-- Lemma 40, arithmetic half. -/
theorem l40_solution {M K : ℤ} (hM : 0 < M) (hMK : M < K) (h : M ^ 2 + 17 = 2 * K ^ 2) : M = 1 ∧ K = 3 := by
  have hK : K ≤ 4 := by nlinarith
  have hM' : M ≤ 3 := by omega
  have hK2 : 2 ≤ K := by omega
  interval_cases K <;> interval_cases M <;> omega

theorem l40_row_Y {g n f : ℕ} (hn : n = 0) (h : 24 = 3 * g + 8 * n + 9 * f) :
    (g, n, f) = (8, 0, 0) ∨ (g, n, f) = (5, 0, 1) ∨ (g, n, f) = (2, 0, 2) := by
  subst hn
  have : f ≤ 2 := by omega
  interval_cases f <;> simp <;> omega

theorem l40_row_Z {g n f : ℕ} (hn : n = 0) (h : 27 = 3 * g + 8 * n + 9 * f) :
    (g, n, f) = (9, 0, 0) ∨ (g, n, f) = (6, 0, 1) ∨ (g, n, f) = (3, 0, 2) ∨ (g, n, f) = (0, 0, 3) := by
  subst hn
  have : f ≤ 3 := by omega
  interval_cases f <;> simp <;> omega

theorem l40_row_X {g d f : ℕ} (h : 17 = 3 * g + 8 * d + 9 * f) :
    (g, d, f) = (0, 1, 1) ∨ (g, d, f) = (3, 1, 0) := by
  have : f ≤ 1 := by omega
  have : d ≤ 2 := by omega
  interval_cases f <;> interval_cases d <;> simp <;> omega

/-- Witness: hypotheses of `l37` hold for the N = 17 data (`j=1,m=1,k=3`, tile `(3,8,9)`, rows `(2,0,2)`, `(3,0,2)`, `(0,1,1)`). -/
theorem l37_wit : ∃ (m k j a b c X Y Z g f n g' f' l e d f'' : ℤ), IsCoprime m k ∧ a = k * m ∧ b = k ^ 2 - m ^ 2 ∧
    c = k ^ 2 ∧ X = j * m * (b + c) ∧ Y = j * k * b ∧ Z = j * k * c ∧ Y = g * a + n * b + f * c ∧
    Z = g' * a + l * b + f' * c ∧ X = e * a + d * b + f'' * c := by
  refine ⟨1, 3, 1, 3, 8, 9, 17, 24, 27, 2, 2, 0, 3, 2, 0, 0, 1, 1, ?_, ?_⟩ <;> norm_num

end Erdos634.BeesonCol3Dmat

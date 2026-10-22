import Mathlib

/-!
# Beeson: small algebraic lemmas of arXiv 1206.1974 v7 (Sect. 11, 12) and arXiv 1206.2229 v4 (Sect. 10, 13)

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.1974 v7, Lemmas 11.12, 11.14, 12.8; arXiv 1206.2229 v4, Lemmas 34, 35, 53, 54,
55 and Corollary 4), Beeson-Rosu, Beeson-Zhang, Laczkovich.  Formalization debt, not progress on the /goal outcomes.
Pure algebra/arithmetic: the geometric inputs (areas, law of cosines, boundary sums) are HYPOTHESES here.  No H1 is used.
WITNESS STATUS (audit round 4, 2026-10-22; only these three results have a witness, and each witness is one real instance):
* witnessed: Lemma 12.8 `l12_8` (`wit_l12_8`, tile `(3,5,7)`); Lemma 11.12 arithmetic `l11_12_dvd` and the arithmetic of
  `l11_12_bound` (`wit_l11_12`, tile `(4,5,6)`, `(k,m)=(2,3)`, `N=20`); Lemma 35 `l35` (`wit_l35`, `lam=1, M=2, K=3`).
* NOT witnessed (the theorem holds for the stated hypotheses, but no instance of those hypotheses is exhibited here):
  `l34`, `l53`, `cor4`, `l54_ii`, `l54_iii`, `l55_core`, `l11_14_finite` (no hypotheses beyond the statement).
  The geometric hypotheses of these results (areas, law of cosines, boundary sums) are unwitnessed.
* `l11_12_dvd` / `l11_12_bound` take `hsum` (`4(p+q+r) < N+1`) as a hypothesis; in the printed proof it is Lemma 11.11 applied
  to one side and is NOT discharged here.  The printed claim `a, b <= m^2` is MISSING from the formalization.
* Lemma 11.14 is formalized ONLY as finiteness of the set of tiles `(k^2, m^2-k^2, mk)` (`l11_14_finite`), nothing more.

Credit (as above): Beeson arXiv 1206.1974 v7 Lemmas 11.12, 11.14, 12.8; Beeson arXiv 1206.2229 v4 Lemmas 34, 35, 53, 54, 55, Cor. 4.
* 1206.1974 Lemma 11.12 (modular step): `l11_12_dvd` (`m | N + (p-q)^2`), `l11_12_bound` (`m < N + (N+1)^2/16` from
  `p+q+r < (N+1)/4`, in the form `16 m < 16 N + (N+1)^2`).
* Lemma 11.14: `l11_14_finite` (finitely many tiles `(k^2, m^2-k^2, mk)` for given `N`).
* Lemma 12.8: `l12_8` (`cos alpha = (2b+a)/(2c)`, `X^2 (2b+a) = N b c^2`, `X Y = N b c`).
* 1206.2229 Lemma 34 `l34`, Lemma 35 `l35` (second proof), Lemma 53 `l53`, Corollary 4 `cor4`, Lemma 54 (ii),(iii)
  `l54_ii`, `l54_iii`, Lemma 55 core `l55_core`.
PRINT NOTE: Lemma 54 (ii) as printed passes from `mu k^2 = M (k^2 + a)` to "`mu = M + (M/k) m`", i.e. uses `a = k m`, `c = k^2`;
this is `mu k = M (k + m)` (`l54_ii`).  Lemma 54 (iii) needs `b` coprime to `k`; `l54_iii` takes `IsCoprime b k` as hypothesis.
-/

namespace Erdos634.Draft.BeesonRow4B

/-! ## Lemma 11.12 -/

theorem l11_12_dvd (k m p q r X N : ℤ) (hX : X = p * k ^ 2 + q * (m ^ 2 - k ^ 2) + r * (m * k))
    (hA : X ^ 2 = N * k ^ 2 * (m ^ 2 - k ^ 2)) (hcop : IsCoprime k m) : m ∣ N + (p - q) ^ 2 := by
  have h1 : m ∣ (N + (p - q) ^ 2) * k ^ 4 := by
    refine ⟨N * k ^ 2 * m - 2 * (p - q) * k ^ 2 * (q * m + r * k) - m * (q * m + r * k) ^ 2, ?_⟩
    subst hX
    linear_combination hA
  exact (hcop.symm.pow_right (n := 4)).dvd_of_dvd_mul_right h1

theorem l11_12_bound (m p q r N : ℤ) (hm : 0 < m) (hN : 0 < N) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hsum : 4 * (p + q + r) < N + 1) (hd : m ∣ N + (p - q) ^ 2) :
    m ≤ N + (p - q) ^ 2 ∧ 16 * m < 16 * N + (N + 1) ^ 2 := by
  have hpos : 0 < N + (p - q) ^ 2 := by positivity
  have h1 := Int.le_of_dvd hpos hd
  refine ⟨h1, ?_⟩
  have h2 : 4 * |p - q| ≤ 4 * (p + q) := by
    have : |p - q| ≤ p + q := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  have h3 : 0 ≤ 4 * |p - q| := by positivity
  have h4 : (4 * |p - q|) ^ 2 < (N + 1) ^ 2 := by
    apply pow_lt_pow_left₀ (by linarith) h3 (by norm_num)
  have h5 : (4 * |p - q|) ^ 2 = 16 * (p - q) ^ 2 := by rw [mul_pow, sq_abs]; ring
  nlinarith

/-! ## Lemma 11.14 -/

theorem l11_14_finite (N : ℕ) :
    {t : ℕ × ℕ × ℕ | ∃ k m : ℕ, Nat.Coprime k m ∧ k < m ∧ m < 2 * k ∧ 16 * m < 16 * N + (N + 1) ^ 2 ∧
      t = (k ^ 2, m ^ 2 - k ^ 2, m * k)}.Finite := by
  set B := 16 * N + (N + 1) ^ 2 with hB
  have hfin : (((Set.Iio B) ×ˢ (Set.Iio B) : Set (ℕ × ℕ)).image
      (fun km : ℕ × ℕ => (km.1 ^ 2, km.2 ^ 2 - km.1 ^ 2, km.2 * km.1))).Finite :=
    ((Set.finite_Iio B).prod (Set.finite_Iio B)).image _
  refine hfin.subset ?_
  rintro t ⟨k, m, -, hkm, -, hmB, rfl⟩
  exact ⟨(k, m), ⟨by simp only [Set.mem_Iio]; omega, by simp only [Set.mem_Iio]; omega⟩, rfl⟩

/-! ## Lemma 12.8 -/

theorem l12_8 (a b c X Y N α : ℝ) (hb : 0 < b) (hc : 0 < c) (hrel : c ^ 2 = a ^ 2 + b ^ 2 + a * b)
    (hlaw : a ^ 2 = b ^ 2 + c ^ 2 - 2 * b * c * Real.cos α)
    (harea : X ^ 2 * Real.sin (2 * α) = N * b * c * Real.sin α) (hs : Real.sin α ≠ 0)
    (hbase : X * Y * Real.sin α = N * b * c * Real.sin α) :
    Real.cos α = (2 * b + a) / (2 * c) ∧ X ^ 2 * (2 * b + a) = N * b * c ^ 2 ∧ X * Y = N * b * c := by
  have hcos : Real.cos α = (2 * b + a) / (2 * c) := by
    rw [eq_div_iff (by positivity)]
    have : 2 * b * c * Real.cos α = 2 * b ^ 2 + a * b := by linarith
    have hb' : b ≠ 0 := hb.ne'
    apply mul_left_cancel₀ hb'
    linear_combination this
  refine ⟨hcos, ?_, mul_right_cancel₀ hs hbase⟩
  rw [Real.sin_two_mul] at harea
  have h2 : 2 * X ^ 2 * Real.cos α = N * b * c := by
    apply mul_right_cancel₀ hs
    linear_combination harea
  rw [hcos] at h2
  field_simp at h2
  nlinarith [h2]

/-! ## Beeson 1206.2229: Lemmas 34, 35, 53, Corollary 4, Lemmas 54, 55 -/

/-- Lemma 34: `mu b = g a + n b + f c` with `f c > 0` gives `n < mu`. -/
theorem l34 (n g f μ a b c : ℕ) (hb : 0 < b) (hf : 0 < f) (hc : 0 < c) (h : μ * b = g * a + n * b + f * c) :
    n < μ := by
  by_contra hn
  push_neg at hn
  have : μ * b ≤ n * b := Nat.mul_le_mul_right _ hn
  have : 0 < f * c := Nat.mul_pos hf hc
  omega

/-- Lemma 35 (second proof): `X - Y + Z = M (a+b+c)`, `Y = K b`, `Z = K c`, `a = lam M`, `c = lam K`,
`b = lam (K - M^2/K)` give `X = M (b + c)`. -/
theorem l35 (lam M K a b c X Y Z : ℝ) (hK : K ≠ 0) (ha : a = lam * M) (hc : c = lam * K)
    (hb : b = lam * (K - M ^ 2 / K)) (hsum : X - Y + Z = M * (a + b + c)) (hY : Y = K * b) (hZ : Z = K * c) :
    X = M * (b + c) := by
  have hKb : K * b = lam * (K ^ 2 - M ^ 2) := by rw [hb]; field_simp
  have : X = M * (a + b + c) + Y - Z := by linarith
  rw [this, hY, hZ, hKb, ha, hc]
  ring

/-- Lemma 53: `X = mu c`, `Y = mu a`, `X Y = N a b` give `mu^2 c = N b`. -/
theorem l53 (μ a b c X Y N : ℝ) (ha : a ≠ 0) (hX : X = μ * c) (hY : Y = μ * a) (hXY : X * Y = N * a * b) :
    μ ^ 2 * c = N * b := by
  apply mul_left_cancel₀ ha
  rw [hX, hY] at hXY
  linear_combination hXY

/-- Corollary 4: `s = a/c = Y/X` and `N (1 - s) = M^2 (1 + s)` give `M^2 = N (X - Y)/(X + Y)`. -/
theorem cor4 (M N X Y s : ℝ) (hX : 0 < X) (hY : 0 ≤ Y) (hs : s = Y / X) (heq : N * (1 - s) = M ^ 2 * (1 + s)) :
    M ^ 2 = N * (X - Y) / (X + Y) := by
  have hXY : 0 < X + Y := by linarith
  rw [eq_div_iff hXY.ne']
  have hX' : X ≠ 0 := hX.ne'
  subst hs
  field_simp at heq
  linear_combination -heq

/-- Lemma 54 (ii): `mu c = M (c + a)` with `c = k^2`, `a = k m`, `k != 0` gives `mu k = M (k + m)`. -/
theorem l54_ii (μ M k m a c : ℝ) (hk : k ≠ 0) (hc : c = k ^ 2) (ha : a = k * m) (h : μ * c = M * (c + a)) :
    μ * k = M * (k + m) := by
  apply mul_left_cancel₀ hk
  rw [hc, ha] at h
  linear_combination h

/-- Lemma 54 (iii): `M (a + b + c) = 2 X - Y`, `k | X, a, c`, `Y = q b + k t`, `b` coprime to `k` give `k | M + q`
(i.e. `M = -q mod k`). -/
theorem l54_iii (k M q a b c X Y t : ℤ) (hX : k ∣ X) (ha : k ∣ a) (hc : k ∣ c) (hY : Y = q * b + k * t)
    (hsum : M * (a + b + c) = 2 * X - Y) (hcop : IsCoprime b k) : k ∣ M + q := by
  obtain ⟨x, hx⟩ := hX
  obtain ⟨a', ha'⟩ := ha
  obtain ⟨c', hc'⟩ := hc
  have : k ∣ b * (M + q) := ⟨2 * x - t - M * a' - M * c', by
    rw [hx, ha', hc', hY] at hsum; linear_combination hsum⟩
  exact hcop.symm.dvd_of_dvd_mul_left this

/-- Lemma 55, core: `X^2 = N b c`, `N (c - a) = M^2 (c + a)`, `b` squarefree and coprime to `c - a` give `b | X`. -/
theorem l55_core (N M a b c X : ℤ) (hsq : Squarefree b) (hcop : IsCoprime b (c - a)) (hX : X ^ 2 = N * b * c)
    (hN : N * (c - a) = M ^ 2 * (c + a)) : b ∣ X := by
  have h1 : b ∣ X ^ 2 * (c - a) := ⟨M ^ 2 * (c + a) * c, by
    rw [hX]; linear_combination c * b * hN⟩
  have h2 : b ∣ X ^ 2 := hcop.dvd_of_dvd_mul_right h1
  exact (hsq.dvd_pow_iff_dvd (by norm_num)).mp h2

/-! ## Witnesses: every hypothesis is satisfiable -/

/-- Lemma 11.12 on the tile `(4,5,6)`, `(k,m) = (2,3)`, `N = 20`, `X = 20 = a + 2b + c`. -/
theorem wit_l11_12 : IsCoprime (2 : ℤ) 3 ∧ ((20 : ℤ) = 1 * 2 ^ 2 + 2 * (3 ^ 2 - 2 ^ 2) + 1 * (3 * 2)) ∧
    ((20 : ℤ) ^ 2 = 20 * 2 ^ 2 * (3 ^ 2 - 2 ^ 2)) ∧ (3 : ℤ) ∣ 20 + (1 - 2) ^ 2 ∧ 4 * (1 + 2 + 1 : ℤ) < 20 + 1 := by
  refine ⟨⟨-1, 1, by norm_num⟩, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Lemma 12.8 on the tile `(3,5,7)` (`N = 75140`, `X = 1190`, `Y = 2210`): all hypotheses hold, `cos alpha = 13/14`. -/
theorem wit_l12_8 : ∃ α : ℝ, (7 : ℝ) ^ 2 = 3 ^ 2 + 5 ^ 2 + 3 * 5 ∧
    (3 : ℝ) ^ 2 = 5 ^ 2 + 7 ^ 2 - 2 * 5 * 7 * Real.cos α ∧
    (1190 : ℝ) ^ 2 * Real.sin (2 * α) = 75140 * 5 * 7 * Real.sin α ∧ Real.sin α ≠ 0 ∧
    (1190 : ℝ) * 2210 * Real.sin α = 75140 * 5 * 7 * Real.sin α := by
  have hc : Real.cos (Real.arccos (13 / 14)) = 13 / 14 := Real.cos_arccos (by norm_num) (by norm_num)
  have hs : 0 < Real.sin (Real.arccos (13 / 14)) := by
    rw [Real.sin_arccos]; apply Real.sqrt_pos.mpr; norm_num
  refine ⟨Real.arccos (13 / 14), by norm_num, ?_, ?_, hs.ne', by ring⟩
  · rw [hc]; norm_num
  · rw [Real.sin_two_mul, hc]; ring

/-- Lemma 35 on `lam = 1`, `M = 2`, `K = 3` (`N = 14`). -/
theorem wit_l35 : (2 : ℝ) = 1 * 2 ∧ (3 : ℝ) = 1 * 3 ∧ (5 / 3 : ℝ) = 1 * (3 - 2 ^ 2 / 3) ∧
    (28 / 3 : ℝ) - 5 + 9 = 2 * (2 + 5 / 3 + 3) ∧ (5 : ℝ) = 3 * (5 / 3) ∧ (9 : ℝ) = 3 * 3 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

#print axioms l11_12_dvd
#print axioms l11_12_bound
#print axioms l11_14_finite
#print axioms l12_8
#print axioms l34
#print axioms l35
#print axioms l53
#print axioms cor4
#print axioms l54_ii
#print axioms l54_iii
#print axioms l55_core
#print axioms wit_l12_8

end Erdos634.Draft.BeesonRow4B

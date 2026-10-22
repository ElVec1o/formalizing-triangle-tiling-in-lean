import Mathlib
import Erdos634.Draft.BeesonRowSect10
import Erdos634.Draft.BeesonRow2Trig
import Erdos634.Draft.BeesonRow3L48
import Erdos634.Draft.BeesonCol3Dmat

/-!
# Beeson (arXiv 1206.2229 v4) Lemmas 31, 32, 33, 36 (full), 38: the d-matrix block, trigonometric and algebraic parts

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Sect. 10, Lemmas 31, 32, 33, 36, 38, Theorem 1 for the colouring
identity), Beeson-Rosu, Laczkovich (DCG 48 (2012)), Beeson-Zhang.  Formalization debt, not progress on the /goal outcomes.

No tiling is constructed and no H1 is used except in `l38` (named).  What the printed proofs use, and nothing else, is named:
* `l31`  : law of sines in the tile and in `ABC` (angles `2 alpha, beta, alpha + beta`)  ->  `(X, Y, Z) = mu ((2 - s^2) a, b, c)`.
* `l32`  : Theorem 1 colour identity `M (a + b + c) = X - Y + Z` (hypothesis `hthm1`) and the area identity
           `N b c sin alpha = Y Z sin 2 alpha` (hypothesis `harea`)  ->  `M = mu s`, `N = mu^2 (2 - s^2)`, `s^2 (M^2 + N) = 2 M^2`.
* `l33`  : `s = M/K`, `N + M^2 = 2 K^2`  ->  `mu = K`, `(a, b, c) = lam (M, N/K - K, K)`, `(X, Y, Z) = lam (M N/K, N - K^2, K^2)`.
* `l36_dvd_iff`, `l36_main` : `K | M^2 <-> k | j` and the integer parametrisation `M = j m`, `K = j k`, `N = j^2 (2k^2 - m^2)`.
* `l38` : the four hypotheses of printed Lemma 8 are verified from (3 alpha + 2 beta = pi, H1, non-multiples); the conclusion
           `f >= 2` follows from Lemma 8, which is a NAMED hypothesis (`h8`, the open row R-L31 / BR Lemma 31).
-/

namespace Erdos634.BeesonCol5Dmat

open Real

theorem two_sub_s_sq (α : ℝ) : 2 - (2 * Real.sin (α / 2)) ^ 2 = 2 * Real.cos α := by
  have h := Real.cos_two_mul (α / 2)
  rw [show 2 * (α / 2) = α by ring] at h
  have sc := Real.sin_sq_add_cos_sq (α / 2)
  linear_combination (-2) * h + (-4) * sc

/-- Printed Lemma 31. -/
theorem l31 {α β γ a b c X Y Z lam s : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hs : α + β + γ = π)
    (hc : 0 < c) (hsdef : s = 2 * Real.sin (α / 2))
    (la : a * Real.sin γ = c * Real.sin α) (lb : b * Real.sin γ = c * Real.sin β)
    (hlam : 0 < lam) (hX : X = lam * Real.sin (2 * α)) (hY : Y = lam * Real.sin β)
    (hZ : Z = lam * Real.sin (α + β)) :
    ∃ μ : ℝ, 0 < μ ∧ X = μ * ((2 - s ^ 2) * a) ∧ Y = μ * b ∧ Z = μ * c := by
  have hγe : γ = π - (α + β) := by linarith
  have sγ : Real.sin γ = Real.sin (α + β) := by rw [hγe, Real.sin_pi_sub]
  have sγpos : 0 < Real.sin γ := Real.sin_pos_of_pos_of_lt_pi hγ (by linarith)
  have hμc : lam * Real.sin γ / c * c = lam * Real.sin γ := by field_simp
  refine ⟨lam * Real.sin γ / c, by positivity, ?_, ?_, ?_⟩
  · apply mul_left_cancel₀ hc.ne'
    rw [hsdef, two_sub_s_sq, hX, Real.sin_two_mul]
    linear_combination (-2 * Real.cos α * a) * hμc + (-2 * lam * Real.cos α) * la
  · apply mul_left_cancel₀ hc.ne'
    rw [hY]
    linear_combination (-lam) * lb + (-b) * hμc
  · apply mul_left_cancel₀ hc.ne'
    rw [hZ, ← sγ]
    linear_combination (-c) * hμc

/-- Printed Lemma 32 (tiling equation), from Lemma 31 forms, Theorem 1 and the area identity. -/
theorem l32 {α β γ a b c X Y Z μ M N s : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hs : α + β + γ = π)
    (h3 : 3 * α + 2 * β = π) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hsdef : s = 2 * Real.sin (α / 2))
    (la : a * Real.sin γ = c * Real.sin α) (lb : b * Real.sin γ = c * Real.sin β)
    (hμ : 0 < μ) (hX : X = μ * ((2 - s ^ 2) * a)) (hY : Y = μ * b) (hZ : Z = μ * c)
    (hthm1 : M * (a + b + c) = X - Y + Z) (harea : N * b * c * Real.sin α = Y * Z * Real.sin (2 * α)) :
    M = μ * s ∧ N = μ ^ 2 * (2 - s ^ 2) ∧ 0 < M ∧ s ^ 2 * (M ^ 2 + N) = 2 * M ^ 2 := by
  obtain ⟨-, -, hac', -, hbc', -, -⟩ := Erdos634.BeesonRow.lemma25 α β γ a b c hα hβ hγ hs h3 ha hb hc la lb
  rw [← hsdef] at hac'
  have hac : a = s * c := by rw [div_eq_iff hc.ne'] at hac'; exact hac'
  have hbc : b = (1 - s ^ 2) * c := by
    rw [hac'] at hbc'
    rw [div_eq_iff hc.ne'] at hbc'; exact hbc'
  have hδ : 0 < Real.sin (α + β) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hκ : 0 < c / Real.sin (α + β) := by positivity
  have hcκ : c = c / Real.sin (α + β) * Real.sin (α + β) := by field_simp
  obtain ⟨hs0, hs1, -⟩ := Erdos634.BeesonColoring.lemma48 h3 hα hβ hκ hsdef hcκ
  have hsin2 : Real.sin (2 * α) = (2 - s ^ 2) * Real.sin α := by
    rw [Real.sin_two_mul, hsdef, two_sub_s_sq]; ring
  have hsa : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα (by linarith)
  have hMs : M = μ * s := by
    have key : (M - μ * s) * ((2 + s - s ^ 2) * c) = 0 := by
      rw [hX, hY, hZ, hac, hbc] at hthm1
      linear_combination hthm1
    have hpos : 0 < (2 + s - s ^ 2) * c := mul_pos (by nlinarith) hc
    rcases mul_eq_zero.mp key with h | h
    · linarith
    · exact absurd h hpos.ne'
  have hN : N = μ ^ 2 * (2 - s ^ 2) := by
    have key : (N - μ ^ 2 * (2 - s ^ 2)) * (b * c * Real.sin α) = 0 := by
      rw [hY, hZ, hsin2] at harea
      linear_combination harea
    have hpos : 0 < b * c * Real.sin α := by positivity
    rcases mul_eq_zero.mp key with h | h
    · linarith
    · exact absurd h hpos.ne'
  refine ⟨hMs, hN, by rw [hMs]; positivity, ?_⟩
  rw [hMs, hN]; ring

/-- Printed Lemma 33. -/
theorem l33 {a b c X Y Z μ M K N s : ℝ} (hK : 0 < K) (hM : 0 < M) (hc : 0 < c) (hsK : s = M / K)
    (hMs : M = μ * s) (hN : N + M ^ 2 = 2 * K ^ 2) (hac : a = s * c) (hbc : b = (1 - s ^ 2) * c)
    (hX : X = μ * ((2 - s ^ 2) * a)) (hY : Y = μ * b) (hZ : Z = μ * c) :
    μ = K ∧ ∃ lam : ℝ, 0 < lam ∧ a = lam * M ∧ b = lam * (N / K - K) ∧ c = lam * K ∧
      X = lam * (M * N / K) ∧ Y = lam * (N - K ^ 2) ∧ Z = lam * K ^ 2 := by
  have hK' := hK.ne'
  have hM' := hM.ne'
  have hμK : μ = K := by
    subst hsK
    have h2 : μ * (M / K) * K = μ * M := by field_simp
    have h4 : M * K = μ * M := by rw [← h2, ← hMs]
    have : M * (K - μ) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hM'
    · linarith
  subst hsK
  have hN' : N = 2 * K ^ 2 - M ^ 2 := by linarith
  refine ⟨hμK, c / K, by positivity, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hac]; field_simp
  · rw [hbc, hN']; field_simp; try ring
  · field_simp
  · rw [hX, hac, hμK, hN']; field_simp; try ring
  · rw [hY, hbc, hμK, hN']; field_simp; try ring
  · rw [hZ, hμK]; field_simp

/-- Lemma 33, the d-matrix equation in `lam`-form: if row `i` reads `X = p a + d b + e c` etc., substituting the
`lam`-values gives the printed three equations. -/
theorem l33_rows {a b c X Y Z M K N lam p d e g n f h l r : ℝ}
    (ha : a = lam * M) (hb : b = lam * (N / K - K)) (hc : c = lam * K)
    (hX : X = lam * (M * N / K)) (hY : Y = lam * (N - K ^ 2)) (hZ : Z = lam * K ^ 2)
    (r1 : X = p * a + d * b + e * c) (r2 : Y = g * a + n * b + f * c) (r3 : Z = h * a + l * b + r * c) :
    lam * (M * N / K) = p * (lam * M) + d * (lam * (N / K - K)) + e * (lam * K) ∧
    lam * (N - K ^ 2) = g * (lam * M) + n * (lam * (N / K - K)) + f * (lam * K) ∧
    lam * K ^ 2 = h * (lam * M) + l * (lam * (N / K - K)) + r * (lam * K) := by
  subst ha hb hc hX hY hZ
  exact ⟨r1, r2, r3⟩

/-- Printed Lemma 36, last sentence: `K | M^2 <-> k | j`. -/
theorem l36_dvd_iff {m k j : ℤ} (hcop : IsCoprime m k) (hj : 0 < j) :
    (j * k) ∣ (j * m) ^ 2 ↔ k ∣ j := by
  have hk2 : IsCoprime k (m ^ 2) := hcop.symm.pow_right
  constructor
  · rintro ⟨t, ht⟩
    have h1 : k ∣ j * m ^ 2 := ⟨t, by
      apply mul_left_cancel₀ hj.ne'
      linear_combination ht⟩
    exact hk2.dvd_of_dvd_mul_right h1
  · rintro ⟨u, rfl⟩
    exact ⟨u * m ^ 2, by ring⟩

/-- Printed Lemma 36 (arithmetic): `M k = K m`, `gcd(m,k) = 1`, `N = 2K^2 - M^2` give `M = j m`, `K = j k`,
`N = j^2 (2k^2 - m^2)`, and `K | M^2 <-> k | j`. -/
theorem l36_main {m k M K N : ℤ} (hcop : IsCoprime m k) (hm : 0 < m) (hk : 0 < k) (hK : 0 < K) (h : M * k = K * m)
    (hN : M ^ 2 + N = 2 * K ^ 2) :
    ∃ j : ℤ, 0 < j ∧ M = j * m ∧ K = j * k ∧ N = j ^ 2 * (2 * k ^ 2 - m ^ 2) ∧ (K ∣ M ^ 2 ↔ k ∣ j) := by
  obtain ⟨j, hM, hKj⟩ := Erdos634.BeesonCol3Dmat.l36_split hcop hm h
  have hj : 0 < j := by
    by_contra hj
    nlinarith [hKj]
  refine ⟨j, hj, hM, hKj, Erdos634.BeesonCol3Dmat.l36_N hM hKj hN, ?_⟩
  rw [hKj, hM]; exact l36_dvd_iff hcop hj

/-- The hypotheses of printed Lemma 8 are verified from `3 alpha + 2 beta = pi`, H1. -/
theorem l38_hyps {α β γ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hs : α + β + γ = π) (h3 : 3 * α + 2 * β = π)
    (H1 : ¬ ∃ r : ℚ, α = (r : ℝ) * π) :
    π / 2 < γ ∧ (¬ ∃ r : ℚ, α = (r : ℝ) * β) ∧ (2 * α < γ ∧ β < γ ∧ α + β < γ) := by
  refine ⟨by linarith, (Erdos634.BeesonRow2.lemma38_arith α β h3 hβ H1).2, by linarith, by linarith, by linarith⟩

/-- Printed Lemma 38.  `h8` is printed Lemma 8 (at least two c edges on a side), NOT proved here (open row R-L31):
hypotheses (i) `gamma > pi/2`, (ii) `alpha/beta` irrational, (iii) every angle of ABC (`2 alpha, beta, alpha + beta`) is
below `gamma`, (iv) neither of `a, b` is an integer multiple of the other. -/
theorem l38 {α β γ : ℝ} {a b : ℝ} {f : ℕ} (hα : 0 < α) (hβ : 0 < β) (hs : α + β + γ = π)
    (h3 : 3 * α + 2 * β = π) (H1 : ¬ ∃ r : ℚ, α = (r : ℝ) * π)
    (hiv : ¬ (∃ q : ℕ, a = q * b) ∧ ¬ (∃ q : ℕ, b = q * a))
    (h8 : π / 2 < γ → (¬ ∃ r : ℚ, α = (r : ℝ) * β) → (2 * α < γ ∧ β < γ ∧ α + β < γ) →
      (¬ (∃ q : ℕ, a = q * b) ∧ ¬ (∃ q : ℕ, b = q * a)) → 2 ≤ f) :
    2 ≤ f := by
  obtain ⟨h1, h2, h3'⟩ := l38_hyps hα hβ hs h3 H1
  exact h8 h1 h2 h3' hiv

/-! ## Witnesses -/

/-- `l31`: the hypotheses hold for every admissible angle triple (sides and ABC chosen by the law of sines). -/
theorem l31_wit (α β γ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hs : α + β + γ = π) :
    ∃ (a b c X Y Z lam s : ℝ), 0 < c ∧ s = 2 * Real.sin (α / 2) ∧
      a * Real.sin γ = c * Real.sin α ∧ b * Real.sin γ = c * Real.sin β ∧ 0 < lam ∧
      X = lam * Real.sin (2 * α) ∧ Y = lam * Real.sin β ∧ Z = lam * Real.sin (α + β) := by
  have sγpos : 0 < Real.sin γ := Real.sin_pos_of_pos_of_lt_pi hγ (by linarith)
  exact ⟨Real.sin α, Real.sin β, Real.sin γ, 1 * Real.sin (2 * α), 1 * Real.sin β, 1 * Real.sin (α + β), 1,
    2 * Real.sin (α / 2), sγpos, rfl, by ring, by ring, one_pos, rfl, rfl, rfl⟩

/-- `l32` (and `l33`): witness at `alpha = beta = pi/5` (`gamma = 3 pi/5`), `mu = 1`, `M = s`, `N = 2 - s^2`, where the
colour identity and the area identity of the printed proof hold by the trigonometric identities of Lemma 25 / 48. -/
theorem l32_wit : ∃ (α β γ a b c X Y Z μ M N s : ℝ), 0 < α ∧ 0 < β ∧ 0 < γ ∧ α + β + γ = π ∧ 3 * α + 2 * β = π ∧
    0 < a ∧ 0 < b ∧ 0 < c ∧ s = 2 * Real.sin (α / 2) ∧
    a * Real.sin γ = c * Real.sin α ∧ b * Real.sin γ = c * Real.sin β ∧ 0 < μ ∧
    X = μ * ((2 - s ^ 2) * a) ∧ Y = μ * b ∧ Z = μ * c ∧
    M * (a + b + c) = X - Y + Z ∧ N * b * c * Real.sin α = Y * Z * Real.sin (2 * α) := by
  have hpi := Real.pi_pos
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = π / 5 := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = π / 5 := ⟨_, rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = 3 * π / 5 := ⟨_, rfl⟩
  have hs : α + β + γ = π := by rw [hα, hβ, hγ]; ring
  have h3 : 3 * α + 2 * β = π := by rw [hα, hβ]; ring
  have sγpos : 0 < Real.sin γ := Real.sin_pos_of_pos_of_lt_pi (by rw [hγ]; positivity) (by rw [hγ]; linarith)
  have sapos : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi (by rw [hα]; positivity) (by rw [hα]; linarith)
  have sbpos : 0 < Real.sin β := Real.sin_pos_of_pos_of_lt_pi (by rw [hβ]; positivity) (by rw [hβ]; linarith)
  have la : Real.sin α * Real.sin γ = Real.sin γ * Real.sin α := by ring
  have lb : Real.sin β * Real.sin γ = Real.sin γ * Real.sin β := by ring
  obtain ⟨-, -, hac', -, hbc', -, -⟩ := Erdos634.BeesonRow.lemma25 α β γ (Real.sin α) (Real.sin β) (Real.sin γ)
    (by rw [hα]; positivity) (by rw [hβ]; positivity) (by rw [hγ]; positivity) hs h3 sapos sbpos sγpos la lb
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = 2 * Real.sin (α / 2) := ⟨_, rfl⟩
  rw [← hsdef] at hac'
  have hac : Real.sin α = s * Real.sin γ := (div_eq_iff sγpos.ne').1 hac'
  have hbc : Real.sin β = (1 - s ^ 2) * Real.sin γ := by
    rw [hac'] at hbc'; exact (div_eq_iff sγpos.ne').1 hbc'
  have hsin2 : Real.sin (2 * α) = (2 - s ^ 2) * Real.sin α := by
    rw [Real.sin_two_mul, hsdef, two_sub_s_sq]; ring
  refine ⟨α, β, γ, Real.sin α, Real.sin β, Real.sin γ, (2 - s ^ 2) * Real.sin α, Real.sin β, Real.sin γ, 1, s, 2 - s ^ 2, s,
    by rw [hα]; positivity, by rw [hβ]; positivity, by rw [hγ]; positivity, hs, h3, sapos, sbpos, sγpos, hsdef, la, lb,
    one_pos, by ring, by ring, by ring, ?_, ?_⟩
  · rw [hac, hbc]; ring
  · rw [hsin2]; ring

/-- `l33`: hypotheses hold for the tile `(2,3,4)` with `(M,K,N) = (1,2,7)`, `s = 1/2`, `mu = 2`, `(X,Y,Z) = (7,6,8)`. -/
theorem l33_wit : ∃ (a b c X Y Z μ M K N s : ℝ), 0 < K ∧ 0 < M ∧ 0 < c ∧ s = M / K ∧ M = μ * s ∧ N + M ^ 2 = 2 * K ^ 2 ∧
    a = s * c ∧ b = (1 - s ^ 2) * c ∧ X = μ * ((2 - s ^ 2) * a) ∧ Y = μ * b ∧ Z = μ * c :=
  ⟨2, 3, 4, 7, 6, 8, 2, 1, 2, 7, 1 / 2, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- `l36_main`: witness `(m, k, j) = (1, 2, 1)`, `M = 1`, `K = 2`, `N = 7`. -/
theorem l36_main_wit : ∃ (m k M K N : ℤ), IsCoprime m k ∧ 0 < m ∧ 0 < K ∧ M * k = K * m ∧ M ^ 2 + N = 2 * K ^ 2 :=
  ⟨1, 2, 1, 2, 7, ⟨1, 0, by norm_num⟩, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- `l38`: hypotheses (i)-(iii) hold for the tile `(2,3,4)`, `alpha = arccos(7/8)`. -/
theorem l38_wit : ∃ α β γ : ℝ, 0 < α ∧ 0 < β ∧ α + β + γ = π ∧ 3 * α + 2 * β = π ∧
    (¬ ∃ r : ℚ, α = (r : ℝ) * π) ∧ π / 2 < γ ∧ (¬ ∃ r : ℚ, α = (r : ℝ) * β) ∧
    (2 * α < γ ∧ β < γ ∧ α + β < γ) := by
  have hα : 0 < Real.arccos (7 / 8) := Real.arccos_pos.mpr (by norm_num)
  have hlt : Real.arccos (7 / 8) < π / 3 := by
    have h := Real.arccos_lt_arccos (x := 1 / 2) (y := 7 / 8) (by norm_num) (by norm_num) (by norm_num)
    have e : Real.arccos (1 / 2) = π / 3 := by
      rw [show (1 / 2 : ℝ) = Real.cos (π / 3) by rw [Real.cos_pi_div_three]]
      exact Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])
    linarith
  have hβ : 0 < (π - 3 * Real.arccos (7 / 8)) / 2 := by linarith
  have h3 : 3 * Real.arccos (7 / 8) + 2 * ((π - 3 * Real.arccos (7 / 8)) / 2) = π := by ring
  obtain ⟨h1, h2, h3'⟩ := l38_hyps (γ := π - Real.arccos (7 / 8) - (π - 3 * Real.arccos (7 / 8)) / 2) hα hβ
    (by ring) h3 Erdos634.BeesonRow.wit_h1_234
  exact ⟨_, _, _, hα, hβ, by ring, h3, Erdos634.BeesonRow.wit_h1_234, h1, h2, h3'⟩

#print axioms two_sub_s_sq
#print axioms l31
#print axioms l32
#print axioms l33
#print axioms l33_rows
#print axioms l36_dvd_iff
#print axioms l36_main
#print axioms l38_hyps
#print axioms l38
#print axioms l31_wit
#print axioms l32_wit
#print axioms l33_wit
#print axioms l36_main_wit
#print axioms l38_wit

end Erdos634.BeesonCol5Dmat

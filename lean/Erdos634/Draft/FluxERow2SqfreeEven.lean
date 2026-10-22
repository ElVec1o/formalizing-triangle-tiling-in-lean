-- Draft/FluxERow2SqfreeEven.lean — UNAUDITED variant of FluxERow2Sqfree17 for N = 14: hypothesis `17 ≤ N` replaced by `7 ≤ N ∧ (17 ≤ N ∨ N % 4 = 2)` (m' = ±1 killed by U²−4W ≡ 0,1 (mod 4) vs p ≡ 2 (mod 4)).  Formalization debt, NOT /goal progress.  Original header follows.
-- on N: the conclusion is `∃ x y, N = x² + y²` (the paper's "similar-tile N-form"; `HBSimilar N`).  Copy of
-- FluxERow2Sqfree.lean (N ≡ 3 mod 4, N ≥ 7, conclusion `N % 4 ≠ 3`) with two changes:
--   (1) Lemma Q: the bound `p m'² ≤ 16` kills `m' ≠ 0` outright once `p ≥ 17`, so the mod-4 analysis of the case
--       `p m'² = p` (which needed p ≡ 3 mod 4) is not needed;
--   (2) the sorted core ends with `N = A² + B²` and returns it instead of reducing mod 4.
-- Lemma W / Lemma E-abstract / Lemma K / Lemma D / Lemma R are the existing N-free ones.  UNAUDITED.
-- Formalization debt; NOT /goal progress (it does discharge the cited `HBSimilar N` for squarefree N ≥ 17).
import Erdos634.Draft.FluxERow2Sqfree

open scoped Classical
open Real

namespace Erdos634.Geometry

variable {N : ℕ}

/-- **Lemma Q (row 2).**  Let `p ≡ 3 (mod 4)` be a prime, `p ≥ 7`, and `s² = p`.  If `θ ∈ (0, π)` is a
rational multiple of `π` with `cos θ ∈ ℚ + ℚ s`, then `θ ∈ {π/3, π/2, 2π/3}`. -/
theorem Row2.lemmaQ_sqfreeE {p : ℕ} (hp : Squarefree p) (hp7 : 7 ≤ p) (hp17 : 17 ≤ p ∨ p % 4 = 2) {s : ℝ}
    (hs : s ^ 2 = p) {θ : ℝ} (hθ : ∃ r : ℚ, θ = r * π) (hθ0 : 0 < θ) (hθπ : θ < π)
    (hc : Row2.QMu s (Real.cos θ)) :
    θ = π / 3 ∨ θ = π / 2 ∨ θ = π * (2 / 3) := by
  have hpns : ¬ IsSquare p := Row2.sqfree_not_square hp hp7
  obtain ⟨r, hr⟩ := hθ
  obtain ⟨q₁, q₂, hq⟩ := hc
  have hsq : s ^ 2 = ((p : ℚ) : ℝ) := by rw [hs]; push_cast; ring
  -- `s` is irrational
  have hirr : ∀ q : ℚ, s ≠ q := by
    intro q hsq'
    have habs : √(p : ℝ) = |(q : ℝ)| := by
      rw [← hsq', ← hs, Real.sqrt_sq_eq_abs]
    exact (irrational_sqrt_natCast_iff.mpr hpns) ⟨|q|, by rw [habs]; push_cast; rfl⟩
  -- `x = a + b s`, `x' = a − b s`
  set a : ℚ := 2 * q₁ with ha
  set b : ℚ := 2 * q₂ with hb
  set x : ℝ := 2 * Real.cos θ with hx
  have hxab : x = (a : ℝ) + b * s := by rw [hx, hq, ha, hb]; push_cast; ring
  set x' : ℝ := (a : ℝ) - b * s with hx'
  -- `x` is integral; so is `x'`
  have hxint : IsIntegral ℤ x := by
    rw [hx, hr]; exact Real.isIntegral_two_mul_cos_rat_mul_pi r
  have hx'int : IsIntegral ℤ x' := by
    obtain ⟨P, hPm, hP⟩ := hxint
    obtain ⟨A, B, h1, h2⟩ := Row2.poly_conj hsq a b P
    rw [hxab, h1] at hP
    have hB : B = 0 := by
      by_contra hB0
      apply hirr (-A / B)
      have hBr : (B : ℝ) ≠ 0 := by exact_mod_cast hB0
      push_cast; field_simp; linarith
    have hA : (A : ℝ) = 0 := by rw [hB] at hP; simpa using hP
    exact ⟨P, hPm, by rw [hx', h2, hA, hB]; simp⟩
  -- `|x| ≤ 2` and `|x'| ≤ 2`
  have hxle : |x| ≤ 2 := by
    rw [hx, abs_mul, abs_two]
    have := Real.abs_cos_le_one θ
    linarith
  set n : ℕ := 2 * r.den with hn
  have hnpos : 0 < n := by positivity
  have hchebx : Row2.cheb x n = 2 := by
    rw [hx, Row2.cheb_cos θ n, hr]
    have : ((n : ℕ) : ℝ) * ((r : ℝ) * π) = (r.num : ℝ) * (2 * π) := by
      rw [hn]; push_cast
      have hd : (r : ℝ) * r.den = r.num := by exact_mod_cast Rat.mul_den_eq_num r
      linear_combination (2 * π) * hd
    rw [this, Real.cos_int_mul_two_pi]; ring
  have hx'le : |x'| ≤ 2 := by
    obtain ⟨A, B, h1, h2⟩ := Row2.cheb_conj hsq a b n
    rw [← hxab, hchebx] at h1
    have hB : B = 0 := by
      by_contra hB0
      apply hirr ((2 - A) / B)
      have hBr : (B : ℝ) ≠ 0 := by exact_mod_cast hB0
      push_cast; field_simp; linarith
    have hA : (A : ℝ) = 2 := by rw [hB] at h1; simpa using h1.symm
    refine Row2.abs_le_two_of_cheb hnpos ?_
    rw [hx', h2, hA, hB]; simp
  -- `U = x + x' = 2a ∈ ℤ`, `W = x x' = a² − b² p ∈ ℤ`
  obtain ⟨U, hU⟩ := (hxint.add hx'int).exists_int_iff_exists_rat.mp
    ⟨2 * a, by rw [hxab, hx']; push_cast; ring⟩
  obtain ⟨W, hW⟩ := (hxint.mul hx'int).exists_int_iff_exists_rat.mp
    ⟨a * a - b * b * p, by rw [hxab, hx']; push_cast; linear_combination (-(b : ℝ) ^ 2) * hs⟩
  -- `V = 2b`, `p V² = U² − 4W`
  have hVZ : ((p : ℝ)) * ((2 * b : ℚ) : ℝ) ^ 2 = ((U ^ 2 - 4 * W : ℤ) : ℝ) := by
    have e1 : (U : ℝ) = 2 * a := by rw [← hU, hxab, hx']; ring
    have e2 : (W : ℝ) = a * a - b * b * p := by
      rw [← hW, hxab, hx']; linear_combination (-(b : ℝ) ^ 2) * hs
    push_cast; rw [e1, e2]; ring
  -- `pV ∈ ℤ`
  have hpVint : IsIntegral ℤ (((p * (2 * b) : ℚ)) : ℝ) := by
    refine IsIntegral.of_pow (n := 2) two_pos ?_
    have : (((p * (2 * b) : ℚ)) : ℝ) ^ 2 = (((p : ℤ) * (U ^ 2 - 4 * W) : ℤ) : ℝ) := by
      push_cast at hVZ ⊢; rw [← hVZ]; ring
    rw [this]; exact Row2.isIntegral_intCast _
  obtain ⟨m, hm⟩ := hpVint.exists_int_iff_exists_rat.mp ⟨_, rfl⟩
  -- `m² = p (U² − 4W)`, so `p ∣ m`
  have hm2 : m ^ 2 = (p : ℤ) * (U ^ 2 - 4 * W) := by
    have : ((m ^ 2 : ℤ) : ℝ) = (((p : ℤ) * (U ^ 2 - 4 * W) : ℤ) : ℝ) := by
      push_cast at hVZ hm ⊢; rw [← hm, ← hVZ]; ring
    exact_mod_cast this
  obtain ⟨m', hm'⟩ : (p : ℤ) ∣ m :=
    ((Int.squarefree_natCast.mpr hp).dvd_pow_iff_dvd (by norm_num : 2 ≠ 0)).mp ⟨_, hm2⟩
  have hpne : p ≠ 0 := by omega
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hpne
  have hZ : U ^ 2 - 4 * W = (p : ℤ) * m' ^ 2 := by
    rw [hm'] at hm2
    have : (p : ℤ) * ((p : ℤ) * m' ^ 2) = (p : ℤ) * (U ^ 2 - 4 * W) := by rw [← hm2]; ring
    exact (mul_left_cancel₀ hp0 this).symm
  -- `V = m'`
  have hVm : ((2 * b : ℚ) : ℝ) = m' := by
    have hp0' : (p : ℝ) ≠ 0 := by exact_mod_cast hpne
    have : (p : ℝ) * ((2 * b : ℚ) : ℝ) = (p : ℝ) * m' := by
      have := hm.symm; rw [hm'] at this; push_cast at this ⊢; linarith
    exact mul_left_cancel₀ hp0' this
  -- the bound `p m'² ≤ 16`
  have hbound : (p : ℝ) * (m' : ℝ) ^ 2 ≤ 16 := by
    have hdiff : x - x' = ((2 * b : ℚ) : ℝ) * s := by rw [hxab, hx']; push_cast; ring
    have h4 : |x - x'| ≤ 4 := by
      calc |x - x'| ≤ |x| + |x'| := abs_sub _ _
        _ ≤ 4 := by linarith
    rw [hdiff, hVm] at h4
    have h16 : ((m' : ℝ) * s) ^ 2 ≤ 16 := by
      have := sq_le_sq' (abs_le.mp h4).1 (abs_le.mp h4).2
      linarith
    rw [mul_pow, hs] at h16; linarith
  have hbound' : (p : ℤ) * m' ^ 2 ≤ 16 := by exact_mod_cast hbound
  have hm'0 : m' = 0 := by
    by_contra hne
    have h1 : 0 < m' ^ 2 := by positivity
    rcases hp17 with h17 | h42
    · have h17' : (17 : ℤ) ≤ p := by exact_mod_cast h17
      nlinarith
    · have hp7' : (7 : ℤ) ≤ p := by exact_mod_cast hp7
      have hp4 : (p : ℤ) % 4 = 2 := by omega
      have hr : -1 ≤ m' ∧ m' ≤ 1 := by constructor <;> nlinarith
      have hm1 : m' ^ 2 = 1 := by
        obtain ⟨h1', h2'⟩ := hr
        have : m' = -1 ∨ m' = 1 := by omega
        rcases this with rfl | rfl <;> norm_num
      rw [hm1] at hZ
      -- `U² − 4W = p ≡ 2 (mod 4)` is impossible
      rcases Int.even_or_odd' U with ⟨k, hk | hk⟩
      · have : U ^ 2 = 4 * (k * k) := by rw [hk]; ring
        omega
      · have : U ^ 2 = 4 * (k * k + k) + 1 := by rw [hk]; ring
        omega
  -- so `b = 0` and `cos θ = a/2 ∈ ℚ`
  have hb0 : (b : ℝ) = 0 := by
    have := hVm; rw [hm'0] at this; push_cast at this; linarith
  have hcosq : ∃ q : ℚ, Real.cos θ = q := ⟨a / 2, by
    have : x = a := by rw [hxab, hb0]; ring
    rw [hx] at this; push_cast; linarith⟩
  have hmem := niven_angle_eq ⟨r, hr⟩ hcosq ⟨hθ0.le, hθπ.le⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h | h | h | h
  · exact absurd h hθ0.ne'
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exact absurd h hθπ.ne


/-- **Lemma E (row 2).**  A real `N`-tiling (`N` prime, `N ≡ 3 mod 4`, `N ≥ 7`) of a target
similar to the model with ratio `μ`, with `π ∈ 2Λ`, `Λ = ⟨θ₀, θ₁, π⟩`: no model angle is a natural
multiple of another (in particular the angles are distinct), and the model is scalene. -/
theorem Row2.lemmaE_sqfreeE (D : CongruentDissection N) (μ : ℝ)
    (hside : ∀ k, D.target.oppLen k = μ * D.model.oppLen k)
    (hN : Squarefree N) (hN7 : 7 ≤ N) (hN17 : 17 ≤ N ∨ N % 4 = 2)
    (hπ : ∃ y ∈ AddSubgroup.closure ({D.model.angleAt 0, D.model.angleAt 1, π} : Set ℝ),
      π = 2 * y) :
    (∀ i j : Fin 3, i ≠ j → ∀ k : ℕ, D.model.angleAt j ≠ k * D.model.angleAt i) ∧
      (∀ i j : Fin 3, i ≠ j → D.model.oppLen i ≠ D.model.oppLen j) := by
  have hsq : ¬ IsSquare N := Row2.sqfree_not_square hN hN7
  obtain ⟨hμ2, hknot, hcos⟩ := Row2.lemmaK_general D μ hside hsq
  have hsum := D.model.angleAt_sum
  have hQ : ∀ k, (∃ r : ℚ, D.model.angleAt k = r * π) →
      D.model.angleAt k = π / 3 ∨ D.model.angleAt k = π / 2 ∨ D.model.angleAt k = π * (2 / 3) := by
    intro k hr
    have hk0 := D.model.angleAt_pos' k
    have hkπ : D.model.angleAt k < π := by
      have h0 := D.model.angleAt_pos' 0
      have h1 := D.model.angleAt_pos' 1
      have h2 := D.model.angleAt_pos' 2
      rcases (show k = 0 ∨ k = 1 ∨ k = 2 by fin_cases k <;> simp) with rfl | rfl | rfl <;>
        linarith
    exact Row2.lemmaQ_sqfreeE hN hN7 hN17 hμ2 hr hk0 hkπ (hcos k)
  have hneq : ¬ ∀ k, D.model.angleAt k = π / 3 := by
    intro hall
    have hsin : Real.sin (π / 3) ≠ 0 :=
      (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])).ne'
    have hs : ∀ i j, D.model.oppLen i = D.model.oppLen j := by
      intro i j
      have h := D.model.lawSin i j
      rw [hall i, hall j] at h
      exact (mul_left_cancel₀ hsin h).symm
    exact hknot ⟨⟨1, by rw [hs 0 2]; simp⟩, ⟨1, by rw [hs 1 2]; simp⟩⟩
  have hE : ∀ i j : Fin 3, i ≠ j → ∀ k : ℕ, D.model.angleAt j ≠ k * D.model.angleAt i :=
    fun i j hij k => Row2.lemmaE_abs D.model.angleAt hsum hQ hneq hπ hij k
  refine ⟨hE, fun i j hij hl => ?_⟩
  have := D.model.angle_eq_of_oppLen_eq hij hl
  exact hE i j hij 1 (by rw [this]; simp)


/-- **Theorem S, sorted core.**  A tile-similar `N`-tiling (same labels, ratio `μ`), `N` prime,
`N ≡ 3 (mod 4)`, with a scalene model whose angles satisfy `angleAt 0 < angleAt 1 < angleAt 2` and
`angleAt 1 ∉ ℕ·angleAt 0`, does not exist. -/
theorem Row2.theoremS_sorted_sqfreeE (D : CongruentDissection N) (μ : ℝ)
    (hsim : ∀ k, D.target.angleAt k = D.model.angleAt k ∧ D.target.oppLen k = μ * D.model.oppLen k)
    (hN : Squarefree N) (hN7 : 7 ≤ N) (hN17 : 17 ≤ N ∨ N % 4 = 2)
    (h01 : D.model.angleAt 0 < D.model.angleAt 1) (h12 : D.model.angleAt 1 < D.model.angleAt 2)
    (hmult : ∀ k : ℕ, D.model.angleAt 1 ≠ k * D.model.angleAt 0)
    (hscal : ∀ k k', k ≠ k' → D.model.oppLen k ≠ D.model.oppLen k') : ∃ x y : ℕ, N = x ^ 2 + y ^ 2 := by
  have hsq : ¬ IsSquare N := Row2.sqfree_not_square hN hN7
  have hside : ∀ k, D.target.oppLen k = μ * D.model.oppLen k := fun k => (hsim k).2
  have hang : ∀ k, D.target.angleAt k = D.model.angleAt k := fun k => (hsim k).1
  have hA := Row2.cornerA D hang h01 h12
  have hB := Row2.cornerB D hang h01 h12 hmult
  obtain ⟨-, -, -, -, h22, -⟩ := Row2.lemmaD_tiling D μ hside hscal hsq hA hB
  have hR := Row2.lemmaR D hang h01 h12 (Row2.noc_of_sideCount D h22)
  obtain ⟨hμ, hp⟩ := Row2.mu_irrational D μ hside hsq
  obtain ⟨e0, e1, -⟩ := Row2.lemmaD_scale D.sideCount D.model.oppLen D.model.oppLen_pos hμ hp
    (Row2.sideCount_eigen D μ hside hscal) (Row2.sideCount_rows D hscal) hA hB
  have hμ2 : μ ^ 2 = N := by rw [hp]; push_cast; ring
  -- Lemma R: `γ = π/2`, so Pythagoras
  have hcos : Real.cos (D.model.angleAt 2) = 0 := by
    rw [show D.model.angleAt 2 = π / 2 by linarith]; exact Real.cos_pi_div_two
  have hl := D.model.lawCos 2
  rw [hcos] at hl
  simp only [show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl] at hl
  have hc := D.model.oppLen_pos 2
  have hpy : D.model.oppLen 2 ^ 2 = D.model.oppLen 0 ^ 2 + D.model.oppLen 1 ^ 2 := by
    linarith [hl]
  -- `N c² = (μa)² + (μb)² = (A² + B²) c²`
  have key : (N : ℝ) * D.model.oppLen 2 ^ 2
      = (((D.sideCount 0 2 : ℕ) : ℝ) ^ 2 + ((D.sideCount 1 2 : ℕ) : ℝ) ^ 2)
        * D.model.oppLen 2 ^ 2 := by
    have h1 : (N : ℝ) * D.model.oppLen 2 ^ 2
        = (μ * D.model.oppLen 0) ^ 2 + (μ * D.model.oppLen 1) ^ 2 := by
      rw [← hμ2, hpy]; ring
    rw [h1, e0, e1]; ring
  have hN' : (N : ℝ) = ((D.sideCount 0 2 : ℕ) : ℝ) ^ 2 + ((D.sideCount 1 2 : ℕ) : ℝ) ^ 2 :=
    mul_right_cancel₀ (pow_ne_zero 2 hc.ne') key
  have hNnat : N = D.sideCount 0 2 ^ 2 + D.sideCount 1 2 ^ 2 := by exact_mod_cast hN'
  exact ⟨_, _, hNnat⟩


/-- **Theorem S (row 2).**  Let `D` be a dissection of a triangle into `N` congruent copies of a
tile (reflections allowed, not necessarily edge-to-edge) whose target is similar to the tile with
ratio `μ` (same vertex labels: `target.angleAt k = model.angleAt k`,
`target.oppLen k = μ · model.oppLen k`).  If `N` is prime, then `N ≢ 3 (mod 4)` or `N = 3`. -/
theorem Row2.theoremS_sqfreeE (D : CongruentDissection N) (μ : ℝ)
    (hsim : ∀ k, D.target.angleAt k = D.model.angleAt k ∧ D.target.oppLen k = μ * D.model.oppLen k)
    (hN : Squarefree N) (hN7 : 7 ≤ N) (hN17 : 17 ≤ N ∨ N % 4 = 2) : ∃ x y : ℕ, N = x ^ 2 + y ^ 2 := by
  have hside : ∀ k, D.target.oppLen k = μ * D.model.oppLen k := fun k => (hsim k).2
  -- Lemma W: `π ∈ 2Λ`
  have hπ : ∃ y ∈ AddSubgroup.closure ({D.model.angleAt 0, D.model.angleAt 1, π} : Set ℝ),
      π = 2 * y := by
    by_contra hc
    push Not at hc
    exact Row2.lemmaW_not_sq D μ hsim hc (Row2.sqfree_not_square hN hN7)
  -- Lemma E
  obtain ⟨hE, hscal⟩ := Row2.lemmaE_sqfreeE D μ hside hN hN7 hN17 hπ
  have hdist : ∀ i j : Fin 3, i ≠ j → D.model.angleAt i ≠ D.model.angleAt j := fun i j hij h =>
    hE i j hij 1 (by rw [h]; simp)
  -- sort the angles
  obtain ⟨σ, hmono⟩ : ∃ σ : Equiv.Perm (Fin 3), Monotone (D.model.angleAt ∘ σ) :=
    ⟨_, Tuple.monotone_sort _⟩
  have h01 : D.model.angleAt (σ 0) < D.model.angleAt (σ 1) :=
    lt_of_le_of_ne (hmono (show (0 : Fin 3) ≤ 1 by decide))
      (hdist _ _ (σ.injective.ne (by decide)))
  have h12 : D.model.angleAt (σ 1) < D.model.angleAt (σ 2) :=
    lt_of_le_of_ne (hmono (show (1 : Fin 3) ≤ 2 by decide))
      (hdist _ _ (σ.injective.ne (by decide)))
  -- relabel target and model by `σ`
  let D' : CongruentDissection N :=
    { toDissection := Erdos634.NormalPosition.relabelTarget D.toDissection σ
      model := D.model.relabel σ
      tiles_congruent := fun i => (D.tiles_congruent i).relabel σ }
  have hTa := Row2.angleAt_comp D.target D'.target σ (fun k => rfl)
  have hMa := Row2.angleAt_comp D.model D'.model σ (fun k => rfl)
  have hsim' : ∀ k, D'.target.angleAt k = D'.model.angleAt k ∧
      D'.target.oppLen k = μ * D'.model.oppLen k := by
    intro k
    rw [(hTa k).1, (hMa k).1, (hTa k).2, (hMa k).2]
    exact hsim (σ k)
  refine Row2.theoremS_sorted_sqfreeE D' μ hsim' hN hN7 hN17 ?_ ?_ ?_ ?_
  · rw [(hMa 0).1, (hMa 1).1]; exact h01
  · rw [(hMa 1).1, (hMa 2).1]; exact h12
  · intro k
    rw [(hMa 1).1, (hMa 0).1]
    exact hE (σ 0) (σ 1) (σ.injective.ne (by decide)) k
  · intro k k' hkk'
    rw [(hMa k).2, (hMa k').2]
    exact hscal _ _ (σ.injective.ne hkk')


/-- **Theorem S, any vertex correspondence** `τ` between target and model. -/
theorem Row2.theoremS_perm_sqfreeE (D : CongruentDissection N) (μ : ℝ) (τ : Equiv.Perm (Fin 3))
    (hsim : ∀ k, D.target.angleAt k = D.model.angleAt (τ k) ∧
      D.target.oppLen k = μ * D.model.oppLen (τ k))
    (hN : Squarefree N) (hN7 : 7 ≤ N) (hN17 : 17 ≤ N ∨ N % 4 = 2) : ∃ x y : ℕ, N = x ^ 2 + y ^ 2 := by
  have hMa := Row2.angleAt_comp D.model (D.relabelModel τ).model τ (fun k => rfl)
  refine Row2.theoremS_sqfreeE (D.relabelModel τ) μ (fun k => ?_) hN hN7 hN17
  rw [(hMa k).1, (hMa k).2]
  exact hsim k


end Erdos634.Geometry

#print axioms Erdos634.Geometry.Row2.lemmaQ_sqfreeE
#print axioms Erdos634.Geometry.Row2.theoremS_perm_sqfreeE

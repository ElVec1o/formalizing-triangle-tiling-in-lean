-- Draft/FluxDRow4.lean — ROW 4 ((private working notes, not included) §3, P2): the `γ = 2α` tile
-- (`α ∉ ℚπ`) on the isosceles target with base angles `α`.  Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).
--
-- * `Row4.sides` = L4's law-of-sines half: `X₁ = X₀`, `Y = 2κX`, `c = 2κa`, `b = (4κ² − 1)a`,
--   `κ = cos α ∈ (1/2, 1)` (so `ab = c² − a²`, `1 < c/a < 2`).
-- * `Row4.P5_alg` (pure algebra) and `Row4.P5` = THEOREM R4(i): `M = X/(a+c)`, `M′ = X/(c−a)` are
--   positive integers, `N = M·M′`, `M ≡ M′ ≡ N (2)`, `M′ > 3M`, `c/a = (M′+M)/(M′−M)`, with the
--   area identity `X² = N·ab` and `ab = c² − a²`.  Inputs: `Row4.invariants` (Draft/FluxRow4: L2 + L3
--   + L4's boundary values `Y ∓ 2X = S₁,₂·(…)`), the area equation `abs_detTri_target` with Heron in
--   symmetric form (`Tri.four_detTri_sq_symm`, Draft/FluxDRow12b), the law of sines `Tri.lawSin`.
-- * `Row4.not_two_mod_four` = R4(iii): `N ≢ 2 (mod 4)`.
-- * `Row4.L7` (pure ℕ arithmetic, P2's exact hypotheses) and `Row4.prime_leg_words` = C6 + L7 on a
--   real tiling: at prime `N`, `M = 1`, `N = 2k+1` with `k ≥ 2`, and every leg word `pa + qb + rc`
--   (they exist by W, Draft/FluxDSideWord) is `(0, k, 0)` (k b-edges) or `(1, 0, 1)` (a + c).
-- L8 ("neither leg word is possible") is in Draft/FluxDRow4L8.lean (the `{a, c}` half, with L1's
-- corner figures) and Draft/FluxDRow4Bk.lean (the `b^k` half); R4(ii) ("N is not prime") is
-- `Row4.not_prime` in Draft/FluxDRow4Bk.lean.
--
-- CONDITIONAL AT THE GEOMETRIC LEVEL: the base-α target for the `γ = 2α` tile has no Lean witness
-- (DESIGN.md §5; the Laczkovich N = 6028020 rebuild is Python only).  Witnesses
-- (Draft/FluxDRow4Witness.lean): `P5_alg` on the P5 arithmetic core `(a,b,c) = (4,5,6)`, `X = 120`,
-- `N = 720`, `M = 12`, `M′ = 60` (row4/PROOF.md §7); `L7` on `k = 2, 3`; `Row4.sides`' model half on
-- the real (4,5,6) triangle `T456` (Draft/FluxRow4Witness).
--
-- Formalization debt; not progress on the three /goal outcomes.
import Erdos634.Draft.FluxDRow12b
import Erdos634.Draft.FluxRow4

open scoped Classical

namespace Erdos634.Geometry

variable {N : ℕ}

/-! ## S for row 4 -/

/-- **L4's law-of-sines half** for the `γ = 2α` tile on the base-α target: with `κ = cos α`,
`1/2 < κ < 1`, `c = 2κa`, `b = (4κ² − 1)a`, `Y = 2κX`, `X₁ = X`. -/
theorem Row4.sides (D : CongruentDissection N) {α a b c : ℝ}
    (h : D.model.TwoAlphaData α a b c)
    (hA : D.target.angleAt 0 = α) (hB : D.target.angleAt 1 = α) :
    ∃ κ : ℝ, 1 / 2 < κ ∧ κ < 1 ∧ 0 < a ∧ 0 < D.target.oppLen 0 ∧
      c = 2 * κ * a ∧ b = (4 * κ ^ 2 - 1) * a ∧
      D.target.oppLen 2 = 2 * κ * D.target.oppLen 0 ∧
      D.target.oppLen 1 = D.target.oppLen 0 := by
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  have hC : D.target.angleAt 2 = Real.pi - 2 * α := by
    have hs := D.target.angleAt_sum; rw [hA, hB] at hs; linarith
  have hαpos : 0 < α := h0 ▸ D.model.angleAt_pos' (σ 0)
  have hβpos : 0 < Real.pi - 3 * α := h1 ▸ D.model.angleAt_pos' (σ 1)
  have hπ := Real.pi_pos
  have hsα : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hαpos (by linarith)
  have hs2 : Real.sin (Real.pi - 2 * α) = 2 * Real.sin α * Real.cos α := by
    rw [Real.sin_pi_sub, Real.sin_two_mul]
  have hs3 : Real.sin (Real.pi - 3 * α) = Real.sin α * (4 * Real.cos α ^ 2 - 1) := by
    rw [Real.sin_pi_sub, Real.sin_three_mul]
    have p := Real.sin_sq_add_cos_sq α
    linear_combination (-4 * Real.sin α) * p
  have ls1 := D.model.lawSin (σ 0) (σ 2)
  have ls2 := D.model.lawSin (σ 0) (σ 1)
  rw [h0, o2, h2, o0, Real.sin_two_mul] at ls1
  rw [h0, o1, h1, o0, hs3] at ls2
  have lt0 := D.target.lawSin 0 2
  have lt1 := D.target.lawSin 1 2
  rw [hA, hC, hs2] at lt0
  rw [hB, hC, hs2] at lt1
  have hκ1 : 1 / 2 < Real.cos α := by
    rw [← Real.cos_pi_div_three]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi hαpos.le (by linarith) (by linarith)
  have hκ2 : Real.cos α < 1 := by
    rw [← Real.cos_zero]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith) hαpos
  have ha : 0 < a := o0 ▸ D.model.oppLen_pos (σ 0)
  have hX : 0 < D.target.oppLen 0 := D.target.oppLen_pos 0
  have hc : c = 2 * Real.cos α * a := mul_left_cancel₀ hsα.ne' (by linear_combination ls1)
  have hb : b = (4 * Real.cos α ^ 2 - 1) * a :=
    mul_left_cancel₀ hsα.ne' (by linear_combination ls2)
  have hY : D.target.oppLen 2 = 2 * Real.cos α * D.target.oppLen 0 :=
    mul_left_cancel₀ hsα.ne' (by linear_combination lt0)
  have hY1 : D.target.oppLen 2 = 2 * Real.cos α * D.target.oppLen 1 :=
    mul_left_cancel₀ hsα.ne' (by linear_combination lt1)
  have hX1 : D.target.oppLen 1 = D.target.oppLen 0 :=
    mul_left_cancel₀ (mul_pos two_pos (by linarith : (0 : ℝ) < Real.cos α)).ne'
      (by linear_combination hY - hY1)
  exact ⟨Real.cos α, hκ1, hκ2, ha, hX, hc, hb, hY, hX1⟩

/-! ## P5 -/

/-- **P5, the algebra** (row4/PROOF.md §3 P5): from the two boundary identities
`Y − 2X = S₁(a+c−b)`, `Y + 2X = S₂(b+c−a)` read through S (`c = 2κa`, `b = (4κ²−1)a`, `Y = 2κX`,
`1/2 < κ < 1`) and the area `X² = N·ab`: `M = −S₁`, `M′ = S₂` are positive, `M(a+c) = X`,
`M′(c−a) = X`, `N = M·M′`, `M′ > 3M`, `c/a = (M′+M)/(M′−M)`. -/
theorem Row4.P5_alg {a X κ : ℝ} {S₁ S₂ : ℤ} {N : ℕ} (ha : 0 < a) (hX : 0 < X)
    (hκ1 : 1 / 2 < κ) (hκ2 : κ < 1)
    (h1 : 2 * κ * X - 2 * X = S₁ * (a + 2 * κ * a - (4 * κ ^ 2 - 1) * a))
    (h2 : 2 * κ * X + 2 * X = S₂ * ((4 * κ ^ 2 - 1) * a + 2 * κ * a - a))
    (harea : X ^ 2 = N * a * ((4 * κ ^ 2 - 1) * a)) :
    0 < -S₁ ∧ 0 < S₂ ∧ ((-S₁ : ℤ) : ℝ) * (a + 2 * κ * a) = X ∧ (S₂ : ℝ) * (2 * κ * a - a) = X ∧
      (N : ℤ) = -S₁ * S₂ ∧ 3 * (-S₁) < S₂ ∧
      2 * κ = ((S₂ : ℝ) + (-S₁ : ℤ)) / ((S₂ : ℝ) - (-S₁ : ℤ)) := by
  have hκsq : 1 / 4 < κ ^ 2 := by
    have h' : (1 / 2) * (1 / 2) < κ * κ := mul_lt_mul'' hκ1 hκ1 (by norm_num) (by norm_num)
    have : κ ^ 2 = κ * κ := sq κ
    linarith
  have e1 : (1 - κ) * (X + S₁ * (a * (1 + 2 * κ))) = 0 := by linear_combination (-1 / 2 : ℝ) * h1
  have e2 : (κ + 1) * (X - S₂ * (a * (2 * κ - 1))) = 0 := by linear_combination (1 / 2 : ℝ) * h2
  have hM : ((-S₁ : ℤ) : ℝ) * (a + 2 * κ * a) = X := by
    have := (mul_eq_zero.mp e1).resolve_left (by linarith)
    push_cast; linear_combination -this
  have hM' : (S₂ : ℝ) * (2 * κ * a - a) = X := by
    have := (mul_eq_zero.mp e2).resolve_left (by linarith)
    linear_combination -this
  have hpa : 0 < a + 2 * κ * a := by
    have := mul_pos ha (by linarith : (0 : ℝ) < 1 + 2 * κ); linarith
  have hpc : 0 < 2 * κ * a - a := by
    have := mul_pos ha (by linarith : (0 : ℝ) < 2 * κ - 1); linarith
  have hMpos : (0 : ℝ) < ((-S₁ : ℤ) : ℝ) := by
    by_contra hn; push Not at hn
    have := mul_nonpos_of_nonpos_of_nonneg hn hpa.le
    linarith
  have hM'pos : (0 : ℝ) < (S₂ : ℝ) := by
    by_contra hn; push Not at hn
    have := mul_nonpos_of_nonpos_of_nonneg hn hpc.le
    linarith
  set M : ℤ := -S₁ with hMdef
  have hMz : 0 < M := by exact_mod_cast hMpos
  have hM'z : 0 < S₂ := by exact_mod_cast hM'pos
  -- `N = M·M′`
  have hprod : ((M : ℝ) * S₂ - N) * (a ^ 2 * (4 * κ ^ 2 - 1)) = 0 := by
    linear_combination ((S₂ : ℝ) * (2 * κ * a - a)) * hM + X * hM' + harea
  have hq : 0 < a ^ 2 * (4 * κ ^ 2 - 1) := mul_pos (pow_pos ha 2) (by linarith)
  have hN : (M : ℝ) * S₂ = N := sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hq.ne')
  have hNz : (N : ℤ) = M * S₂ := by exact_mod_cast hN.symm
  -- `M′ > 3M`
  have hlt : 3 * M < S₂ := by
    have e : (S₂ : ℝ) * (2 * κ - 1) = M * (1 + 2 * κ) := by
      have : a * ((S₂ : ℝ) * (2 * κ - 1) - M * (1 + 2 * κ)) = 0 := by
        linear_combination hM' - hM
      linear_combination (mul_eq_zero.mp this).resolve_left ha.ne'
    have e4 : ((S₂ : ℝ) - 3 * M) * (2 * κ - 1) = 4 * M * (1 - κ) := by linear_combination e
    have h4 : 0 < 4 * (M : ℝ) * (1 - κ) := mul_pos (by linarith) (by linarith)
    have : (3 * M : ℝ) < S₂ := by
      by_contra hn; push Not at hn
      have := mul_nonpos_of_nonpos_of_nonneg (by linarith : (S₂ : ℝ) - 3 * M ≤ 0)
        (by linarith : (0 : ℝ) ≤ 2 * κ - 1)
      linarith
    exact_mod_cast this
  refine ⟨hMz, hM'z, hM, hM', hNz, hlt, ?_⟩
  have hd : (0 : ℝ) < (S₂ : ℝ) - M := by
    have : (M : ℝ) < S₂ := by exact_mod_cast (by linarith : M < S₂)
    linarith
  rw [eq_div_iff hd.ne']
  have : a * (2 * κ * ((S₂ : ℝ) - M) - ((S₂ : ℝ) + M)) = 0 := by linear_combination hM' - hM
  linear_combination (mul_eq_zero.mp this).resolve_left ha.ne'

/-- **THEOREM R4(i) = P5** (row4/PROOF.md P2, PROVED after two reviews): an `N`-tiling (any `N`) of the
base-α target by the `γ = 2α` tile with `α ∉ ℚπ` has integers `M, M′ > 0` with `M(a+c) = X`,
`M′(c−a) = X`, `N = M·M′`, `M ≡ M′ ≡ N (2)`, `M′ > 3M`, `c/a = (M′+M)/(M′−M)` (the tile is rational),
and `X² = N·ab`, `ab = c² − a²`.  CONDITIONAL: the target shape has no Lean witness. -/
theorem Row4.P5 (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoAlphaData α a b c)
    (hA : D.target.angleAt 0 = α) (hB : D.target.angleAt 1 = α) :
    ∃ M M' : ℤ, 0 < M ∧ 0 < M' ∧ (M : ℝ) * (a + c) = D.target.oppLen 0 ∧
      (M' : ℝ) * (c - a) = D.target.oppLen 0 ∧ (N : ℤ) = M * M' ∧
      (2 : ℤ) ∣ M - N ∧ (2 : ℤ) ∣ M' - N ∧ 3 * M < M' ∧
      c / a = ((M' : ℝ) + M) / ((M' : ℝ) - M) ∧
      D.target.oppLen 0 ^ 2 = N * a * b ∧ a * b = c ^ 2 - a ^ 2 := by
  obtain ⟨κ, hκ1, hκ2, ha, hX, hc, hb, hY, hX1⟩ := Row4.sides D h hA hB
  have hκsq : κ ^ 2 < 1 := by
    have h' : κ * κ < κ * 1 := mul_lt_mul_of_pos_left hκ2 (by linarith)
    have : κ ^ 2 = κ * κ := sq κ
    linarith
  have hκsq' : 1 / 4 < κ ^ 2 := by
    have h' : (1 / 2) * (1 / 2) < κ * κ := mul_lt_mul'' hκ1 hκ1 (by norm_num) (by norm_num)
    have : κ ^ 2 = κ * κ := sq κ
    linarith
  have hG : 0 < 16 * κ ^ 2 * (1 - κ ^ 2) :=
    mul_pos (mul_pos (by norm_num) (by linarith)) (by linarith)
  have hb0 : 0 < (4 * κ ^ 2 - 1) * a := mul_pos (by linarith) ha
  obtain ⟨S₁, S₂, hS1, hS2, -, -, e1, e2⟩ :=
    Row4.invariants D hα h hA hB ⟨rfl, hX1⟩ (rfl : D.target.oppLen 2 = D.target.oppLen 2)
  obtain ⟨σ, -, o0, -, o1, -, o2⟩ := h
  set X := D.target.oppLen 0 with hXdef
  -- area: `X² = N·ab`
  have hA' := D.abs_detTri_target
  have hsq : Erdos634.AreaDet.detTri D.target ^ 2
      = (N : ℝ) ^ 2 * Erdos634.AreaDet.detTri D.model ^ 2 := by
    rw [← sq_abs (Erdos634.AreaDet.detTri D.target), hA', mul_pow, sq_abs]
  have hT := D.target.four_detTri_sq_symm
  have hMo := D.model.four_detTri_sq_symm
  rw [Tri.sum_pow_perm' D.model 2 σ, Tri.sum_pow_perm' D.model 4 σ, o0, o1, o2] at hMo
  rw [Fin.sum_univ_three, Fin.sum_univ_three, hX1, ← hXdef, hY] at hT
  subst hb hc
  have key : (16 * κ ^ 2 * (1 - κ ^ 2)) * ((X ^ 2 - N * a * ((4 * κ ^ 2 - 1) * a))
      * (X ^ 2 + N * a * ((4 * κ ^ 2 - 1) * a))) = 0 := by
    linear_combination (-1 : ℝ) * hT + (N : ℝ) ^ 2 * hMo + 4 * hsq
  have hsum : 0 < X ^ 2 + N * a * ((4 * κ ^ 2 - 1) * a) :=
    add_pos_of_pos_of_nonneg (pow_pos hX 2)
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg N) ha.le) hb0.le)
  have harea : X ^ 2 = N * a * ((4 * κ ^ 2 - 1) * a) := by
    rcases mul_eq_zero.mp key with e | e
    · exact absurd e hG.ne'
    · rcases mul_eq_zero.mp e with e' | e'
      · linarith
      · exact absurd e' hsum.ne'
  have h1 : 2 * κ * X - 2 * X = S₁ * (a + 2 * κ * a - (4 * κ ^ 2 - 1) * a) := by
    linear_combination e1 - hY
  have h2 : 2 * κ * X + 2 * X = S₂ * ((4 * κ ^ 2 - 1) * a + 2 * κ * a - a) := by
    linear_combination e2 - hY
  obtain ⟨hMz, hM'z, hM, hM', hNz, hlt, hratio⟩ := Row4.P5_alg ha hX hκ1 hκ2 h1 h2 harea
  refine ⟨-S₁, S₂, hMz, hM'z, hM, hM', hNz, ?_, hS2, hlt, ?_, harea, by ring⟩
  · rw [show -S₁ - (N : ℤ) = -(S₁ - N) - 2 * N by ring]
    exact dvd_sub (dvd_neg.mpr hS1) (dvd_mul_right 2 _)
  · rw [← hratio, mul_div_assoc, div_self ha.ne', mul_one]

/-- **R4(iii)**: `N ≢ 2 (mod 4)` (if `N` is even, `M` and `M′` are both even). -/
theorem Row4.not_two_mod_four (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoAlphaData α a b c)
    (hA : D.target.angleAt 0 = α) (hB : D.target.angleAt 1 = α) : N % 4 ≠ 2 := by
  obtain ⟨M, M', -, -, -, -, hN, hM2, hM'2, -⟩ := Row4.P5 D hα h hA hB
  intro h4
  have hN2 : (2 : ℤ) ∣ (N : ℤ) := by omega
  obtain ⟨u, hu⟩ : (2 : ℤ) ∣ M := by
    have := dvd_add hM2 hN2; rwa [sub_add_cancel] at this
  obtain ⟨v, hv⟩ : (2 : ℤ) ∣ M' := by
    have := dvd_add hM'2 hN2; rwa [sub_add_cancel] at this
  obtain ⟨w, hw⟩ : ∃ w, u * v = w := ⟨_, rfl⟩
  have : (N : ℤ) = 4 * w := by rw [hN, hu, hv, ← hw]; ring
  omega

/-! ## C6 + L7 -/

/-- **L7** (row4/PROOF.md P2, exact hypotheses): integers `k ≥ 2`, `p, q, r ≥ 0` with
`k(2k+1) = pk² + q(2k+1) + rk(k+1)` force `(p,q,r) = (0,k,0)` or `(1,0,1)`. -/
theorem Row4.L7 {k p q r : ℕ} (hk : 2 ≤ k)
    (h : k * (2 * k + 1) = p * k ^ 2 + q * (2 * k + 1) + r * (k * (k + 1))) :
    (p = 0 ∧ q = k ∧ r = 0) ∨ (p = 1 ∧ q = 0 ∧ r = 1) := by
  have hk0 : 0 < k := by omega
  -- `k ∣ q`
  have hdiv : k ∣ q * (2 * k + 1) := by
    have h1 : k ∣ p * k ^ 2 + r * (k * (k + 1)) :=
      dvd_add (Dvd.intro (p * k) (by ring)) (Dvd.intro (r * (k + 1)) (by ring))
    have h2 : k ∣ (p * k ^ 2 + r * (k * (k + 1))) + q * (2 * k + 1) := by
      rw [show (p * k ^ 2 + r * (k * (k + 1))) + q * (2 * k + 1)
        = p * k ^ 2 + q * (2 * k + 1) + r * (k * (k + 1)) by ring, ← h]
      exact Dvd.intro _ rfl
    exact (Nat.dvd_add_right h1).mp h2
  have hcop : Nat.Coprime k (2 * k + 1) := by
    rw [Nat.coprime_mul_right_add_right]; exact Nat.coprime_one_right k
  have hkq : k ∣ q := hcop.dvd_of_dvd_mul_right hdiv
  have hqk : q ≤ k := by
    by_contra hn; push Not at hn
    have : k * (2 * k + 1) < q * (2 * k + 1) := Nat.mul_lt_mul_of_pos_right hn (by omega)
    nlinarith
  obtain ⟨t, rfl⟩ := hkq
  have ht : t ≤ 1 := by
    by_contra hn; push Not at hn
    have : k * 2 ≤ k * t := Nat.mul_le_mul_left k hn
    nlinarith
  interval_cases t
  · -- `q = 0`: `pk + r(k+1) = 2k + 1`
    right
    have e : k * (p * k + r * (k + 1)) = k * (2 * k + 1) := by rw [h]; ring
    have e' := Nat.eq_of_mul_eq_mul_left hk0 e
    have hr : r ≤ 1 := by
      by_contra hn; push Not at hn
      have : 2 * (k + 1) ≤ r * (k + 1) := Nat.mul_le_mul_right _ hn
      nlinarith
    interval_cases r
    · exfalso
      have hp : p ≤ 2 ∨ 3 ≤ p := by omega
      rcases hp with hp | hp
      · have : p * k ≤ 2 * k := Nat.mul_le_mul_right _ hp
        linarith
      · have : 3 * k ≤ p * k := Nat.mul_le_mul_right _ hp
        linarith
    · refine ⟨?_, by ring, rfl⟩
      have e2 : p * k = 1 * k := by linarith
      exact Nat.eq_of_mul_eq_mul_right hk0 e2
  · -- `q = k`: `pk² + rk(k+1) = 0`
    left
    have e : p * k ^ 2 + r * (k * (k + 1)) = 0 := by
      have : k * 1 * (2 * k + 1) = k * (2 * k + 1) := by ring
      linarith
    have hp : p * k ^ 2 = 0 := (Nat.add_eq_zero_iff.mp e).1
    have hr : r * (k * (k + 1)) = 0 := (Nat.add_eq_zero_iff.mp e).2
    refine ⟨?_, by ring, ?_⟩
    · rcases Nat.mul_eq_zero.mp hp with h' | h'
      · exact h'
      · exact absurd h' (pow_pos hk0 2).ne'
    · rcases Nat.mul_eq_zero.mp hr with h' | h'
      · exact h'
      · exact absurd h' (Nat.mul_pos hk0 (Nat.succ_pos k)).ne'

/-- **C6 + L7 on a real tiling** (row4/PROOF.md §3): at prime `N`, `M = 1`, `M′ = N = 2k + 1` with
`k ≥ 2`, `k·c = (k+1)·a`, `k²·b = N·a`, `X = a + c`, and every word `X = pa + qb + rc` of a leg is
`(0, k, 0)` or `(1, 0, 1)`.  (L8, which kills both: Draft/FluxDRow4L8.lean, Draft/FluxDRow4Bk.lean.) -/
theorem Row4.prime_leg_words (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoAlphaData α a b c)
    (hA : D.target.angleAt 0 = α) (hB : D.target.angleAt 1 = α) (hN : N.Prime) :
    ∃ k : ℕ, 2 ≤ k ∧ N = 2 * k + 1 ∧ D.target.oppLen 0 = a + c ∧
      (k : ℝ) * c = (k + 1) * a ∧ (k : ℝ) ^ 2 * b = N * a ∧
      ∀ p q r : ℕ, D.target.oppLen 0 = p * a + q * b + r * c →
        (p = 0 ∧ q = k ∧ r = 0) ∨ (p = 1 ∧ q = 0 ∧ r = 1) := by
  obtain ⟨M, M', hM0, hM'0, hM, hM', hNM, hM2, -, hlt, -, -, hab⟩ := Row4.P5 D hα h hA hB
  obtain ⟨κ, -, -, ha, -, -, -, -, -⟩ := Row4.sides D h hA hB
  have hN2 := hN.two_le
  -- C6: `M = 1` (a proper divisor of the prime `N`: `N = M·M′ > M` since `M′ > 3M ≥ 3`)
  have hM1 : M = 1 := by
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hM0.le
    have hmN : (m : ℤ) < N := by
      have := mul_pos hM0 (show (0 : ℤ) < M' - 1 by linarith)
      linarith
    have hdvd : m ∣ N := by
      have : (m : ℤ) ∣ (N : ℤ) := ⟨M', hNM⟩
      exact_mod_cast this
    rcases (Nat.dvd_prime hN).mp hdvd with h1 | h1
    · rw [h1]; norm_num
    · exfalso; rw [h1] at hmN; exact lt_irrefl _ hmN
  subst hM1
  have hM'N : M' = N := by linarith
  have hN4 : 4 ≤ N := by omega
  obtain ⟨k, hk⟩ : ∃ k, N = 2 * k + 1 := ⟨(N - 1) / 2, by omega⟩
  have hk2 : 2 ≤ k := by omega
  -- the tile, read in `k`
  rw [hM'N] at hM'
  push_cast at hM hM'
  have hkN : (N : ℝ) = 2 * k + 1 := by rw [hk]; push_cast; ring
  have hkc : (k : ℝ) * c = (k + 1) * a := by
    linear_combination (1 / 2 : ℝ) * hM' - (1 / 2 : ℝ) * hM - (1 / 2 : ℝ) * (c - a) * hkN
  have hkb : (k : ℝ) ^ 2 * b = N * a := by
    have e : a * ((k : ℝ) ^ 2 * b - N * a) = 0 := by
      linear_combination (k : ℝ) ^ 2 * hab + ((k : ℝ) * c + (k + 1) * a) * hkc - a ^ 2 * hkN
    exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left ha.ne')
  refine ⟨k, hk2, hk, by linear_combination -hM, hkc, hkb, fun p q r hw => ?_⟩
  apply Row4.L7 hk2
  have e : a * ((k : ℝ) * (2 * k + 1) - (p * k ^ 2 + q * (2 * k + 1) + r * (k * (k + 1)))) = 0 := by
    linear_combination (k : ℝ) ^ 2 * hM + (k : ℝ) ^ 2 * hw + ((r : ℝ) * k - k) * hkc
      + (q : ℝ) * hkb + (q : ℝ) * a * hkN
  have e2 := sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left ha.ne')
  exact_mod_cast e2

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Row4.sides
#print axioms Erdos634.Geometry.Row4.P5_alg
#print axioms Erdos634.Geometry.Row4.P5
#print axioms Erdos634.Geometry.Row4.not_two_mod_four
#print axioms Erdos634.Geometry.Row4.L7
#print axioms Erdos634.Geometry.Row4.prime_leg_words

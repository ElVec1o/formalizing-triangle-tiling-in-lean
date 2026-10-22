-- Draft/LemmaSB1Hurwitz.lean — closes the gap left open in Draft/LemmaSB1.lean:
--   `HurwitzOddZero` : hurwitzZetaOdd x 0 = 1/2 − x  for 0 < x < 1
-- (the k = 0 case of Mathlib's `hurwitzZeta_neg_nat`, stated there as a TODO), and hence
--   **B1** (unconditional): Σ_{j mod N} χ(j)·((j/N)) ≠ 0 for every odd primitive χ.
--
-- Route (no Fourier series of the sawtooth is needed):
--  (1) Mathlib's functional equation `hurwitzZetaOdd_one_sub` at s = 1:
--        hurwitzZetaOdd x 0 = sinZeta x 1 / π.
--  (2) `sinZeta_eq`: sinZeta = (expZeta x − expZeta (−x)) / (2i).
--  (3) expZeta y 1 = −log(1 − e(y)) for y ∉ ℤ: for real s > 1, summation by parts writes
--        expZeta y s = (D(s) − z)/(z − 1),  D(s) = Σ_n z^{n+2} ((n+1)^{-s} − (n+2)^{-s}),
--      D is right-continuous at 1 by dominated convergence (bound 2/(n+1)²), D(1) = F(z) with
--      F(w) = Σ w^{n+2}/((n+1)(n+2)) = (1−w)log(1−w) + w on the open disc (Mathlib's log series),
--      F continuous on the closed disc (M-test); expZeta y is continuous at 1 (Mathlib).
--  (4) arg(1 − e(x)) = πx − π/2, so sinZeta x 1 = π(1/2 − x).
--
-- Formalization debt on a paper-level PROVED node; NOT progress on the /goal. Imported into All.lean (All.lean:638; header corrected 2026-10-03).
import Mathlib
import Erdos634.Draft.LemmaSB1

open scoped BigOperators Topology ComplexConjugate Real
open Complex HurwitzZeta Filter

namespace Erdos634.LemmaSB1H

/-- `m^{-s}` as `(m^s)⁻¹` (real). -/
noncomputable def c (m : ℕ) (s : ℝ) : ℝ := ((m : ℝ) ^ s)⁻¹

theorem c_zero {s : ℝ} (hs : s ≠ 0) : c 0 s = 0 := by
  simp [c, Real.zero_rpow hs]

theorem c_one (s : ℝ) : c 1 s = 1 := by simp [c]

/-- Uniform bound on the differences, for 1 ≤ s ≤ 2. -/
theorem c_diff_bound (n : ℕ) {s : ℝ} (h1 : 1 ≤ s) (h2 : s ≤ 2) :
    0 ≤ c (n + 1) s - c (n + 2) s ∧ c (n + 1) s - c (n + 2) s ≤ 2 / ((n : ℝ) + 1) ^ 2 := by
  set m : ℝ := (n : ℝ) + 1 with hm
  have hm1 : 1 ≤ m := by rw [hm]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hm0 : 0 < m := by linarith
  have hcast1 : ((n + 1 : ℕ) : ℝ) = m := by push_cast; ring
  have hcast2 : ((n + 2 : ℕ) : ℝ) = m + 1 := by push_cast; ring
  unfold c
  rw [hcast1, hcast2]
  set q : ℝ := m / (m + 1) with hq
  have hq0 : 0 < q := by positivity
  have hq1 : q ≤ 1 := by rw [hq, div_le_one (by linarith)]; linarith
  have hsplit : ((m + 1) ^ s)⁻¹ = (m ^ s)⁻¹ * q ^ s := by
    rw [hq, Real.div_rpow hm0.le (by linarith)]
    have : (0 : ℝ) < (m + 1) ^ s := Real.rpow_pos_of_pos (by linarith) s
    have : (0 : ℝ) < m ^ s := Real.rpow_pos_of_pos hm0 s
    field_simp
  rw [hsplit]
  have hms : m ≤ m ^ s := by
    calc m = m ^ (1 : ℝ) := (Real.rpow_one m).symm
      _ ≤ m ^ s := Real.rpow_le_rpow_of_exponent_le hm1 h1
  have hinv : (m ^ s)⁻¹ ≤ m⁻¹ := inv_anti₀ hm0 hms
  have hinv0 : 0 ≤ (m ^ s)⁻¹ := inv_nonneg.mpr (Real.rpow_pos_of_pos hm0 s).le
  have hqs1 : q ^ s ≤ 1 := Real.rpow_le_one hq0.le hq1 (by linarith)
  have hqs2 : q ^ (2 : ℝ) ≤ q ^ s := Real.rpow_le_rpow_of_exponent_ge hq0 hq1 h2
  rw [Real.rpow_two] at hqs2
  constructor
  · nlinarith
  · have e1 : (m ^ s)⁻¹ - (m ^ s)⁻¹ * q ^ s = (m ^ s)⁻¹ * (1 - q ^ s) := by ring
    rw [e1]
    have hb : 1 - q ^ s ≤ 1 - q ^ 2 := by linarith
    have hb0 : 0 ≤ 1 - q ^ s := by linarith
    calc (m ^ s)⁻¹ * (1 - q ^ s) ≤ m⁻¹ * (1 - q ^ 2) :=
          mul_le_mul hinv hb hb0 (inv_nonneg.mpr hm0.le)
      _ ≤ 2 / m ^ 2 := by
          rw [hq]
          have : m + 1 ≠ 0 := by linarith
          rw [div_pow, one_sub_div (by positivity), inv_mul_eq_div, div_div,
            div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith

/-! ## The auxiliary power series F -/

/-- `F(w) = Σ_{n≥0} w^{n+2} / ((n+1)(n+2))`. -/
noncomputable def F (w : ℂ) : ℂ := ∑' n : ℕ, w ^ (n + 2) / (((n : ℂ) + 1) * ((n : ℂ) + 2))

theorem hasSum_F {w : ℂ} (hw : ‖w‖ < 1) :
    HasSum (fun n : ℕ => w ^ (n + 2) / (((n : ℂ) + 1) * ((n : ℂ) + 2)))
      ((1 - w) * log (1 - w) + w) := by
  have h1 := hasSum_taylorSeries_neg_log hw
  have h2 : HasSum (fun n : ℕ => w ^ (n + 1) / ((n : ℂ) + 1)) (-log (1 - w)) := by
    have := (hasSum_nat_add_iff' 1).mpr h1
    simpa using this
  have h3 : HasSum (fun n : ℕ => w ^ (n + 2) / ((n : ℂ) + 2)) (-log (1 - w) - w) := by
    have := (hasSum_nat_add_iff' 1).mpr h2
    convert this using 2 with n
    · push_cast; ring_nf
    · simp
  have h4 := (h2.mul_left w).sub h3
  convert h4 using 1
  · funext n
    have a1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have a2 : (n : ℂ) + 2 ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
    field_simp
    ring
  · ring

theorem norm_F_term_le {w : ℂ} (hw : ‖w‖ ≤ 1) (n : ℕ) :
    ‖w ^ (n + 2) / (((n : ℂ) + 1) * ((n : ℂ) + 2))‖ ≤ 1 / ((n : ℝ) + 1) ^ 2 := by
  rw [norm_div, norm_pow, norm_mul]
  have e1 : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by exact_mod_cast Complex.norm_natCast (n + 1)
  have e2 : ‖(n : ℂ) + 2‖ = (n : ℝ) + 2 := by exact_mod_cast Complex.norm_natCast (n + 2)
  rw [e1, e2]
  have hp : ‖w‖ ^ (n + 2) ≤ 1 := pow_le_one₀ (norm_nonneg _) hw
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [pow_nonneg (norm_nonneg w) (n + 2)]

theorem summable_bound : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
  have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  simpa using this

theorem continuousOn_F : ContinuousOn F (Metric.closedBall 0 1) := by
  refine continuousOn_tsum (u := fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) (fun n => ?_) summable_bound
    (fun n w hw => norm_F_term_le (by simpa using hw) n)
  exact ((continuous_pow _).div_const _).continuousOn

theorem slit_of {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) : 0 < (1 - z).re := by
  rw [sub_re, one_re, sub_pos]
  by_contra h
  push_neg at h
  have hre : z.re ≤ 1 := (Complex.re_le_norm z).trans hz.le
  have hre1 : z.re = 1 := le_antisymm hre h
  have hsq := Complex.sq_norm z
  rw [hz, Complex.normSq_apply, hre1] at hsq
  have him : z.im = 0 := by nlinarith
  exact hz1 (Complex.ext (by simp [hre1]) (by simp [him]))

/-- `F(z) = (1 − z) log(1 − z) + z` on the unit circle minus 1. -/
theorem F_boundary {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    F z = (1 - z) * log (1 - z) + z := by
  have hslit : 1 - z ∈ slitPlane := Or.inl (slit_of hz hz1)
  -- path r ↦ r z, r → 1⁻
  have hpath : Tendsto (fun r : ℝ => (r : ℂ) * z) (𝓝[<] 1) (𝓝 z) := by
    have : Tendsto (fun r : ℝ => (r : ℂ) * z) (𝓝 1) (𝓝 ((1 : ℝ) * z)) :=
      ((continuous_ofReal.mul continuous_const).tendsto 1)
    simpa using this.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ r : ℝ in 𝓝[<] 1, 0 < r ∧ r < 1 := by
    have : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[<] (1 : ℝ) := Ioo_mem_nhdsLT (by norm_num)
    filter_upwards [this] with r hr using hr
  have hnorm : ∀ r : ℝ, 0 < r → r < 1 → ‖(r : ℂ) * z‖ < 1 := fun r h0 h1 => by
    rw [norm_mul, hz, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h0]; exact h1
  -- limit of F along the path
  have hF1 : Tendsto (fun r : ℝ => F ((r : ℂ) * z)) (𝓝[<] 1) (𝓝 (F z)) := by
    have hcw : ContinuousWithinAt F (Metric.closedBall 0 1) z :=
      continuousOn_F z (by simp [hz])
    refine hcw.tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hpath, ?_⟩)
    filter_upwards [hev] with r hr
    simpa using (hnorm r hr.1 hr.2).le
  -- limit of the closed form along the path
  have hG : ContinuousAt (fun w : ℂ => (1 - w) * log (1 - w) + w) z := by
    have hlog : ContinuousAt (fun w : ℂ => log (1 - w)) z :=
      (continuousAt_clog hslit).comp (continuous_const.sub continuous_id).continuousAt
    exact ((continuous_const.sub continuous_id).continuousAt.mul hlog).add continuousAt_id
  have hF2 : Tendsto (fun r : ℝ => F ((r : ℂ) * z)) (𝓝[<] 1)
      (𝓝 ((1 - z) * log (1 - z) + z)) := by
    refine (hG.tendsto.comp hpath).congr' ?_
    filter_upwards [hev] with r hr
    exact ((hasSum_F (hnorm r hr.1 hr.2)).tsum_eq).symm
  exact tendsto_nhds_unique hF1 hF2

/-! ## The Dirichlet series side -/

/-- `D(s) = Σ_n z^{n+2} ((n+1)^{-s} − (n+2)^{-s})`. -/
noncomputable def D (z : ℂ) (s : ℝ) : ℂ :=
  ∑' n : ℕ, z ^ (n + 2) * ((c (n + 1) s - c (n + 2) s : ℝ) : ℂ)

theorem D_one (z : ℂ) : D z 1 = F z := by
  unfold D F
  congr 1; funext n
  simp only [c, Real.rpow_one]
  have a1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have a2 : (n : ℂ) + 2 ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
  push_cast
  field_simp
  ring

theorem D_tendsto {z : ℂ} (hz : ‖z‖ = 1) : Tendsto (D z) (𝓝[>] 1) (𝓝 (D z 1)) := by
  unfold D
  have hbound : Summable (fun n : ℕ => 2 / ((n : ℝ) + 1) ^ 2) := by
    have := summable_bound.mul_left 2
    simpa [mul_one_div] using this
  refine tendsto_tsum_of_dominated_convergence hbound (fun n => ?_) ?_
  · -- pointwise continuity in s
    have hc : ∀ m : ℕ, 0 < m → Continuous (fun s : ℝ => c m s) := fun m hm => by
      unfold c
      refine Continuous.inv₀ (Real.continuous_const_rpow (by positivity)) fun s => ?_
      exact (Real.rpow_pos_of_pos (by exact_mod_cast hm) s).ne'
    have : Continuous (fun s : ℝ => z ^ (n + 2) * ((c (n + 1) s - c (n + 2) s : ℝ) : ℂ)) :=
      continuous_const.mul (continuous_ofReal.comp ((hc _ (by omega)).sub (hc _ (by omega))))
    exact (this.tendsto 1).mono_left nhdsWithin_le_nhds
  · have : Set.Ioo (1 : ℝ) 2 ∈ 𝓝[>] (1 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
    filter_upwards [this] with s hs n
    obtain ⟨b0, b1⟩ := c_diff_bound n hs.1.le hs.2.le
    rw [norm_mul, norm_pow, hz, one_pow, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg b0]
    exact b1

/-- The expZeta series in terms of `z^n c n s`. -/
theorem hasSum_expZeta_c (y : ℝ) {s : ℝ} (hs : 1 < s) :
    HasSum (fun n : ℕ => cexp (2 * π * I * y) ^ n * (c n s : ℂ)) (expZeta y s) := by
  have h := hasSum_expZeta_of_one_lt_re y (s := (s : ℂ)) (by simpa using hs)
  convert h using 1
  funext n
  rw [← Complex.exp_nat_mul, c, ofReal_inv, ← div_eq_mul_inv]
  congr 1
  · ring_nf
  · rw [ofReal_cpow (Nat.cast_nonneg n)]; simp

/-- Summation by parts: for `s > 1`, `expZeta y s = (D(s) − z)/(z − 1)`. -/
theorem expZeta_eq_D (y : ℝ) {s : ℝ} (hs : 1 < s) (hz1 : cexp (2 * π * I * y) ≠ 1) :
    expZeta y s = (D (cexp (2 * π * I * y)) s - cexp (2 * π * I * y)) /
      (cexp (2 * π * I * y) - 1) := by
  set z := cexp (2 * π * I * y) with hzdef
  set S := expZeta y s
  have h0 := hasSum_expZeta_c y hs
  rw [← hzdef] at h0
  have hs0 : s ≠ 0 := by linarith
  have hA : HasSum (fun n : ℕ => z ^ (n + 1) * (c (n + 1) s : ℂ)) S := by
    have := (hasSum_nat_add_iff' 1).mpr h0
    simpa [c_zero hs0] using this
  have hB : HasSum (fun n : ℕ => z ^ (n + 2) * (c (n + 2) s : ℂ)) (S - z) := by
    have := (hasSum_nat_add_iff' 1).mpr hA
    simpa [c_one] using this
  have hC : HasSum (fun n : ℕ => z ^ (n + 2) * ((c (n + 1) s - c (n + 2) s : ℝ) : ℂ))
      (z * S - (S - z)) := by
    have := (hA.mul_left z).sub hB
    convert this using 1
    funext n; push_cast; ring
  have hD : D z s = z * S - (S - z) := hC.tsum_eq
  have hz1' : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  rw [hD]; field_simp; ring

/-- **expZeta at s = 1**: `expZeta y 1 = −log(1 − e(y))` for `y ∉ ℤ`. -/
theorem expZeta_one (y : ℝ) (hy : (y : UnitAddCircle) ≠ 0) (hz1 : cexp (2 * π * I * y) ≠ 1) :
    expZeta y 1 = -log (1 - cexp (2 * π * I * y)) := by
  set z := cexp (2 * π * I * y) with hzdef
  have hz : ‖z‖ = 1 := by
    rw [hzdef, show 2 * π * I * y = ((2 * π * y : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hcont : Tendsto (fun s : ℝ => expZeta y s) (𝓝[>] 1) (𝓝 (expZeta y 1)) := by
    have hc := (differentiableAt_expZeta (y : UnitAddCircle) 1 (Or.inr hy)).continuousAt
    have : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝 1) (𝓝 (1 : ℂ)) := by
      simpa using (continuous_ofReal.tendsto (1 : ℝ))
    exact (hc.tendsto.comp this).mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun s : ℝ => expZeta y s) (𝓝[>] 1) (𝓝 ((D z 1 - z) / (z - 1))) := by
    refine (((D_tendsto hz).sub_const z).div_const (z - 1)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (expZeta_eq_D y hs hz1).symm
  rw [tendsto_nhds_unique hcont hlim, D_one, F_boundary hz hz1]
  have hz1' : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  field_simp
  ring

/-! ## The argument computation and the value at 0 -/

theorem not_int_facts {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    ((x : UnitAddCircle) ≠ 0) ∧ (((-x : ℝ) : UnitAddCircle) ≠ 0) ∧
      cexp (2 * π * I * x) ≠ 1 ∧ cexp (2 * π * I * ((-x : ℝ) : ℂ)) ≠ 1 := by
  have hint : ∀ n : ℤ, (n : ℝ) ≠ x := fun n hn => by
    have a : (0 : ℝ) < n := hn ▸ h0
    have b : (n : ℝ) < 1 := hn ▸ h1
    have a' : 0 < n := by exact_mod_cast a
    have b' : n < 1 := by exact_mod_cast b
    omega
  have hcirc : ∀ t : ℝ, (∀ n : ℤ, (n : ℝ) ≠ t) → (t : UnitAddCircle) ≠ 0 := fun t ht h => by
    rw [AddCircle.coe_eq_zero_iff] at h
    obtain ⟨n, hn⟩ := h
    exact ht n (by simpa using hn)
  have hexp : ∀ t : ℝ, (∀ n : ℤ, (n : ℝ) ≠ t) → cexp (2 * π * I * t) ≠ 1 := fun t ht h => by
    rw [Complex.exp_eq_one_iff] at h
    obtain ⟨n, hn⟩ := h
    have hπ : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    have : (t : ℂ) = n := by
      have := hn; rw [show (n : ℂ) * (2 * π * I) = 2 * π * I * n by ring] at this
      exact mul_left_cancel₀ hπ this
    exact ht n (by exact_mod_cast this.symm)
  have hint' : ∀ n : ℤ, (n : ℝ) ≠ -x := fun n hn => hint (-n) (by push_cast; linarith)
  exact ⟨hcirc x hint, hcirc (-x) hint', hexp x hint, hexp (-x) hint'⟩

theorem arg_one_sub_exp {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    arg (1 - cexp (2 * π * I * x)) = π * x - π / 2 := by
  set θ : ℝ := π * x - π / 2
  have hsin : 0 < Real.sin (π * x) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have key : 1 - cexp (2 * π * I * x) =
      ((2 * Real.sin (π * x) : ℝ) : ℂ) * (cos θ + sin θ * I) := by
    have hz : cexp (2 * π * I * x) = ((Real.cos (2 * π * x) : ℝ) : ℂ) +
        ((Real.sin (2 * π * x) : ℝ) : ℂ) * I := by
      rw [show 2 * π * I * x = ((2 * π * x : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I,
        ← ofReal_cos, ← ofReal_sin]
    have hθ : cos (θ : ℂ) + sin (θ : ℂ) * I = ((Real.cos θ : ℝ) : ℂ) + ((Real.sin θ : ℝ) : ℂ) * I := by
      rw [ofReal_cos, ofReal_sin]
    have hc : Real.cos θ = Real.sin (π * x) := by simp [θ, Real.cos_sub_pi_div_two]
    have hs : Real.sin θ = -Real.cos (π * x) := by simp [θ, Real.sin_sub_pi_div_two]
    have hc2 : Real.cos (2 * π * x) = 1 - 2 * Real.sin (π * x) ^ 2 := by
      rw [show 2 * π * x = 2 * (π * x) by ring, Real.cos_two_mul, Real.cos_sq']; ring
    have hs2 : Real.sin (2 * π * x) = 2 * Real.sin (π * x) * Real.cos (π * x) := by
      rw [show 2 * π * x = 2 * (π * x) by ring, Real.sin_two_mul]
    rw [hz, hθ, hc, hs, hc2, hs2]
    apply Complex.ext <;>
      simp only [add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, sub_re, one_re, add_im, mul_im,
        sub_im, one_im] <;> ring
  rw [key, arg_real_mul _ (by positivity)]
  apply arg_cos_add_sin_mul_I
  constructor <;> simp only [θ] <;>
    nlinarith [Real.pi_pos, mul_pos Real.pi_pos h0, mul_lt_mul_of_pos_left h1 Real.pi_pos]

/-- **The missing Mathlib value**, proved: `hurwitzZetaOdd x 0 = 1/2 − x` for `0 < x < 1`. -/
theorem hurwitzOddZero : Erdos634.LemmaSB1.HurwitzOddZero := by
  intro x h0 h1
  obtain ⟨hx0, hmx0, hz1, hw1⟩ := not_int_facts h0 h1
  -- (1) functional equation at s = 1
  have hfe := hurwitzZetaOdd_one_sub (x : UnitAddCircle) (s := 1) (fun n h => by
    have := congrArg re h
    simp at this
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  rw [sub_self, cpow_neg_one, Complex.Gamma_one, mul_one, mul_div_assoc,
    show (π : ℂ) * (1 / 2) = π / 2 by ring, Complex.sin_pi_div_two, mul_one] at hfe
  rw [hfe]
  -- (2) sinZeta via expZeta
  rw [sinZeta_eq, ← AddCircle.coe_neg, expZeta_one x hx0 hz1, expZeta_one (-x) hmx0 hw1]
  set z := cexp (2 * π * I * x) with hzdef
  have hw : cexp (2 * π * I * ((-x : ℝ) : ℂ)) = conj z := by
    rw [hzdef, ← Complex.exp_conj]; congr 1
    simp only [map_mul, map_ofNat, conj_ofReal, conj_I, ofReal_neg]; ring
  rw [hw, show (1 : ℂ) - conj z = conj (1 - z) by simp]
  have hz : ‖z‖ = 1 := by
    rw [hzdef, show 2 * π * I * x = ((2 * π * x : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hre := slit_of hz hz1
  have hargpi : (1 - z).arg ≠ π := fun h => by
    have := (Complex.arg_eq_pi_iff.mp h).1; linarith
  rw [log_conj _ hargpi]
  set L := log (1 - z)
  have him : L.im = π * x - π / 2 := by rw [log_im]; exact arg_one_sub_exp h0 h1
  have hL : L = L.re + L.im * I := (Complex.re_add_im L).symm
  have hcL : conj L = L.re - L.im * I := by
    apply Complex.ext <;> simp
  rw [hcL, hL, him]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  push_cast
  ring_nf
  simp
  ring

/-- **B1 (unconditional)**: for every odd primitive Dirichlet character χ mod N,
`Σ_{j mod N} χ(j)·((j/N)) ≠ 0`, i.e. B_{1,χ} ≠ 0. -/
theorem B1 {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hp : χ.IsPrimitive) (ho : χ.Odd) :
    ∑ j : ZMod N, χ j * ((Erdos634.LemmaS.saw ((j.val : ℚ) / N) : ℚ) : ℂ) ≠ 0 :=
  Erdos634.LemmaSB1.B1_of_hurwitzOddZero hurwitzOddZero hp ho

/-- Joint witness: B1 fires on a real odd primitive character mod 3. -/
theorem B1_witness_mod3 : ∃ χ : DirichletCharacter ℂ 3,
    ∑ j : ZMod 3, χ j * ((Erdos634.LemmaS.saw ((j.val : ℚ) / 3) : ℚ) : ℂ) ≠ 0 := by
  obtain ⟨χ, hp, ho⟩ := Erdos634.LemmaSB1.exists_odd_primitive_mod3
  exact ⟨χ, by simpa using B1 hp ho⟩

end Erdos634.LemmaSB1H

#print axioms Erdos634.LemmaSB1H.hurwitzOddZero
#print axioms Erdos634.LemmaSB1H.B1
#print axioms Erdos634.LemmaSB1H.B1_witness_mod3

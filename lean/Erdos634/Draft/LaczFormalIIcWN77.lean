-- Draft/LaczFormalIIcWN77.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3), Lemma 6.2: an EQUIANGULAR polygon is strictly convex.
-- `equiangular_SC`: `q : Fin M -> C` injective, `M >= 3`, `M gamma = 2 pi`, `0 < gamma`, `sigma = +-1`, `sigma * extAng q k = gamma` for every `k`  ==>  `SC q sigma` (strict convexity in the sense of WN57).
-- Route (pure plane geometry, no Jordan theorem): the edge vectors satisfy `e_{j+t} = nu_t (e^{i sigma gamma})^t e_j` with `nu_t > 0`; the vertex `q(j+i) - q j = (sum_{t<i} nu_t w^t) e_j`; its side value is
-- `sum_{t<i} nu_t sin(t gamma)`, positive for `2 <= i <= M-1` by the closure equation `sum_{t<M} nu_t sin(t gamma) = 0` (positive head while `t gamma < pi`, positive tail afterwards).
-- Consumed by the ring step: `RingSetup.SCc` for the innermost cycle (so that field is no longer part of the tile-level supply).  NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN76

open scoped Classical Fin.NatCast
open Complex

namespace Erdos634.Draft.LaczFormal.WN

variable {M : ℕ} [NeZero M]

/-- Edge vector. -/
def ev (q : Fin M → ℂ) (k : Fin M) : ℂ := q (k + 1) - q k

theorem ev_ratio {q : Fin M → ℂ} (hinj : Function.Injective q) (hM : 3 ≤ M) {σ γ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hturn : ∀ k, σ * extAng q k = γ) (k : Fin M) :
    ∃ μ : ℝ, 0 < μ ∧ ev q k = (μ : ℂ) * Complex.exp ((σ * γ : ℝ) * Complex.I) * ev q (k - 1) := by
  have h1 : ev q k ≠ 0 := sub_ne_zero.2 (nd hinj hM k)
  have h2 : ev q (k - 1) ≠ 0 := sub_ne_zero.2 (nd hinj hM (k - 1))
  have hev : ev q (k - 1) = q k - q (k - 1) := by unfold ev; rw [sub_add_cancel]
  have hr : extAng q k = Complex.arg (ev q k / ev q (k - 1)) := by
    unfold extAng; rw [hev]; rfl
  have harg : Complex.arg (ev q k / ev q (k - 1)) = σ * γ := by
    rw [← hr]
    have := hturn k
    rcases hσ with rfl | rfl
    · linarith
    · linarith
  have hne : ev q k / ev q (k - 1) ≠ 0 := div_ne_zero h1 h2
  refine ⟨‖ev q k / ev q (k - 1)‖, norm_pos_iff.2 hne, ?_⟩
  have := Complex.norm_mul_exp_arg_mul_I (ev q k / ev q (k - 1))
  rw [harg] at this
  rw [this]
  field_simp

theorem ev_iter {q : Fin M → ℂ} (hinj : Function.Injective q) (hM : 3 ≤ M) {σ γ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hturn : ∀ k, σ * extAng q k = γ) (j : Fin M) :
    ∀ t : ℕ, ∃ ν : ℝ, 0 < ν ∧ ev q (j + (t : Fin M)) = (ν : ℂ) * Complex.exp ((σ * γ : ℝ) * Complex.I) ^ t * ev q j := by
  intro t
  induction t with
  | zero => exact ⟨1, one_pos, by simp⟩
  | succ t ih =>
    obtain ⟨ν, hν, hνe⟩ := ih
    obtain ⟨μ, hμ, hμe⟩ := ev_ratio hinj hM hσ hturn (j + (t : Fin M) + 1)
    refine ⟨μ * ν, mul_pos hμ hν, ?_⟩
    have e1 : j + ((t + 1 : ℕ) : Fin M) = j + (t : Fin M) + 1 := by rw [Nat.cast_succ, add_assoc]
    rw [e1, hμe, add_sub_cancel_right, hνe]
    push_cast
    ring

theorem q_sum {q : Fin M → ℂ} (j : Fin M) (ν : ℕ → ℝ) (ω : ℂ) (hν : ∀ t : ℕ, ev q (j + (t : Fin M)) = (ν t : ℂ) * ω ^ t * ev q j) :
    ∀ i : ℕ, q (j + (i : Fin M)) - q j = (∑ t ∈ Finset.range i, (ν t : ℂ) * ω ^ t) * ev q j := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    have e1 : j + ((i + 1 : ℕ) : Fin M) = j + (i : Fin M) + 1 := by rw [Nat.cast_succ, add_assoc]
    rw [Finset.sum_range_succ, e1]
    have h2 : q (j + (i : Fin M) + 1) - q (j + (i : Fin M)) = (ν i : ℂ) * ω ^ i * ev q j := hν i
    linear_combination h2 + ih


omit [NeZero M] in
theorem sin_tg_pos {t : ℕ} (hM : 0 < M) (h0 : 0 < t) (h : 2 * t < M) : 0 < Real.sin ((t : ℝ) * (2 * Real.pi / M)) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · have : (0 : ℝ) < t := by exact_mod_cast h0
    have : (0 : ℝ) < M := by exact_mod_cast hM
    positivity
  · have hM' : (0 : ℝ) < M := by exact_mod_cast hM
    have h2 : (2 * t : ℝ) < M := by exact_mod_cast h
    rw [mul_div_assoc', div_lt_iff₀ hM']
    nlinarith [Real.pi_pos]

omit [NeZero M] in
theorem sin_tg_neg {t : ℕ} (hM : 0 < M) (h : M < 2 * t) (h2 : t < M) : Real.sin ((t : ℝ) * (2 * Real.pi / M)) < 0 := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have e : (t : ℝ) * (2 * Real.pi / M) = ((t : ℝ) * (2 * Real.pi / M) - Real.pi) + Real.pi := by ring
  rw [e, Real.sin_add_pi]
  have : 0 < Real.sin ((t : ℝ) * (2 * Real.pi / M) - Real.pi) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · have h' : (M : ℝ) < 2 * t := by exact_mod_cast h
      have : (M : ℝ) * Real.pi < 2 * t * Real.pi := by nlinarith [Real.pi_pos]
      have e2 : (t : ℝ) * (2 * Real.pi / M) - Real.pi = (2 * t * Real.pi - M * Real.pi) / M := by field_simp
      rw [e2]; apply div_pos <;> linarith
    · have h' : (t : ℝ) < M := by exact_mod_cast h2
      have e2 : (t : ℝ) * (2 * Real.pi / M) - Real.pi = (2 * t * Real.pi - M * Real.pi) / M := by field_simp
      rw [e2, div_lt_iff₀ hM']
      nlinarith [Real.pi_pos]
  linarith

omit [NeZero M] in
theorem partial_pos (hM : 3 ≤ M) (ν : ℕ → ℝ) (hν : ∀ t, 0 < ν t)
    (hclos : ∑ t ∈ Finset.range M, ν t * Real.sin ((t : ℝ) * (2 * Real.pi / M)) = 0) {i : ℕ} (hi2 : 2 ≤ i) (hiM : i ≤ M - 1) :
    0 < ∑ t ∈ Finset.range i, ν t * Real.sin ((t : ℝ) * (2 * Real.pi / M)) := by
  have hMpos : 0 < M := by omega
  by_cases hcase : 2 * (i - 1) < M
  · apply Finset.sum_pos'
    · intro t ht
      rcases Nat.eq_zero_or_pos t with rfl | htp
      · simp
      · have : t ≤ i - 1 := by have := Finset.mem_range.1 ht; omega
        exact (mul_pos (hν t) (sin_tg_pos hMpos htp (by omega))).le
    · exact ⟨1, Finset.mem_range.2 (by omega), mul_pos (hν 1) (sin_tg_pos hMpos one_pos (by omega))⟩
  · have hsplit := Finset.sum_range_add_sum_Ico (fun t => ν t * Real.sin ((t : ℝ) * (2 * Real.pi / M))) (show i ≤ M by omega)
    have hneg : ∑ t ∈ Finset.Ico i M, ν t * Real.sin ((t : ℝ) * (2 * Real.pi / M)) < 0 := by
      apply Finset.sum_neg
      · intro t ht
        have ht' := Finset.mem_Ico.1 ht
        exact mul_neg_of_pos_of_neg (hν t) (sin_tg_neg hMpos (by omega) ht'.2)
      · exact ⟨i, Finset.mem_Ico.2 ⟨le_rfl, by omega⟩⟩
    simp only at hsplit
    linarith

theorem im_omega_pow (σ γ : ℝ) (t : ℕ) : (Complex.exp ((σ * γ : ℝ) * Complex.I) ^ t).im = Real.sin (t * (σ * γ)) := by
  rw [← Complex.exp_nat_mul]
  have : (t : ℂ) * (((σ * γ : ℝ) : ℂ) * Complex.I) = ((t * (σ * γ) : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.exp_ofReal_mul_I_im]

theorem equiangular_SC {q : Fin M → ℂ} (hinj : Function.Injective q) (hM : 3 ≤ M) {σ γ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hγ : γ = 2 * Real.pi / M) (hturn : ∀ k, σ * extAng q k = γ) : SC q σ := by
  intro j m hmj hmj1
  choose ν hν0 hν using ev_iter hinj hM hσ hturn j
  set ω : ℂ := Complex.exp ((σ * γ : ℝ) * Complex.I) with hω
  have hsum := q_sum (q := q) j ν ω hν
  have hE : ev q j ≠ 0 := sub_ne_zero.2 (nd hinj hM j)
  have hMpos : 0 < M := by omega
  -- sin(t sigma gamma) = sigma sin(t gamma)
  have hsin : ∀ t : ℕ, Real.sin (t * (σ * γ)) = σ * Real.sin (t * γ) := by
    intro t
    rcases hσ with rfl | rfl
    · simp
    · have : (t : ℝ) * (-1 * γ) = -((t : ℝ) * γ) := by ring
      rw [this, Real.sin_neg]; ring
  have himS : ∀ i : ℕ, (∑ t ∈ Finset.range i, (ν t : ℂ) * ω ^ t).im = σ * ∑ t ∈ Finset.range i, ν t * Real.sin ((t : ℝ) * γ) := by
    intro i
    rw [Complex.im_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [Complex.im_ofReal_mul, hω, im_omega_pow, hsin]
    ring
  -- closure
  have hclos : ∑ t ∈ Finset.range M, ν t * Real.sin ((t : ℝ) * (2 * Real.pi / M)) = 0 := by
    have h1 := hsum M
    have hz : q (j + ((M : ℕ) : Fin M)) = q j := by simp
    rw [hz, sub_self] at h1
    have h2 : (∑ t ∈ Finset.range M, (ν t : ℂ) * ω ^ t) = 0 := by
      rcases mul_eq_zero.1 h1.symm with h | h
      · exact h
      · exact absurd h hE
    have h3 := himS M
    rw [h2, Complex.zero_im] at h3
    rw [← hγ]
    rcases hσ with rfl | rfl <;> linarith
  -- index
  set i := (m - j).val with hi
  have hmi : j + ((i : ℕ) : Fin M) = m := by simp [hi]
  have hi2 : 2 ≤ i := by
    by_contra hlt
    have : i = 0 ∨ i = 1 := by omega
    rcases this with h0 | h1
    · apply hmj
      have : m - j = ((i : ℕ) : Fin M) := by simp [hi]
      rw [h0] at this
      simpa [sub_eq_zero] using this
    · apply hmj1
      have : m - j = ((i : ℕ) : Fin M) := by simp [hi]
      rw [h1] at this
      have : m = j + 1 := by rw [← sub_eq_iff_eq_add'] ; simpa using this
      exact this
  have hiM : i ≤ M - 1 := by have := (m - j).isLt; omega
  have hP := partial_pos hM ν hν0 hclos hi2 hiM
  have hqm := hsum i
  rw [hmi] at hqm
  unfold sideFn
  have : (q m - q j) / (q (j + 1) - q j) = ∑ t ∈ Finset.range i, (ν t : ℂ) * ω ^ t := by
    rw [hqm]
    have : q (j + 1) - q j = ev q j := rfl
    rw [this]
    field_simp
  rw [this, himS i]
  have hP' : 0 < ∑ t ∈ Finset.range i, ν t * Real.sin ((t : ℝ) * γ) := by rw [hγ]; exact hP
  rcases hσ with rfl | rfl <;> linarith

#print axioms equiangular_SC

end Erdos634.Draft.LaczFormal.WN

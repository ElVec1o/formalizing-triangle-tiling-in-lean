-- Draft/LaczFormalIIcSymB.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.3, two-exceptional-point case: CENTRAL SYMMETRY of the equiangular 2k-gon, as vector algebra (blueprint A.4, "central symmetry (vector algebra)").
-- Hypotheses (PURE geometry): a closed convex-position polygon `V : N -> Plane` of period 2k with all interior angles pi - gamma (k gamma = pi), spokes of angle alpha at the start / beta at the end of each side from the first k corners to E and from the last k
-- corners to F.  Conclusion: |V_{n+k} V_{n+k+1}| = |V_n V_{n+1}| for all n.
-- Route (NOT the paper's reflection argument, whose "coincides" step is not spelled out): both halves have geometric side lengths (law of sines, `sine_ratio_step`) with the SAME ratio; the sides turn by gamma (`turn_step`) so
-- e_{n+k} = -e_n in direction; the closure sum then reads  d_0 S + d_{k-1} w^{k-1} = 0  (d_n = s_n - s_{n+k}, S = sum (q w)^n) and S is not a real multiple of w^{k-1} because V_0 is strictly left of the side V_{k-1} V_k.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3, (18) and the central symmetry argument), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcSymA

open Erdos634.Geometry EuclideanGeometry
open scoped RealInnerProductSpace

namespace Erdos634.Draft.LaczFormal.Thm21

theorem cv_sub (x y : Plane) : cv (x - y) = cv x - cv y := by
  apply Complex.ext <;> simp [cv]

theorem cross2_cv (x y : Plane) : cross2 x y = ((starRingEnd ℂ) (cv x) * cv y).im := by
  simp [cv, cross2, Complex.mul_im]; ring


theorem cv_eq_zero {x : Plane} (h : cv x = 0) : x = 0 := by
  have h1 : x 0 = 0 := congrArg Complex.re h
  have h2 : x 1 = 0 := congrArg Complex.im h
  ext i; fin_cases i <;> simp [h1, h2]

theorem omega_pow_k {γ : ℝ} {k : ℕ} (hkγ : (k : ℝ) * γ = Real.pi) :
    (Complex.exp (γ * Complex.I)) ^ k = -1 := by
  rw [← Complex.exp_nat_mul]
  have : (k : ℂ) * (γ * Complex.I) = ((k * γ : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, hkγ, Complex.exp_pi_mul_I]

theorem omega_eq (γ : ℝ) : (Complex.exp (γ * Complex.I)) = ⟨Real.cos γ, Real.sin γ⟩ := by
  apply Complex.ext
  · simp [Complex.exp_ofReal_mul_I_re]
  · simp [Complex.exp_ofReal_mul_I_im]

set_option maxHeartbeats 3200000 in
theorem central_symmetry_core {k : ℕ} (hk : 3 ≤ k) (V : ℕ → Plane) (E F : Plane) (α β γ : ℝ)
    (hper : ∀ n, V (n + 2 * k) = V n)
    (hcr : ∀ n, 0 < cross2 (V (n + 1) - V n) (V (n + 2) - V (n + 1)))
    (hnc : 0 < cross2 (V k - V (k - 1)) (V 0 - V (k - 1)))
    (hang : ∀ n, ∠ (V n) (V (n + 1)) (V (n + 2)) = Real.pi - γ)
    (hα : 0 < α) (hβ : 0 < β) (hαβ : α + β + γ = Real.pi) (hγ0 : 0 < γ) (hkγ : (k : ℝ) * γ = Real.pi)
    (hEa : ∀ n, n < k → ∠ (V (n + 1)) (V n) E = α) (hEb : ∀ n, n + 1 < k → ∠ (V n) (V (n + 1)) E = β)
    (hFa : ∀ n, k ≤ n → n < 2 * k → ∠ (V (n + 1)) (V n) F = α) (hFb : ∀ n, k ≤ n → n + 1 < 2 * k → ∠ (V n) (V (n + 1)) F = β) :
    ∀ n, dist (V (n + k)) (V (n + k + 1)) = dist (V n) (V (n + 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hnc
  have hpi := Real.pi_pos
  have hγpi : γ < Real.pi := by linarith
  set s : ℕ → ℝ := fun n => dist (V n) (V (n + 1)) with hs
  have hne : ∀ n, V n ≠ V (n + 1) := by
    intro n h
    have := hcr n
    have e : V (n + 1) - V n = 0 := by rw [← h]; simp
    rw [e] at this
    simp [cross2] at this
  have hspos : ∀ n, 0 < s n := fun n => dist_pos.mpr (hne n)
  have hsnorm : ∀ n, ‖V (n + 1) - V n‖ = s n := by
    intro n; simp only [hs]; rw [dist_comm, dist_eq_norm]
  set ω : ℂ := Complex.exp (γ * Complex.I) with hω
  have hω0 : ω ≠ 0 := Complex.exp_ne_zero _
  -- turning
  have hturn : ∀ n, cv (V (n + 2) - V (n + 1)) * (s n : ℂ) = (s (n + 1) : ℂ) * ω * cv (V (n + 1) - V n) := by
    intro n
    have := turn_step hγ0 hγpi (hne n) (hne (n + 1)) (hcr n) (hang n)
    rw [hsnorm n] at this
    have h2 : ‖V (n + 2) - V (n + 1)‖ = s (n + 1) := hsnorm (n + 1)
    rw [h2, ← omega_eq] at this
    exact this
  set u0 : ℂ := cv (V 1 - V 0) / (s 0 : ℂ) with hu0
  have hs0c : (s 0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hspos 0).ne'
  have hB : ∀ n, cv (V (n + 1) - V n) = (s n : ℂ) * ω ^ n * u0 := by
    intro n
    induction n with
    | zero => simp only [hu0]; field_simp
    | succ n ih =>
      have h := hturn n
      have hsn : (s n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hspos n).ne'
      rw [ih] at h
      have e : cv (V (n + 1 + 1) - V (n + 1)) = (s (n + 1) : ℂ) * ω ^ (n + 1) * u0 := by
        have h' : cv (V (n + 2) - V (n + 1)) * (s n : ℂ) = (s (n + 1) : ℂ) * ω ^ (n + 1) * u0 * (s n : ℂ) := by
          rw [h]; ring
        exact mul_right_cancel₀ hsn h'
      exact e
  -- closure
  have hclos : ∑ n ∈ Finset.range (2 * (m + 1)), cv (V (n + 1) - V n) = 0 := by
    have e : ∀ n, cv (V (n + 1) - V n) = cv (V (n + 1)) - cv (V n) := fun n => cv_sub _ _
    simp only [e]
    rw [Finset.sum_range_sub (fun n => cv (V n))]
    have : V (2 * (m + 1)) = V 0 := by simpa using hper 0
    rw [this]; simp
  have hu0ne : u0 ≠ 0 := by
    simp only [hu0]
    apply div_ne_zero _ hs0c
    intro h
    have h1 := cv_eq_zero h
    apply hne 0
    have : V 1 = V 0 := sub_eq_zero.mp h1
    exact this.symm
  have hsum2 : ∑ n ∈ Finset.range (2 * (m + 1)), (s n : ℂ) * ω ^ n = 0 := by
    have := hclos
    simp only [hB] at this
    rw [← Finset.sum_mul] at this
    exact (mul_eq_zero.mp this).resolve_right hu0ne
  have hωk : ω ^ (m + 1) = -1 := omega_pow_k hkγ
  have hsplit : ∑ n ∈ Finset.range (m + 1), ((s n : ℂ) - (s (n + (m + 1)) : ℂ)) * ω ^ n = 0 := by
    have := hsum2
    rw [two_mul, Finset.sum_range_add] at this
    have e : ∀ x, (s (m + 1 + x) : ℂ) * ω ^ (m + 1 + x) = -((s (x + (m + 1)) : ℂ) * ω ^ x) := by
      intro x; rw [pow_add, hωk, add_comm (m + 1) x]; ring
    simp only [e] at this
    rw [Finset.sum_neg_distrib, ← sub_eq_add_neg, ← Finset.sum_sub_distrib] at this
    simp only [sub_mul]
    exact this
  -- the two geometric progressions
  set r := Real.sin α with hr
  set t := Real.sin β with ht
  have hrpos : 0 < r := Real.sin_pos_of_pos_of_lt_pi hα (by linarith)
  have htpos : 0 < t := Real.sin_pos_of_pos_of_lt_pi hβ (by linarith)
  have hprE : ∀ n, n + 2 < m + 1 → s (n + 1) * t = r * s n := by
    intro n hn
    exact sine_ratio_step (A := V n) (B := V (n + 1)) (C := V (n + 2)) (E := E) hα hβ (by linarith) (hne n) (hne (n + 1))
      (hEa n (by omega)) (hEb n (by omega)) (hEa (n + 1) (by omega)) (hEb (n + 1) (by omega))
  have hprF : ∀ n, m + 1 ≤ n → n + 2 < 2 * (m + 1) → s (n + 1) * t = r * s n := by
    intro n h1 hn
    exact sine_ratio_step (A := V n) (B := V (n + 1)) (C := V (n + 2)) (E := F) hα hβ (by linarith) (hne n) (hne (n + 1))
      (hFa n h1 (by omega)) (hFb n h1 (by omega)) (hFa (n + 1) (by omega) (by omega)) (hFb (n + 1) (by omega) (by omega))
  set d : ℕ → ℝ := fun n => s n - s (n + (m + 1)) with hd
  have hdstep : ∀ n, n + 2 < m + 1 → d (n + 1) * t = r * d n := by
    intro n hn
    have h1 := hprE n hn
    have h2 := hprF (n + (m + 1)) (by omega) (by omega)
    have e : n + 1 + (m + 1) = n + (m + 1) + 1 := by omega
    simp only [hd, e]
    linarith
  have hdgeo : ∀ n, n + 1 < m + 1 → d n * t ^ n = r ^ n * d 0 := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have := ih (by omega)
      have h2 := hdstep n (by omega)
      calc d (n + 1) * t ^ (n + 1) = (d (n + 1) * t) * t ^ n := by ring
        _ = r * (d n * t ^ n) := by rw [h2]; ring
        _ = r ^ (n + 1) * d 0 := by rw [this]; ring
  have hsgeo : ∀ n, n < m → s n * t ^ n = r ^ n * s 0 := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have := ih (by omega)
      have h2 := hprE n (by omega)
      calc s (n + 1) * t ^ (n + 1) = (s (n + 1) * t) * t ^ n := by ring
        _ = r * (s n * t ^ n) := by rw [h2]; ring
        _ = r ^ (n + 1) * s 0 := by rw [this]; ring
  set q : ℝ := r / t with hq
  have htne : t ≠ 0 := htpos.ne'
  have hdq : ∀ n, n < m → d n = q ^ n * d 0 := by
    intro n hn
    have := hdgeo n (by omega)
    rw [hq, div_pow]
    field_simp
    linarith
  have hsq : ∀ n, n < m → s n = q ^ n * s 0 := by
    intro n hn
    have := hsgeo n hn
    rw [hq, div_pow]
    field_simp
    linarith
  have hc : ∀ n, ((s n : ℂ) - (s (n + (m + 1)) : ℂ)) = (d n : ℂ) := fun n => by simp [hd]
  have hsplit' : ∑ n ∈ Finset.range m, (d n : ℂ) * ω ^ n + (d m : ℂ) * ω ^ m = 0 := by
    have := hsplit
    rw [Finset.sum_range_succ] at this
    simpa only [hc] using this
  set S : ℂ := ∑ n ∈ Finset.range m, ((q : ℂ) * ω) ^ n with hS
  have hmain : (d 0 : ℂ) * S + (d m : ℂ) * ω ^ m = 0 := by
    have e : ∑ n ∈ Finset.range m, (d n : ℂ) * ω ^ n = (d 0 : ℂ) * S := by
      rw [hS, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      have := hdq n (Finset.mem_range.mp hn)
      rw [this]; push_cast; rw [mul_pow]; ring
    rw [← e]; exact hsplit'
  have hcvm : cv (V m - V 0) = (s 0 : ℂ) * u0 * S := by
    have e1 : cv (V m) - cv (V 0) = ∑ n ∈ Finset.range m, cv (V (n + 1) - V n) := by
      have e : ∀ n, cv (V (n + 1) - V n) = cv (V (n + 1)) - cv (V n) := fun n => cv_sub _ _
      simp only [e]
      rw [Finset.sum_range_sub (fun n => cv (V n))]
    rw [cv_sub, e1, hS, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [hB n, hsq n (Finset.mem_range.mp hn)]
    push_cast; rw [mul_pow]; ring
  clear_value u0 S
  have hdall : ∀ n, n < m + 1 → s n = s (n + (m + 1)) := by
    by_cases hd0 : d 0 = 0
    · have hdm : d m = 0 := by
        have h0 : (d 0 : ℂ) = 0 := by rw [hd0]; simp
        rw [h0, zero_mul, zero_add] at hmain
        have := (mul_eq_zero.mp hmain).resolve_right (pow_ne_zero _ hω0)
        exact_mod_cast this
      intro n hn
      have : d n = 0 := by
        rcases Nat.lt_or_ge n m with h | h
        · rw [hdq n h, hd0]; ring
        · have : n = m := by omega
          rw [this]; exact hdm
      simp only [hd] at this
      linarith
    · exfalso
      have hd0c : (d 0 : ℂ) ≠ 0 := by exact_mod_cast hd0
      have hsmc : (s m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hspos m).ne'
      have hX : cv (V 0 - V m) = (((s 0 * d m / (d 0 * s m) : ℝ)) : ℂ) * cv (V (m + 1) - V m) := by
        apply mul_left_cancel₀ hd0c
        rw [cv_sub, hB m]
        have h1 : cv (V 0) - cv (V m) = -(cv (V m - V 0)) := by rw [cv_sub]; ring
        rw [h1, hcvm]
        push_cast
        field_simp
        linear_combination (-1 : ℂ) * hmain
      have hcross : cross2 (V (m + 1) - V m) (V 0 - V m) = 0 := by
        rw [cross2_cv, hX]
        set c := cv (V (m + 1) - V m)
        have : (starRingEnd ℂ) c * (((s 0 * d m / (d 0 * s m) : ℝ) : ℂ) * c) = (((s 0 * d m / (d 0 * s m) : ℝ) : ℂ)) * ((starRingEnd ℂ) c * c) := by ring
        rw [this, Complex.conj_mul']
        norm_cast
      linarith
  intro n
  have hsper : ∀ n, s (n + 2 * (m + 1)) = s n := by
    intro n
    simp only [hs]
    have h1 := hper n
    have h2 := hper (n + 1)
    have e : n + 1 + 2 * (m + 1) = n + 2 * (m + 1) + 1 := by omega
    rw [e] at h2
    rw [h1, h2]
  show s (n + (m + 1)) = s n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n (m + 1) with h | h
    · exact (hdall n h).symm
    · rcases Nat.lt_or_ge n (2 * (m + 1)) with h2 | h2
      · obtain ⟨j, rfl⟩ : ∃ j, n = j + (m + 1) := ⟨n - (m + 1), by omega⟩
        have e : j + (m + 1) + (m + 1) = j + 2 * (m + 1) := by omega
        rw [e, hsper]
        exact (hdall j (by omega))
      · obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 * (m + 1) := ⟨n - 2 * (m + 1), by omega⟩
        have e : j + 2 * (m + 1) + (m + 1) = (j + (m + 1)) + 2 * (m + 1) := by omega
        rw [e, hsper, hsper]
        exact ih j (by omega)

end Erdos634.Draft.LaczFormal.Thm21

#print axioms Erdos634.Draft.LaczFormal.Thm21.central_symmetry_core

-- Draft/LaczFormalGraphDir.lean -- D0 (part 5): ANGULAR POSITION of the rays of a cyclic fan.
-- In the cyclic fan of `fan_cycle` (rays `r_n = p (e n)`, sectors of widths `w_n = wd (p (e n)) (q (e n))`), the ray `r_{n+m}` is `r_n` rotated by
-- the block sum `w_n + .. + w_{n+m-1}` (as complex numbers: `U r_{n+m} = c * exp (i * blocksum) * U r_n`, `c > 0`).  Consequences:
--  * `opposite_iff_blocksum`: `r_{n+m}` is a negative multiple of `r_n` iff the block sum is `pi` mod `2 pi`; for `0 < m < k` iff it equals `pi`
--    (this is the `col` predicate of `LaczFormalRegFan`: "the ray `h_i` has an opposite ray in the fan");
--  * a block of fewer than `k` consecutive sectors has total width `< 2 pi`.
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 4: angles between the half-lines h_i).
import Erdos634.Draft.LaczFormalGraphFan

namespace Erdos634.Draft.LaczFormal.Graph

/-- A plane vector as a complex number. -/
def Uc (x : V2) : ℂ := ⟨x.1, x.2⟩

theorem Uc_ne_zero {x : V2} (hx : x ≠ 0) : Uc x ≠ 0 := by
  intro h
  apply hx
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp [Uc] at h1 h2
  exact Prod.ext h1 h2

/-- One step: the next ray is the current ray rotated by the sector width (times a positive factor). -/
theorem dir_step {u v u' : V2} (hu : u ≠ 0) (hpar : Par u' v) (hok : SecOK u v) :
    ∃ c : ℝ, 0 < c ∧ Uc u' = (c : ℂ) * Complex.exp ((wd u v : ℂ) * Complex.I) * Uc u := by
  obtain ⟨c, hc, hcu⟩ := hpar.smul
  have hUu : Uc u ≠ 0 := Uc_ne_zero hu
  have hv : v ≠ 0 := hpar.ne_right
  set W : ℂ := ⟨dt u v, crs u v⟩ with hW
  have hWne : W ≠ 0 := by
    intro h0
    have h1 := congrArg Complex.re h0
    have h2 := congrArg Complex.im h0
    simp [hW] at h1 h2
    exact hu (eq_zero_of_crs_dt hv h2 h1)
  have hconj : (starRingEnd ℂ) (Uc u) * Uc v = W := by
    apply Complex.ext
    · simp [Uc, hW, dt]; try ring
    · simp [Uc, hW, crs]; try ring
  have hmul : ((‖Uc u‖ ^ 2 : ℝ) : ℂ) * Uc v = W * Uc u := by
    rw [← hconj]
    have h := Complex.conj_mul' (Uc u)
    push_cast
    rw [← h]
    ring
  have hWexp : ((‖W‖ : ℝ) : ℂ) * Complex.exp ((wd u v : ℂ) * Complex.I) = W :=
    Complex.norm_mul_exp_arg_mul_I W
  have hnpos : 0 < ‖Uc u‖ ^ 2 := by positivity
  have hu' : Uc u' = (c : ℂ) * Uc v := by
    apply Complex.ext
    · simp [Uc, hcu]
    · simp [Uc, hcu]
  refine ⟨c * ‖W‖ / ‖Uc u‖ ^ 2, by positivity, ?_⟩
  have hn0 : ((‖Uc u‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hnpos.ne'
  apply mul_left_cancel₀ hn0
  have : ((‖Uc u‖ ^ 2 : ℝ) : ℂ) * Uc u' = (c : ℂ) * (W * Uc u) := by
    rw [hu', ← hmul]; ring
  rw [this]
  have hn1 : ((‖Uc u‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hUu)
  have hR : ((‖Uc u‖ ^ 2 : ℝ) : ℂ) * (((c * ‖W‖ / ‖Uc u‖ ^ 2 : ℝ) : ℂ) * Complex.exp ((wd u v : ℂ) * Complex.I) * Uc u)
      = (c : ℂ) * (((‖W‖ : ℝ) : ℂ) * Complex.exp ((wd u v : ℂ) * Complex.I)) * Uc u := by
    push_cast; field_simp
  rw [hR, hWexp]; ring

section Cyc

variable {ι : Type*} (p q : ι → V2) (e : ℕ → ι)

/-- Total width of the `m` sectors starting at position `n`. -/
noncomputable def blockSum (n m : ℕ) : ℝ := ∑ j ∈ Finset.range m, wd (p (e (n + j))) (q (e (n + j)))

theorem dir_block (hok : ∀ s, SecOK (p s) (q s)) (hpar : ∀ n, Par (p (e (n + 1))) (q (e n))) (n m : ℕ) :
    ∃ c : ℝ, 0 < c ∧ Uc (p (e (n + m))) = (c : ℂ) * Complex.exp ((blockSum p q e n m : ℂ) * Complex.I) * Uc (p (e n)) := by
  induction m with
  | zero => exact ⟨1, one_pos, by simp [blockSum]⟩
  | succ m ih =>
    obtain ⟨c1, hc1, h1⟩ := ih
    obtain ⟨c2, hc2, h2⟩ := dir_step (hok (e (n + m))).ne_p (hpar (n + m)) (hok (e (n + m)))
    refine ⟨c2 * c1, mul_pos hc2 hc1, ?_⟩
    have e1 : n + (m + 1) = n + m + 1 := by ring
    rw [e1, h2, h1]
    have : blockSum p q e n (m + 1) = blockSum p q e n m + wd (p (e (n + m))) (q (e (n + m))) := by
      unfold blockSum; rw [Finset.sum_range_succ]
    rw [this]
    push_cast
    rw [add_mul, Complex.exp_add]
    ring


theorem blockSum_add (n m1 m2 : ℕ) :
    blockSum p q e n (m1 + m2) = blockSum p q e n m1 + blockSum p q e (n + m1) m2 := by
  unfold blockSum
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [show n + (m1 + j) = n + m1 + j by ring]

theorem blockSum_pos (hok : ∀ s, SecOK (p s) (q s)) (n : ℕ) {m : ℕ} (hm : 0 < m) : 0 < blockSum p q e n m := by
  unfold blockSum
  exact Finset.sum_pos (fun j _ => wd_pos (hok _)) ⟨0, Finset.mem_range.mpr hm⟩

/-- Opposite rays: `a` is a negative multiple of `b`. -/
def Opp (a b : V2) : Prop := Par a (-b.1, -b.2)

variable [Fintype ι]

/-- A full period of the cyclic fan has total width the sum over all sectors. -/
theorem blockSum_full (hper : ∀ n, e (n + Fintype.card ι) = e n)
    (hinj : Set.InjOn e (Set.Iio (Fintype.card ι))) (n : ℕ) :
    blockSum p q e n (Fintype.card ι) = ∑ s, wd (p s) (q s) := by
  classical
  set k := Fintype.card ι with hk
  have hmul : ∀ q' x, e (x + q' * k) = e x := by
    intro q'
    induction q' with
    | zero => intro x; simp
    | succ q ih => intro x; rw [Nat.succ_mul, ← add_assoc, hper (x + q * k), ih]
  have hmod : ∀ x, e x = e (x % k) := by
    intro x
    have := hmul (x / k) (x % k)
    rw [show x % k + x / k * k = x by rw [mul_comm]; exact Nat.mod_add_div x k] at this
    exact this
  have hinjn : Set.InjOn (fun j => e (n + j)) (↑(Finset.range k) : Set ℕ) := by
    intro j hj j' hj' h
    simp only [Finset.coe_range, Set.mem_Iio] at hj hj'
    have h1 : e ((n + j) % k) = e ((n + j') % k) := by rw [← hmod, ← hmod]; exact h
    have hk0 : 0 < k := by omega
    have h2 := hinj (Set.mem_Iio.mpr (Nat.mod_lt _ hk0)) (Set.mem_Iio.mpr (Nat.mod_lt _ hk0)) h1
    have h3 : n + j ≡ n + j' [MOD k] := h2
    exact Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.add_left_cancel' n h3) hj hj'
  have himg : (Finset.range k).image (fun j => e (n + j)) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [Finset.card_image_of_injOn hinjn, Finset.card_range])
  unfold blockSum
  rw [← Finset.sum_image (f := fun s => wd (p s) (q s)) hinjn, himg]

/-- **Opposite rays and block sums** (`col` of `LaczFormalRegFan`).  In the cyclic fan, for `0 < m < k` the ray `r_{n+m}` is a negative multiple
of `r_n` iff the `m` sectors between them have total width exactly `pi`. -/
theorem opposite_iff_blocksum (hok : ∀ s, SecOK (p s) (q s)) (hpar : ∀ n, Par (p (e (n + 1))) (q (e n)))
    (hper : ∀ n, e (n + Fintype.card ι) = e n) (hinj : Set.InjOn e (Set.Iio (Fintype.card ι)))
    (hsum : ∑ s, wd (p s) (q s) = 2 * Real.pi) (n m : ℕ) (hm0 : 0 < m) (hmk : m < Fintype.card ι) :
    Opp (p (e (n + m))) (p (e n)) ↔ blockSum p q e n m = Real.pi := by
  have hfull := blockSum_full p q e hper hinj n
  have hsplit := blockSum_add p q e n m (Fintype.card ι - m)
  rw [show m + (Fintype.card ι - m) = Fintype.card ι by omega, hfull, hsum] at hsplit
  have hpos1 := blockSum_pos p q e hok n hm0
  have hpos2 := blockSum_pos p q e hok (n + m) (show 0 < Fintype.card ι - m by omega)
  have hlt : blockSum p q e n m < 2 * Real.pi := by linarith
  obtain ⟨c, hc, hdir⟩ := dir_block p q e hok hpar n m
  have hbne : Uc (p (e n)) ≠ 0 := Uc_ne_zero (hok (e n)).ne_p
  constructor
  · intro hopp
    obtain ⟨c', hc', hcc⟩ := hopp.smul
    have hUa : Uc (p (e (n + m))) = -(c' : ℂ) * Uc (p (e n)) := by
      apply Complex.ext <;> simp [Uc, hcc]
    rw [hdir] at hUa
    have h1 : (c : ℂ) * Complex.exp ((blockSum p q e n m : ℂ) * Complex.I) = -(c' : ℂ) := by
      apply mul_right_cancel₀ hbne
      exact hUa
    have h2 : ‖Complex.exp ((blockSum p q e n m : ℂ) * Complex.I)‖ = 1 := by
      have := Complex.norm_exp_ofReal_mul_I (blockSum p q e n m)
      exact this
    have h3 : c = c' := by
      have := congrArg norm h1
      rw [norm_mul, h2, mul_one, norm_neg] at this
      simpa [abs_of_pos hc, abs_of_pos hc'] using this
    have h4 : Complex.exp ((blockSum p q e n m : ℂ) * Complex.I) = Complex.exp ((Real.pi : ℂ) * Complex.I) := by
      rw [Complex.exp_pi_mul_I]
      subst h3
      have hcn : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
      apply mul_left_cancel₀ hcn
      rw [h1]; ring
    obtain ⟨j, hj⟩ := Complex.exp_eq_exp_iff_exists_int.mp h4
    have hj' := congrArg Complex.im hj
    simp at hj'
    have hj2 := congrArg Complex.re hj
    have hθ : blockSum p q e n m = Real.pi + j * (2 * Real.pi) := by
      have := hj'
      linarith
    have hj0 : j = 0 := by
      have h5 : (j : ℝ) < 1 := by nlinarith [Real.pi_pos]
      have h6 : (-1 : ℝ) < j := by nlinarith [Real.pi_pos]
      have h7 : j < 1 := by exact_mod_cast h5
      have h8 : -1 < j := by exact_mod_cast h6
      omega
    rw [hθ, hj0]; simp
  · intro hθ
    rw [hθ] at hdir
    rw [Complex.exp_pi_mul_I] at hdir
    have hb0 : p (e n) ≠ 0 := (hok (e n)).ne_p
    have hv : ((-(p (e n)).1, -(p (e n)).2) : V2) ≠ 0 := by
      intro h; apply hb0
      have h1 : -(p (e n)).1 = 0 := congrArg Prod.fst h
      have h2 : -(p (e n)).2 = 0 := congrArg Prod.snd h
      exact Prod.ext (show (p (e n)).1 = 0 by linarith) (show (p (e n)).2 = 0 by linarith)
    apply smul_par hc hv
    have hr := congrArg Complex.re hdir
    have hi := congrArg Complex.im hdir
    simp [Uc] at hr hi
    exact Prod.ext (by simp; linarith) (by simp; linarith)

end Cyc

end Erdos634.Draft.LaczFormal.Graph

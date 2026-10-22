import Erdos634.Draft.FluxCRow5Complete
import Erdos634.Draft.FluxCRow5TwoPiThreeFull
import Erdos634.Draft.FluxPaperCorIntAnchored

/-! Draft/GapE120Arith.lean -- the prime-free arithmetic of the `2π/3` equilateral branch at `N = 15`:
    `Row5.theoremE_twoPiThree` (N-free) gives `(s,t)` with `st = 45`, `s,t ≤ 15` odd, so
    `(s,t) ∈ {(3,15),(15,3),(5,9),(9,5)}`.  The first two die by the side-decomposition/irrationality argument of
    `Row5.twoPiThree_forces_le_three` (here `twoPiThree_forces_le_three'`: a verbatim copy with `N.Prime` weakened to `1 ≤ N`,
    the only use of primality in its proof being `hNp.pos`); the last two force the tile to be `λ(3,5,7)` in the side-`15λ`
    equilateral triangle.  UNAUDITED. -/

open scoped Classical

namespace Erdos634.Geometry.GapE120

theorem twoPiThree_forces_le_three' {N : ℕ} {a b c S : ℝ} (hN1 : 1 ≤ N)
    (hc2 : 2 * (N : ℝ) * c = S * ((N : ℝ) + 3))
    (hD : 2 * (N : ℝ) * (a - b) = S * ((N : ℝ) - 3)
      ∨ 2 * (N : ℝ) * (a - b) = S * (3 - (N : ℝ)))
    (hab2 : 4 * (N : ℝ) ^ 2 * (a + b) ^ 2 = S ^ 2 * ((N : ℝ) + 1) * ((N : ℝ) + 9))
    (hS0 : 0 < S) (haPos : 0 < a) (hbPos : 0 < b) (p q r : ℤ)
    (hp0 : 0 ≤ p) (hq0 : 0 ≤ q) (hside : S = p * a + q * b + r * c) : N ≤ 3 := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hSne : S ≠ 0 := ne_of_gt hS0
  -- irrationality of `X / S`, `X := 2N(a+b)`
  have hxirr : Irrational (2 * (N : ℝ) * (a + b) / S) := by
    have hnotsq : ¬ IsSquare ((N + 1) * (N + 9)) := not_isSquare_nat_Np1Np9 N hN1
    have hirr0 : Irrational (Real.sqrt (((N + 1) * (N + 9) : ℕ) : ℝ)) :=
      irrational_sqrt_natCast_iff.mpr hnotsq
    have hxsq : (2 * (N : ℝ) * (a + b) / S) ^ 2 = (((N + 1) * (N + 9) : ℕ) : ℝ) := by
      rw [div_pow, div_eq_iff (pow_ne_zero 2 hSne)]
      push_cast
      linear_combination hab2
    have hxnn : 0 ≤ 2 * (N : ℝ) * (a + b) / S := by positivity
    have hxeq : 2 * (N : ℝ) * (a + b) / S = Real.sqrt (((N + 1) * (N + 9) : ℕ) : ℝ) := by
      rw [← Real.sqrt_sq hxnn, hxsq]
    rwa [hxeq]
  -- Both signs of `hD` give `(p+q)•X = S•M` for an integer `M` (case 2 is case 1 with `p,q`
  -- swapped); either way this forces `p + q = 0`, hence (with `p, q ≥ 0`) `p = q = 0`.
  have hpq0 : p + q = 0 := by
    rcases hD with hD | hD
    · set M : ℤ := 4 * (N : ℤ) - (p - q) * ((N : ℤ) - 3) - 2 * r * ((N : ℤ) + 3) with hMdef
      have heqM : ((p : ℝ) + q) * (2 * (N : ℝ) * (a + b)) = S * (M : ℝ) := by
        have hMcast : (M : ℝ) = 4 * (N : ℝ) - ((p : ℝ) - q) * ((N : ℝ) - 3)
            - 2 * (r : ℝ) * ((N : ℝ) + 3) := by rw [hMdef]; push_cast; ring
        rw [hMcast]
        linear_combination (-4 * (N : ℝ)) * hside - ((p : ℝ) - q) * hD - 2 * (r : ℝ) * hc2
      by_contra hne
      have hnz : ((p : ℝ) + q) ≠ 0 := by exact_mod_cast hne
      apply hxirr
      refine ⟨(M : ℚ) / ((p : ℚ) + q), ?_⟩
      push_cast
      rw [div_eq_div_iff hnz hSne]
      linear_combination -heqM
    · set M : ℤ := 4 * (N : ℤ) - (q - p) * ((N : ℤ) - 3) - 2 * r * ((N : ℤ) + 3) with hMdef
      have heqM : ((p : ℝ) + q) * (2 * (N : ℝ) * (a + b)) = S * (M : ℝ) := by
        have hMcast : (M : ℝ) = 4 * (N : ℝ) - ((q : ℝ) - p) * ((N : ℝ) - 3)
            - 2 * (r : ℝ) * ((N : ℝ) + 3) := by rw [hMdef]; push_cast; ring
        rw [hMcast]
        linear_combination (-4 * (N : ℝ)) * hside + ((q : ℝ) - p) * hD - 2 * (r : ℝ) * hc2
      by_contra hne
      have hnz : ((p : ℝ) + q) ≠ 0 := by exact_mod_cast hne
      apply hxirr
      refine ⟨(M : ℚ) / ((p : ℚ) + q), ?_⟩
      push_cast
      rw [div_eq_div_iff hnz hSne]
      linear_combination -heqM
  have hp0' : p = 0 := by omega
  have hq0' : q = 0 := by omega
  subst hp0'; subst hq0'
  have hrS : S = r * c := by rw [hside]; push_cast; ring
  have hr0 : r ≠ 0 := by
    rintro h0; rw [h0] at hrS; simp at hrS; linarith
  have hcne : c ≠ 0 := by rintro h0; rw [h0, mul_zero] at hrS; exact hSne hrS
  -- substitute `S = r•c` into `hc2` and cancel `c` to get `2N = r(N+3)`.
  have hc2' : 2 * (N : ℝ) * c = ((r : ℝ) * c) * ((N : ℝ) + 3) := by rw [hrS] at hc2; exact hc2
  have hc2'' : (2 * (N : ℝ)) * c = ((r : ℝ) * ((N : ℝ) + 3)) * c := by linear_combination hc2'
  have hrform : 2 * (N : ℝ) = (r : ℝ) * ((N : ℝ) + 3) := mul_right_cancel₀ hcne hc2''
  have hrZ : 2 * (N : ℤ) = r * ((N : ℤ) + 3) := by exact_mod_cast hrform
  have hdvd : ((N : ℤ) + 3) ∣ 6 := ⟨2 - r, by linear_combination -hrZ⟩
  have hle : (N : ℤ) + 3 ≤ 6 := Int.le_of_dvd (by norm_num) hdvd
  omega


theorem closed_3N (N S a b c : ℝ) (e1 : 3 * (c + a - b) = 3 * S) (e2 : N * (c + b - a) = 3 * S)
    (harea : S ^ 2 = N * a * b) :
    2 * N * c = S * (N + 3) ∧ 2 * N * (a - b) = S * (N - 3) ∧
      4 * N ^ 2 * (a + b) ^ 2 = S ^ 2 * (N + 1) * (N + 9) := by
  have eq1 : c + a - b = S := by linarith
  have hc2 : 2 * N * c = S * (N + 3) := by linear_combination N * eq1 + e2
  have hD : 2 * N * (a - b) = S * (N - 3) := by linear_combination N * eq1 - e2
  have hD2 : 4 * N ^ 2 * (a - b) ^ 2 = S ^ 2 * (N - 3) ^ 2 := by
    rw [show (4 * N ^ 2 * (a - b) ^ 2) = (2 * N * (a - b)) ^ 2 by ring,
      show S ^ 2 * (N - 3) ^ 2 = (S * (N - 3)) ^ 2 by ring, hD]
  exact ⟨hc2, hD, by linear_combination hD2 - 16 * N * harea⟩

theorem closed_N3 (N S a b c : ℝ) (e1 : N * (c + a - b) = 3 * S) (e2 : 3 * (c + b - a) = 3 * S)
    (harea : S ^ 2 = N * a * b) :
    2 * N * c = S * (N + 3) ∧ 2 * N * (a - b) = S * (3 - N) ∧
      4 * N ^ 2 * (a + b) ^ 2 = S ^ 2 * (N + 1) * (N + 9) := by
  have eq2 : c + b - a = S := by linarith
  have hc2 : 2 * N * c = S * (N + 3) := by linear_combination e1 + N * eq2
  have hD : 2 * N * (a - b) = S * (3 - N) := by linear_combination e1 - N * eq2
  have hD2 : 4 * N ^ 2 * (a - b) ^ 2 = S ^ 2 * (N - 3) ^ 2 := by
    rw [show (4 * N ^ 2 * (a - b) ^ 2) = (2 * N * (a - b)) ^ 2 by ring,
      show S ^ 2 * (N - 3) ^ 2 = (S * (3 - N)) ^ 2 by ring, hD]
  exact ⟨hc2, hD, by linear_combination hD2 - 16 * N * harea⟩

/-- the `(5,9)` case: pure algebra. -/
theorem shape_59 (S a b c : ℝ) (hS : 0 < S) (ha : 0 < a) (hb : 0 < b)
    (e1 : 5 * (c + a - b) = 3 * S) (e2 : 9 * (c + b - a) = 3 * S) (harea : S ^ 2 = 15 * a * b) :
    c = 7 * (S / 15) ∧ a = 5 * (S / 15) ∧ b = 3 * (S / 15) := by
  have hc : c = 7 * S / 15 := by linarith
  have hd : a - b = 2 * S / 15 := by linarith
  have hsq : (a + b) ^ 2 = (8 * S / 15) ^ 2 := by nlinarith [hd, harea]
  have hab : a + b = 8 * S / 15 := by
    have h0 : 0 ≤ 8 * S / 15 := by positivity
    exact (pow_left_inj₀ (by positivity) h0 (by norm_num)).mp hsq
  refine ⟨by rw [hc]; ring, by linarith, by linarith⟩

/-- the `(9,5)` case: pure algebra. -/
theorem shape_95 (S a b c : ℝ) (hS : 0 < S) (ha : 0 < a) (hb : 0 < b)
    (e1 : 9 * (c + a - b) = 3 * S) (e2 : 5 * (c + b - a) = 3 * S) (harea : S ^ 2 = 15 * a * b) :
    c = 7 * (S / 15) ∧ a = 3 * (S / 15) ∧ b = 5 * (S / 15) := by
  have hc : c = 7 * S / 15 := by linarith
  have hd : a - b = -(2 * S / 15) := by linarith
  have hsq : (a + b) ^ 2 = (8 * S / 15) ^ 2 := by nlinarith [hd, harea]
  have hab : a + b = 8 * S / 15 := by
    have h0 : 0 ≤ 8 * S / 15 := by positivity
    exact (pow_left_inj₀ (by positivity) h0 (by norm_num)).mp hsq
  refine ⟨by rw [hc]; ring, by linarith, by linarith⟩

/-- **The shape of an `N = 15` equilateral dissection by a `2π/3` tile with `α ∉ ℚπ`**: the tile is `λ(3,5,7)` and the
target has side `15λ` (`λ = S/15`).  The `(3,15)`/`(15,3)` cases are refuted. -/
theorem e120_shape (D : CongruentDissection 15) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoPiThreeData α a b c)
    (hP : ∀ k, D.target.angleAt k = Real.pi / 3) :
    ∃ l : ℝ, 0 < l ∧ D.target.oppLen 0 = 15 * l ∧ c = 7 * l ∧
      ((a = 5 * l ∧ b = 3 * l) ∨ (a = 3 * l ∧ b = 5 * l)) := by
  obtain ⟨s, t, hs2, ht2, hs1, hsN, ht1, htN, hSeq1, hSeq2, harea, hst, -⟩ :=
    Row5.theoremE_twoPiThree D hα h hP
  set S := D.target.oppLen 0 with hSdef
  have hS0 : 0 < S := D.target.oppLen_pos 0
  obtain ⟨t1, t2, t3⟩ := h.tri_ineq
  have ha : 0 < a := by linarith
  have hb : 0 < b := by linarith
  have hst' : s * t = 45 := by push_cast at hst; omega
  have hcases : (s = 3 ∧ t = 15) ∨ (s = 15 ∧ t = 3) ∨ (s = 5 ∧ t = 9) ∨ (s = 9 ∧ t = 5) := by
    push_cast at hsN htN hs2 ht2
    have hs15 : s ≤ 15 := by exact_mod_cast hsN
    have ht15 : t ≤ 15 := by exact_mod_cast htN
    interval_cases s <;> omega
  have hh : ((15 : ℕ) : ℝ) = 15 := by norm_num
  have harea' : S ^ 2 = 15 * a * b := by have := harea; push_cast at this; linarith
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- (3,15): refuted by the side decomposition
    exfalso
    push_cast at hSeq1 hSeq2
    obtain ⟨hc2, hD, hab2⟩ := closed_3N 15 S a b c hSeq1 hSeq2 (by push_cast at harea; linarith)
    obtain ⟨p, q, r, hpqr⟩ := Row5TwoPiThreeFull.side_decomposition D h
    obtain ⟨-, e2, -⟩ := Row5.equilateral_boundary D hα 0 (fun k => D.model.data_angles_mem hα h 0 k) hP
    have hd : dist (D.target.pts 0) (D.target.pts 1) = D.target.oppLen 0 := by
      rw [← e2]; unfold Tri.oppLen; rfl
    rw [hd] at hpqr
    have := twoPiThree_forces_le_three' (N := 15) (a := a) (b := b) (c := c) (S := S) (by norm_num)
      (by push_cast; linarith) (Or.inl (by push_cast; linarith)) (by push_cast; linarith) hS0 ha hb
      (p : ℤ) (q : ℤ) (r : ℤ) (by positivity) (by positivity) (by rw [hSdef, hpqr]; push_cast; ring)
    omega
  · exfalso
    push_cast at hSeq1 hSeq2
    obtain ⟨hc2, hD, hab2⟩ := closed_N3 15 S a b c hSeq1 hSeq2 (by push_cast at harea; linarith)
    obtain ⟨p, q, r, hpqr⟩ := Row5TwoPiThreeFull.side_decomposition D h
    obtain ⟨-, e2, -⟩ := Row5.equilateral_boundary D hα 0 (fun k => D.model.data_angles_mem hα h 0 k) hP
    have hd : dist (D.target.pts 0) (D.target.pts 1) = D.target.oppLen 0 := by
      rw [← e2]; unfold Tri.oppLen; rfl
    rw [hd] at hpqr
    have := twoPiThree_forces_le_three' (N := 15) (a := a) (b := b) (c := c) (S := S) (by norm_num)
      (by push_cast; linarith) (Or.inr (by push_cast; linarith)) (by push_cast; linarith) hS0 ha hb
      (p : ℤ) (q : ℤ) (r : ℤ) (by positivity) (by positivity) (by rw [hSdef, hpqr]; push_cast; ring)
    omega
  · push_cast at hSeq1 hSeq2
    obtain ⟨hc, ha', hb'⟩ := shape_59 S a b c hS0 ha hb hSeq1 hSeq2 harea'
    exact ⟨S / 15, by positivity, by ring, hc, Or.inl ⟨ha', hb'⟩⟩
  · push_cast at hSeq1 hSeq2
    obtain ⟨hc, ha', hb'⟩ := shape_95 S a b c hS0 ha hb hSeq1 hSeq2 harea'
    exact ⟨S / 15, by positivity, by ring, hc, Or.inr ⟨ha', hb'⟩⟩

end Erdos634.Geometry.GapE120

#print axioms Erdos634.Geometry.GapE120.e120_shape

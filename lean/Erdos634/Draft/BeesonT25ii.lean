import Erdos634.Draft.BeesonL27T6
import Erdos634.EdgeWordConversion

/-!
# Beeson (arXiv 1206.2229v4) Theorem 25 (ii), the integer form of the isosceles-alpha tiling equation

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Thm 25 (ii)), Laczkovich (DCG 48 (2012)), Beeson-Zhang.
Formalization debt, not progress on the /goal outcomes.

Printed: `3 alpha + 2 beta = pi`, ABC isosceles with base angles `alpha`, `N`-tiled by the tile with integer sides
`(a, b, c) = (m k, k^2 - m^2, k^2)`, `k, m` coprime, `M` the coloring number.  Then `2k + m | M`, and with
`j = M / (2k + m)`: `N (k - m) = j^2 (m + k)(2 k^2 - m^2)`.
Proof as printed: the leg `X` of ABC is an integer (a side of the target is a sum of tile edges: `side_walk_congruent`,
all of whose lengths are among `a, b, c`), `X (2k + m) = M k^2 (k + m)` (from `M = Lambda s (2+s)/(1+s)`, `X = Lambda a`), and
`2k + m` is coprime to `k` and to `k + m` because `gcd(k, m) = 1` (no parity case is needed for the divisibility; the printed
text does not use one).  The equation then follows from `lemma27` (`N = Lambda^2 s^2 (2-s^2)/(1-s^2)`).
Here `g k m : ℕ`, the tile sides are the reals `a = g m k`, `b = g (k^2 - m^2)`, `c = g k^2`; `g = 1` is the printed case
("no common factor" is replaced by the explicit form, equivalent by `gcd(k^2, mk, k^2-m^2) = 1`).  The statement is proved for any
scale `g >= 1` (the same divisibility `2k + m | M` holds because the target side is `g` times an integer), which lets the
existing 84-tiling (tile `(16,24,32) = 8 (2,3,4)`) serve as a witness.
Project hypothesis (H1) `alpha notin Q*pi` (through `t4_M1`) replaces Beeson's Lemma 1.  Vertex order as in `thm1`.
-/

open scoped Classical

namespace Erdos634.BeesonColoring

open Erdos634.Geometry Erdos634.Geometry.A1Field

variable {N : ℕ}

/-- every side of the target is an integer when the model's three side lengths are integers (a side of the target is a
sum of tile edges, each of length one of `a, b, c`). -/
theorem target_side_int (D : CongruentDissection N) {α β a b c : ℝ}
    (h : D.model.ThreeAlphaData α β a b c) (g : ℝ) (za zb zc : ℤ)
    (ha : a = g * za) (hb : b = g * zb) (hc : c = g * zc) (i : Fin 3) :
    ∃ z : ℤ, dist (D.target.pts i) (D.target.pts (i + 1)) = g * z := by
  obtain ⟨P, Q, R, hPQR, -⟩ := Erdos634.EdgeWordConversion.side_walk_congruent D i
  have hint : ∀ i : Fin 3, ∃ z : ℤ, Erdos634.EdgeWordConversion.sideLen D i = g * z := by
    intro i
    obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
    have hmem : ∀ k : Fin 3, ∃ z : ℤ, D.model.oppLen k = g * z := by
      intro k
      obtain ⟨i, hi⟩ : ∃ i, i = σ.symm k := ⟨_, rfl⟩
      have hk : k = σ i := by rw [hi]; simp
      rw [hk]
      fin_cases i
      · exact ⟨za, by simpa [o0] using ha⟩
      · exact ⟨zb, by simpa [o1] using hb⟩
      · exact ⟨zc, by simpa [o2] using hc⟩
    have : Erdos634.EdgeWordConversion.sideLen D i = D.model.oppLen (i + 2) := by
      fin_cases i <;> rfl
    rw [this]; exact hmem _
  obtain ⟨z0, e0⟩ := hint 0
  obtain ⟨z1, e1⟩ := hint 1
  obtain ⟨z2, e2⟩ := hint 2
  refine ⟨P * z0 + Q * z1 + R * z2, ?_⟩
  rw [← hPQR, e0, e1, e2]; push_cast; ring

set_option maxHeartbeats 1000000 in
theorem t25_ii (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (e0 : D.target.angleAt 0 = α) (e1 : D.target.angleAt 1 = α)
    (e2 : D.target.angleAt 2 = α + 2 * β)
    (g k m : ℕ) (hg : 0 < g) (hcop : Nat.Coprime k m)
    (ha : a = (g : ℝ) * ((m : ℝ) * k)) (hb : b = (g : ℝ) * ((k : ℝ) ^ 2 - (m : ℝ) ^ 2))
    (hc : c = (g : ℝ) * (k : ℝ) ^ 2) :
    ∃ M j : ℤ, 0 < M ∧ M = ((2 * k + m : ℕ) : ℤ) * j ∧
      (N : ℤ) * ((k : ℤ) - m) = j ^ 2 * ((m : ℤ) + k) * (2 * (k : ℤ) ^ 2 - (m : ℤ) ^ 2) := by
  obtain ⟨hΛ, hs0, hs1⟩ := t4_aux D hrel h
  obtain ⟨-, -, -, -, -⟩ := lemma27 D hrel h
  have L4 := (lemma27 D hrel h).2.2.2.1 ⟨e0, e1, e2⟩
  obtain ⟨M, hMp, hM⟩ := (t4_M1 D hα hrel h).1 ⟨e0, e1, e2⟩
  -- k, m positive
  obtain ⟨ha0, hb0, hc0, hαpos, hβpos⟩ := model_abc_pos h
  have hk0 : (0 : ℝ) < k := by
    by_contra hh
    have : (k : ℝ) = 0 := le_antisymm (not_lt.mp hh) (Nat.cast_nonneg k)
    rw [hc, this] at hc0; norm_num at hc0
  have hm0 : (0 : ℝ) < m := by
    by_contra hh
    have : (m : ℝ) = 0 := le_antisymm (not_lt.mp hh) (Nat.cast_nonneg m)
    rw [ha, this] at ha0; norm_num at ha0
  have hg0 : (0 : ℝ) < g := by exact_mod_cast hg
  have hsmk : a / c = (m : ℝ) / k := by rw [ha, hc]; field_simp
  -- X is an integer and equals Lambda * a
  have hXint : ∃ z : ℤ, D.target.oppLen 0 = g * z := by
    obtain ⟨z, hz⟩ := target_side_int D h g (m * k) (k ^ 2 - m ^ 2) (k ^ 2)
      (by rw [ha]; push_cast; ring) (by rw [hb]; push_cast; ring) (by rw [hc]; push_cast; ring) 1
    exact ⟨z, hz⟩
  obtain ⟨n, hn⟩ := hXint
  have hXΛ : D.target.oppLen 0 = (circD D.target / circD D.model) * a := by
    obtain ⟨σ, h0, o0, h1', o1, h2', o2⟩ := h
    have ea : a = circD D.model * Real.sin α := by rw [← o0, oppLen_eq, h0]
    have hD : 0 < circD D.model := circD_pos _
    rw [oppLen_eq, e0, ea]; field_simp
  set Λ := circD D.target / circD D.model with hΛd
  rw [hsmk] at hM L4
  have hkm : (0 : ℝ) < (k : ℝ) + m := by positivity
  have h2km : (0 : ℝ) < 2 * k + m := by positivity
  have hs1' : (m : ℝ) / k < 1 := by rw [← hsmk]; exact hs1
  have hmk : (m : ℝ) < k := by
    have := hs1; rw [hsmk, div_lt_one hk0] at this; exact this
  -- M * k * (k+m) = Lambda * m * (2k+m)
  have hMΛ : (M : ℝ) * (k * (k + m)) = Λ * (m * (2 * k + m)) := by
    rw [hM]; field_simp
  have hX2 : (n : ℝ) * (2 * k + m) = M * (k ^ 2 * (k + m)) := by
    have e : (g : ℝ) * ((n : ℝ) * (2 * k + m)) = (g : ℝ) * (M * (k ^ 2 * (k + m))) := by
      have e1 : (g : ℝ) * n = Λ * ((g : ℝ) * ((m : ℝ) * k)) := by rw [← hn, hXΛ, ha]
      have : (M : ℝ) * (k * (k + m)) * k = Λ * (m * (2 * k + m)) * k := by rw [hMΛ]
      linear_combination (2 * (k : ℝ) + m) * e1 + (-(g : ℝ)) * this
    exact mul_left_cancel₀ hg0.ne' e
  have hX2z : n * (2 * (k : ℤ) + m) = M * ((k : ℤ) ^ 2 * (k + m)) := by exact_mod_cast hX2
  -- coprimality
  have hc1 : IsCoprime (k : ℤ) (m : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  obtain ⟨u, v, hu⟩ := hc1
  have c1 : IsCoprime (2 * (k : ℤ) + m) (k : ℤ) := ⟨v, u - 2 * v, by linear_combination hu⟩
  have c2 : IsCoprime (2 * (k : ℤ) + m) ((k : ℤ) + m) :=
    ⟨u - v, 2 * v - u, by linear_combination hu⟩
  have hc2 : IsCoprime ((2 * k + m : ℕ) : ℤ) ((k : ℤ) ^ 2 * (k + m)) := by
    push_cast
    exact (c1.pow_right (n := 2)).mul_right c2
  have hdvd : ((2 * k + m : ℕ) : ℤ) ∣ M := by
    have : ((2 * k + m : ℕ) : ℤ) ∣ M * ((k : ℤ) ^ 2 * (k + m)) :=
      ⟨n, by rw [← hX2z]; push_cast; ring⟩
    exact hc2.dvd_of_dvd_mul_right this
  obtain ⟨j, hj⟩ := hdvd
  refine ⟨M, j, hMp, hj, ?_⟩
  -- the tiling equation, real form
  have hNr : (N : ℝ) * ((k - m) * (2 * k + m) ^ 2) = (M : ℝ) ^ 2 * ((m + k) * (2 * k ^ 2 - m ^ 2)) := by
    have hΛe : Λ = (M : ℝ) * (k * (k + m)) / (m * (2 * k + m)) := by
      rw [eq_div_iff (by positivity)]; linarith
    rw [L4, hΛe]
    have n1 : (k : ℝ) - m ≠ 0 := by linarith
    have n2 : (k : ℝ) + m ≠ 0 := hkm.ne'
    have n3 : (1 - ((m : ℝ) / k) ^ 2) ≠ 0 := by
      have : ((m : ℝ) / k) < 1 := hs1' 
      have h0 : 0 < (m : ℝ) / k := by positivity
      nlinarith
    have n7 : (k : ℝ) ^ 2 - (m : ℝ) ^ 2 ≠ 0 := (by nlinarith : (0:ℝ) < (k : ℝ) ^ 2 - (m : ℝ) ^ 2).ne'
    have n4 : (k : ℝ) ≠ 0 := hk0.ne'
    have n5 : (m : ℝ) ≠ 0 := hm0.ne'
    have n6 : (2 * k + m : ℝ) ≠ 0 := h2km.ne'
    field_simp
    ring
  have hNz : (N : ℤ) * (((k : ℤ) - m) * (2 * (k : ℤ) + m) ^ 2)
      = M ^ 2 * (((m : ℤ) + k) * (2 * (k : ℤ) ^ 2 - (m : ℤ) ^ 2)) := by exact_mod_cast hNr
  rw [hj] at hNz
  push_cast at hNz
  have hkn : 0 < k := by exact_mod_cast hk0
  have hkz : (0 : ℤ) < 2 * (k : ℤ) + m := by
    have := Int.natCast_pos.mpr hkn
    have : (0 : ℤ) ≤ m := Int.natCast_nonneg m
    linarith
  have hpos : (0 : ℤ) < (2 * (k : ℤ) + m) ^ 2 := pow_pos hkz 2
  refine mul_right_cancel₀ hpos.ne' ?_
  linear_combination hNz

end Erdos634.BeesonColoring

#print axioms Erdos634.BeesonColoring.target_side_int
#print axioms Erdos634.BeesonColoring.t25_ii

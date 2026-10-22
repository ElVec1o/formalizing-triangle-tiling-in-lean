import Erdos634.Draft.LaczFormal9b

/-!
# Laczkovich, Discrete Math. 140 (1995), Theorem 3.3 and Theorem 3.4

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) Thm 3.1, Lemma 2.1, Lemma 3.2, Thm 3.3, Thm 3.4), Beeson,
Beeson-Zhang, Zhang.  Formalization debt, not progress on the /goal outcomes.

* `dm140_thm33` (printed Thm 3.3): `x, y` non-zero integers, `x + 2y != 0 != y + 2x`: there are `k > 0` and a real
  `CongruentDissection` of an equilateral triangle into `N = |x y (x+2y)(y+2x)| k^2` congruent triangles whose model has
  sides `s (|x(x+2y)|, |y(y+2x)|, x^2+xy+y^2)` in some order (i.e. similar to the triangle `Delta` of Lemma 3.2).
* `dm140_thm34` (printed Thm 3.4): every finite set of primes `P` there is `n`, a tile count of an equilateral triangle,
  such that every `p in P` has an odd exponent in `n`.  (As printed: `x = 4q`, `y = 1`, `q` = product of the odd elements of `P`;
  the prime 2 is covered because `4q` contributes `2^2`; see the note on `2` below.)
-/

open scoped Classical
open EuclideanGeometry Erdos634.Geometry Erdos634.RegionDissection Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional
  Erdos634.Draft.LaczFormal Erdos634.LaczL35 Erdos634.LaczL22 Erdos634.CertCoord Erdos634.LaczThm33If
  Erdos634.Realizable Erdos634.DissectionMap

namespace Erdos634.Laczkovich9

theorem heron_rel (A B C ε : ℝ) (hε : ε = 1 ∨ ε = -1) (h : C ^ 2 = A ^ 2 + B ^ 2 - ε * A * B) :
    (A ^ 2 + B ^ 2 + C ^ 2) ^ 2 - 2 * (A ^ 4 + B ^ 4 + C ^ 4) = 3 * (A * B) ^ 2 := by
  rcases hε with rfl | rfl
  · linear_combination (2 * (A ^ 2 + B ^ 2) - C ^ 2 - (A ^ 2 + B ^ 2 - 1 * A * B)) * h
  · linear_combination (2 * (A ^ 2 + B ^ 2) - C ^ 2 - (A ^ 2 + B ^ 2 - (-1) * A * B)) * h

/-- **Laczkovich DM 140 (1995), Theorem 3.3.** -/
theorem dm140_thm33 (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) (h1 : x + 2 * y ≠ 0) (h2 : y + 2 * x ≠ 0) :
    ∃ (k N : ℕ), 0 < k ∧ N = (x * y * (x + 2 * y) * (y + 2 * x)).natAbs * k ^ 2 ∧
      ∃ D : CongruentDissection N, Equilateral D ∧ ∃ s : ℝ, 0 < s ∧ ∃ σ : Equiv.Perm (Fin 3),
        D.model.oppLen (σ 0) = s * ((x * (x + 2 * y)).natAbs : ℝ) ∧
        D.model.oppLen (σ 1) = s * ((y * (y + 2 * x)).natAbs : ℝ) ∧
        D.model.oppLen (σ 2) = s * ((x ^ 2 + x * y + y ^ 2).natAbs : ℝ) := by
  set P : ℤ := x * (x + 2 * y) with hP
  set Q : ℤ := y * (y + 2 * x) with hQ
  set cI : ℤ := x ^ 2 + x * y + y ^ 2 with hcI
  have hP0 : P ≠ 0 := mul_ne_zero hx h1
  have hQ0 : Q ≠ 0 := mul_ne_zero hy h2
  have hcpos : 0 < cI := by
    rcases eq_or_ne x 0 with h | h
    · exact absurd h hx
    · rw [hcI]; nlinarith [sq_nonneg (x + 2 * y), sq_pos_of_ne_zero h, sq_pos_of_ne_zero hy]
  set A : ℕ := P.natAbs with hAdef
  set B : ℕ := Q.natAbs with hBdef
  set C : ℕ := cI.natAbs with hCdef
  have hA : 0 < A := Int.natAbs_pos.mpr hP0
  have hB : 0 < B := Int.natAbs_pos.mpr hQ0
  have hC : 0 < C := Int.natAbs_pos.mpr hcpos.ne'
  have hid : cI ^ 2 = P ^ 2 + Q ^ 2 - P * Q := by rw [hcI, hP, hQ]; ring
  have hAsq : (A : ℤ) ^ 2 = P ^ 2 := by rw [hAdef]; exact Int.natAbs_sq P
  have hBsq : (B : ℤ) ^ 2 = Q ^ 2 := by rw [hBdef]; exact Int.natAbs_sq Q
  have hCsq : (C : ℤ) ^ 2 = cI ^ 2 := by rw [hCdef]; exact Int.natAbs_sq cI
  have hAB : (A : ℤ) * B = |P * Q| := by
    rw [abs_mul, hAdef, hBdef, Int.natCast_natAbs, Int.natCast_natAbs]
  have hNabs : (x * y * (x + 2 * y) * (y + 2 * x)).natAbs = A * B := by
    have : x * y * (x + 2 * y) * (y + 2 * x) = P * Q := by rw [hP, hQ]; ring
    rw [this, Int.natAbs_mul]
  -- the dilation and the final assembly, common to both signs
  have final : ∀ (q M : ℕ) (hq : 0 < q) (D : CongruentDissection M), Equilateral D →
      (∃ n : ℕ, 0 < n ∧ M * (A * B) = n ^ 2) →
      ∀ (σ : Equiv.Perm (Fin 3)),
        D.model.oppLen (σ 0) = (1 / (q : ℝ)) * (A : ℝ) → D.model.oppLen (σ 1) = (1 / (q : ℝ)) * (B : ℝ) →
        D.model.oppLen (σ 2) = (1 / (q : ℝ)) * (C : ℝ) →
        ∃ (k N : ℕ), 0 < k ∧ N = (x * y * (x + 2 * y) * (y + 2 * x)).natAbs * k ^ 2 ∧
          ∃ D : CongruentDissection N, Equilateral D ∧ ∃ s : ℝ, 0 < s ∧ ∃ σ : Equiv.Perm (Fin 3),
            D.model.oppLen (σ 0) = s * ((x * (x + 2 * y)).natAbs : ℝ) ∧
            D.model.oppLen (σ 1) = s * ((y * (y + 2 * x)).natAbs : ℝ) ∧
            D.model.oppLen (σ 2) = s * ((x ^ 2 + x * y + y ^ 2).natAbs : ℝ) := by
    intro q M hq D hEq ⟨n, hn, hMn⟩ σ e0 e1 e2
    obtain ⟨D', hEq', hmod⟩ := dilate_equi D hEq (A * B) (Nat.mul_pos hA hB)
    refine ⟨n, A * B * (A * B) * M, hn, ?_, D', hEq', 1 / (q : ℝ), by positivity, σ, ?_, ?_, ?_⟩
    · rw [hNabs]
      calc A * B * (A * B) * M = (A * B) * (M * (A * B)) := by ring
        _ = A * B * n ^ 2 := by rw [hMn]
    · rw [hmod]; exact e0
    · rw [hmod]; exact e1
    · rw [hmod]; exact e2
  have hAR : (0 : ℝ) < A := Nat.cast_pos.mpr hA
  have hBR : (0 : ℝ) < B := Nat.cast_pos.mpr hB
  have hCR : (0 : ℝ) < C := Nat.cast_pos.mpr hC
  rcases lt_or_gt_of_ne (mul_ne_zero hP0 hQ0) with hneg | hpos
  · -- P Q < 0 : C^2 = A^2 + B^2 + A B, gamma = 2 pi / 3
    have hABneg : (A : ℤ) * B = -(P * Q) := by rw [hAB, abs_of_neg hneg]
    have hZ : (C : ℤ) ^ 2 = (A : ℤ) ^ 2 + (B : ℤ) ^ 2 - (-1) * (A : ℤ) * B := by
      rw [hCsq, hAsq, hBsq, hid]; linear_combination (-1 : ℤ) * hABneg
    have hQr : ((C : ℚ)) ^ 2 = (A : ℚ) ^ 2 + (B : ℚ) ^ 2 - (-1) * (A : ℚ) * B := by exact_mod_cast hZ
    have hRr : ((C : ℝ)) ^ 2 = (A : ℝ) ^ 2 + (B : ℝ) ^ 2 - (-1) * (A : ℝ) * B := by exact_mod_cast hZ
    obtain ⟨i1, i2, i3⟩ := tri_ineq (A : ℚ) B C (-1) (by exact_mod_cast hA) (by exact_mod_cast hB)
      (by exact_mod_cast hC) (Or.inr rfl) hQr
    obtain ⟨R, ra, rb, rc⟩ := exists_RTri_rat (A : ℚ) B C (by exact_mod_cast hA) (by exact_mod_cast hB)
      (by exact_mod_cast hC) i1 i2 i3
    have hq : R.a ^ 2 + R.a * R.b + R.b ^ 2 = R.c ^ 2 := by rw [ra, rb, rc]; linear_combination -hQr
    obtain ⟨T, h, -, a0, a1, a2⟩ := Erdos634.LaczL33.equi_all R hq
    obtain ⟨q, hq0, M, D, hEq, hm⟩ := equi_model R T h a0 a1 a2
    have o0 : R.Δ.oppLen 0 = (A : ℝ) := by
      have : R.Δ.oppLen 0 = R.a := R.ha
      rw [this, ra]; norm_cast
    have o1 : R.Δ.oppLen 1 = (B : ℝ) := by
      have : R.Δ.oppLen 1 = R.b := R.hb
      rw [this, rb]; norm_cast
    have o2 : R.Δ.oppLen 2 = (C : ℝ) := by
      have : R.Δ.oppLen 2 = R.c := R.hc
      rw [this, rc]; norm_cast
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq0.ne'
    have h0 : D.model.oppLen 0 = (A : ℝ) / q := by rw [hm 0, o0]; ring
    have h1 : D.model.oppLen 1 = (B : ℝ) / q := by rw [hm 1, o1]; ring
    have h2 : D.model.oppLen 2 = (C : ℝ) / q := by rw [hm 2, o2]; ring
    have hH := heron_rel (A : ℝ) B C (-1) (Or.inr rfl) hRr
    have hn := equi_n_formula D hEq q hq0 A B C A B hA hB h0 h1 h2 (by exact_mod_cast hH)
    exact final q M hq0 D hEq hn (Equiv.refl _) (by show D.model.oppLen 0 = _; rw [h0]; ring)
      (by show D.model.oppLen 1 = _; rw [h1]; ring) (by show D.model.oppLen 2 = _; rw [h2]; ring)
  · -- P Q > 0 : C^2 = A^2 + B^2 - A B, gamma = pi / 3; the tile is entered as (A, C, B) so that pi/3 sits at vertex 1
    have hABpos : (A : ℤ) * B = P * Q := by rw [hAB, abs_of_pos hpos]
    have hZ : (C : ℤ) ^ 2 = (A : ℤ) ^ 2 + (B : ℤ) ^ 2 - 1 * (A : ℤ) * B := by
      rw [hCsq, hAsq, hBsq, hid]; linear_combination hABpos
    have hQr : ((C : ℚ)) ^ 2 = (A : ℚ) ^ 2 + (B : ℚ) ^ 2 - 1 * (A : ℚ) * B := by exact_mod_cast hZ
    have hRr : ((C : ℝ)) ^ 2 = (A : ℝ) ^ 2 + (B : ℝ) ^ 2 - 1 * (A : ℝ) * B := by exact_mod_cast hZ
    obtain ⟨i1, i2, i3⟩ := tri_ineq (A : ℚ) B C 1 (by exact_mod_cast hA) (by exact_mod_cast hB)
      (by exact_mod_cast hC) (Or.inl rfl) hQr
    obtain ⟨R, ra, rb, rc⟩ := exists_RTri_rat (A : ℚ) C B (by exact_mod_cast hA) (by exact_mod_cast hC)
      (by exact_mod_cast hB) (by linarith) (by linarith) (by linarith)
    have hβ : vang R.Δ 1 = Real.pi / 3 := by
      have hc1 := RTri.cos_vang1 R
      have hA' : ((R.a : ℚ) : ℝ) = A := by rw [ra]; norm_cast
      have hB' : ((R.b : ℚ) : ℝ) = C := by rw [rb]; norm_cast
      have hC' : ((R.c : ℚ) : ℝ) = B := by rw [rc]; norm_cast
      rw [hA', hB', hC'] at hc1
      have hpi := Real.pi_pos
      refine angle_eq_of_cos (angle_nonneg _ _ _) (angle_le_pi _ _ _) (by positivity) (by linarith) ?_
      rw [hc1, Real.cos_pi_div_three]
      field_simp
      linear_combination (-1 : ℝ) * hRr
    obtain ⟨T, h, a0, a1, a2⟩ := equi_pi3 R hβ
    obtain ⟨q, hq0, M, D, hEq, hm⟩ := equi_model R T h a0 a1 a2
    have o0 : R.Δ.oppLen 0 = (A : ℝ) := by
      have : R.Δ.oppLen 0 = R.a := R.ha
      rw [this, ra]; norm_cast
    have o1 : R.Δ.oppLen 1 = (C : ℝ) := by
      have : R.Δ.oppLen 1 = R.b := R.hb
      rw [this, rb]; norm_cast
    have o2 : R.Δ.oppLen 2 = (B : ℝ) := by
      have : R.Δ.oppLen 2 = R.c := R.hc
      rw [this, rc]; norm_cast
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq0.ne'
    have h0 : D.model.oppLen 0 = (A : ℝ) / q := by rw [hm 0, o0]; ring
    have h1 : D.model.oppLen 1 = (C : ℝ) / q := by rw [hm 1, o1]; ring
    have h2 : D.model.oppLen 2 = (B : ℝ) / q := by rw [hm 2, o2]; ring
    have hH := heron_rel (A : ℝ) B C 1 (Or.inl rfl) hRr
    have hn := equi_n_formula D hEq q hq0 A C B A B hA hB h0 h1 h2
      (by linear_combination hH)
    have w0 : (Equiv.swap (1 : Fin 3) 2) 0 = 0 := by decide
    have w1 : (Equiv.swap (1 : Fin 3) 2) 1 = 2 := by decide
    have w2 : (Equiv.swap (1 : Fin 3) 2) 2 = 1 := by decide
    exact final q M hq0 D hEq hn (Equiv.swap 1 2) (by rw [w0, h0]; ring) (by rw [w1, h2]; ring) (by rw [w2, h1]; ring)

end Erdos634.Laczkovich9

#print axioms Erdos634.Laczkovich9.heron_rel
#print axioms Erdos634.Laczkovich9.dm140_thm33

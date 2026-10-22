-- Draft/KConjField.lean — CASE A, node A3 (Lemma K, K2 half): the Galois embedding σ = σ_m of
-- K = ℚ(ζ_{4n}) used to conjugate a dissection (PROOF_row0c.md §3.3 "Setup").
--
--   * `exists_m`: every unit k mod n has a lift m ≡ ±k (mod n), m ≡ 1 (mod 4), gcd(m, 4n) = 1
--     (the sign is harmless: K2(k) depends on k only up to ±, see Draft/KConjLemmaK.lean);
--   * σ(ζ) = ζ^m (`LemmaK1.exists_sigma`), hence σ(i) = i;
--   * K is closed under complex conjugation and σ ∘ conj = conj ∘ σ on K (`sigma_conj`), so σ maps
--     real elements of K to reals;
--   * σ(e^{ijπ/n}) = e^{ijmπ/n}.
-- With σ(i) = i the paper's Φ(x + iy) = σ(x) + iσ(y) is σ itself on complex coordinates.
-- Formalization debt on a paper-level PROVED node; NOT /goal progress.  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
-- H59: no parameter pair (e, f) is evaluated here.
import Erdos634.Draft.CaseALemmaK1
import Erdos634.Draft.A1FieldClause

open Complex

namespace Erdos634.KConj

open Erdos634.Geometry Erdos634.Geometry.CaseA.LemmaV Erdos634.Geometry.CaseA.LemmaK1
open Erdos634.Geometry.A1Field

variable {n : ℕ}

/-! ## The lift m -/

theorem coprime_of (m n : ℕ) (hm : m % 2 = 1) (hmn : m.Coprime n) : m.Coprime (4 * n) := by
  have h2 : m.Coprime 2 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]; omega
  have h4 : m.Coprime 4 := by simpa using Nat.Coprime.pow_right 2 h2
  exact Nat.Coprime.mul_right h4 hmn

theorem exists_m (hn : 0 < n) {k : ℤ} (hk : Int.gcd k n = 1) :
    ∃ m : ℕ, m.Coprime (4 * n) ∧ m % 4 = 1 ∧ ((n : ℤ) ∣ (m : ℤ) - k ∨ (n : ℤ) ∣ (m : ℤ) + k) := by
  obtain ⟨k', hc, hd⟩ := exists_lift hn hk
  have hc4 : k'.Coprime 4 := Nat.Coprime.coprime_mul_right_right hc
  have hcn : k'.Coprime n := Nat.Coprime.coprime_mul_left_right hc
  have hodd : k' % 2 = 1 := by
    by_contra h
    have : 2 ∣ Nat.gcd k' 4 := Nat.dvd_gcd (by omega) (by norm_num)
    rw [hc4] at this; norm_num at this
  by_cases h1 : k' % 4 = 1
  · exact ⟨k', hc, h1, Or.inl hd⟩
  · have h3 : k' % 4 = 3 := by omega
    by_cases hn2 : n % 2 = 1
    · refine ⟨k' + 2 * n, coprime_of _ _ (by omega)
        ((Nat.coprime_add_mul_right_left k' n 2).mpr hcn), by omega, Or.inl ?_⟩
      obtain ⟨t, ht⟩ := hd
      exact ⟨t + 2, by push_cast; linarith⟩
    · by_cases hn4 : n % 4 = 2
      · refine ⟨k' + 1 * n, coprime_of _ _ (by omega)
          ((Nat.coprime_add_mul_right_left k' n 1).mpr hcn), by omega, Or.inl ?_⟩
        obtain ⟨t, ht⟩ := hd
        exact ⟨t + 1, by push_cast; linarith⟩
      · have h4n : (4 : ℤ) ∣ n := by
          have : 4 ∣ n := by omega
          exact_mod_cast this
        obtain ⟨k'', hc', hd'⟩ := exists_lift hn (LemmaKStar.gcd_neg' hk)
        have hsum : (n : ℤ) ∣ (k'' : ℤ) + k' := by
          have := dvd_add hd' hd
          convert this using 1; ring
        have h4 : (4 : ℤ) ∣ (k'' : ℤ) + k' := dvd_trans h4n hsum
        refine ⟨k'', hc', by omega, Or.inr ?_⟩
        convert hd' using 1; ring

/-! ## σ, i, and conjugation -/

theorem zeta_mem' : zeta n ∈ Kf n := IntermediateField.mem_adjoin_simple_self ℚ _

theorem conj_zeta : (starRingEnd ℂ) (zeta n) = (zeta n)⁻¹ := by
  rw [zeta, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp [map_div₀, Complex.conj_ofReal, map_ofNat]
  ring

/-- Complex conjugation as a `ℚ`-algebra map. -/
noncomputable def cQ : ℂ →ₐ[ℚ] ℂ := (Complex.conjAe.toAlgHom).restrictScalars ℚ

theorem cQ_apply (z : ℂ) : cQ z = (starRingEnd ℂ) z := rfl

theorem conj_mem {x : ℂ} (hx : x ∈ Kf n) : (starRingEnd ℂ) x ∈ Kf n := by
  have hmap : (Kf n).map cQ ≤ Kf n := by
    rw [IntermediateField.adjoin_map, Set.image_singleton, IntermediateField.adjoin_simple_le_iff,
      cQ_apply, conj_zeta]
    exact inv_mem zeta_mem'
  exact hmap ⟨x, hx, rfl⟩

/-- Conjugation on `K`. -/
noncomputable def conjK (n : ℕ) : Kf n →ₐ[ℚ] Kf n where
  toFun x := ⟨(starRingEnd ℂ) (x : ℂ), conj_mem x.2⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
  map_zero' := by ext; simp
  map_add' x y := by ext; simp
  commutes' q := by ext; simp

theorem coe_conjK (x : Kf n) : ((conjK n x : Kf n) : ℂ) = (starRingEnd ℂ) (x : ℂ) := rfl

theorem I_mem (hn : 0 < n) : I ∈ Kf n := by rw [← zeta_pow_n hn]; exact pow_mem zeta_mem' n

theorem exp_eq_zeta (hn : 0 < n) (j : ℤ) :
    Complex.exp (((j : ℝ) * Real.pi / n : ℝ) * I) = zeta n ^ (2 * j) := by
  rw [zeta, ← Complex.exp_int_mul]
  congr 1
  have : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  push_cast; field_simp; ring

section Sigma

variable {m : ℕ} (σ : Kf n →ₐ[ℚ] ℂ)
  (hσ : σ (IntermediateField.AdjoinSimple.gen ℚ (zeta n)) = zeta n ^ m)
include hσ

/-- **σ commutes with complex conjugation on K.** -/
theorem sigma_conj (x : Kf n) : σ (conjK n x) = (starRingEnd ℂ) (σ x) := by
  have h : σ.comp (conjK n) = cQ.comp σ := by
    apply IntermediateField.adjoin_algHom_ext ℚ
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    have e1 : conjK n ⟨zeta n, zeta_mem'⟩ = (IntermediateField.AdjoinSimple.gen ℚ (zeta n))⁻¹ := by
      ext; rw [coe_conjK]
      show (starRingEnd ℂ) (zeta n) = _
      rw [conj_zeta, IntermediateField.coe_inv, IntermediateField.AdjoinSimple.coe_gen]
    have e2 : (⟨zeta n, zeta_mem'⟩ : Kf n) = IntermediateField.AdjoinSimple.gen ℚ (zeta n) := rfl
    show σ (conjK n ⟨zeta n, zeta_mem'⟩) = cQ (σ ⟨zeta n, zeta_mem'⟩)
    rw [e1, map_inv₀, e2, hσ, cQ_apply, map_pow, conj_zeta, inv_pow]
  exact congrArg (fun φ : Kf n →ₐ[ℚ] ℂ => φ x) h

/-- σ maps real elements of K to reals. -/
theorem sigma_real (x : Kf n) (hx : (starRingEnd ℂ) (x : ℂ) = x) :
    (starRingEnd ℂ) (σ x) = σ x := by
  rw [← sigma_conj σ hσ]
  congr 1
  ext; rw [coe_conjK, hx]


/-- **σ(i) = i** when m ≡ 1 (mod 4). -/
theorem sigma_I (hn : 0 < n) (hm4 : m % 4 = 1) : σ ⟨I, I_mem hn⟩ = I := by
  have e : (⟨I, I_mem hn⟩ : Kf n) = (IntermediateField.AdjoinSimple.gen ℚ (zeta n)) ^ n := by
    ext; simp [zeta_pow_n hn]
  rw [e, map_pow, hσ, ← pow_mul, mul_comm, pow_mul, zeta_pow_n hn]
  obtain ⟨q, hq⟩ : ∃ q, m = 4 * q + 1 := ⟨m / 4, by omega⟩
  rw [hq, pow_succ, pow_mul, Complex.I_pow_four, one_pow, one_mul]

/-- **σ(e^{ijπ/n}) = e^{ijmπ/n}.** -/
theorem sigma_exp (hn : 0 < n) (j : ℤ) :
    σ ⟨Complex.exp (((j : ℝ) * Real.pi / n : ℝ) * I), exp_int_mem hn j⟩
      = Complex.exp ((((j * m : ℤ) : ℝ) * Real.pi / n : ℝ) * I) := by
  have e : (⟨Complex.exp (((j : ℝ) * Real.pi / n : ℝ) * I), exp_int_mem hn j⟩ : Kf n)
      = (IntermediateField.AdjoinSimple.gen ℚ (zeta n)) ^ (2 * j) := by
    ext
    show Complex.exp (((j : ℝ) * Real.pi / n : ℝ) * I) = _
    rw [exp_eq_zeta hn]
    exact (map_zpow₀ ((Kf n).val) (IntermediateField.AdjoinSimple.gen ℚ (zeta n)) (2 * j)).symm
  rw [e, map_zpow₀, hσ, exp_eq_zeta hn, ← zpow_natCast, ← zpow_mul]
  congr 1; ring

end Sigma

end Erdos634.KConj

#print axioms Erdos634.KConj.exists_m
#print axioms Erdos634.KConj.sigma_conj
#print axioms Erdos634.KConj.sigma_I
#print axioms Erdos634.KConj.sigma_exp

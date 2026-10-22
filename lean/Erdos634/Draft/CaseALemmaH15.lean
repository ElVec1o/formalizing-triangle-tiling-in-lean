-- Draft/CaseALemmaH15.lean — Lemma H ported to N = 15 (not prime): 2X² ≠ 15 for every rational
-- angle.  Every step of `lemmaH` that used primality of p is replaced by an elementary fact at 15
-- (parity; x² ≠ 5; y² ≠ 10; m² ≠ 15, 30).  Formalization debt; NOT /goal progress.
import Erdos634.Draft.CaseALemmaHExc2

namespace Erdos634.Geometry.CaseA.LemmaH

open Real

/-- The N = 15 core at θ. -/
def HCore15 (θ : ℝ) : Prop :=
  ∀ r x y : ℕ, 2 * ((r : ℝ) + x * Real.sin θ + y * Real.cos θ) ^ 2 ≠ 15

theorem sq_ne_k (t k : ℕ) (hk : k < 49) (h : ∀ s < 7, s ^ 2 ≠ k) : t ^ 2 ≠ k := by
  intro ht
  have : t < 7 := by nlinarith
  exact h t this ht

theorem sq_ne_15 (t : ℕ) : t ^ 2 ≠ 15 := sq_ne_k t 15 (by norm_num) (by decide)
theorem sq_ne_30 (t : ℕ) : t ^ 2 ≠ 30 := sq_ne_k t 30 (by norm_num) (by decide)
theorem sq_ne_10 (t : ℕ) : t ^ 2 ≠ 10 := sq_ne_k t 10 (by norm_num) (by decide)
theorem sq_ne_5 (t : ℕ) : t ^ 2 ≠ 5 := sq_ne_k t 5 (by norm_num) (by decide)

theorem hcore15_compl {θ : ℝ} (h : HCore15 θ) : HCore15 (Real.pi / 2 - θ) := by
  intro r x y hX
  rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub] at hX
  exact h r y x (by linear_combination hX)

/-- generic case, with `p` free and `hne : 2r² ≠ p`. -/
theorem generic_kill15 {θ : ℝ} (hind : GenericIndep θ) : HCore15 θ := by
  intro r x y hX
  set p : ℕ := 15 with hp15
  set e := Complex.exp (θ * Complex.I) with he_def
  set e' := Complex.exp (-(θ : ℂ) * Complex.I) with he'_def
  have hee : e * e' = 1 := by rw [he_def, he'_def, ← Complex.exp_add]; ring_nf; simp
  have hXc : 2 * ((r : ℂ) + x * Complex.sin θ + y * Complex.cos θ) ^ 2 = p := by
    have := congrArg (fun t : ℝ => (t : ℂ)) hX
    push_cast at this
    simpa [p] using this
  have hsin : Complex.sin θ = (e' - e) * Complex.I / 2 := rfl
  have hcos : Complex.cos θ = (e + e') / 2 := rfl
  rw [hsin, hcos] at hXc
  set Xc := (r : ℂ) + x * ((e' - e) * Complex.I / 2) + y * ((e + e') / 2) with hXc_def
  have hXc' : 2 * Xc ^ 2 = p := hXc
  set iQ : QI := ⟨Complex.I, I_mem⟩
  set A : QI := ((y : QI) - iQ * (x : QI)) / 2
  set B : QI := ((y : QI) + iQ * (x : QI)) / 2
  have hc2 : ((2 : QI) : ℂ) = 2 := by
    rw [show (2 : QI) = ((2 : ℕ) : QI) from (Nat.cast_ofNat).symm]; push_cast; rfl
  have hA : (A : ℂ) = ((y : ℂ) - Complex.I * x) / 2 := by simp [A, iQ, hc2]
  have hB : (B : ℂ) = ((y : ℂ) + Complex.I * x) / 2 := by simp [B, iQ, hc2]
  have hXe : Xc * e = r * e + (A : ℂ) * e ^ 2 + (B : ℂ) := by
    rw [hA, hB, hXc_def]
    linear_combination (↑x * Complex.I / 2 + ↑y / 2) * hee
  set g : Fin 5 → QI := ![B ^ 2, 2 * (r : QI) * B, (r : QI) ^ 2 + 2 * A * B - (p : QI) / 2,
    2 * (r : QI) * A, A ^ 2]
  have hsum : ∑ k, g k • (fun k : Fin 5 => e ^ (k : ℕ)) k = 0 := by
    rw [Fin.sum_univ_five]
    simp only [IntermediateField.smul_def, smul_eq_mul]
    have g0 : g 0 = B ^ 2 := rfl
    have g1 : g 1 = 2 * (r : QI) * B := rfl
    have g2 : g 2 = (r : QI) ^ 2 + 2 * A * B - (p : QI) / 2 := rfl
    have g3 : g 3 = 2 * (r : QI) * A := rfl
    have g4 : g 4 = A ^ 2 := rfl
    have c0 : ((0 : Fin 5) : ℕ) = 0 := rfl
    have c1 : ((1 : Fin 5) : ℕ) = 1 := rfl
    have c2 : ((2 : Fin 5) : ℕ) = 2 := rfl
    have c3 : ((3 : Fin 5) : ℕ) = 3 := rfl
    have c4 : ((4 : Fin 5) : ℕ) = 4 := rfl
    rw [g0, g1, g2, g3, g4, c0, c1, c2, c3, c4]
    push_cast
    simp only [hc2]
    linear_combination (-(Xc * e + (r * e + (A : ℂ) * e ^ 2 + (B : ℂ)))) * hXe
      + (e ^ 2 / 2) * hXc'
  have hg4 := Fintype.linearIndependent_iff.mp hind g hsum 4
  have hA0 : (A : ℂ) = 0 := by
    have : A = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by simpa [g] using hg4)
    simp [this]
  rw [hA] at hA0
  have hre := congrArg Complex.re hA0
  have him := congrArg Complex.im hA0
  simp at hre him
  subst hre; subst him
  have h2 : 2 * (r : ℝ) ^ 2 = 15 := by simpa using hX
  have h3 : 2 * r ^ 2 = 15 := by exact_mod_cast h2
  omega

theorem hcore15_of_primitive {θ : ℝ} (u : QI) (hu : u ≠ 0) {M : ℕ} (hM : 0 < M)
    (hω : IsPrimitiveRoot ((u : ℂ) * Complex.exp (θ * Complex.I)) M) (h10 : 10 ≤ M.totient) :
    HCore15 θ :=
  generic_kill15 (indep_of_scaled u hu rfl (indep_of_totient hω hM h10))

theorem core15_pi_div_four : HCore15 (Real.pi / 4) := by
  intro r x y hX
  rw [Real.sin_pi_div_four, Real.cos_pi_div_four] at hX
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hkey : (2 * (r : ℝ) ^ 2 + ((x : ℝ) + y) ^ 2 - 15) + 2 * r * (x + y) * Real.sqrt 2 = 0 := by
    linear_combination hX - (((x : ℝ) + y) ^ 2 / 2) * hs
  have hirr : Irrational (Real.sqrt 2) := irrational_sqrt_two
  have hrt : (r : ℝ) * (x + y) = 0 := by
    by_contra hne
    apply hirr
    have hne' : (2 * (r : ℝ) * (x + y)) ≠ 0 := by
      intro h0; apply hne; linarith
    refine ⟨(15 - 2 * r ^ 2 - ((x : ℚ) + y) ^ 2) / (2 * r * (x + y)), ?_⟩
    push_cast
    rw [div_eq_iff hne']
    linear_combination -hkey
  rcases mul_eq_zero.mp hrt with h | h
  · have hr : r = 0 := by exact_mod_cast h
    subst hr
    have ht : ((x + y : ℕ) : ℝ) ^ 2 = 15 := by push_cast; simp at hkey; linarith
    have ht' : (x + y) ^ 2 = 15 := by exact_mod_cast ht
    exact sq_ne_15 _ ht'
  · have ht : 2 * ((r : ℝ)) ^ 2 = 15 := by
      have : ((x : ℝ) + y) = 0 := h
      linear_combination hkey - (((x : ℝ) + y) + 2 * r * Real.sqrt 2) * this
    have : 2 * r ^ 2 = 15 := by exact_mod_cast ht
    omega

theorem core15_pi_div_six : HCore15 (Real.pi / 6) := by
  intro r x y hX
  rw [Real.sin_pi_div_six, Real.cos_pi_div_six] at hX
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  set a : ℝ := r + x / 2
  set b : ℝ := y / 2
  have hkey : (2 * a ^ 2 + 6 * b ^ 2 - 15) + 4 * a * b * Real.sqrt 3 = 0 := by
    linear_combination hX - (2 * b ^ 2) * hs
  have hirr : Irrational (Real.sqrt 3) := Nat.prime_three.irrational_sqrt
  have hab : a * b = 0 := by
    by_contra hne
    apply hirr
    have hne' : (4 * a * b) ≠ 0 := by intro h0; apply hne; linarith
    refine ⟨(15 - 2 * ((r : ℚ) + x / 2) ^ 2 - 6 * ((y : ℚ) / 2) ^ 2) / (4 * ((r : ℚ) + x / 2) * (y / 2)),
      ?_⟩
    push_cast
    rw [div_eq_iff hne']
    linear_combination -hkey
  rcases mul_eq_zero.mp hab with h | h
  · have hr : (r : ℝ) = 0 := by
      have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      have : (0 : ℝ) ≤ x := Nat.cast_nonneg x
      simp only [a] at h; linarith
    have hx : (x : ℝ) = 0 := by simp only [a] at h; linarith
    have h3 : ((3 * y ^ 2 : ℕ) : ℝ) = ((30 : ℕ) : ℝ) := by
      push_cast
      have : (2 : ℝ) * a ^ 2 + 6 * b ^ 2 - 15 + 4 * a * b * Real.sqrt 3 = 0 := hkey
      rw [h] at this; simp only [b] at this; linarith
    have h3' : 3 * y ^ 2 = 30 := by exact_mod_cast h3
    exact sq_ne_10 y (by omega)
  · have h2 : (((2 * r + x) ^ 2 : ℕ) : ℝ) = ((30 : ℕ) : ℝ) := by
      push_cast
      have : (2 : ℝ) * a ^ 2 + 6 * b ^ 2 - 15 + 4 * a * b * Real.sqrt 3 = 0 := hkey
      rw [h] at this; simp only [a] at this; linarith
    exact sq_ne_30 _ (by exact_mod_cast h2)

theorem core15_pi_div_three : HCore15 (Real.pi / 3) := by
  have := hcore15_compl core15_pi_div_six
  rwa [show Real.pi / 2 - Real.pi / 6 = Real.pi / 3 by ring] at this

end Erdos634.Geometry.CaseA.LemmaH

#print axioms Erdos634.Geometry.CaseA.LemmaH.generic_kill15
#print axioms Erdos634.Geometry.CaseA.LemmaH.core15_pi_div_four
#print axioms Erdos634.Geometry.CaseA.LemmaH.core15_pi_div_six
#print axioms Erdos634.Geometry.CaseA.LemmaH.core15_pi_div_three

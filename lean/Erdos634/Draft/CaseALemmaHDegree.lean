-- Draft/CaseALemmaHDegree.lean — CASE A, node A9 (Lemma H), step 5's cyclotomic input:
-- if ω is a primitive M-th root of unity in ℂ then φ(M) ≤ 2·deg_{ℚ(i)} ω (tower law over
-- ℚ ⊂ ℚ(i) ⊂ ℚ(i)(ω)); hence φ(M) ≥ 10 gives 1, ω, …, ω⁴ linearly independent over ℚ(i), and the
-- same for ζ = u⁻¹ω for any nonzero u ∈ ℚ(i).  Feeds `CaseALemmaH.GenericIndep` / `generic_kill`.
-- Mathlib only (+ CaseALemmaH for the names).  Formalization debt; NOT /goal progress.
-- Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).  Hazard H59: no parameter pair (e, f) is evaluated here.
import Erdos634.Draft.CaseALemmaH

namespace Erdos634.Geometry.CaseA.LemmaH

open Polynomial IntermediateField

theorem I_isIntegral : IsIntegral ℚ Complex.I := by
  refine ⟨X ^ 2 + 1, by monicity!, ?_⟩
  simp

theorem finrank_QI_le : Module.finrank ℚ QI ≤ 2 := by
  rw [adjoin.finrank I_isIntegral]
  have h := minpoly.degree_le_of_ne_zero ℚ Complex.I (p := X ^ 2 + 1)
    (by intro h; have := congrArg (Polynomial.eval 0) h; simp at this) (by simp)
  rw [show (X ^ 2 + 1 : ℚ[X]) = X ^ 2 + C 1 by simp, degree_X_pow_add_C (by norm_num)] at h
  exact natDegree_le_of_degree_le h

/-- **Degree bound.**  A primitive `M`-th root of unity has degree ≥ φ(M)/2 over ℚ(i). -/
theorem totient_le_two_mul_deg {ω : ℂ} {M : ℕ} (hω : IsPrimitiveRoot ω M) (hM : 0 < M) :
    M.totient ≤ 2 * (minpoly QI ω).natDegree := by
  have hωZ : IsIntegral ℚ ω := (hω.isIntegral hM).tower_top
  have hωQ : IsIntegral QI ω := hωZ.tower_top
  haveI : FiniteDimensional ℚ QI := adjoin.finiteDimensional I_isIntegral
  set E : IntermediateField QI ℂ := QI⟮ω⟯
  haveI : FiniteDimensional QI E := adjoin.finiteDimensional hωQ
  haveI : FiniteDimensional ℚ E := Module.Finite.trans QI E
  have htower := Module.finrank_mul_finrank ℚ QI E
  have hE : Module.finrank QI E = (minpoly QI ω).natDegree := adjoin.finrank hωQ
  set x : E := ⟨ω, mem_adjoin_simple_self QI ω⟩
  have hx : (minpoly ℚ x).natDegree ≤ Module.finrank ℚ E := minpoly.natDegree_le x
  have hmx : minpoly ℚ x = minpoly ℚ ω := by
    rw [← minpoly.algebraMap_eq (algebraMap E ℂ).injective x]; rfl
  have hdeg : (minpoly ℚ ω).natDegree = M.totient := by
    rw [← cyclotomic_eq_minpoly_rat hω hM, natDegree_cyclotomic]
  rw [hmx, hdeg] at hx
  have h2 := finrank_QI_le
  rw [← htower, hE] at hx
  calc M.totient ≤ Module.finrank ℚ QI * (minpoly QI ω).natDegree := hx
    _ ≤ 2 * (minpoly QI ω).natDegree := Nat.mul_le_mul_right _ h2

/-- **Step 5's input, from the degree.**  φ(M) ≥ 10 ⇒ 1, ω, …, ω⁴ are ℚ(i)-independent. -/
theorem indep_of_totient {ω : ℂ} {M : ℕ} (hω : IsPrimitiveRoot ω M) (hM : 0 < M)
    (h10 : 10 ≤ M.totient) :
    LinearIndependent QI (fun k : Fin 5 => ω ^ (k : ℕ)) := by
  have hd := totient_le_two_mul_deg hω hM
  have h5 : 5 ≤ (minpoly QI ω).natDegree := by omega
  exact (linearIndependent_pow (K := QI) ω).comp (Fin.castLE h5) (Fin.castLE_injective h5)

/-- Transfer to `ζ` with `u·ζ = ω`, `u ∈ ℚ(i)` nonzero: the powers of `ζ` are the powers of `ω`
rescaled by the units `u⁻ᵏ`. -/
theorem indep_of_scaled {ζ ω : ℂ} (u : QI) (hu : u ≠ 0) (hω : (u : ℂ) * ζ = ω)
    (h : LinearIndependent QI (fun k : Fin 5 => ω ^ (k : ℕ))) :
    LinearIndependent QI (fun k : Fin 5 => ζ ^ (k : ℕ)) := by
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro g hg k
  have hu' : (u : ℂ) ≠ 0 := by exact_mod_cast hu
  have := h (fun k => g k * u⁻¹ ^ (k : ℕ)) (by
    rw [← hg]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [IntermediateField.smul_def, smul_eq_mul]
    rw [← hω]
    push_cast
    have e1 : (u : ℂ)⁻¹ ^ (k : ℕ) * ((u : ℂ) * ζ) ^ (k : ℕ) = ζ ^ (k : ℕ) := by
      rw [← mul_pow]; congr 1; field_simp
    rw [mul_assoc, e1]) k
  simpa [hu] using this

/-- **`GenericIndep` from a primitive root.**  If `u·e^{iθ}` is a primitive `M`-th root of unity for
some nonzero `u ∈ ℚ(i)` and φ(M) ≥ 10, then `GenericIndep θ`, hence `HCore θ`. -/
theorem hcore_of_primitive {θ : ℝ} (u : QI) (hu : u ≠ 0) {M : ℕ} (hM : 0 < M)
    (hω : IsPrimitiveRoot ((u : ℂ) * Complex.exp (θ * Complex.I)) M) (h10 : 10 ≤ M.totient) :
    HCore θ :=
  generic_kill (indep_of_scaled u hu rfl (indep_of_totient hω hM h10))

end Erdos634.Geometry.CaseA.LemmaH

#print axioms Erdos634.Geometry.CaseA.LemmaH.totient_le_two_mul_deg
#print axioms Erdos634.Geometry.CaseA.LemmaH.indep_of_totient
#print axioms Erdos634.Geometry.CaseA.LemmaH.hcore_of_primitive

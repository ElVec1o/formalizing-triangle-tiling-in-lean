-- Draft/CaseALemmaVDissection.lean — CASE A, node A2 (Lemma V) on a REAL `CongruentDissection`.
-- Source: (private working notes, not included) §3.2 and P2 row "V".
--   `lemmaV`:        model angles a_k·π/n (a_k ∈ ℕ) ⇒ v_ℓ(N) even for every prime ℓ ∤ 2n.
--   `lemmaV_prime`:  N prime, N ≠ 2 ⇒ N ∣ n.
-- Assembly: target angles in (π/n)ℕ (angle sum at a target corner, `sum_localAngle_eq` +
-- `interior_localAngle_mem`: the paper's F1); the side word of target side 0 (`oppLen_word`);
-- area (`abs_det_target`, `abs_det_eq`); the law of sines (`TriLawSin`); then
-- `LemmaV.even_of_sine_identity` (Draft/CaseALemmaVSines).  No gcd hypothesis, no scaling.
-- Formalization debt on a paper-level PROVED result; NOT /goal progress.  NOT imported into
-- All.lean.  Hazard H59: no parameter pair (e, f) is evaluated here.
import Erdos634.Draft.CaseALemmaVSines
import Erdos634.Draft.FluxGRow3RP
import Erdos634.Draft.FluxDSideWord
import Erdos634.VertexFigureReal
import Erdos634.AngleSumDissection
import Erdos634.CongruentAngles
import Erdos634.RouteOneVertexKill
import Erdos634.MarchFlank
import Erdos634.TriLawSin

namespace Erdos634.Geometry.CaseA.LemmaV

open Erdos634.Geometry

theorem angle_pos (T : Tri) (k : Fin 3) : 0 < T.angleAt k := Erdos634.MarchFlank.cornerAngle_pos T k

theorem angle_lt_pi (T : Tri) (k : Fin 3) : T.angleAt k < Real.pi :=
  Erdos634.RouteOneVertexKill.cornerAngle_lt_pi T k

theorem law_sines (T : Tri) (j : Fin 3) :
    Real.sin (T.angleAt (j + 1)) * T.oppLen j = Real.sin (T.angleAt j) * T.oppLen (j + 1) :=
  Erdos634.TriLawSin.sin_angleAt_mul_sideOpp T j

/-- An angle `x ∈ (0, π)` of the form `u·π/n` has `0 < u < n`. -/
theorem nat_bounds {n : ℕ} (hn : 0 < n) {u : ℕ} {x : ℝ} (hx : x = u * Real.pi / n) (h0 : 0 < x)
    (hπ : x < Real.pi) : 0 < u ∧ u < n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hp := Real.pi_pos
  rw [hx] at h0 hπ
  constructor
  · have : (0 : ℝ) < u := by
      by_contra hc; push Not at hc
      have : (u : ℝ) * Real.pi / n ≤ 0 := div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg hc hp.le) hn'.le
      linarith
    exact_mod_cast this
  · rw [div_lt_iff₀ hn'] at hπ
    have : (u : ℝ) < n := by nlinarith
    exact_mod_cast this

/-- **F1 (target angles).**  If the model's angles are in `(π/n)ℕ`, so are the target's. -/
theorem target_angle_nat {N : ℕ} (D : CongruentDissection N) {n : ℕ} (hn : 0 < n) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n) (k : Fin 3) :
    ∃ u : ℕ, D.target.angleAt k = u * Real.pi / n := by
  classical
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hcorners : ∀ (i : Fin N) (j : Fin 3),
      cornerAngle ((D.tile i).pts (j + 1)) ((D.tile i).pts j) ((D.tile i).pts (j + 2))
        ∈ ({D.model.angleAt 0, D.model.angleAt 1, D.model.angleAt 2} : Finset ℝ) := by
    intro i j
    obtain ⟨k', hk'⟩ := congruent_corner_angles (D.tiles_congruent i).symm j
    rw [hk']
    show D.model.angleAt k' ∈ _
    fin_cases k' <;> simp
  have hval : ∀ i, ∃ u : ℕ, (D.tile i).localAngle (D.target.pts k) = u * Real.pi / n := by
    intro i
    have hm := Erdos634.VertexFigureReal.interior_localAngle_mem D.toDissection _ _ _ hcorners
      (D.target.pts k) i
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h | h | h | h | h | h <;> rw [h]
    · exact ⟨a 0, ha 0⟩
    · exact ⟨a 1, ha 1⟩
    · exact ⟨a 2, ha 2⟩
    · exact ⟨n, by field_simp⟩
    · exact ⟨2 * n, by push_cast; field_simp⟩
    · exact ⟨0, by simp⟩
  choose u hu using hval
  refine ⟨∑ i, u i, ?_⟩
  have hs := D.toDissection.sum_localAngle_eq (D.target.pts k)
  rw [D.target.localAngle_vertex k] at hs
  show cornerAngle _ _ _ = _
  rw [← hs, Finset.sum_congr rfl (fun i _ => hu i)]
  push_cast
  rw [Finset.sum_mul, Finset.sum_div]

/-- **(★), sine form.**  For any `CongruentDissection` (no rationality needed):
`N·sin A₀ sin A₁ sin A₂ sin B₀ = X²·sin B₁ sin B₂` with `X = Σ c_k sin A_k`, `c_k ∈ ℕ`
(`A` model angles, `B` target angles; `c` = side word of target side 0). -/
theorem star {N : ℕ} (D : CongruentDissection N) :
    ∃ c : Fin 3 → ℕ,
      (N : ℝ) * Real.sin (D.model.angleAt 0) * Real.sin (D.model.angleAt 1) *
        Real.sin (D.model.angleAt 2) * Real.sin (D.target.angleAt 0)
      = (∑ k, (c k : ℝ) * Real.sin (D.model.angleAt k)) ^ 2 *
        Real.sin (D.target.angleAt 1) * Real.sin (D.target.angleAt 2) := by
  obtain ⟨c, hc⟩ := D.oppLen_word 0
  refine ⟨c, ?_⟩
  set M := D.model; set T := D.target
  have sp : ∀ (U : Tri) k, 0 < Real.sin (U.angleAt k) := fun U k =>
    Real.sin_pos_of_pos_of_lt_pi (angle_pos U k) (angle_lt_pi U k)
  have hM0 := law_sines M 0; have hM1 := law_sines M 1
  have hT0 := law_sines T 0; have hT1 := law_sines T 1
  simp only [show (0 : Fin 3) + 1 = 1 from rfl, show (1 : Fin 3) + 1 = 2 from rfl] at hM0 hM1 hT0 hT1
  have harea := Row3.RP.abs_det_target D
  rw [Row3.RP.abs_det_eq, Row3.RP.abs_det_eq] at harea
  rw [Fin.sum_univ_three] at hc ⊢
  set a0 := Real.sin (M.angleAt 0); set a1 := Real.sin (M.angleAt 1)
  set a2 := Real.sin (M.angleAt 2)
  set b0 := Real.sin (T.angleAt 0); set b1 := Real.sin (T.angleAt 1)
  set b2 := Real.sin (T.angleAt 2)
  have ha1 : 0 < a1 := sp M 1
  have hb0 : 0 < b0 := sp T 0; have hb1 : 0 < b1 := sp T 1
  set m0 := M.oppLen 0; set m1 := M.oppLen 1; set m2 := M.oppLen 2
  set t0 := T.oppLen 0; set t1 := T.oppLen 1; set t2 := T.oppLen 2
  set X := (c 0 : ℝ) * a0 + c 1 * a1 + c 2 * a2 with hX
  have hm0 : 0 < m0 := Row3.RP.oppLen_pos M 0
  have f1 : a2 * m0 = a0 * m2 := by
    apply mul_left_cancel₀ ha1.ne'
    linear_combination a2 * hM0 + a0 * hM1
  have g2 : b2 * t0 = b0 * t2 := by
    apply mul_left_cancel₀ hb1.ne'
    linear_combination b2 * hT0 + b0 * hT1
  have f2 : m0 * X = a0 * t0 := by
    rw [hX, hc]; linear_combination (c 1 : ℝ) * hM0 + (c 2 : ℝ) * f1
  have key : (m0 ^ 2 * b0) * ((N : ℝ) * a0 * a1 * a2 * b0 - X ^ 2 * b1 * b2) = 0 := by
    linear_combination (-(X * m0 + a0 * t0) * b1 * b2 * b0) * f2
      - (a0 ^ 2 * b0 * b2 * t0) * hT0 - (a0 ^ 2 * b0 * b0 * t1) * g2
      - (a0 ^ 2 * b0 ^ 2) * harea + ((N : ℝ) * a0 * b0 ^ 2 * a0 * m2) * hM0
      + ((N : ℝ) * a0 * b0 ^ 2 * a1 * m0) * f1
  have := (mul_eq_zero.mp key).resolve_left (by positivity)
  linarith

/-- **Lemma V (A2), on a real dissection.**  Every tile congruent to a model whose angles are
`a_k·π/n` (`a_k ∈ ℕ`; reflections allowed, not edge-to-edge): for every prime `ℓ ∤ 2n`,
`v_ℓ(N)` is even. -/
theorem lemmaV {N : ℕ} (D : CongruentDissection N) {n : ℕ} (hn : 0 < n) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ¬ ℓ ∣ 2 * n) : Even (padicValNat ℓ N) := by
  choose b hb using target_angle_nat D hn a ha
  obtain ⟨c, hc⟩ := star D
  have hN : N ≠ 0 := D.toDissection.pos.ne'
  have hA := fun k => nat_bounds hn (ha k) (angle_pos _ k) (angle_lt_pi _ k)
  have hB := fun k => nat_bounds hn (hb k) (angle_pos _ k) (angle_lt_pi _ k)
  refine even_of_sine_identity hn hℓ hℓ2 hN a (fun k => (hA k).1) (fun k => (hA k).2)
    b (fun k => (hB k).1) (fun k => (hB k).2) c ?_
  simp only [ha, hb] at hc
  exact hc

/-- **Lemma V, prime form.**  A prime tile count `N ≠ 2` divides `n`. -/
theorem lemmaV_prime {N : ℕ} (D : CongruentDissection N) {n : ℕ} (hn : 0 < n) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n) (hp : N.Prime) (h2 : N ≠ 2) : N ∣ n := by
  by_contra hd
  have hd2 : ¬ N ∣ 2 * n := by
    intro h
    rcases (Nat.Prime.dvd_mul hp).mp h with h' | h'
    · exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
    · exact hd h'
  have hev := lemmaV D hn a ha hp hd2
  haveI : Fact N.Prime := ⟨hp⟩
  rw [padicValNat_self] at hev
  exact Nat.not_even_one hev

end Erdos634.Geometry.CaseA.LemmaV

#print axioms Erdos634.Geometry.CaseA.LemmaV.target_angle_nat
#print axioms Erdos634.Geometry.CaseA.LemmaV.star
#print axioms Erdos634.Geometry.CaseA.LemmaV.lemmaV
#print axioms Erdos634.Geometry.CaseA.LemmaV.lemmaV_prime

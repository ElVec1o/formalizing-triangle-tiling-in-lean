-- Draft/CaseALemmaH.lean — CASE A, node A9: row 1's **Lemma H** (the half tile),
-- (private working notes, not included) §1–§2.  PARTIAL.
--
-- Lemma H: isosceles target, base angle θ ∈ ℚπ, tiled by N congruent right tiles with an acute
-- angle θ  ⇒  N is not an odd prime ≥ 5.
--
-- What this file proves (on a real `CongruentDissection`, any labelling, reflections, no
-- edge-to-edge assumption):
--   * `count_eq` (steps 1–2, (F1)+(F2)): N = 2X², X = r + x·sin θ + y·cos θ, r, x, y ∈ ℕ.
--     ASSEMBLED, NOT RE-PROVED: the area half IS `Row3.RP.row3_RP_area_any_label` (A44, which has
--     no irrationality hypothesis); the side word is `CongruentDissection.oppLen_word`.
--   * `generic_kill` (steps 4–5): if 1, ζ, …, ζ⁴ (ζ = e^{iθ}) are linearly independent over
--     ℚ(i) = `QI`, then 2X² ≠ p for every prime p ≥ 5 (in fact every odd prime).  The degree fact that supplies this
--     independence when φ(lcm(4,n)) ≥ 10 is NOT proved here.
--   * `core_pi_div_four`: the exceptional-angle kill at θ = π/4 (one of the eleven angles).
--   * `lemmaH_conditional`: Lemma H as written, for any θ at which `GenericIndep θ ∨ HCore θ`.
-- The remainder of (b) is closed in sibling files (2026-09-26, same session):
-- (i) the degree fact, CaseALemmaHDegree.lean; (ii) the exceptional cores, CaseALemmaHExc.lean
-- (π/6, π/3) and CaseALemmaHExc2.lean (π/8, π/12, π/10, π/5); (iii) the exceptional-set split,
-- CaseALemmaHGlue.lean.  Unconditional Lemma H: `lemmaH` in CaseALemmaHExc2.lean; joint witness
-- CaseALemmaHPiFour.lean.
--
-- Formalization debt on a paper-level PROVED node; NOT progress on the three /goal outcomes.
-- Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).  Hazard H59: no parameter pair (e, f) is evaluated here.
import Mathlib
import Erdos634.Draft.FluxGRow3RPAnyLabel
import Erdos634.Draft.FluxDSideWord

namespace Erdos634.Geometry.CaseA.LemmaH

open Real Erdos634.Geometry Erdos634.Geometry.Row3.RP

/-! ## Part (a): the dissection gives N = 2X² with X a ℕ-word in 1, sin θ, cos θ -/

theorem third_eq : ∀ p q r s : Fin 3, p ≠ q → p ≠ r → q ≠ r → s ≠ p → s ≠ q → s = r := by
  intro p q r s; fin_cases p <;> fin_cases q <;> fin_cases r <;> fin_cases s <;> simp

theorem sum_three (f : Fin 3 → ℝ) : ∀ p q s : Fin 3, p ≠ q → p ≠ s → q ≠ s →
    ∑ k, f k = f p + f q + f s := by
  intro p q s hpq hps hqs
  rw [Fin.sum_univ_three]
  fin_cases p <;> fin_cases q <;> fin_cases s <;> simp at hpq hps hqs ⊢ <;> ring

/-- The legs of a right tile with an acute angle θ at `p` and the right angle at `q`:
`oppLen p = c sin θ`, `oppLen s = c cos θ` (`s` the third vertex, `c = oppLen q`). -/
theorem model_legs (T : Tri) {θ : ℝ} {p q s : Fin 3} (hpq : p ≠ q) (hps : p ≠ s) (hqs : q ≠ s)
    (hp : T.angleAt p = θ) (hq : T.angleAt q = Real.pi / 2) :
    T.oppLen p = T.oppLen q * Real.sin θ ∧ T.oppLen s = T.oppLen q * Real.cos θ := by
  obtain ⟨τ, hτ0, hτ2⟩ := perm_exists p q 0 2 hpq (by decide)
  have hτ1 : τ 1 = s := by
    refine third_eq p q s (τ 1) hpq hps hqs ?_ ?_
    · intro h; rw [← hτ0] at h; exact absurd (τ.injective h) (by decide)
    · intro h; rw [← hτ2] at h; exact absurd (τ.injective h) (by decide)
  set U := T.relabel τ
  have hU : ∀ k, U.pts k = T.pts (τ k) := fun k => rfl
  have hU2 : U.angleAt 2 = Real.pi / 2 := by rw [angleAt_of_pts τ hU, hτ2, hq]
  have hU0 : U.angleAt 0 = θ := by rw [angleAt_of_pts τ hU, hτ0, hp]
  obtain ⟨h1, h0⟩ := right_sides U hU2
  rw [hU0, oppLen_of_pts τ hU, oppLen_of_pts τ hU, hτ2, hτ1] at h1
  rw [hU0, oppLen_of_pts τ hU, oppLen_of_pts τ hU, hτ2, hτ0] at h0
  exact ⟨h0, h1⟩

/-- **Lemma H, steps 1–2** ((F1) side covering + (F2) area) on a real `CongruentDissection`:
model angle θ at `p`, right angle at `q`; target angle θ at two distinct vertices `i, j` ⇒
`N = 2X²` with `X = r + x sin θ + y cos θ`, `r, x, y ∈ ℕ` (`X` = equal side / hypotenuse). -/
theorem count_eq {N : ℕ} (D : CongruentDissection N) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ2 : θ < Real.pi / 2)
    {p q : Fin 3} (hpq : p ≠ q) (hmp : D.model.angleAt p = θ) (hmq : D.model.angleAt q = Real.pi / 2)
    {i j : Fin 3} (hij : i ≠ j) (hi : D.target.angleAt i = θ) (hj : D.target.angleAt j = θ) :
    ∃ r x y : ℕ, (N : ℝ) = 2 * ((r : ℝ) + x * Real.sin θ + y * Real.cos θ) ^ 2 := by
  obtain ⟨s, hps, hqs⟩ : ∃ s : Fin 3, p ≠ s ∧ q ≠ s := by
    fin_cases p <;> fin_cases q <;> simp at hpq ⊢ <;> decide
  have harea := row3_RP_area_any_label D hθ0 hθ2 hpq hmp hmq (Or.inl rfl) hij hi hj
  obtain ⟨hlp, hls⟩ := model_legs D.model hpq hps hqs hmp hmq
  obtain ⟨n, hn⟩ := D.oppLen_word j
  rw [sum_three _ p q s hpq hps hqs, hlp, hls] at hn
  have hc := oppLen_pos D.model q
  refine ⟨n q, n p, n s, ?_⟩
  rw [harea, hn]
  congr 2
  field_simp
  ring

/-! ## Part (b), steps 4–5: the generic kill, conditional on independence over ℚ(i) -/

/-- ℚ(i) inside ℂ. -/
noncomputable abbrev QI : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {Complex.I}

/-- Step 5's input: 1, ζ, ζ², ζ³, ζ⁴ are ℚ(i)-linearly independent, ζ = e^{iθ}.
(Holds when [ℚ(i,ζ):ℚ(i)] ≥ 5, i.e. φ(lcm(4,n)) ≥ 10 — NOT proved here.) -/
def GenericIndep (θ : ℝ) : Prop :=
  LinearIndependent QI (fun k : Fin 5 => Complex.exp (θ * Complex.I) ^ (k : ℕ))

/-- The conclusion of Lemma H's algebraic core at one angle. -/
def HCore (θ : ℝ) : Prop :=
  ∀ r x y p : ℕ, p.Prime → 5 ≤ p → 2 * ((r : ℝ) + x * Real.sin θ + y * Real.cos θ) ^ 2 ≠ p

theorem I_mem : Complex.I ∈ QI := IntermediateField.mem_adjoin_simple_self ℚ Complex.I

/-- 2r² is never an odd prime. -/
theorem two_sq_ne_prime {r p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : 2 * r ^ 2 ≠ p := by
  intro h
  have : 2 ∣ p := ⟨r ^ 2, h.symm⟩
  rcases hp.eq_one_or_self_of_dvd 2 this with h1 | h1 <;> omega

/-- **Steps 4–5 (generic case).**  Write `X = r + Aζ + Bζ⁻¹`, `A = (y − ix)/2`, `B = (y + ix)/2`;
`ζ²(X² − p/2) = B² + 2rB ζ + (r² + 2AB − p/2) ζ² + 2rA ζ³ + A² ζ⁴`.  Independence kills the ζ⁴
coefficient `A²`, so `x = y = 0`, `X = r`, and `2r² = p` is impossible. -/
theorem generic_kill {θ : ℝ} (hind : GenericIndep θ) : HCore θ := by
  intro r x y p hp hp5 hX
  have hp2 : p ≠ 2 := by omega
  set e := Complex.exp (θ * Complex.I) with he_def
  set e' := Complex.exp (-(θ : ℂ) * Complex.I) with he'_def
  have hee : e * e' = 1 := by rw [he_def, he'_def, ← Complex.exp_add]; ring_nf; simp
  have hXc : 2 * ((r : ℂ) + x * Complex.sin θ + y * Complex.cos θ) ^ 2 = p := by
    have := congrArg (fun t : ℝ => (t : ℂ)) hX
    push_cast at this
    exact this
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
  apply two_sq_ne_prime (r := r) hp hp2
  exact_mod_cast (by simpa using hX : (2 * (r : ℝ) ^ 2 = p))

/-! ## Part (b), one exceptional angle: θ = π/4 -/

/-- **HCore at π/4**: `X = r + t·√2/2` (`t = x + y`); `2X² = 2r² + t² + 2rt√2 = p` forces
`rt = 0` (√2 irrational), and then `2r² = p` or `t² = p`, both impossible. -/
theorem core_pi_div_four : HCore (Real.pi / 4) := by
  intro r x y p hp hp5 hX
  have hp2 : p ≠ 2 := by omega
  rw [Real.sin_pi_div_four, Real.cos_pi_div_four] at hX
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hkey : (2 * (r : ℝ) ^ 2 + ((x : ℝ) + y) ^ 2 - p) + 2 * r * (x + y) * Real.sqrt 2 = 0 := by
    linear_combination hX - (((x : ℝ) + y) ^ 2 / 2) * hs
  have hirr : Irrational (Real.sqrt 2) := irrational_sqrt_two
  have hrt : (r : ℝ) * (x + y) = 0 := by
    by_contra hne
    apply hirr
    have hne' : (2 * (r : ℝ) * (x + y)) ≠ 0 := by
      intro h0; apply hne; linarith
    refine ⟨(p - 2 * r ^ 2 - ((x : ℚ) + y) ^ 2) / (2 * r * (x + y)), ?_⟩
    push_cast
    rw [div_eq_iff hne']
    linear_combination -hkey
  rcases mul_eq_zero.mp hrt with h | h
  · have hr : r = 0 := by exact_mod_cast h
    subst hr
    have ht : ((x + y : ℕ) : ℝ) ^ 2 = p := by push_cast; simp at hkey; linarith
    have ht' : (x + y) ^ 2 = p := by exact_mod_cast ht
    exact hp.not_isSquare ⟨x + y, by rw [← ht']; ring⟩
  · have hxy : x + y = 0 := by exact_mod_cast h
    have ht : 2 * ((r : ℝ)) ^ 2 = p := by
      have : ((x : ℝ) + y) = 0 := h
      linear_combination hkey - (((x : ℝ) + y) + 2 * r * Real.sqrt 2) * this
    exact two_sq_ne_prime hp hp2 (by exact_mod_cast ht)

/-! ## Assembly: Lemma H as written, at every θ where the core holds -/

/-- **Lemma H (conditional on the core at θ).**  Isosceles target with base angle θ at two distinct
vertices, 0 < θ < π/2, tiled by N congruent right tiles with an acute angle θ (any labelling,
reflections, no edge-to-edge) ⇒ N is not a prime ≥ 5 (exactly §1's conclusion).  Hypothesis `hcore` is the unformalized
remainder of (b); θ ∈ ℚπ is where the paper supplies it. -/
theorem lemmaH_conditional {N : ℕ} (D : CongruentDissection N) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ2 : θ < Real.pi / 2) (hcore : GenericIndep θ ∨ HCore θ)
    {p q : Fin 3} (hpq : p ≠ q) (hmp : D.model.angleAt p = θ) (hmq : D.model.angleAt q = Real.pi / 2)
    {i j : Fin 3} (hij : i ≠ j) (hi : D.target.angleAt i = θ) (hj : D.target.angleAt j = θ) :
    ¬ (N.Prime ∧ 5 ≤ N) := by
  rintro ⟨hN, hN5⟩
  obtain ⟨r, x, y, h⟩ := count_eq D hθ0 hθ2 hpq hmp hmq hij hi hj
  have hC : HCore θ := hcore.elim generic_kill id
  exact hC r x y N hN hN5 h.symm

/-- Lemma H at θ = π/4, unconditionally (the core is `core_pi_div_four`). -/
theorem lemmaH_pi_div_four {N : ℕ} (D : CongruentDissection N)
    {p q : Fin 3} (hpq : p ≠ q) (hmp : D.model.angleAt p = Real.pi / 4)
    (hmq : D.model.angleAt q = Real.pi / 2)
    {i j : Fin 3} (hij : i ≠ j) (hi : D.target.angleAt i = Real.pi / 4)
    (hj : D.target.angleAt j = Real.pi / 4) :
    ¬ (N.Prime ∧ 5 ≤ N) :=
  lemmaH_conditional D (by positivity) (by linarith [Real.pi_pos]) (Or.inr core_pi_div_four)
    hpq hmp hmq hij hi hj

end Erdos634.Geometry.CaseA.LemmaH

#print axioms Erdos634.Geometry.CaseA.LemmaH.count_eq
#print axioms Erdos634.Geometry.CaseA.LemmaH.generic_kill
#print axioms Erdos634.Geometry.CaseA.LemmaH.core_pi_div_four
#print axioms Erdos634.Geometry.CaseA.LemmaH.lemmaH_conditional
#print axioms Erdos634.Geometry.CaseA.LemmaH.lemmaH_pi_div_four

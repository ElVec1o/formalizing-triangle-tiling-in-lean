/-
Draft/H1aSetup.lean — atom H1.a of (private working notes, not included) §1/§6 (right-tile branch, setup).
Contents:
  * `RightNormal D α` : the paper's WLOG normal form: model angle `α` at vertex 0 (`a = oppLen 0 = c sin α`),
    `π/2` at vertex 2 (hypotenuse `c = oppLen 2`), `π/2 - α` at vertex 1 (`b = oppLen 1 = c cos α`); target base angles
    `α` at vertices 0, 1, apex vertex 2 (so `AB = oppLen 1 = oppLen 0`, `BC = oppLen 2`).
  * `rightCase_normalize`: `RightCase D → ∃ D' α, RightNormal D' α` (`D'` has the same `N`; relabel `γ = π/2 - α`
    to `γ = α` by swapping the model's `α`/`β` vertices; relabel model/target vertices; no orientation assumption).
  * `RightFacts N M a b c lam`: (F1) `N = 2M`, `lam² = M` (`lam = AB/c`), (F2) `Even N` (used for `M = N/2`),
    (F3) side words of `AB` and `BC`; positivity and `a² + b² = c²`.
  * `rightCase_facts`: from `RightCase D` produce such a normal `D'` and `RightFacts`.
  * `lam ∈ ℚ ⇒ M = m²` (so `N = 2m² = 2(m² + 0²)`), and `h1_of_irrational_case`: the `∃ x y : ℕ` goal reduces to the
    case `lam ∉ ℚ`.
*** UNAUDITED.  Formalization debt, NOT /goal progress.  No sorry, no native_decide, no cited theorem. ***
Not covered here (belongs to other atoms): the flux coordinates of Case C (F4/flux, H1.c) and corner geometry (H1.e).
-/
import Erdos634.Draft.TheoremPConditional
import Erdos634.Draft.FluxGRow3RPAnyLabel
import Erdos634.Draft.FluxDSideWord

open scoped Classical

namespace Erdos634.Draft.H1a

open Erdos634.Geometry Erdos634.Geometry.Row3.RP Erdos634.Draft.TheoremPConditional

/-- Normal form of a `RightCase` dissection (paper §1, after WLOG `γ = α`): model angles `α` at vertex 0,
`π/2` at vertex 2 (so `π/2 - α` at vertex 1); target angles `α` at vertices 0 and 1. -/
structure RightNormal {N : ℕ} (D : CongruentDissection N) (α : ℝ) : Prop where
  pos : 0 < α
  lt : α < Real.pi / 2
  irr : Irrational (α / Real.pi)
  m0 : D.model.angleAt 0 = α
  m2 : D.model.angleAt 2 = Real.pi / 2
  t0 : D.target.angleAt 0 = α
  t1 : D.target.angleAt 1 = α

/-- Core of the normalization: `α`-case, arbitrary labelling. -/
theorem normalize_alpha {N : ℕ} (D : CongruentDissection N) {α : ℝ} (hα0 : 0 < α)
    (hα2 : α < Real.pi / 2) (hirr : Irrational (α / Real.pi))
    {p q : Fin 3} (hpq : p ≠ q) (hmp : D.model.angleAt p = α) (hmq : D.model.angleAt q = Real.pi / 2)
    {i j : Fin 3} (hij : i ≠ j) (hi : D.target.angleAt i = α) (hj : D.target.angleAt j = α) :
    ∃ D' : CongruentDissection N, RightNormal D' α := by
  obtain ⟨τ, hτ0, hτ2⟩ := perm_exists p q 0 2 hpq (by decide)
  obtain ⟨σ, hσ0, hσ1⟩ := perm_exists i j 0 1 hij (by decide)
  refine ⟨(relabelModel D τ).relabelTarget' σ, ?_⟩
  refine ⟨hα0, hα2, hirr, ?_, ?_, ?_, ?_⟩
  · show (D.model.relabel τ).angleAt 0 = α
    rw [angleAt_of_pts (T := D.model) τ (fun k => rfl), hτ0, hmp]
  · show (D.model.relabel τ).angleAt 2 = Real.pi / 2
    rw [angleAt_of_pts (T := D.model) τ (fun k => rfl), hτ2, hmq]
  · rw [angleAt_of_pts (T := D.target) σ (fun k => rfl), hσ0, hi]
  · rw [angleAt_of_pts (T := D.target) σ (fun k => rfl), hσ1, hj]

/-- **WLOG `γ = α`.**  Every `RightCase` dissection has a normalized version with the same `N`. -/
theorem rightCase_normalize {N : ℕ} {D : CongruentDissection N} (hR : RightCase D) :
    ∃ (D' : CongruentDissection N) (α : ℝ), RightNormal D' α := by
  obtain ⟨α, h0, h2, hi, ⟨p, q, hpq, hmp, hmq⟩, γ, hγ, i, j, hij, hi', hj'⟩ := hR
  rcases hγ with hγ | hγ
  · subst hγ
    obtain ⟨D', h⟩ := normalize_alpha D h0 h2 hi hpq hmp hmq hij hi' hj'
    exact ⟨D', _, h⟩
  · subst hγ
    obtain ⟨r, hrp, hrq⟩ : ∃ r : Fin 3, p ≠ r ∧ q ≠ r := by
      fin_cases p <;> fin_cases q <;> simp at hpq ⊢ <;> decide
    have hmr : D.model.angleAt r = Real.pi / 2 - α := by
      have := angle_third (T := D.model) hpq hrp hrq; linarith
    have hirr' : Irrational ((Real.pi / 2 - α) / Real.pi) := by
      have h : (Real.pi / 2 - α) / Real.pi = ((1 / 2 : ℚ) : ℝ) - α / Real.pi := by
        field_simp; push_cast; ring
      rw [h]; exact irrational_ratCast_sub_iff.mpr hi
    obtain ⟨D', h⟩ := normalize_alpha D (by linarith) (by linarith) hirr' (Ne.symm hrq) hmr hmq hij hi' hj'
    exact ⟨D', _, h⟩

/-- The scalar data extracted from a normal-form dissection (paper §1 `(F1)`–`(F3)`):
`a = oppLen 0` (opposite `α`), `b = oppLen 1`, `c = oppLen 2` (hypotenuse), `lam = |AB|/c`, `N = 2M`. -/
structure RightFacts (N M : ℕ) (a b c lam : ℝ) : Prop where
  hN : N = 2 * M
  ha : 0 < a
  hb : 0 < b
  hc : 0 < c
  pyth : a ^ 2 + b ^ 2 = c ^ 2
  hlam : 0 < lam
  hlam2 : lam ^ 2 = M
  /-- word of `|AB| = lam·c` -/
  wAB : ∃ ua ub uc : ℕ, lam * c = ua * a + ub * b + uc * c
  /-- word of `|BC| = 2·lam·b` -/
  wBC : ∃ wa wb wc : ℕ, 2 * lam * b = wa * a + wb * b + wc * c

/-- Geometric side relations in normal form: `|AB| = |AC| = lam c`, `|BC| = 2 lam b`, `a = c sin α`, `b = c cos α`. -/
theorem RightNormal.sides {N : ℕ} {D : CongruentDissection N} {α : ℝ} (h : RightNormal D α) :
    D.model.oppLen 0 = D.model.oppLen 2 * Real.sin α ∧ D.model.oppLen 1 = D.model.oppLen 2 * Real.cos α ∧
    D.target.oppLen 0 = D.target.oppLen 1 ∧
    D.target.oppLen 2 = 2 * D.target.oppLen 1 * Real.cos α := by
  obtain ⟨hb, ha⟩ := right_sides D.model h.m2
  rw [h.m0] at hb ha
  exact ⟨ha, hb, iso_sides D.target h.pos h.lt h.t0 h.t1⟩

/-- **(F1)–(F3) in normal form.**  With `M = N/2` (`N` even by Row 3 RP). -/
theorem RightNormal.facts {N : ℕ} {D : CongruentDissection N} {α : ℝ} (h : RightNormal D α) :
    ∃ M : ℕ, RightFacts N M (D.model.oppLen 0) (D.model.oppLen 1) (D.model.oppLen 2)
      (D.target.oppLen 1 / D.model.oppLen 2) := by
  have hc : 0 < D.model.oppLen 2 := oppLen_pos _ _
  have hL : 0 < D.target.oppLen 1 := oppLen_pos _ _
  obtain ⟨sa, sb, tt0, tt2⟩ := h.sides
  -- (F2): N even
  obtain ⟨M, hM⟩ := row3_RP_even_any_label D h.pos h.lt h.irr (p := 0) (q := 2) (by decide)
    h.m0 h.m2 (γ := α) (Or.inl rfl) (i := 0) (j := 1) (by decide) h.t0 h.t1
  -- (F1): N = 2 lam²
  have hA := row3_RP_area_any_label D h.pos h.lt (p := 0) (q := 2) (by decide) h.m0 h.m2
    (γ := α) (Or.inl rfl) (i := 0) (j := 1) (by decide) h.t0 h.t1
  set lam := D.target.oppLen 1 / D.model.oppLen 2 with hlamdef
  have hlam : 0 < lam := by positivity
  have hLc : D.target.oppLen 1 = lam * D.model.oppLen 2 := by rw [hlamdef]; field_simp
  refine ⟨M, ⟨by omega, oppLen_pos _ _, oppLen_pos _ _, hc, ?_, hlam, ?_, ?_, ?_⟩⟩
  · rw [sa, sb]
    have := Real.sin_sq_add_cos_sq α
    linear_combination (D.model.oppLen 2) ^ 2 * this
  · have h2 : (N : ℝ) = 2 * M := by exact_mod_cast hM.trans (by ring)
    nlinarith
  · obtain ⟨n, hn⟩ := D.oppLen_word 1
    refine ⟨n 0, n 1, n 2, ?_⟩
    rw [← hLc, hn, Fin.sum_univ_three]
  · obtain ⟨n, hn⟩ := D.oppLen_word 2
    refine ⟨n 0, n 1, n 2, ?_⟩
    have : 2 * lam * D.model.oppLen 1 = D.target.oppLen 2 := by
      rw [tt2, hLc, sb]; ring
    rw [this, hn, Fin.sum_univ_three]

/-- **H1.a output.**  A `RightCase` dissection yields a normal-form dissection (same `N`) together with the scalar data. -/
theorem rightCase_facts {N : ℕ} {D : CongruentDissection N} (hR : RightCase D) :
    ∃ (D' : CongruentDissection N) (α : ℝ) (M : ℕ), RightNormal D' α ∧
      RightFacts N M (D'.model.oppLen 0) (D'.model.oppLen 1) (D'.model.oppLen 2)
        (D'.target.oppLen 1 / D'.model.oppLen 2) := by
  obtain ⟨D', α, h⟩ := rightCase_normalize hR
  obtain ⟨M, hM⟩ := h.facts
  exact ⟨D', α, M, h, hM⟩

/-! ### `lam ∈ ℚ ⇒ N = 2 m²` and the reduction of the goal to the irrational case -/

/-- A rational `lam` with `lam² = M ∈ ℕ` gives `M = m²`. -/
theorem sq_of_rational {M : ℕ} {lam : ℝ} (hlam2 : lam ^ 2 = M) (hq : ¬ Irrational lam) :
    ∃ m : ℕ, M = m ^ 2 := by
  rw [Irrational, not_not] at hq
  obtain ⟨q, rfl⟩ := hq
  have h : (q : ℚ) ^ 2 = (M : ℚ) := by exact_mod_cast hlam2
  have hs : IsSquare (M : ℚ) := ⟨q, by rw [← h]; ring⟩
  obtain ⟨m, hm⟩ := Rat.isSquare_natCast_iff.mp hs
  exact ⟨m, by rw [hm]; ring⟩

/-- `N = 2M` and `M = x² + y²` give the paper's `N = 2(x² + y²)`. -/
theorem goal_of_M {N M : ℕ} (hN : N = 2 * M) (h : ∃ x y : ℕ, M = x ^ 2 + y ^ 2) :
    ∃ x y : ℕ, N = 2 * (x ^ 2 + y ^ 2) := by
  obtain ⟨x, y, hxy⟩ := h
  exact ⟨x, y, by rw [hN, hxy]⟩

/-- **Reduction to `lam ∉ ℚ`** (paper §1): the `∃ x y : ℕ` goal holds as soon as it holds when `lam` is irrational. -/
theorem h1_of_irrational_case {N M : ℕ} {a b c lam : ℝ} (hF : RightFacts N M a b c lam)
    (hirr : Irrational lam → ∃ x y : ℕ, M = x ^ 2 + y ^ 2) :
    ∃ x y : ℕ, N = 2 * (x ^ 2 + y ^ 2) := by
  apply goal_of_M hF.hN
  by_cases hl : Irrational lam
  · exact hirr hl
  · obtain ⟨m, hm⟩ := sq_of_rational hF.hlam2 hl
    exact ⟨m, 0, by simp [hm]⟩

end Erdos634.Draft.H1a

#print axioms Erdos634.Draft.H1a.rightCase_normalize
#print axioms Erdos634.Draft.H1a.RightNormal.facts
#print axioms Erdos634.Draft.H1a.rightCase_facts
#print axioms Erdos634.Draft.H1a.h1_of_irrational_case

-- Draft/CaseAR0c.lean — CASE A, node A8: **Theorem R0c, assembled from Lemma S as a hypothesis (`r0c_of_lemmaS`)**
-- ((private working notes, not included) §3.7; PRIME_CASE_PROOF.md §2 Case A / §3.1 A8).
--
--   Theorem R0c.  No prime p ≡ 3 (mod 4), p > 3, is the number of tiles in a congruent tiling of
--   a triangle whose tile has all angles in ℚπ.
--
-- *** UPDATED 2026-10-02 (stale-header fix): `r0c_of_lemmaS` in THIS file still takes Lemma S
-- *** (`LemmaSStatement`, PROOF_lemmaS.md P2 "Theorem S (Lemma S)", verbatim) as an explicit
-- *** hypothesis.  That hypothesis is now DISCHARGED: `Erdos634.LemmaSAll.lemmaS` (Draft/LemmaSAll.lean,
-- *** UNAUDITED) proves it for every n, and `Erdos634.LemmaSAll.r0c` is Theorem R0c UNCONDITIONALLY
-- *** (it is what TheoremPConditional / TheoremP6 consume).  Cite `LemmaSAll.r0c`, not `r0c_of_lemmaS`.
-- *** `r0c_unconditional_finite` (below) is the earlier finite-residue form.
--
-- Chain (every step a cited, already-built node; nothing re-derived):
--   rational angles ⇒ primitive (n; a) (this file, `exists_primitive`: n = exact denominator)
--   ⇒ Lemma V  `CaseA.LemmaV.lemmaV_prime`       : N ∣ n
--   ⇒ Lemma K  `KConj.lemmaK` (K1 ∧ K2, target angles = (f_j·a)π/n)
--   ⇒ K* + [Lemma S at (n, a, p = N)] + Lemma F   `LemmaF.shapes_of_K` : Similar ∨ HalfIso
--   ⇒ Similar : row 2 `Row2.theoremS_perm` (sides proportional via the law of sines
--               `A1Field.oppLen_eq`)  : N % 4 ≠ 3 ∨ N = 3
--     HalfIso : `CaseA.LemmaH.lemmaH`              : ¬ (N prime ∧ 5 ≤ N).
--
-- Interface check (recorded):
--   * Lemma S needs gcd(a) = 1, which a real dissection does not hand you: it is manufactured by
--     `exists_primitive` (divide (n; a) by gcd(a)); Lemma V / K / F need no gcd.
--   * Lemma S's `7 ≤ p` is met with p = N: N prime, N % 4 = 3, N > 3 ⇒ N ≥ 7 (5 ≢ 3 mod 4, and
--     p = 3 is excluded by the hypothesis N > 3).  `p ∣ n` is Lemma V's output.
--   * Lemma F's right-isosceles exclusion is not needed (`lemmaF_all` inside `shapes_of_K`).
--   * The "Similar" branch of Lemma F is a multiset statement on angles; Theorem S needs a vertex
--     correspondence τ AND a scale μ.  τ: `perm_of_counts` (sorting); μ = circD target / circD model.
--
-- Formalization debt on a paper-level node (PROVED-pending); NOT /goal progress.
-- Imported into All.lean (via LemmaSAll / TheoremP6 chain; header corrected 2026-10-02).
import Erdos634.Draft.KConjLemmaK
import Erdos634.Draft.CaseALemmaF
import Erdos634.Draft.CaseALemmaHExc2
import Erdos634.Draft.FluxERow2S
import Erdos634.Draft.A1FieldClause
import Mathlib.Data.Fin.Tuple.Sort

open scoped BigOperators

namespace Erdos634.CaseA.R0c

open Erdos634.Geometry Erdos634.LemmaS Erdos634.LemmaKStar Erdos634.LemmaF Erdos634.KConj
open Erdos634.Geometry.CaseA.LemmaV (lemmaV_prime nat_bounds angle_pos angle_lt_pi)

variable {N : ℕ}

/-- **Lemma S, exactly as written** (PROOF_lemmaS.md P2 "Theorem S (Lemma S)", Lean vocabulary
l.868–871): T1–T3 and a prime `p ≥ 7` dividing `n` ⇒ `R(a) = R₀(a)`.  (Stated here; PROVED in
`Draft/LemmaSAll.lean` as `Erdos634.LemmaSAll.lemmaS`, UNAUDITED. Updated 2026-10-01.) -/
def LemmaSStatement : Prop :=
  ∀ (n : ℕ) (a : Fin 3 → ℕ), (∀ i, 0 < a i) → ∑ i, a i = n →
    Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1 →
    ∀ p : ℕ, p.Prime → 7 ≤ p → p ∣ n → relSpace n a = trivSpace n a

/-! ## Arithmetic helpers -/

theorem sum_of_angles {T : Tri} {n : ℕ} (hn : 0 < n) {b : Fin 3 → ℕ}
    (hb : ∀ i, T.angleAt i = b i * Real.pi / n) : ∑ i, b i = n := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hs := T.angleAt_sum
  rw [hb 0, hb 1, hb 2] at hs
  have hnn : (n : ℝ) * (Real.pi / n) = Real.pi := by field_simp
  have key : (((b 0 + b 1 + b 2 : ℕ) : ℝ) - n) * (Real.pi / n) = 0 := by
    push_cast; linear_combination hs - hnn
  have := sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_right (div_ne_zero Real.pi_ne_zero hn'))
  rw [Fin.sum_univ_three]; exact_mod_cast this

/-- Rational angles ⇒ angles `a_k π/n` for some `n > 0`. -/
theorem exists_nat_angles (T : Tri) (hrat : ∀ k, ∃ q : ℚ, T.angleAt k = q * Real.pi) :
    ∃ n : ℕ, 0 < n ∧ ∃ a : Fin 3 → ℕ, ∀ k, T.angleAt k = a k * Real.pi / n := by
  choose q hq using hrat
  set M : ℕ := ∏ k, (q k).den with hM
  have hMpos : 0 < M := Finset.prod_pos (fun k _ => (q k).den_pos)
  have hdvd : ∀ k, (q k).den ∣ M := fun k => Finset.dvd_prod_of_mem _ (Finset.mem_univ k)
  have hz : ∀ k, (q k) * M = (((q k).num * ((M / (q k).den : ℕ) : ℤ) : ℤ) : ℚ) := by
    intro k
    have hc : ((M / (q k).den : ℕ) : ℚ) * (q k).den = M := by
      exact_mod_cast Nat.div_mul_cancel (hdvd k)
    have e : (q k) * M = (q k * (q k).den) * ((M / (q k).den : ℕ) : ℚ) := by
      rw [← hc]; ring
    rw [e, Rat.mul_den_eq_num, Int.cast_mul, Int.cast_natCast]
  have hqpos : ∀ k, 0 < q k := by
    intro k
    have h := angle_pos T k
    rw [hq k] at h
    exact_mod_cast (pos_of_mul_pos_left h Real.pi_pos.le)
  refine ⟨M, hMpos, fun k => ((q k).num * ((M / (q k).den : ℕ) : ℤ)).toNat, fun k => ?_⟩
  have hzpos : (0 : ℚ) < (((q k).num * ((M / (q k).den : ℕ) : ℤ) : ℤ) : ℚ) := by
    rw [← hz k]; exact mul_pos (hqpos k) (by exact_mod_cast hMpos)
  have hz0 : 0 ≤ (q k).num * ((M / (q k).den : ℕ) : ℤ) := by exact_mod_cast hzpos.le
  have hcast : (((((q k).num * ((M / (q k).den : ℕ) : ℤ)).toNat : ℕ) : ℝ))
      = (((q k * M : ℚ)) : ℝ) := by
    rw [hz k]
    have : ((((q k).num * ((M / (q k).den : ℕ) : ℤ)).toNat : ℕ) : ℤ)
        = (q k).num * ((M / (q k).den : ℕ) : ℤ) := Int.toNat_of_nonneg hz0
    rw [← this]; push_cast; rfl
  rw [hcast, hq k]
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hMpos.ne'
  push_cast; field_simp

/-- Reduce `(n; a)` to the exact denominator: `gcd(a) = 1`. -/
theorem exists_primitive (T : Tri) {n : ℕ} (hn : 0 < n) (a : Fin 3 → ℕ)
    (ha : ∀ k, T.angleAt k = a k * Real.pi / n) :
    ∃ n' : ℕ, 0 < n' ∧ ∃ a' : Fin 3 → ℕ, Nat.gcd (a' 0) (Nat.gcd (a' 1) (a' 2)) = 1 ∧
      ∀ k, T.angleAt k = a' k * Real.pi / n' := by
  have hsum := sum_of_angles hn ha
  have ha1 : ∀ k, 0 < a k := fun k => (nat_bounds hn (ha k) (angle_pos T k) (angle_lt_pi T k)).1
  set g := Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ (ha1 0)
  have hgd : ∀ k, g ∣ a k := by
    intro k; fin_cases k
    · exact Nat.gcd_dvd_left _ _
    · exact (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)
    · exact (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)
  have hgn : g ∣ n := by
    rw [← hsum, Fin.sum_univ_three]
    exact Nat.dvd_add (Nat.dvd_add (hgd 0) (hgd 1)) (hgd 2)
  refine ⟨n / g, Nat.div_pos (Nat.le_of_dvd hn hgn) hgpos, fun k => a k / g, ?_, fun k => ?_⟩
  · show Nat.gcd (a 0 / g) (Nat.gcd (a 1 / g) (a 2 / g)) = 1
    have h12 : g ∣ Nat.gcd (a 1) (a 2) := Nat.gcd_dvd_right _ _
    rw [Nat.gcd_div (hgd 1) (hgd 2), Nat.gcd_div (hgd 0) h12, ← hg, Nat.div_self hgpos]
  · rw [ha k]
    have e1 : ((a k / g : ℕ) : ℝ) * g = a k := by exact_mod_cast Nat.div_mul_cancel (hgd k)
    have e2 : ((n / g : ℕ) : ℝ) * g = n := by exact_mod_cast Nat.div_mul_cancel hgn
    have hg' : (g : ℝ) ≠ 0 := by exact_mod_cast hgpos.ne'
    have hn2 : ((n / g : ℕ) : ℝ) ≠ 0 := by
      intro h; rw [h, zero_mul] at e2; exact (by exact_mod_cast hn.ne' : (n : ℝ) ≠ 0) e2.symm
    rw [← e1, ← e2]; field_simp

/-- Equal value-counts on `Fin 3` give a vertex correspondence. -/
theorem perm_of_counts (g h : Fin 3 → ℕ)
    (hc : ∀ x : ℕ, ∑ j, (if g j = x then 1 else 0 : ℕ) = ∑ i, (if h i = x then 1 else 0 : ℕ)) :
    ∃ τ : Equiv.Perm (Fin 3), ∀ j, g j = h (τ j) := by
  have hp : List.Perm (List.ofFn g) (List.ofFn h) := by
    rw [List.perm_iff_count]
    intro x
    have := hc x
    simp only [Fin.sum_univ_three] at this
    simp only [List.ofFn_succ, List.ofFn_zero, List.count_cons, List.count_nil, beq_iff_eq]
    simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at *
    split_ifs at this ⊢ <;> omega
  have hsg := (Equiv.Perm.ofFn_comp_perm (Tuple.sort g) g)
  have hsh := (Equiv.Perm.ofFn_comp_perm (Tuple.sort h) h)
  have heq : List.ofFn (g ∘ Tuple.sort g) = List.ofFn (h ∘ Tuple.sort h) :=
    List.Perm.eq_of_sortedLE (List.sortedLE_ofFn_iff.mpr (Tuple.monotone_sort g))
      (List.sortedLE_ofFn_iff.mpr (Tuple.monotone_sort h)) (hsg.trans (hp.trans hsh.symm))
  have hf := List.ofFn_injective heq
  refine ⟨(Tuple.sort g).symm.trans (Tuple.sort h), fun j => ?_⟩
  have := congrFun hf ((Tuple.sort g).symm j)
  simpa using this

/-! ## The assembly, with Lemma S at `(n, a)` as the one hypothesis -/

/-- **A8 core.** Primitive angle data `(n; a)` for the tile of a real `CongruentDissection N`,
Lemma S at `(n, a)` (for every prime `p ≥ 7` dividing `n`), `N` prime, `N ≡ 3 (mod 4)`, `N > 3`
⇒ `False`. -/
theorem r0c_core (D : CongruentDissection N) {n : ℕ} (hn : 0 < n) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n)
    (hSn : ∀ p : ℕ, p.Prime → 7 ≤ p → p ∣ n → relSpace n a = trivSpace n a)
    (hp : N.Prime) (h4 : N % 4 = 3) (h3 : 3 < N) : False := by
  have hN2 : N ≠ 2 := by omega
  have hNn : N ∣ n := lemmaV_prime D hn a ha hp hN2
  have h7 : 7 ≤ N := by omega
  have hn7 : 7 ≤ n := h7.trans (Nat.le_of_dvd hn hNn)
  obtain ⟨idx, hidx⟩ := exists_idx D a ha
  obtain ⟨hf, hK⟩ := lemmaK D hn a ha idx hidx
  set f := fig D idx
  have hsum := sum_of_angles hn ha
  have hsu := sum_of_angles hn hf
  have ha1 : ∀ i, 1 ≤ a i := fun i => (nat_bounds hn (ha i) (angle_pos _ i) (angle_lt_pi _ i)).1
  have hu1 : ∀ j, 1 ≤ uu a f j := fun j =>
    (nat_bounds hn (hf j) (angle_pos _ j) (angle_lt_pi _ j)).1
  have hfne : ∀ j, f j ≠ 0 := by
    intro j h
    have := hu1 j
    rw [uu, h] at this; simp at this
  have hshape := shapes_of_K (by omega) ha1 hsum hfne hsu (hSn N hp h7 hNn) hK
  rcases hshape with hsim | ⟨k, l, hk, hlk, j₁, j₂, hj, h1, h2⟩
  · -- ABC ~ T: row 2's Theorem S
    obtain ⟨τ, hτ⟩ := perm_of_counts (uu a f) a hsim
    have hang : ∀ j, D.target.angleAt j = D.model.angleAt (τ j) := by
      intro j; rw [hf j, ha (τ j), hτ j]
    set μ := A1Field.circD D.target / A1Field.circD D.model
    have hcm := (A1Field.circD_pos D.model).ne'
    have hsim' : ∀ j, D.target.angleAt j = D.model.angleAt (τ j) ∧
        D.target.oppLen j = μ * D.model.oppLen (τ j) := by
      intro j
      refine ⟨hang j, ?_⟩
      rw [A1Field.oppLen_eq D.target j, A1Field.oppLen_eq D.model (τ j), hang j]
      simp only [μ]; field_simp
    rcases Row2.theoremS_perm D μ τ hsim' hp with h | h <;> omega
  · -- half-isosceles: Lemma H
    have hlt : 2 * a l < n := by
      rw [Fin.sum_univ_three] at hsum
      have := ha1 0; have := ha1 1; have := ha1 2
      fin_cases k <;> fin_cases l <;> simp at hk hlk ⊢ <;> omega
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hθ0 : 0 < (a l : ℝ) * Real.pi / n := by
      have : (0 : ℝ) < a l := by exact_mod_cast ha1 l
      positivity
    have hθ2 : (a l : ℝ) * Real.pi / n < Real.pi / 2 := by
      rw [div_lt_div_iff₀ hn' (by norm_num : (0 : ℝ) < 2)]
      have : (2 * a l : ℝ) < n := by exact_mod_cast hlt
      nlinarith [Real.pi_pos]
    have hq : ∃ q : ℚ, (a l : ℝ) * Real.pi / n = q * Real.pi :=
      ⟨(a l : ℚ) / n, by push_cast; ring⟩
    have hmk : D.model.angleAt k = Real.pi / 2 := by
      rw [ha k]
      have : (2 * a k : ℝ) = n := by exact_mod_cast hk
      field_simp; linarith
    have hi : D.target.angleAt j₁ = (a l : ℝ) * Real.pi / n := by rw [hf j₁, h1]
    have hj' : D.target.angleAt j₂ = (a l : ℝ) * Real.pi / n := by rw [hf j₂, h2]
    exact CaseA.LemmaH.lemmaH D hq hθ0 hθ2 hlk (ha l) hmk hj hi hj' ⟨hp, by omega⟩

/-- **Theorem R0c, from Lemma S as an explicit hypothesis** (`LemmaSStatement`; discharged by `LemmaSAll.lemmaS`, giving `LemmaSAll.r0c`).
A real `CongruentDissection N` (reflections, not edge-to-edge) whose tile has all angles in ℚπ
has no prime `N ≡ 3 (mod 4)`, `N > 3`.  Conditional form only: Lemma S is proved in `LemmaSAll.lemmaS` (UNAUDITED); cite `LemmaSAll.r0c`. -/
theorem r0c_of_lemmaS (hS : LemmaSStatement) (D : CongruentDissection N)
    (hrat : ∀ k, ∃ q : ℚ, D.model.angleAt k = q * Real.pi)
    (hp : N.Prime) (h4 : N % 4 = 3) (h3 : 3 < N) : False := by
  obtain ⟨n₀, hn₀, a₀, ha₀⟩ := exists_nat_angles D.model hrat
  obtain ⟨n, hn, a, hgcd, ha⟩ := exists_primitive D.model hn₀ a₀ ha₀
  have hsum := sum_of_angles hn ha
  have hpos : ∀ i, 0 < a i := fun i => (nat_bounds hn (ha i) (angle_pos _ i) (angle_lt_pi _ i)).1
  exact r0c_core D hn a ha (fun p hpp hp7 hpn => hS n a hpos hsum hgcd p hpp hp7 hpn) hp h4 h3

/-- **R0c, unconditional, on the finite residue** (Lemma S discharged by `lemmaS_finite`,
Corollary F): tiles whose EXACT angle denominator (`gcd(a) = 1`) is `n ∈ {21, 28, 42, 66}`. -/
theorem r0c_unconditional_finite (D : CongruentDissection N) {n : ℕ}
    (hn : n = 21 ∨ n = 28 ∨ n = 42 ∨ n = 66) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n)
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1)
    (hp : N.Prime) (h4 : N % 4 = 3) (h3 : 3 < N) : False := by
  have hn0 : 0 < n := by omega
  have hsum := sum_of_angles hn0 ha
  have hpos : ∀ i, 0 < a i := fun i => (nat_bounds hn0 (ha i) (angle_pos _ i) (angle_lt_pi _ i)).1
  exact r0c_core D hn0 a ha (fun _ _ _ _ => lemmaS_finite hn a hpos hsum hgcd) hp h4 h3

/-- What `r0c_unconditional_finite` covers: by Lemma V (`N ∣ n`) the only (N, n) in its scope
are `N = 7` with `n ∈ {21, 28, 42}` and `N = 11` with `n = 66`. -/
theorem finite_scope {n : ℕ} (hn : n = 21 ∨ n = 28 ∨ n = 42 ∨ n = 66)
    (hp : N.Prime) (h4 : N % 4 = 3) (h3 : 3 < N) (hd : N ∣ n) :
    (N = 7 ∧ (n = 21 ∨ n = 28 ∨ n = 42)) ∨ (N = 11 ∧ n = 66) := by
  have hle : N ≤ 66 := (Nat.le_of_dvd (by omega) hd).trans (by omega)
  rcases hn with rfl | rfl | rfl | rfl <;> interval_cases N <;> simp_all

/-! ## Witnesses and controls -/

/-- The rationality hypothesis is met by a real `CongruentDissection` (the `CaseALemmaHPiFour`
dissection, N = 2, angles (1,2,1)π/4). -/
theorem hrat_witness : ∀ k, ∃ q : ℚ,
    Erdos634.Draft.CaseALemmaHPiFour.dissection.model.angleAt k = q * Real.pi := by
  intro k
  refine ⟨((![1, 2, 1] : Fin 3 → ℕ) k : ℚ) / 4, ?_⟩
  rw [Erdos634.Draft.CaseALemmaVWitness.model_angles k]; push_cast; ring

/-- The arithmetic hypotheses of `r0c_unconditional_finite` (all but the tiling at a prime) are
jointly satisfiable: n = 21, a = (1, 2, 18) primitive, N = 7 prime, 7 ≡ 3 (mod 4), 7 > 3, and
the Lemma S instance holds there. -/
theorem finite_witness :
    Nat.gcd ((![1, 2, 18] : Fin 3 → ℕ) 0) (Nat.gcd ((![1, 2, 18] : Fin 3 → ℕ) 1)
      ((![1, 2, 18] : Fin 3 → ℕ) 2)) = 1 ∧ (7 : ℕ).Prime ∧ 7 % 4 = 3 ∧ 3 < 7 ∧ (7 : ℕ) ∣ 21 ∧
    relSpace 21 ![1, 2, 18] = trivSpace 21 ![1, 2, 18] :=
  ⟨by decide, by norm_num, by norm_num, by norm_num, by norm_num, lemmaS_finite_witness⟩

/-- **Negative control**: the hypothesis `7 ≤ p` of `LemmaSStatement` cannot be weakened to
`5 ≤ p` — that version is FALSE (tile (1,2,7)/10, `negative_control_n10`).  So the assembly's
use of `N ≥ 7` (from `N ≡ 3 mod 4`, `N > 3`) is load-bearing. -/
theorem lemmaS_five_false :
    ¬ ∀ (n : ℕ) (a : Fin 3 → ℕ), (∀ i, 0 < a i) → ∑ i, a i = n →
      Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1 →
      ∀ p : ℕ, p.Prime → 5 ≤ p → p ∣ n → relSpace n a = trivSpace n a := by
  intro h
  exact negative_control_n10 (h 10 ![1, 2, 7] (by intro i; fin_cases i <;> decide)
    (by simp [Fin.sum_univ_three]) (by decide) 5 (by norm_num) le_rfl (by norm_num))

end Erdos634.CaseA.R0c

#print axioms Erdos634.CaseA.R0c.exists_nat_angles
#print axioms Erdos634.CaseA.R0c.exists_primitive
#print axioms Erdos634.CaseA.R0c.perm_of_counts
#print axioms Erdos634.CaseA.R0c.r0c_core
#print axioms Erdos634.CaseA.R0c.r0c_of_lemmaS
#print axioms Erdos634.CaseA.R0c.r0c_unconditional_finite
#print axioms Erdos634.CaseA.R0c.finite_scope
#print axioms Erdos634.CaseA.R0c.hrat_witness
#print axioms Erdos634.CaseA.R0c.finite_witness
#print axioms Erdos634.CaseA.R0c.lemmaS_five_false

/-
Lemma S, node A5, and Theorem R0c, node A8: **Lemma S for every n** (`LemmaSStatement` of
Draft/CaseAR0c.lean, discharged), and hence **Theorem R0c unconditionally**.

  Lemma S (PROOF_lemmaS.md P2 "Theorem S (Lemma S)"): a_j ≥ 1, Σ a_j = n, gcd(a) = 1, p ≥ 7 a prime
  dividing n ⇒ R(a) = R₀(a).

Proof: write n = p^r·m with p ∤ m (r = v_p(n) ≥ 1).  If m ≢ 2 (mod 4) this is
`LemmaSOddAll.lemmaS_oddAll`; if m ≡ 2 (mod 4) it is `LemmaSEven.lemmaS_even`.

  Theorem R0c (row0c/PROOF_row0c.md §3.7): no prime N ≡ 3 (mod 4), N > 3, is the number of tiles
  of a congruent dissection of a triangle whose tile has all angles in ℚπ.

Proof: `CaseA.R0c.r0c_of_lemmaS` applied to `lemmaS`.

Formalization debt on paper-level nodes (Case A of the prime case); NOT /goal progress: R0c is a
statement about the rational-angle (commensurable) tiles only.  (Header corrected 2026-10-02: this
file is imported into All.lean and by TheoremPConditional/TheoremP6, where `r0c` is node A8 of the
prime proof; the earlier text calling the base-β branch the "open front" and saying "NOT imported"
was stale.  Status: UNAUDITED.)
-/
import Mathlib
import Erdos634.Draft.CaseAR0c
import Erdos634.Draft.LemmaSOddAll
import Erdos634.Draft.LemmaSEven

open scoped BigOperators

namespace Erdos634.LemmaSAll

open Erdos634.LemmaS (relSpace trivSpace)

/-- **Lemma S, for every n** — `LemmaSStatement` exactly as stated in Draft/CaseAR0c.lean. -/
theorem lemmaS : Erdos634.CaseA.R0c.LemmaSStatement := by
  intro n a hpos hsum hgcd p hp hp7 hpn
  haveI : Fact p.Prime := ⟨hp⟩
  have hn0 : n ≠ 0 := by
    have := hpos 0; rw [← hsum, Fin.sum_univ_three]; omega
  obtain ⟨r, m, rfl, hr, hpm, hm0⟩ : ∃ r m : ℕ, n = p ^ r * m ∧ 1 ≤ r ∧ ¬ p ∣ m ∧ m ≠ 0 :=
    ⟨n.factorization p, n / p ^ n.factorization p, (Nat.ordProj_mul_ordCompl_eq_self n p).symm,
      (hp.dvd_iff_one_le_factorization hn0).1 hpn, Nat.not_dvd_ordCompl hp hn0,
      (Nat.ordCompl_pos p hn0).ne'⟩
  haveI : NeZero m := ⟨hm0⟩
  by_cases hm4 : m % 4 = 2
  · exact Erdos634.LemmaSEven.lemmaS_even hp7 hr hpm hm4 a hpos hsum hgcd
  · exact Erdos634.LemmaSOddAll.lemmaS_oddAll hp7 hr hpm hm4 a hpos hsum hgcd

/-- **Theorem R0c, unconditional.** A congruent dissection (reflections allowed, not necessarily
edge-to-edge) of a triangle into N copies of a tile whose angles are all rational multiples of π
has no prime N ≡ 3 (mod 4) with N > 3. -/
theorem r0c {N : ℕ} (D : Erdos634.Geometry.CongruentDissection N)
    (hrat : ∀ k, ∃ q : ℚ, D.model.angleAt k = q * Real.pi)
    (hp : N.Prime) (h4 : N % 4 = 3) (h3 : 3 < N) : False :=
  Erdos634.CaseA.R0c.r0c_of_lemmaS lemmaS D hrat hp h4 h3

/-! ## Witnesses and controls -/

/-- Every hypothesis of `LemmaSStatement` is met, on each branch: odd branch (n = 35, m = 5) and
EVEN branch (n = 70, m = 10; n = 42, m = 6, the finite residue). -/
theorem witness_odd : relSpace 35 ![1, 8, 26] = trivSpace 35 ![1, 8, 26] :=
  lemmaS 35 ![1, 8, 26] (by intro i; fin_cases i <;> decide) (by simp [Fin.sum_univ_three])
    (by decide) 7 (by norm_num) le_rfl (by norm_num)

theorem witness_even : relSpace 70 ![3, 33, 34] = trivSpace 70 ![3, 33, 34] :=
  lemmaS 70 ![3, 33, 34] (by intro i; fin_cases i <;> decide) (by simp [Fin.sum_univ_three])
    (by decide) 7 (by norm_num) le_rfl (by norm_num)

theorem witness_even_finite : relSpace 66 ![5, 23, 38] = trivSpace 66 ![5, 23, 38] :=
  lemmaS 66 ![5, 23, 38] (by intro i; fin_cases i <;> decide) (by simp [Fin.sum_univ_three])
    (by decide) 11 (by norm_num) (by norm_num) (by norm_num)

/-- Every hypothesis of `r0c` except the tiling at a prime is met by a real dissection (the
`CaseALemmaHPiFour` dissection has rational angles); the arithmetic hypotheses N = 7 prime,
7 ≡ 3 (mod 4), 7 > 3 are jointly satisfiable.  (`r0c` concludes False, so no single object can
satisfy all hypotheses at once — that is its content.) -/
theorem witness_r0c_hyps :
    (∀ k, ∃ q : ℚ, Erdos634.Draft.CaseALemmaHPiFour.dissection.model.angleAt k = q * Real.pi) ∧
      (7 : ℕ).Prime ∧ 7 % 4 = 3 ∧ 3 < 7 :=
  ⟨Erdos634.CaseA.R0c.hrat_witness, by norm_num, by norm_num, by norm_num⟩

end Erdos634.LemmaSAll

#print axioms Erdos634.LemmaSAll.lemmaS
#print axioms Erdos634.LemmaSAll.r0c
#print axioms Erdos634.LemmaSAll.witness_odd
#print axioms Erdos634.LemmaSAll.witness_even
#print axioms Erdos634.LemmaSAll.witness_even_finite
#print axioms Erdos634.LemmaSAll.witness_r0c_hyps

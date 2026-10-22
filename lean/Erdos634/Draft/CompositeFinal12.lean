/-
Draft/CompositeFinal12.lean — pair tables (`GapE60`, `GapE120`), the F1 leaves (`GapF1`) and the final chains for the odd squarefree
composites N = 21, 33, 57, 69 (all N ≡ 1 mod 4, 3 ∣ N).  Recipe of CompositeFinal8/9/10.

  N = 57, 69 :  `chain_N_final`  has NO residual hypothesis.
  N = 21     :  residual `S3Closed 21` only  (the base-α member (2,3,4) on the target (12,12,21): the Row-11 equation has the
                arithmetic solution (e,d,m) = (1,1,1); the paper closes it by a 13,659-node search, `isoalpha 21` in data/SETTLED.tsv).
  N = 33     :  residual `GapIsoSporadic33` only  (the 2π/3-isosceles leaf: tile (5,3,7), α opposite 5, target (21,21,33);
                `IsoH9b 33` is FALSE at (a,b,c,k,nA) = (5,3,7,3,−1); the paper closes it by Beeson's cited N < 36 boundary analysis).
  The pair tables are the `CompositeE5Gen` argument (side matching + E7b at the pin); D = (m₁+m₂)²−16N is NEGATIVE for the non-pin
  π/3 pair at all four N, so no `E60Pair` exception arises (contrast N = 87).
*** UNAUDITED.  Formalization debt, NOT /goal progress.  No sorry, no native_decide. ***
-/
import Erdos634.Draft.CompositeFinal11

set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000
set_option maxRecDepth 4000

namespace Erdos634.Draft.CompositeFinal12

section G4
open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.Chain15 Erdos634.Draft.ChainComposite
open Erdos634.Draft.CompositeGen2 Erdos634.Draft.CompositeArith Erdos634.Draft.CompositeS2Arith
open Erdos634.Draft.CompositeS1Arith Erdos634.Draft.CompositeIsoB Erdos634.Draft.CompositeFinal2
open Erdos634.Draft.CompositeFinal3
/-! ## N = 33: the 2π/3-isosceles leaf is a named residual (`IsoH9b 33` is false) -/

/-- **`GapIsoSporadic33`** — the `IsoTP` leaf at N = 33: tile `(α, π/3−α, 2π/3)` (`α ∉ ℚπ`), isosceles target.  The only arithmetic
candidate is the sporadic primitive 120°-triple `(5,3,7)` (`e = a+2b = 11 ∣ 33`), target `(21,21,33)`, base angles `α`. -/
def GapIsoSporadic33 : Prop :=
  ∀ (D : CongruentDissection 33) (α a b c : ℝ), IrrPi α → D.model.TwoPiThreeData α a b c → IsoTP D α → False

open scoped Classical in
/-- `chain_gen3` with the `IsoTP` leaf abstracted (instead of `IsoH9b N`). -/
theorem chain_gen4 (N : ℕ)
    (hsq : Squarefree N)
    (gS1 : S1Closed N) (gS2 : S2Closed N) (gS3 : S3Closed N)
    (gIso : ∀ (D : CongruentDissection N) (α a b c : ℝ), IrrPi α → D.model.TwoPiThreeData α a b c → IsoTP D α → False)
    (gA : GapAcomp N) (gB : CaseBClosed N) (gR : CaseRClosed N) (gG : CaseGClosed N)
    (gE60 : GapE60 N) (gE120 : GapE120 N) (gF1 : GapF1 N) (gR8 : GapR8 N)
    (D : CongruentDissection N) : False := by
  by_cases hA : ∀ k, ∃ q : ℚ, D.model.angleAt k = q * Real.pi
  · exact gA Erdos634.LemmaSAll.lemmaS D hA
  have hirr : ∃ k, IrrPi (D.model.angleAt k) := by
    by_contra hc
    exact hA fun k => by_contra fun hk => hc ⟨k, hk⟩
  by_cases hB : SimilarTM D
  · obtain ⟨μ, τ, hs⟩ := hB
    exact gB D μ τ hs
  rcases Erdos634.Draft.LemmaCFinal.lemmaC_general D hirr hB with hR | hT | hS | hTP | h32
  · exact gR D hR
  · obtain ⟨α, a, b, c, hα, hd, i, j, hij, hi, hj⟩ := hT
    exact gG D α a b c hα hd i j hij hi hj
  · obtain ⟨α, a, b, c, hα, hd⟩ := hS
    exact gE60 D α a b c hα hd (Erdos634.Draft.LemmaPProof.lemmaP_general D α a b c hα hd hB)
  · obtain ⟨α, a, b, c, hα, hd, hsh⟩ := hTP
    rcases hsh with he | hi | hf | hr
    · exact gE120 D α a b c hα hd he
    · exact gIso D α a b c hα hd hi
    · exact gF1 D α a b c hα hd hf
    · exact gR8 D α a b c hα hd hr
  · obtain ⟨α, β, a, b, c, hα, hrel, hd, hsh⟩ := h32
    obtain ⟨σ, m0, o0, m1, o1, m2, o2⟩ := id hd
    have s01 : σ 0 ≠ σ 1 := σ.injective.ne (by decide)
    have s20 : σ 2 ≠ σ 0 := σ.injective.ne (by decide)
    have s21 : σ 2 ≠ σ 1 := σ.injective.ne (by decide)
    rcases hsh with ⟨τ, t0, t1, t2⟩ | ⟨τ, t0, t1, t2⟩ | ⟨τ, t0, t1, t2⟩ | ⟨τ, t0, t1, t2⟩ |
        ⟨τ, t0, t1, t2⟩
    · obtain ⟨r, hr, hb⟩ := Row12.rational_any_label D hα hrel hd
        (τ.injective.ne (by decide : (0 : Fin 3) ≠ 1)) t0 t1
      exact gS1 D α β a b c r hα hrel hd hr hb ⟨τ, t0, t1, t2⟩
    · obtain ⟨r, hr, hb⟩ := Row13.rational_any_label D hα hrel hd
        (τ.injective.ne (by decide : (0 : Fin 3) ≠ 1)) t0 t1
      exact not_baseBetaTiled (Erdos634.Draft.RASquarefree.raStatement_sqfree N D hsq α β a b c r hα hrel hd hr hb
        ⟨τ, t0, t1, t2⟩)
    · obtain ⟨r, hr⟩ := Row14.rational_any_label D α β hα hrel s01 s20 s21 m0 m1
        (τ.injective.ne (by decide : (0 : Fin 3) ≠ 1)) t0 t1
      rw [o0, o2] at hr
      exact not_baseBetaTiled (Erdos634.Draft.RWSquarefree.rwStatement_sqfree N D hsq α β a b c r hα hrel hd hr
        (Rows11_13AnyLabel.b_of_rational hrel hd hr) ⟨τ, t0, t1, t2⟩)
    · obtain ⟨r, hr, -⟩ := Row15.rational_any_label D α β hα hrel s01 s20 s21 m0 m1
        (τ.injective.ne (by decide : (0 : Fin 3) ≠ 1)) t0 t1
      rw [o0, o2] at hr
      exact gS2 D α β a b c r hα hrel hd hr
        (Rows11_13AnyLabel.b_of_rational hrel hd hr) ⟨τ, t0, t1, t2⟩
    · exact gS3 D α β a b c hα hrel hd (τ 0) (τ 1)
        (τ.injective.ne (by decide : (0 : Fin 3) ≠ 1)) t0 t1


end G4

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.Chain15 Erdos634.Draft.ChainComposite
open Erdos634.Draft.CompositeGen2 Erdos634.Draft.CompositeArith Erdos634.Draft.CompositeS2Arith
open Erdos634.Draft.CompositeS1Arith Erdos634.Draft.CompositeIsoB Erdos634.Draft.CompositeFinal2
open Erdos634.Draft.CompositeFinal3 Erdos634.Draft.CompositeFinal6 Erdos634.Draft.CompositeFinal11
open Erdos634.Draft.CompositeE5Gen Erdos634.Draft.CompositeF1Gen Erdos634.Draft.F1KappaSide

/-! ## N = 21 -/
theorem pairs120_21 : ∀ s t : ℤ, 1 ≤ s → s ≤ ((21 : ℕ) : ℤ) → 1 ≤ t → t ≤ ((21 : ℕ) : ℤ) → s * t = 3 * ((21 : ℕ) : ℤ) →
    ¬ IsSquare ((t - s) ^ 2 + 16 * ((21 : ℕ) : ℤ)) ∧ ∀ r : ℤ, 0 ≤ r → 2 * ((21 : ℕ) : ℤ) ≠ r * (s + t) := by
  intro s t h1 h2 h3 h4 h5
  push_cast at *
  interval_cases s <;>
    first
    | (exfalso; omega)
    | (interval_cases t <;> first | (exfalso; omega) | exact ⟨by decide +kernel, fun r hr => by omega⟩)

theorem gapE120_21 : GapE120 21 := gapE120_of_pairs 21 (by norm_num) pairs120_21

theorem pairs60_21 : ∀ m₁ m₂ : ℤ, 1 ≤ m₁ → m₁ ≤ ((21 : ℕ) : ℤ) → 1 ≤ m₂ → m₂ ≤ ((21 : ℕ) : ℤ) →
    m₁ * m₂ = 3 * ((21 : ℕ) : ℤ) → m₂ < m₁ →
    (m₁ = ((21 : ℕ) : ℤ) ∧ m₂ = 3) ∨ (¬ IsSquare ((m₁ + m₂) ^ 2 - 16 * ((21 : ℕ) : ℤ)) ∧
      (0 ≤ (m₁ + m₂) ^ 2 - 16 * ((21 : ℕ) : ℤ) →
        ∀ p r : ℤ, 0 ≤ p → 0 ≤ r → 2 * ((21 : ℕ) : ℤ) ≠ p * (m₁ + m₂) + r * (m₁ - m₂))) := by
  intro m₁ m₂ h1 h2 h3 h4 h5 h6
  push_cast at *
  interval_cases m₁ <;>
    first
    | (exfalso; omega)
    | (interval_cases m₂ <;> first | (exfalso; omega) | (left; omega) |
        (right; exact ⟨by decide +kernel, fun hnn p r hp hr => by
          first | (exfalso; norm_num at hnn; done) | omega⟩))

theorem gapE60_21 : GapE60 21 := gapE60_of_pairs 21 (by norm_num) pairs60_21

theorem f1MaGt1_21 : F1MaGt1 21 := by
  refine f1MaGt1_of_list 21 ?_
  intro Ma Mb h1 h2 h3
  have hMa : Ma ≤ 9 := by nlinarith
  interval_cases Ma <;> first | (exfalso; omega) | skip
  obtain rfl : Mb = 7 := by omega
  exact ⟨2, by norm_num, by norm_num, by decide +kernel, by norm_num⟩

theorem gapF1_21 : GapF1 21 := gapF1_of_MaGt1 21 (by norm_num) f1MaGt1_21

/-! ## N = 33 -/
theorem pairs120_33 : ∀ s t : ℤ, 1 ≤ s → s ≤ ((33 : ℕ) : ℤ) → 1 ≤ t → t ≤ ((33 : ℕ) : ℤ) → s * t = 3 * ((33 : ℕ) : ℤ) →
    ¬ IsSquare ((t - s) ^ 2 + 16 * ((33 : ℕ) : ℤ)) ∧ ∀ r : ℤ, 0 ≤ r → 2 * ((33 : ℕ) : ℤ) ≠ r * (s + t) := by
  intro s t h1 h2 h3 h4 h5
  push_cast at *
  interval_cases s <;>
    first
    | (exfalso; omega)
    | (interval_cases t <;> first | (exfalso; omega) | exact ⟨by decide +kernel, fun r hr => by omega⟩)

theorem gapE120_33 : GapE120 33 := gapE120_of_pairs 33 (by norm_num) pairs120_33

theorem pairs60_33 : ∀ m₁ m₂ : ℤ, 1 ≤ m₁ → m₁ ≤ ((33 : ℕ) : ℤ) → 1 ≤ m₂ → m₂ ≤ ((33 : ℕ) : ℤ) →
    m₁ * m₂ = 3 * ((33 : ℕ) : ℤ) → m₂ < m₁ →
    (m₁ = ((33 : ℕ) : ℤ) ∧ m₂ = 3) ∨ (¬ IsSquare ((m₁ + m₂) ^ 2 - 16 * ((33 : ℕ) : ℤ)) ∧
      (0 ≤ (m₁ + m₂) ^ 2 - 16 * ((33 : ℕ) : ℤ) →
        ∀ p r : ℤ, 0 ≤ p → 0 ≤ r → 2 * ((33 : ℕ) : ℤ) ≠ p * (m₁ + m₂) + r * (m₁ - m₂))) := by
  intro m₁ m₂ h1 h2 h3 h4 h5 h6
  push_cast at *
  interval_cases m₁ <;>
    first
    | (exfalso; omega)
    | (interval_cases m₂ <;> first | (exfalso; omega) | (left; omega) |
        (right; exact ⟨by decide +kernel, fun hnn p r hp hr => by
          first | (exfalso; norm_num at hnn; done) | omega⟩))

theorem gapE60_33 : GapE60 33 := gapE60_of_pairs 33 (by norm_num) pairs60_33

theorem f1MaGt1_33 : F1MaGt1 33 := by
  refine f1MaGt1_of_list 33 ?_
  intro Ma Mb h1 h2 h3
  have hMa : Ma ≤ 9 := by nlinarith
  interval_cases Ma <;> first | (exfalso; omega) | skip
  obtain rfl : Mb = 11 := by omega
  exact ⟨4, by norm_num, by norm_num, by decide +kernel, by norm_num⟩

theorem gapF1_33 : GapF1 33 := gapF1_of_MaGt1 33 (by norm_num) f1MaGt1_33

/-! ## N = 57 -/
theorem pairs120_57 : ∀ s t : ℤ, 1 ≤ s → s ≤ ((57 : ℕ) : ℤ) → 1 ≤ t → t ≤ ((57 : ℕ) : ℤ) → s * t = 3 * ((57 : ℕ) : ℤ) →
    ¬ IsSquare ((t - s) ^ 2 + 16 * ((57 : ℕ) : ℤ)) ∧ ∀ r : ℤ, 0 ≤ r → 2 * ((57 : ℕ) : ℤ) ≠ r * (s + t) := by
  intro s t h1 h2 h3 h4 h5
  push_cast at *
  interval_cases s <;>
    first
    | (exfalso; omega)
    | (interval_cases t <;> first | (exfalso; omega) | exact ⟨by decide +kernel, fun r hr => by omega⟩)

theorem gapE120_57 : GapE120 57 := gapE120_of_pairs 57 (by norm_num) pairs120_57

theorem pairs60_57 : ∀ m₁ m₂ : ℤ, 1 ≤ m₁ → m₁ ≤ ((57 : ℕ) : ℤ) → 1 ≤ m₂ → m₂ ≤ ((57 : ℕ) : ℤ) →
    m₁ * m₂ = 3 * ((57 : ℕ) : ℤ) → m₂ < m₁ →
    (m₁ = ((57 : ℕ) : ℤ) ∧ m₂ = 3) ∨ (¬ IsSquare ((m₁ + m₂) ^ 2 - 16 * ((57 : ℕ) : ℤ)) ∧
      (0 ≤ (m₁ + m₂) ^ 2 - 16 * ((57 : ℕ) : ℤ) →
        ∀ p r : ℤ, 0 ≤ p → 0 ≤ r → 2 * ((57 : ℕ) : ℤ) ≠ p * (m₁ + m₂) + r * (m₁ - m₂))) := by
  intro m₁ m₂ h1 h2 h3 h4 h5 h6
  push_cast at *
  interval_cases m₁ <;>
    first
    | (exfalso; omega)
    | (interval_cases m₂ <;> first | (exfalso; omega) | (left; omega) |
        (right; exact ⟨by decide +kernel, fun hnn p r hp hr => by
          first | (exfalso; norm_num at hnn; done) | omega⟩))

theorem gapE60_57 : GapE60 57 := gapE60_of_pairs 57 (by norm_num) pairs60_57

theorem f1MaGt1_57 : F1MaGt1 57 := by
  refine f1MaGt1_of_list 57 ?_
  intro Ma Mb h1 h2 h3
  have hMa : Ma ≤ 9 := by nlinarith
  interval_cases Ma <;> first | (exfalso; omega) | skip
  obtain rfl : Mb = 19 := by omega
  exact ⟨8, by norm_num, by norm_num, by decide +kernel, by norm_num⟩

theorem gapF1_57 : GapF1 57 := gapF1_of_MaGt1 57 (by norm_num) f1MaGt1_57

/-! ## N = 69 -/
theorem pairs120_69 : ∀ s t : ℤ, 1 ≤ s → s ≤ ((69 : ℕ) : ℤ) → 1 ≤ t → t ≤ ((69 : ℕ) : ℤ) → s * t = 3 * ((69 : ℕ) : ℤ) →
    ¬ IsSquare ((t - s) ^ 2 + 16 * ((69 : ℕ) : ℤ)) ∧ ∀ r : ℤ, 0 ≤ r → 2 * ((69 : ℕ) : ℤ) ≠ r * (s + t) := by
  intro s t h1 h2 h3 h4 h5
  push_cast at *
  interval_cases s <;>
    first
    | (exfalso; omega)
    | (interval_cases t <;> first | (exfalso; omega) | exact ⟨by decide +kernel, fun r hr => by omega⟩)

theorem gapE120_69 : GapE120 69 := gapE120_of_pairs 69 (by norm_num) pairs120_69

theorem pairs60_69 : ∀ m₁ m₂ : ℤ, 1 ≤ m₁ → m₁ ≤ ((69 : ℕ) : ℤ) → 1 ≤ m₂ → m₂ ≤ ((69 : ℕ) : ℤ) →
    m₁ * m₂ = 3 * ((69 : ℕ) : ℤ) → m₂ < m₁ →
    (m₁ = ((69 : ℕ) : ℤ) ∧ m₂ = 3) ∨ (¬ IsSquare ((m₁ + m₂) ^ 2 - 16 * ((69 : ℕ) : ℤ)) ∧
      (0 ≤ (m₁ + m₂) ^ 2 - 16 * ((69 : ℕ) : ℤ) →
        ∀ p r : ℤ, 0 ≤ p → 0 ≤ r → 2 * ((69 : ℕ) : ℤ) ≠ p * (m₁ + m₂) + r * (m₁ - m₂))) := by
  intro m₁ m₂ h1 h2 h3 h4 h5 h6
  push_cast at *
  interval_cases m₁ <;>
    first
    | (exfalso; omega)
    | (interval_cases m₂ <;> first | (exfalso; omega) | (left; omega) |
        (right; exact ⟨by decide +kernel, fun hnn p r hp hr => by
          first | (exfalso; norm_num at hnn; done) | omega⟩))

theorem gapE60_69 : GapE60 69 := gapE60_of_pairs 69 (by norm_num) pairs60_69

theorem f1MaGt1_69 : F1MaGt1 69 := by
  refine f1MaGt1_of_list 69 ?_
  intro Ma Mb h1 h2 h3
  have hMa : Ma ≤ 9 := by nlinarith
  interval_cases Ma <;> first | (exfalso; omega) | skip
  obtain rfl : Mb = 23 := by omega
  exact ⟨10, by norm_num, by norm_num, by decide +kernel, by norm_num⟩

theorem gapF1_69 : GapF1 69 := gapF1_of_MaGt1 69 (by norm_num) f1MaGt1_69

/-! ## Final theorems -/

/-- **N = 57: no residual hypothesis.** -/
theorem chain_57_final (D : CongruentDissection 57) : False := chain_cond_57 gapE60_57 gapE120_57 gapF1_57 D
/-- **N = 69: no residual hypothesis.** -/
theorem chain_69_final (D : CongruentDissection 69) : False := chain_cond_69 gapE60_69 gapE120_69 gapF1_69 D
/-- **N = 21, modulo `S3Closed 21`** (the base-α member `(2,3,4)` on `(12,12,21)`). -/
theorem chain_21_final (gS3 : S3Closed 21) (D : CongruentDissection 21) : False :=
  chain_cond_21 gS3 gapE60_21 gapE120_21 gapF1_21 D
/-- **N = 33, modulo `GapIsoSporadic33`** (tile `(5,3,7)`, target `(21,21,33)`). -/
theorem chain_33_final (gI : GapIsoSporadic33) (D : CongruentDissection 33) : False :=
  chain_gen4 33 sqfree_33 s1Closed_33 s2Closed_33 (s3Closed_of_isoQRef 33 isoQRef_33) (fun D α a b c h1 h2 h3 => gI D α a b c h1 h2 h3)
    gapAcomp_33 caseB_33 caseR_33 gamma_33 gapE60_33 gapE120_33 gapF1_33 gapR8_33 D

/-! ## S1 at every squarefree N: `3q²−p² = 4N` is impossible for coprime p, q (mod 4), so `s1_arith_gen` needs no finite check -/

theorem three_sq_sub_ne_four_mul (N : ℤ) (p q : ℤ) (hcop : IsCoprime p q) : 3 * q ^ 2 - p ^ 2 ≠ 4 * N := by
  intro h
  obtain ⟨u, v, huv⟩ := hcop
  rcases Int.even_or_odd' p with ⟨a, ha | ha⟩ <;> rcases Int.even_or_odd' q with ⟨b, hb | hb⟩
  · subst ha; subst hb
    have : 2 * (u * a + v * b) = 1 := by linear_combination huv
    omega
  · subst ha; subst hb
    have : 3 * (2 * b + 1) ^ 2 - (2 * a) ^ 2 = 4 * (3 * b ^ 2 + 3 * b - a ^ 2) + 3 := by ring
    omega
  · subst ha; subst hb
    have : 3 * (2 * b) ^ 2 - (2 * a + 1) ^ 2 = 4 * (3 * b ^ 2 - a ^ 2 - a - 1) + 3 := by ring
    omega
  · subst ha; subst hb
    have : 3 * (2 * b + 1) ^ 2 - (2 * a + 1) ^ 2 = 4 * (3 * b ^ 2 + 3 * b - a ^ 2 - a) + 2 := by ring
    omega

/-- **S1 arithmetic at every squarefree N** (N-uniform strengthening of `CompositeFinal11.s1_arith_gen`). -/
theorem s1_arith_sqfree (N : ℕ) (hsq : Squarefree N) (hN0 : 0 < N) :
    ∀ p q M : ℤ, 0 < p → p < q → IsCoprime p q → 0 < M →
    (N : ℤ) * (p + q) ^ 2 = M ^ 2 * (3 * q ^ 2 - p ^ 2) → M = p + q :=
  s1_arith_gen N hsq hN0 (fun p q _ _ hc h => three_sq_sub_ne_four_mul (N : ℤ) p q hc h)

/-- Negative control for the N-free pair tables: the F1 pair list of `CompositeFinal9` FAILS at N = 105 (see `CompositeFinal9.not_f1list_105`);
here, `S1Arith` has genuine solutions (so the I6 route, not an arithmetic contradiction, is what closes S1): N = 39, (p,q,M) = (3,4,7). -/
theorem s1_solution_exists_39 : ∃ p q M : ℤ, 0 < p ∧ p < q ∧ IsCoprime p q ∧ 0 < M ∧ (39 : ℤ) * (p + q) ^ 2 = M ^ 2 * (3 * q ^ 2 - p ^ 2) :=
  ⟨3, 4, 7, by norm_num, by norm_num, by rw [Int.isCoprime_iff_gcd_eq_one]; decide, by norm_num, by norm_num⟩

end Erdos634.Draft.CompositeFinal12

#print axioms Erdos634.Draft.CompositeFinal12.gapE60_21
#print axioms Erdos634.Draft.CompositeFinal12.gapE120_21
#print axioms Erdos634.Draft.CompositeFinal12.gapF1_21
#print axioms Erdos634.Draft.CompositeFinal12.gapE60_33
#print axioms Erdos634.Draft.CompositeFinal12.gapE120_33
#print axioms Erdos634.Draft.CompositeFinal12.gapF1_33
#print axioms Erdos634.Draft.CompositeFinal12.gapE60_57
#print axioms Erdos634.Draft.CompositeFinal12.gapE120_57
#print axioms Erdos634.Draft.CompositeFinal12.gapF1_57
#print axioms Erdos634.Draft.CompositeFinal12.gapE60_69
#print axioms Erdos634.Draft.CompositeFinal12.gapE120_69
#print axioms Erdos634.Draft.CompositeFinal12.gapF1_69
#print axioms Erdos634.Draft.CompositeFinal12.chain_gen4
#print axioms Erdos634.Draft.CompositeFinal12.three_sq_sub_ne_four_mul
#print axioms Erdos634.Draft.CompositeFinal12.s1_arith_sqfree
#print axioms Erdos634.Draft.CompositeFinal12.s1_solution_exists_39
#print axioms Erdos634.Draft.CompositeFinal12.chain_57_final
#print axioms Erdos634.Draft.CompositeFinal12.chain_69_final
#print axioms Erdos634.Draft.CompositeFinal12.chain_21_final
#print axioms Erdos634.Draft.CompositeFinal12.chain_33_final

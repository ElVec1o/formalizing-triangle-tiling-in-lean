/-
Draft/ChainComposite.lean — the primality-free dispatch of Theorem P generalised from `Chain15.chain_conditional`
so that EVERY branch whose Lean proof is prime-specific or parity-specific becomes an explicit named `Prop`
(a `…Closed` hypothesis), with the helper lemmas that discharge it WHEN the arithmetic of N allows.

*** THIS IS NOT A PROOF THAT ANY COMPOSITE N IS NOT A TILE COUNT. ***  `chain_conditional_gen` is a conditional:
it composes already-proved leaves with the residual hypotheses listed below.  UNAUDITED.  Formalization debt, NOT
/goal progress.  No `sorry`, no `native_decide`.

Branches of the case tree (PRIME_CASE_PROOF.md §2), the Lean leaf that closes each, and the residual `Prop`:

  Case A (all angles in ℚπ)          `GapA N`                       residual (no composite Lean; Lemma S, N-free, is proved)
  Case B (target ~ tile)             `CaseBClosed N`                helpers `caseB_of_mod4_three` (Row2 sqfree, N ≡ 3 mod 4)
                                                                    and `caseB_of_sumsq` (hyp `HBSimilar N`; proved for squarefree N ≥ 17, CaseAComposite)
  Case C, Lemma C                    `LemmaCFinal.lemmaC_general`   Lean, no primality
   right tile                        `CaseRClosed N`                helpers `caseR_of_odd` (Row3, N odd) and
                                                                    `caseR_of_H1` (hyp `H1Right N`; now PROVED as `H1k.h1Right`, H1kFinal)
   γ = 2α                            `CaseGClosed N`                helpers `caseG_of_M1Div` (Row4.not_M1) and
                                                                    `caseG_of_mod4_two` (Row4.not_two_mod_four)
   π/3                               `LemmaPProof.lemmaP_general` + `GapE60 N`; helper `gapE60_of_mod4_two`
   2π/3 equilateral                  `GapE120 N`;                    helper `gapE120_of_mod4_two`
   2π/3 isosceles                    `ThmIsoH9.thmIso_H9`           hyp `IsoH9 N`
   2π/3 F1/F1'                       `GapF1 N`;                      helper `gapF1_of_mod4_two`
   2π/3 F2-F4'                       `GapR8 N`                       residual
   3α+2β: S1 (β,β,3α)                `ScaleBaseBetaQNR.scaleBaseBeta_qnr`   hyp: prime ℓ, odd val, 3 non-residue
          S2 (2α,α,2β)               `RMinus4QNR.rMinus4_qnr`               hyp: 2 and 3 non-residues mod ℓ
          S3 (α,α,α+2β)              `Row11IsoQ`                            hyp `IsoQDvd N`
          S4 (2α,β,α+β)              `RWSquarefree.rwStatement_sqfree` + I6 hyp `Squarefree N`
          S5 (α+β,α+β,α)             `RASquarefree.raStatement_sqfree` + I6 hyp `Squarefree N`
-/
import Erdos634.Draft.Chain15
import Erdos634.Draft.F1Bridge
import Erdos634.Draft.F1AreaIdentity
import Erdos634.Draft.F1AlgebraReal
import Erdos634.Draft.FluxPaper
import Erdos634.Draft.FluxE2Pi3Row7
import Erdos634.Draft.FluxDRow4
import Erdos634.Draft.FluxDRow4M1AnyLabel
import Erdos634.Draft.LemmaSAll

open scoped Classical

namespace Erdos634.Draft.ChainComposite

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.Chain15

/-! ## Named residual hypotheses -/

/-- **GapAcomp N — Case A at composite N.**  `LemmaSStatement` (Lemma S) is PROVED in Lean
(`LemmaSAll.lemmaS`, N-free) and is supplied as the premise; the residual is the rest of `r0c_core` at composite N:
Lemma V (`N ∣ n`, `CaseA.LemmaV.lemmaV_prime` is prime-only), Lemma K/K*, Lemma F, Lemma H exit, and the Similar exit
(= Case B).  STATUS: paper-level PROVED for N with an odd-valuation prime ℓ ≥ 7 (Lemma S route) / cited
[BeesonSeven Thm 3] otherwise; NO Lean at composite N.  Cheapest discharge: SCOPE_composites_lean §4 item S-A. -/
def GapAcomp (N : ℕ) : Prop := Erdos634.CaseA.R0c.LemmaSStatement → GapA N

/-- **CaseBClosed N** — target similar to the tile (`ABC ~ T`, some vertex correspondence, scale μ) is impossible. -/
def CaseBClosed (N : ℕ) : Prop :=
  ∀ (D : CongruentDissection N) (μ : ℝ) (τ : Equiv.Perm (Fin 3)),
    (∀ k, D.target.angleAt k = D.model.angleAt (τ k) ∧ D.target.oppLen k = μ * D.model.oppLen (τ k)) → False

/-- **HBSimilar N — similar-tile case N-form (Prop; proved for squarefree N ≥ 17).**  If the target is similar to the tile, then N is a sum of two squares (`N = n²` included as `y = 0`).  Source: paper `erdos-634.tex` l.440-441,
l.1055 "right-angle and similar-tile cases give N a sum of two squares or N = n²", citing [BeesonI, SWW 1991 Disc. Math.
91]; the paper gives it no `\label` and no proof; SWW unread (SCOPE_H1_right_tile §1).  STATUS: the Prop carries no irrationality hypothesis; proved in Lean for squarefree N ≥ 17 (CaseAComposite); the paper citation is unread.  (Lean: `Row2.theoremS_perm_sqfree` proves only `N % 4 ≠ 3`, i.e. closes the branch for N ≡ 3 mod 4
squarefree and is VACUOUS at N ≡ 2 mod 4.)  Cheapest discharge: SCOPE_composites_lean §4 item S-B (Lemma Q at the
squarefree part), 150-300 lines, medium risk, unverified. -/
def HBSimilar (N : ℕ) : Prop :=
  ∀ (D : CongruentDissection N) (μ : ℝ) (τ : Equiv.Perm (Fin 3)),
    (∀ k, D.target.angleAt k = D.model.angleAt (τ k) ∧ D.target.oppLen k = μ * D.model.oppLen (τ k)) →
    ∃ x y : ℕ, N = x ^ 2 + y ^ 2

/-- **CaseRClosed N** — the right-tile / isosceles-target branch (`RightCase D`) is impossible. -/
def CaseRClosed (N : ℕ) : Prop := ∀ D : CongruentDissection N, RightCase D → False

/-- **H1Right N — right tile N-form (now PROVED: `Erdos634.Draft.H1k.h1Right`, H1kFinal).**  A right tile with irrational acute angle dissecting an isosceles
target (`RightCase`) forces `N = 2λ²` with `N/2` a sum of two squares (`N = 2m²` included as `y = 0`).  Source:
[BeesonI Thm 4(v)], resting on BeesonI Thm 3 / Lemma 21 (field theory + sweep; unrevised 2012 preprint).  STATUS: PROVED in Lean as `H1k.h1Right` (H1kFinal; the original citation below is historical).
Historically Lean had only: `Row3.RP.row3_RP_even_any_label` (`Even N`, VACUOUS at even N) and `row3_RP_area_any_label`
(`N = 2λ²`, λ real).  SCOPE_H1_right_tile §3: the s = 0, y ≠ 0, λ-irrational residue ("lemma (R)") is NOT excluded by the
flux identity (e.g. N = 10, λ = √5 and N = 20, λ = √10 are real tilings).  Cheapest discharge: UNKNOWN, large. -/
def H1Right (N : ℕ) : Prop :=
  ∀ D : CongruentDissection N, RightCase D → ∃ x y : ℕ, N = 2 * (x ^ 2 + y ^ 2)

/-- **CaseGClosed N** — the `γ = 2α` tile with isosceles target (base angles α) is impossible. -/
def CaseGClosed (N : ℕ) : Prop :=
  ∀ (D : CongruentDissection N) (α a b c : ℝ), IrrPi α → D.model.TwoAlphaData α a b c →
    ∀ i j : Fin 3, i ≠ j → D.target.angleAt i = α → D.target.angleAt j = α → False

/-! ## Case B helpers -/

/-- Case B for squarefree `N ≥ 7`, `N ≡ 3 (mod 4)`: `Row2.theoremS_perm_sqfree`. -/
theorem caseB_of_mod4_three (N : ℕ) (hsq : Squarefree N) (h7 : 7 ≤ N) (h4 : N % 4 = 3) : CaseBClosed N := by
  intro D μ τ hs
  have := Row2.theoremS_perm_sqfree D μ τ hs hsq h7
  omega

/-- Case B from the cited N-form `HBSimilar N` plus the arithmetic fact that N is not a sum of two squares. -/
theorem caseB_of_sumsq (N : ℕ) (hB : HBSimilar N) (hns : ¬ ∃ x y : ℕ, N = x ^ 2 + y ^ 2) : CaseBClosed N :=
  fun D μ τ hs => hns (hB D μ τ hs)

/-! ## Right-tile helpers -/

/-- Right tile for odd `N`: `Row3.RP.row3_RP_even_any_label` gives `Even N`. -/
theorem caseR_of_odd (N : ℕ) (hodd : N % 2 = 1) : CaseRClosed N := by
  intro D hR
  obtain ⟨α, h0, h2, hi, ⟨p, q, hpq, hp, hq⟩, γ, hγ, i, j, hij, hi', hj'⟩ := hR
  obtain ⟨m, hm⟩ := Row3.RP.row3_RP_even_any_label D h0 h2 hi hpq hp hq hγ hij hi' hj'
  omega

/-- Right tile from the cited `H1Right N` plus: `N/2` is not a sum of two squares. -/
theorem caseR_of_H1 (N : ℕ) (hH1 : H1Right N) (hns : ¬ ∃ x y : ℕ, N = 2 * (x ^ 2 + y ^ 2)) : CaseRClosed N :=
  fun D hR => hns (hH1 D hR)

/-! ## γ = 2α helpers -/

private theorem cA'' (p q r : Plane) : cornerAngle p q r = cornerAngle r q p :=
  EuclideanGeometry.angle_comm (V := Plane) p q r

/-- `γ = 2α`, `M1Div N`: any-label form of `Row4.not_M1` (`FluxDRow4M1AnyLabel.Row4.not_M1_any_label`). -/
theorem caseG_of_M1Div (N : ℕ) (hM1 : M1Div N) : CaseGClosed N := by
  intro D α a b c hα hd i j hij hi hj
  exact Row4.not_M1_any_label D hα hd hij hi hj hM1

/-- **`γ = 2α` at `N ≡ 2 (mod 4)`**: any-label form of `Row4.not_two_mod_four` (R4(iii), N-free; `M ≡ M′ ≡ N mod 2`
forces `4 ∣ N`).  Proof pattern copied from `Row4.not_M1_any_label` (the three unordered α-pair positions). -/
theorem caseG_of_mod4_two (N : ℕ) (h4 : N % 4 = 2) : CaseGClosed N := by
  intro D α a b c hα h i j hij hi hj
  have key : ∀ σ : Equiv.Perm (Fin 3),
      (D.relabelTarget' σ).target.angleAt 0 = α → (D.relabelTarget' σ).target.angleAt 1 = α → False :=
    fun σ h0 h1 => Row4.not_two_mod_four (D.relabelTarget' σ) hα h h0 h1 h4
  have p01 : D.target.angleAt 0 = α → D.target.angleAt 1 = α → False := fun h0 h1 =>
    key 1 (by simpa [CongruentDissection.relabelTarget', Erdos634.NormalPosition.relabelTri,
        Tri.angleAt] using h0)
      (by simpa [CongruentDissection.relabelTarget', Erdos634.NormalPosition.relabelTri,
        Tri.angleAt] using h1)
  have p02 : D.target.angleAt 0 = α → D.target.angleAt 2 = α → False := fun h0 h2 =>
    key (Equiv.swap 1 2)
      (by
        have := h0; simp only [Tri.angleAt] at this ⊢
        simp [CongruentDissection.relabelTarget', Erdos634.NormalPosition.relabelTri,
          Equiv.swap_apply_of_ne_of_ne] at this ⊢
        rw [cA'']; simpa using this)
      (by
        have := h2; simp only [Tri.angleAt] at this ⊢
        simp [CongruentDissection.relabelTarget', Erdos634.NormalPosition.relabelTri,
          Equiv.swap_apply_of_ne_of_ne] at this ⊢
        rw [cA'']; simpa using this)
  have p12 : D.target.angleAt 1 = α → D.target.angleAt 2 = α → False := fun h1 h2 =>
    key (Equiv.swap 0 2)
      (by
        have := h2; simp only [Tri.angleAt] at this ⊢
        simp [CongruentDissection.relabelTarget', Erdos634.NormalPosition.relabelTri,
          Equiv.swap_apply_of_ne_of_ne] at this ⊢
        rw [cA'']; simpa using this)
      (by
        have := h1; simp only [Tri.angleAt] at this ⊢
        simp [CongruentDissection.relabelTarget', Erdos634.NormalPosition.relabelTri,
          Equiv.swap_apply_of_ne_of_ne] at this ⊢
        rw [cA'']; simpa using this)
  fin_cases i <;> fin_cases j <;> simp at hij
  all_goals first
    | exact p01 hi hj | exact p01 hj hi | exact p02 hi hj | exact p02 hj hi
    | exact p12 hi hj | exact p12 hj hi

/-! ## Equilateral-target helpers at `N ≡ 2 (mod 4)` (Theorem E pins, parity) -/

/-- two even integers cannot multiply to `3N` when `N ≡ 2 (mod 4)`. -/
theorem even_prod_contra (N : ℕ) (h4 : N % 4 = 2) (s t : ℤ) (hs : (2 : ℤ) ∣ s - N) (ht : (2 : ℤ) ∣ t - N)
    (hp : s * t = 3 * (N : ℤ)) : False := by
  have hN2 : (2 : ℤ) ∣ (N : ℤ) := by omega
  obtain ⟨u, hu⟩ : (2 : ℤ) ∣ s := by
    have := dvd_add hs hN2; rwa [sub_add_cancel] at this
  obtain ⟨v, hv⟩ : (2 : ℤ) ∣ t := by
    have := dvd_add ht hN2; rwa [sub_add_cancel] at this
  obtain ⟨w, hw⟩ : ∃ w, u * v = w := ⟨_, rfl⟩
  have : 3 * (N : ℤ) = 4 * w := by rw [← hp, hu, hv, ← hw]; ring
  omega

/-- `π/3` tile, equilateral target, `N ≡ 2 (mod 4)`: `Row5.theoremE_sixty` gives `m₁ m₂ = 3N`, `m₁ ≡ m₂ ≡ N (2)`. -/
theorem gapE60_of_mod4_two (N : ℕ) (h4 : N % 4 = 2) : GapE60 N := by
  intro D α a b c hα hd hE
  obtain ⟨m₁, m₂, h1, h2, -, -, -, -, -, -, -, hp, -⟩ := Row5.theoremE_sixty D hα hd hE
  exact even_prod_contra N h4 m₁ m₂ h1 h2 hp

/-- `2π/3` tile, equilateral target, `N ≡ 2 (mod 4)`: `Row5.theoremE_twoPiThree` gives `s t = 3N`, `s ≡ t ≡ N (2)`. -/
theorem gapE120_of_mod4_two (N : ℕ) (h4 : N % 4 = 2) : GapE120 N := by
  intro D α a b c hα hd hE
  obtain ⟨s, t, h1, h2, -, -, -, -, -, -, -, hp, -⟩ := Row5.theoremE_twoPiThree D hα hd hE
  exact even_prod_contra N h4 s t h1 h2 hp

/-! ## F1 at `N ≡ 2 (mod 4)` (cor:int parity + product `Mα Mβ = ±N`) -/

private theorem twoPiThree_c_sq'' (T : Tri) {α a b c : ℝ} (h : T.TwoPiThreeData α a b c) :
    c ^ 2 = a ^ 2 + a * b + b ^ 2 := by
  obtain ⟨σ, -, ha, -, hb, hγ, hc⟩ := h
  have hl := T.lawCos_perm σ
  rw [ha, hb, hc, hγ,
      show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three] at hl
  linarith

/-- **F1 / F1′ data at `N ≡ 2 (mod 4)`.**  `Paper.cor_int` gives integers `Mα ≡ Mβ ≡ N (mod 2)`; the area identity
`N b = μ²(a+b)` with the two flux equations (`Row7.lemmaW_*`, either sign) gives `Mα Mβ = ±N`
(`F1AlgebraReal.F1_product_real`).  Both factors even ⇒ `4 ∣ N`. -/
theorem f1_parity_mod4_two {N : ℕ} (h4 : N % 4 = 2) (D : CongruentDissection N) {α a b c μ : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hm : D.model.TwoPiThreeData α a b c)
    (hF1 : D.target.F1Data α a b c μ) (hμ : 0 < μ) : False := by
  obtain ⟨-, hc0, ha0, hb0⟩ := cos_alpha_of_TwoPiThree D.model hm
  have hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2 := twoPiThree_c_sq'' D.model hm
  have hN_b : (N : ℝ) * b = μ ^ 2 * (a + b) :=
    Erdos634.Draft.F1AreaIdentity.F1_area_identity D hm hF1 ha0 hb0 hμ
  obtain ⟨Mα, Mβ, hpα, hpβ, hcα, hcβ⟩ := Paper.cor_int D hα hm
  have hWα := Row7.lemmaW_alpha D.target hα hF1
  have hWβ := Row7.lemmaW_beta D.target hα hF1
  have hN2 : (2 : ℤ) ∣ (N : ℤ) := by omega
  obtain ⟨u, hu⟩ : (2 : ℤ) ∣ Mα := by
    have := dvd_add hpα hN2; rwa [sub_add_cancel] at this
  obtain ⟨v, hv⟩ : (2 : ℤ) ∣ Mβ := by
    have := dvd_add hpβ hN2; rwa [sub_add_cancel] at this
  obtain ⟨w, hw⟩ : ∃ w, u * v = w := ⟨_, rfl⟩
  have h4w : Mα * Mβ = 4 * w := by rw [hu, hv, ← hw]; ring
  have hfin : (Mα * Mβ = (N : ℤ)) ∨ (Mα * Mβ = -(N : ℤ)) → False := by
    intro h
    rcases h with h | h <;> omega
  rcases hWα with hα1 | hα2 <;> rcases hWβ with hβ1 | hβ2
  · have hpr := Erdos634.F1AlgebraReal.F1_product_real a b c μ N (Mα : ℝ) (Mβ : ℝ) hc2 ha0.ne' hb0.ne' hN_b
      (hcα.symm.trans hα1) (hcβ.symm.trans hβ1)
    exact hfin (Or.inl (by exact_mod_cast hpr))
  · have hpr := Erdos634.F1AlgebraReal.F1_product_real a b c μ N (Mα : ℝ) (-(Mβ : ℝ)) hc2 ha0.ne' hb0.ne' hN_b
      (hcα.symm.trans hα1) (by linarith [hcβ.symm.trans hβ2])
    have : (Mα : ℝ) * (Mβ : ℝ) = -(N : ℝ) := by linarith
    exact hfin (Or.inr (by exact_mod_cast this))
  · have hpr := Erdos634.F1AlgebraReal.F1_product_real a b c μ N (-(Mα : ℝ)) (Mβ : ℝ) hc2 ha0.ne' hb0.ne' hN_b
      (by linarith [hcα.symm.trans hα2]) (hcβ.symm.trans hβ1)
    have : (Mα : ℝ) * (Mβ : ℝ) = -(N : ℝ) := by linarith
    exact hfin (Or.inr (by exact_mod_cast this))
  · have hpr := Erdos634.F1AlgebraReal.F1_product_real a b c μ N (-(Mα : ℝ)) (-(Mβ : ℝ)) hc2 ha0.ne' hb0.ne' hN_b
      (by linarith [hcα.symm.trans hα2]) (by linarith [hcβ.symm.trans hβ2])
    have : (Mα : ℝ) * (Mβ : ℝ) = (N : ℝ) := by linarith
    exact hfin (Or.inl (by exact_mod_cast this))

/-- `2π/3` tile, F1/F1′ targets, `N ≡ 2 (mod 4)`: `f1_data_of_f1shape` + `f1_parity_mod4_two` on each branch. -/
theorem gapF1_of_mod4_two (N : ℕ) (h4 : N % 4 = 2) : GapF1 N := by
  intro D α a b c hirr hm hshape
  rcases Erdos634.Geometry.f1_data_of_f1shape D hm hshape with ⟨μ, hμ, hF1⟩ | ⟨μ, hμ, hF1'⟩
  · exact f1_parity_mod4_two h4 D hirr hm hF1 hμ
  · have hirr' : IrrPi (Real.pi / 3 - α) := by
      intro ⟨q, hq⟩; apply hirr; exact ⟨1/3 - q, by push_cast; linarith⟩
    have hm' : D.model.TwoPiThreeData (Real.pi / 3 - α) b a c :=
      Erdos634.Geometry.twoPiThreeData_swap D.model hm
    exact f1_parity_mod4_two h4 D hirr' hm' hF1' hμ

/-! ## The generalised dispatch -/

/-- **`chain_conditional_gen`** — the dispatch of `Chain15.chain_conditional` with every prime/parity-specific branch
turned into a named hypothesis.  Hypotheses are exactly:
* arithmetic of N: `Squarefree N`, an odd-valuation prime ℓ with 2, 3 non-residues (S1/S2), `IsoQDvd N` (S3),
  `IsoH9 N` (IsoTP);
* branch closures: `GapAcomp` (Case A), `CaseBClosed`, `CaseRClosed`, `CaseGClosed`, `GapE60`, `GapE120`, `GapF1`,
  `GapR8`.
Each closure is supplied either by one of the helper lemmas above (when the arithmetic of N allows) or stays an open
named hypothesis. -/
theorem chain_conditional_gen (N : ℕ)
    (hsq : Squarefree N)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hval : Odd (padicValNat ℓ N))
    (hq2 : ∀ x : ZMod ℓ, x ^ 2 ≠ 2) (hq3 : ∀ x : ZMod ℓ, x ^ 2 ≠ 3)
    (hQ : IsoQDvd N) (hH : IsoH9 N)
    (gA : GapAcomp N) (gB : CaseBClosed N) (gR : CaseRClosed N) (gG : CaseGClosed N)
    (gE60 : GapE60 N) (gE120 : GapE120 N) (gF1 : GapF1 N) (gR8 : GapR8 N)
    (D : CongruentDissection N) : False := by
  -- Case A (Lemma S is proved, N-free, and supplied)
  by_cases hA : ∀ k, ∃ q : ℚ, D.model.angleAt k = q * Real.pi
  · exact gA Erdos634.LemmaSAll.lemmaS D hA
  have hirr : ∃ k, IrrPi (D.model.angleAt k) := by
    by_contra hc
    exact hA fun k => by_contra fun hk => hc ⟨k, hk⟩
  -- Case B
  by_cases hB : SimilarTM D
  · obtain ⟨μ, τ, hs⟩ := hB
    exact gB D μ τ hs
  -- Case C
  rcases Erdos634.Draft.LemmaCFinal.lemmaC_general D hirr hB with hR | hT | hS | hTP | h32
  · exact gR D hR
  · obtain ⟨α, a, b, c, hα, hd, i, j, hij, hi, hj⟩ := hT
    exact gG D α a b c hα hd i j hij hi hj
  · obtain ⟨α, a, b, c, hα, hd⟩ := hS
    exact gE60 D α a b c hα hd (Erdos634.Draft.LemmaPProof.lemmaP_general D α a b c hα hd hB)
  · obtain ⟨α, a, b, c, hα, hd, hsh⟩ := hTP
    rcases hsh with he | hi | hf | hr
    · exact gE120 D α a b c hα hd he
    · exact Erdos634.Draft.ThmIsoH9.thmIso_H9 N D hH α a b c hα hd hi
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
      exact Erdos634.Draft.ScaleBaseBetaQNR.scaleBaseBeta_qnr N D ℓ hℓ hval hq3 α β a b c r hα hrel hd hr hb
        ⟨τ, t0, t1, t2⟩
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
      exact rMinus4_qnr N D ℓ hℓ hval hq2 hq3 α β a b c r hα hrel hd hr
        (Rows11_13AnyLabel.b_of_rational hrel hd hr) ⟨τ, t0, t1, t2⟩
    · exact Row11.excluded_isoQ_any_label D hα hrel hd
        (τ.injective.ne (by decide : (0 : Fin 3) ≠ 1)) t0 t1 hQ

end Erdos634.Draft.ChainComposite

#print axioms Erdos634.Draft.ChainComposite.chain_conditional_gen
#print axioms Erdos634.Draft.ChainComposite.caseG_of_mod4_two
#print axioms Erdos634.Draft.ChainComposite.gapE60_of_mod4_two
#print axioms Erdos634.Draft.ChainComposite.gapE120_of_mod4_two
#print axioms Erdos634.Draft.ChainComposite.gapF1_of_mod4_two

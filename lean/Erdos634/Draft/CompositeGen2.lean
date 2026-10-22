/-
Draft/CompositeGen2.lean — the dispatch `ChainComposite.chain_conditional_gen` with the two prime/residue-specific
leaves S2 (2α,α,2β) and S3 (α,α,α+2β) abstracted to the named propositions `S2Closed N`, `S3Closed N` (exactly the
statements `RMinus4QNR.rMinus4_qnr` / `Row11.excluded_isoQ_any_label` conclude, with N fixed).  Reason: for
N = 14, 42, 62, 70 the QNR hypothesis of S2 (2 AND 3 non-residues mod an odd-valuation prime) and `IsoQDvd N`
(S3) are FALSE, so those leaves need N-specific discharges (CompositeS2Arith, CompositeS3Refined).
UNAUDITED.  Formalization debt, NOT /goal progress.  No sorry, no native_decide.
-/
import Erdos634.Draft.ChainComposite
import Erdos634.Draft.RMinus4QNR
import Erdos634.Draft.ScaleBaseBetaQNR
import Erdos634.Draft.Row11IsoQ
import Erdos634.Draft.RASquarefree
import Erdos634.Draft.RWSquarefree

open scoped Classical

namespace Erdos634.Draft.CompositeGen2

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.Chain15 Erdos634.Draft.ChainComposite

/-- **S2Closed N**: shape (2α, α, 2β) (3α+2β = π, α irrational, model `ThreeAlphaData`, `a = r c`, `b = (1−r²)c`,
`r ∈ ℚ`) is impossible.  Exactly the conclusion of `RMinus4QNR.S2QNRStatement` at fixed `N`, without ℓ. -/
def S2Closed (N : ℕ) : Prop :=
  ∀ (D : CongruentDissection N) (α β a b c : ℝ) (r : ℚ), IrrPi α → 3 * α + 2 * β = Real.pi →
    D.model.ThreeAlphaData α β a b c → a = (r : ℝ) * c → b = (1 - (r : ℝ) ^ 2) * c →
    TgtAngles D (2 * α) α (2 * β) → False

/-- **S3Closed N**: shape (α, α, α+2β) (two target angles α at distinct vertices) is impossible.  Exactly the
conclusion of `Row11.excluded_isoQ_any_label` at fixed `N`, without `IsoQDvd N`. -/
def S3Closed (N : ℕ) : Prop :=
  ∀ (D : CongruentDissection N) (α β a b c : ℝ), (¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) → 3 * α + 2 * β = Real.pi →
    D.model.ThreeAlphaData α β a b c → ∀ t₀ t₁ : Fin 3, t₀ ≠ t₁ →
    D.target.angleAt t₀ = α → D.target.angleAt t₁ = α → False

/-- `S2Closed N` from the existing QNR leaf (needs prime ℓ, odd valuation, 2 and 3 non-residues mod ℓ). -/
theorem s2Closed_of_qnr (N : ℕ) (ℓ : ℕ) (hℓ : ℓ.Prime) (hval : Odd (padicValNat ℓ N))
    (hq2 : ∀ x : ZMod ℓ, x ^ 2 ≠ 2) (hq3 : ∀ x : ZMod ℓ, x ^ 2 ≠ 3) : S2Closed N :=
  fun D α β a b c r hα hrel hd hr hb htg =>
    rMinus4_qnr N D ℓ hℓ hval hq2 hq3 α β a b c r hα hrel hd hr hb htg

/-- `S3Closed N` from `IsoQDvd N`. -/
theorem s3Closed_of_isoQDvd (N : ℕ) (hQ : IsoQDvd N) : S3Closed N :=
  fun D α β a b c hα hrel hd t₀ t₁ ht h0 h1 => Row11.excluded_isoQ_any_label D hα hrel hd ht h0 h1 hQ

/-- The dispatch of `chain_conditional_gen` with S2, S3 abstracted. -/
theorem chain_gen2 (N : ℕ)
    (hsq : Squarefree N)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hval : Odd (padicValNat ℓ N))
    (hq3 : ∀ x : ZMod ℓ, x ^ 2 ≠ 3)
    (gS2 : S2Closed N) (gS3 : S3Closed N) (hH : IsoH9 N)
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
      exact gS2 D α β a b c r hα hrel hd hr
        (Rows11_13AnyLabel.b_of_rational hrel hd hr) ⟨τ, t0, t1, t2⟩
    · exact gS3 D α β a b c hα hrel hd (τ 0) (τ 1)
        (τ.injective.ne (by decide : (0 : Fin 3) ≠ 1)) t0 t1

end Erdos634.Draft.CompositeGen2

#print axioms Erdos634.Draft.CompositeGen2.chain_gen2
#print axioms Erdos634.Draft.CompositeGen2.s2Closed_of_qnr
#print axioms Erdos634.Draft.CompositeGen2.s3Closed_of_isoQDvd

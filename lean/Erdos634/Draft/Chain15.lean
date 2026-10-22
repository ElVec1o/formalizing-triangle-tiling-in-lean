-- Draft/Chain15.lean — the primality-free dispatch of `theoremP_conditional`, CONDITIONAL on the leaves that
-- still have no primality-free Lean proof.  This is NOT a proof that N is not a tile count: the five `Gap…`
-- hypotheses are exactly the open obligations (room ALLN SCOPE_N15_L1.md).  Instantiated at N = 15.  UNAUDITED.
--   GapA   : Case A (all model angles in Qπ) at N            [Lemma S only for prime p ≥ 7; Beeson Seven Thm 3, cited]
--   GapE60 : π/3 tile, equilateral target (Theorem E, pins)  [existing chain is prime-specific]
--   GapE120: 2π/3 tile, equilateral target                    [needs a certificate at N=15: rational tile ∝ (3,5,7)]
--   GapF1  : 2π/3 tile, F1/F1' targets                        [f1_free prime-specific; new geometry]
--   GapR8  : 2π/3 tile, F2–F4' targets                        [five contradiction files, port pending]
import Erdos634.Draft.TheoremPConditional
import Erdos634.Draft.LemmaCFinal
import Erdos634.Draft.LemmaPProof
import Erdos634.Draft.FluxERow2Sqfree
import Erdos634.Draft.FluxDRow4M1AnyLabel
import Erdos634.Draft.ScaleBaseBetaQNR
import Erdos634.Draft.RMinus4QNR
import Erdos634.Draft.RASquarefree
import Erdos634.Draft.RWSquarefree
import Erdos634.Draft.Row11IsoQ
import Erdos634.Draft.ThmIsoH9

open scoped Classical

namespace Erdos634.Draft.Chain15

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional

def GapA (N : ℕ) : Prop :=
  ∀ D : CongruentDissection N, (∀ k, ∃ q : ℚ, D.model.angleAt k = q * Real.pi) → False

def GapE60 (N : ℕ) : Prop :=
  ∀ D : CongruentDissection N, ∀ α a b c : ℝ, IrrPi α → D.model.SixtyData α a b c → Equilateral D → False

def GapE120 (N : ℕ) : Prop :=
  ∀ D : CongruentDissection N, ∀ α a b c : ℝ, IrrPi α → D.model.TwoPiThreeData α a b c → Equilateral D → False

def GapF1 (N : ℕ) : Prop :=
  ∀ D : CongruentDissection N, ∀ α a b c : ℝ, IrrPi α → D.model.TwoPiThreeData α a b c → F1Shape D α → False

def GapR8 (N : ℕ) : Prop :=
  ∀ D : CongruentDissection N, ∀ α a b c : ℝ, IrrPi α → D.model.TwoPiThreeData α a b c → F2to4Shape D α → False

/-- The primality-free dispatch, conditional on the five gap leaves and the residual hypotheses of the
leaves already proved without primality. -/
theorem chain_conditional (N : ℕ)
    (hsq : Squarefree N) (h7 : 7 ≤ N) (h4 : N % 4 = 3) (hodd : N % 2 = 1) (hM1 : M1Div N)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hval : Odd (padicValNat ℓ N))
    (hq2 : ∀ x : ZMod ℓ, x ^ 2 ≠ 2) (hq3 : ∀ x : ZMod ℓ, x ^ 2 ≠ 3)
    (hQ : IsoQDvd N) (hH : IsoH9 N)
    (gA : GapA N) (gE60 : GapE60 N) (gE120 : GapE120 N) (gF1 : GapF1 N) (gR8 : GapR8 N)
    (D : CongruentDissection N) : False := by
  -- Case A
  by_cases hA : ∀ k, ∃ q : ℚ, D.model.angleAt k = q * Real.pi
  · exact gA D hA
  have hirr : ∃ k, IrrPi (D.model.angleAt k) := by
    by_contra hc
    exact hA fun k => by_contra fun hk => hc ⟨k, hk⟩
  -- Case B
  by_cases hB : SimilarTM D
  · obtain ⟨μ, τ, hs⟩ := hB
    have := Row2.theoremS_perm_sqfree D μ τ hs hsq h7
    omega
  -- Case C
  rcases Erdos634.Draft.LemmaCFinal.lemmaC_general D hirr hB with hR | hT | hS | hTP | h32
  · obtain ⟨α, h0, h2, hi, ⟨p, q, hpq, hp, hq⟩, γ, hγ, i, j, hij, hi', hj'⟩ := hR
    obtain ⟨m, hm⟩ := Row3.RP.row3_RP_even_any_label D h0 h2 hi hpq hp hq hγ hij hi' hj'
    omega
  · obtain ⟨α, a, b, c, hα, hd, i, j, hij, hi, hj⟩ := hT
    exact Row4.not_M1_any_label D hα hd hij hi hj hM1
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

/-- **Instance N = 15**: conditional on the five gap leaves only. -/
theorem chain_fifteen (gA : GapA 15) (gE60 : GapE60 15) (gE120 : GapE120 15) (gF1 : GapF1 15)
    (gR8 : GapR8 15) (D : CongruentDissection 15) : False := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact chain_conditional 15 (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) M1Div_fifteen 5 (by norm_num)
    s1_excluded_fifteen qnr_two_five
    qnr_five IsoQDvd_fifteen IsoH9_fifteen gA gE60 gE120 gF1 gR8 D

end Erdos634.Draft.Chain15

#print axioms Erdos634.Draft.Chain15.chain_fifteen

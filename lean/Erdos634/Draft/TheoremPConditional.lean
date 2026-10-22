/-
Draft/TheoremPConditional.lean — **Theorem P (the prime case) as ONE Lean statement**, composed from
the VERIFIED pieces, with every node that has no Lean carried as an explicit, named `Prop`
hypothesis.

  Theorem P (PRIME_CASE_PROOF.md §1; paper/erdos-634.tex `thm:primesolved`): no prime N ≡ 3 (mod 4)
  with N > 3 is the number of tiles of a congruent dissection of a triangle (reflections allowed,
  not edge-to-edge).  [The statement "no prime N > 3" WITHOUT N ≡ 3 (mod 4) is false: 5 = 1² + 2²
  and every prime ≡ 1 (mod 4) is a tile count (Soifer).]

Case tree (PRIME_CASE_PROOF.md §2) and where each node lives here:
  Case A (all model angles in ℚπ)      — `LemmaSAll.r0c` (A1–A9, Lean, unconditional).
  Case B (target ~ model)              — `Row2.theoremS_perm` (B1, Lean).
  Case C (irrational angle, target ≁ T):
    C1+C2 Lemma C + Corollary C′        — HYPOTHESIS `LemmaCStatement`.
    right tile, C5 Proposition RP       — `Row3.RP.row3_RP_even_any_label` (Lean).
    γ = 2α, C6 Theorem R4               — `Row4.not_prime_any_label` (Lean).
    angle π/3, C3 Lemma P               — HYPOTHESIS `LemmaPStatement`;
                C7 Theorem E (π/3)      — `Row5Hr0.Row5.theoremE_sixty_full` (Lean).
    angle 2π/3: equilateral, C7         — `Row5TwoPiThreeFull.Row5.theoremE_twoPiThree_full` (Lean);
                isosceles, C10 thm:iso  — HYPOTHESIS `ThmIsoStatement`;
                F₁, F₁′, C8 prop:F1free — HYPOTHESIS `F1FreeStatement`;
                F₂–F₄′, C9 R8+reduction — HYPOTHESIS `R8ReductionStatement`.
    3α + 2β = π: rationality D1–D3      — `Row11/12/13/14/15.rational_any_label` (Lean);
                (α,α,α+2β), S3          — `Row11.prime_excluded_any_label` (Lean);
                (β,β,3α), S1            — HYPOTHESIS `ScaleBaseBetaStatement`;
                (2α,α,2β), S2 R-4       — HYPOTHESIS `RMinus4Statement`;
                (2α,β,α+β), S4 R-W      — HYPOTHESIS `RWStatement` (S1 + S7 cevianatom + gluing);
                (α+β,α+β,α), S5 R-A     — HYPOTHESIS `RAStatement` (S1 + gluing);
                I6 (all members)        — `BaseBetaFullUnc.basebeta_full_unc` (Lean).

Every hypothesis is its paper node RESTRICTED to Theorem P's regime (N prime, N ≡ 3 mod 4, N > 3),
and, in the 3α+2β branch, additionally given the (Lean-proved) rationality output as a premise; so
each is implied by the node as written.  Non-vacuity controls are at the end of the file.

Formalization debt, NOT /goal progress: this composes existing pieces; the nine hypotheses are the
Case C nodes with no Lean.  No `sorry`, no `native_decide`, no axioms.  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
-/
import Erdos634.Draft.LemmaSAll
import Erdos634.Draft.BaseBetaFullUnc
import Erdos634.Draft.FluxERow2S
import Erdos634.Draft.FluxGRow3RPAnyLabel
import Erdos634.Draft.FluxDRow4AnyLabel
import Erdos634.Draft.FluxCRow5Hr0
import Erdos634.Draft.FluxCRow5TwoPiThreeFull
import Erdos634.Draft.FluxFRow14AnyLabel
import Erdos634.Draft.FluxFRow15AnyLabel
import Erdos634.Draft.Rows11_13AnyLabel
import Erdos634.Draft.FluxRow11Witness
import Erdos634.Draft.Row14JointWitness
import Erdos634.Draft.Row15JointWitness
import Erdos634.Draft.Tiling77Bridge

open scoped Classical

namespace Erdos634.Draft.TheoremPConditional

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.BaseBetaTargetCoord

/-! ## Vocabulary -/

/-- `x ∉ ℚπ`. -/
def IrrPi (x : ℝ) : Prop := ¬ ∃ r : ℚ, x = (r : ℝ) * Real.pi

/-- The target's angles are `x, y, z` in some order. -/
def TgtAngles {N : ℕ} (D : CongruentDissection N) (x y z : ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3), D.target.angleAt (σ 0) = x ∧ D.target.angleAt (σ 1) = y ∧
    D.target.angleAt (σ 2) = z

/-- `ABC ~ T` (any vertex correspondence) — exactly the hypothesis of `Row2.theoremS_perm`. -/
def SimilarTM {N : ℕ} (D : CongruentDissection N) : Prop :=
  ∃ (μ : ℝ) (τ : Equiv.Perm (Fin 3)), ∀ k, D.target.angleAt k = D.model.angleAt (τ k) ∧
    D.target.oppLen k = μ * D.model.oppLen (τ k)

/-- Some member's unit base-β target `Δ₁(e,f)` is tiled by `T(e,f)` (I6's excluded object). -/
def BaseBetaTiled : Prop :=
  ∃ (e f : ℕ) (he : 0 < e) (hef : e < f), Nat.Coprime e f ∧
    ∃ (N' : ℕ) (D' : CongruentDissection N'),
      D'.target.Congruent (baseBetaTarget (e : ℝ) f (by exact_mod_cast he) (by exact_mod_cast hef)) ∧
      sideOpp D'.model 0 = (e : ℝ) * f ∧ sideOpp D'.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∧
      sideOpp D'.model 2 = (f : ℝ) ^ 2

/-- **I6**, from Lean: no member's `Δ₁(e,f)` is tiled by `T(e,f)`. -/
theorem not_baseBetaTiled : ¬ BaseBetaTiled := by
  rintro ⟨e, f, he, hef, hco, N', D', ht, h0, h1, h2⟩
  exact BaseBetaFullUnc.basebeta_full_unc D' hco he hef ht h0 h1 h2

/-! ### Case C shapes (Lemma C / Corollary C′, PRIME_CASE_PROOF §2; paper erdos-634.tex:980–988) -/

/-- Right tile `(α, π/2−α, π/2)`, `α ∉ ℚπ`; target `(2x₂, x₃, x₃)` or `(2x₃, x₂, x₂)`, i.e. two equal
target angles `γ ∈ {α, π/2 − α}`. -/
def RightCase {N : ℕ} (D : CongruentDissection N) : Prop :=
  ∃ α : ℝ, 0 < α ∧ α < Real.pi / 2 ∧ Irrational (α / Real.pi) ∧
    (∃ p q : Fin 3, p ≠ q ∧ D.model.angleAt p = α ∧ D.model.angleAt q = Real.pi / 2) ∧
    ∃ γ : ℝ, (γ = α ∨ γ = Real.pi / 2 - α) ∧
      ∃ i j : Fin 3, i ≠ j ∧ D.target.angleAt i = γ ∧ D.target.angleAt j = γ

/-- `γ = 2α` tile `(α, π−3α, 2α)`, `α ∉ ℚπ`; target isosceles with base angles `α`. -/
def TwoAlphaCase {N : ℕ} (D : CongruentDissection N) : Prop :=
  ∃ α a b c : ℝ, IrrPi α ∧ D.model.TwoAlphaData α a b c ∧
    ∃ i j : Fin 3, i ≠ j ∧ D.target.angleAt i = α ∧ D.target.angleAt j = α

/-- Tile with an angle `π/3`: `(α, 2π/3 − α, π/3)`, `α ∉ ℚπ` (target: Lemma P). -/
def SixtyTile {N : ℕ} (D : CongruentDissection N) : Prop :=
  ∃ α a b c : ℝ, IrrPi α ∧ D.model.SixtyData α a b c

def Equilateral {N : ℕ} (D : CongruentDissection N) : Prop :=
  ∀ k, D.target.angleAt k = Real.pi / 3

/-- 2π/3 tile `(α, β, 2π/3)`, `β = π/3 − α`: the two isosceles targets
`(α, α, α+3β)`, `(β, β, β+3α)`. -/
def IsoTP {N : ℕ} (D : CongruentDissection N) (α : ℝ) : Prop :=
  TgtAngles D α α (α + 3 * (Real.pi / 3 - α)) ∨
    TgtAngles D (Real.pi / 3 - α) (Real.pi / 3 - α) ((Real.pi / 3 - α) + 3 * α)

/-- `F₁ = (α, α+β, α+2β)` and `F₁′ = (β, α+β, 2α+β)`, `β = π/3 − α`. -/
def F1Shape {N : ℕ} (D : CongruentDissection N) (α : ℝ) : Prop :=
  TgtAngles D α (α + (Real.pi / 3 - α)) (α + 2 * (Real.pi / 3 - α)) ∨
    TgtAngles D (Real.pi / 3 - α) (α + (Real.pi / 3 - α)) (2 * α + (Real.pi / 3 - α))

/-- `F₂ = (2α, 2β, α+β)`, `F₃ = (α, 2α, 3β)`, `F₃′ = (β, 2β, 3α)`, `F₄ = (α, 2β, 2α+β)`,
`F₄′ = (β, 2α, α+2β)`, `β = π/3 − α`. -/
def F2to4Shape {N : ℕ} (D : CongruentDissection N) (α : ℝ) : Prop :=
  TgtAngles D (2 * α) (2 * (Real.pi / 3 - α)) (α + (Real.pi / 3 - α)) ∨
  TgtAngles D α (2 * α) (3 * (Real.pi / 3 - α)) ∨
  TgtAngles D (Real.pi / 3 - α) (2 * (Real.pi / 3 - α)) (3 * α) ∨
  TgtAngles D α (2 * (Real.pi / 3 - α)) (2 * α + (Real.pi / 3 - α)) ∨
  TgtAngles D (Real.pi / 3 - α) (2 * α) (α + 2 * (Real.pi / 3 - α))

/-- 2π/3 tile `(α, π/3 − α, 2π/3)`, `α ∉ ℚπ`, target one of the ten non-similar shapes. -/
def TwoPiThreeCase {N : ℕ} (D : CongruentDissection N) : Prop :=
  ∃ α a b c : ℝ, IrrPi α ∧ D.model.TwoPiThreeData α a b c ∧
    (Equilateral D ∨ IsoTP D α ∨ F1Shape D α ∨ F2to4Shape D α)

/-- `3α + 2β = π` tile `(α, β, 2α+β)`, `α ∉ ℚπ`, target one of the five non-similar shapes. -/
def ThreeTwoCase {N : ℕ} (D : CongruentDissection N) : Prop :=
  ∃ α β a b c : ℝ, IrrPi α ∧ 3 * α + 2 * β = Real.pi ∧ D.model.ThreeAlphaData α β a b c ∧
    (TgtAngles D β β (3 * α) ∨ TgtAngles D (α + β) (α + β) α ∨
     TgtAngles D (2 * α) β (α + β) ∨ TgtAngles D (2 * α) α (2 * β) ∨
     TgtAngles D α α (α + 2 * β))

/-! ## The named hypotheses (the Case C nodes with no Lean) -/

/-- **C1 + C2 (Lemma C and Corollary C′).** Irrational angle, target not similar ⇒ one of the
tile types right / γ=2α / π/3 / 2π/3 / 3α+2β with its listed target shapes (the isosceles tile
forces ABC ~ T, excluded). -/
def LemmaCStatement : Prop :=
  ∀ (N : ℕ) (D : CongruentDissection N), N.Prime → N % 4 = 3 → 3 < N →
    (∃ k, IrrPi (D.model.angleAt k)) → ¬ SimilarTM D →
    RightCase D ∨ TwoAlphaCase D ∨ SixtyTile D ∨ TwoPiThreeCase D ∨ ThreeTwoCase D

/-- **C3 (row 6's Lemma P).** A tile with an angle π/3 and an irrational angle: ABC is equilateral
or ~ T. -/
def LemmaPStatement : Prop :=
  ∀ (N : ℕ) (D : CongruentDissection N), N.Prime → N % 4 = 3 → 3 < N →
    ∀ α a b c : ℝ, IrrPi α → D.model.SixtyData α a b c → ¬ SimilarTM D → Equilateral D

/-- **C10 (thm:iso).** No prime count tiles an isosceles non-equilateral target by a 2π/3 tile
with an irrational angle. -/
def ThmIsoStatement : Prop :=
  ∀ (N : ℕ) (D : CongruentDissection N), N.Prime → N % 4 = 3 → 3 < N →
    ∀ α a b c : ℝ, IrrPi α → D.model.TwoPiThreeData α a b c → IsoTP D α → False

/-- **C8 (prop:F1free).** No F₁ or F₁′ target is N-tiled by a 2π/3 tile, N > 3 prime. -/
def F1FreeStatement : Prop :=
  ∀ (N : ℕ) (D : CongruentDissection N), N.Prime → N % 4 = 3 → 3 < N →
    ∀ α a b c : ℝ, IrrPi α → D.model.TwoPiThreeData α a b c → F1Shape D α → False

/-- **C9 (Proposition R8 + prop:reduction's primitivity step).** F₂–F₄′ targets: the tile is
rational and N = k²N₀ with N₀ composite, so N is not prime. -/
def R8ReductionStatement : Prop :=
  ∀ (N : ℕ) (D : CongruentDissection N), N.Prime → N % 4 = 3 → 3 < N →
    ∀ α a b c : ℝ, IrrPi α → D.model.TwoPiThreeData α a b c → F2to4Shape D α → False

/-- **S1 (Lemma S-scale) at the base-β shape (β, β, 3α).** With s = a/c ∈ ℚ, s = e/f: ABC = k·Δ₁(e,f),
N = k²(3f²−e²), so k = 1 at prime N and (after rescaling) Δ₁(e,f) is tiled by T(e,f). -/
def ScaleBaseBetaStatement : Prop :=
  ∀ (N : ℕ) (D : CongruentDissection N), N.Prime → N % 4 = 3 → 3 < N →
    ∀ (α β a b c : ℝ) (r : ℚ), IrrPi α → 3 * α + 2 * β = Real.pi →
      D.model.ThreeAlphaData α β a b c → a = (r : ℝ) * c → b = (1 - (r : ℝ) ^ 2) * c →
      TgtAngles D β β (3 * α) → BaseBetaTiled

/-- **S2 (R-4, with S1).** Target (2α, α, 2β): N₀ = (2f²−e²)(3f²−e²), N composite. -/
def RMinus4Statement : Prop :=
  ∀ (N : ℕ) (D : CongruentDissection N), N.Prime → N % 4 = 3 → 3 < N →
    ∀ (α β a b c : ℝ) (r : ℚ), IrrPi α → 3 * α + 2 * β = Real.pi →
      D.model.ThreeAlphaData α β a b c → a = (r : ℝ) * c → b = (1 - (r : ℝ) ^ 2) * c →
      TgtAngles D (2 * α) α (2 * β) → False

/-- **S4 (R-W, with S1, S7 prop:cevianatom and thm:ladder).** Target (2α, β, α+β): k = 1,
ABC ≅ W₁(e,f), and Δ₁ = W₁ ⊔ f·T glues to a tiling of Δ₁(e,f) by T(e,f). -/
def RWStatement : Prop :=
  ∀ (N : ℕ) (D : CongruentDissection N), N.Prime → N % 4 = 3 → 3 < N →
    ∀ (α β a b c : ℝ) (r : ℚ), IrrPi α → 3 * α + 2 * β = Real.pi →
      D.model.ThreeAlphaData α β a b c → a = (r : ℝ) * c → b = (1 - (r : ℝ) ^ 2) * c →
      TgtAngles D (2 * α) β (α + β) → BaseBetaTiled

/-- **S5 (R-A, with S1 and thm:ladder).** Target (α+β, α+β, α): p | k, the atom A₁ = s·ABC, and
Δ₁ = f·T ⊔ A₁ ⊔ f·T glues to a tiling of Δ₁(e,f) by T(e,f). -/
def RAStatement : Prop :=
  ∀ (N : ℕ) (D : CongruentDissection N), N.Prime → N % 4 = 3 → 3 < N →
    ∀ (α β a b c : ℝ) (r : ℚ), IrrPi α → 3 * α + 2 * β = Real.pi →
      D.model.ThreeAlphaData α β a b c → a = (r : ℝ) * c → b = (1 - (r : ℝ) ^ 2) * c →
      TgtAngles D (α + β) (α + β) α → BaseBetaTiled

/-! ## Theorem P, conditional on exactly the nine named nodes -/

theorem theoremP_conditional
    (hC : LemmaCStatement) (hP : LemmaPStatement) (hIso : ThmIsoStatement)
    (hF1 : F1FreeStatement) (hR8 : R8ReductionStatement) (hS1 : ScaleBaseBetaStatement)
    (hR4m : RMinus4Statement) (hRW : RWStatement) (hRA : RAStatement) :
    ∀ (N : ℕ) (D : CongruentDissection N), N.Prime → N % 4 = 3 → 3 < N → False := by
  intro N D hN h4 h3
  -- Case A: every model angle in ℚπ.
  by_cases hA : ∀ k, ∃ q : ℚ, D.model.angleAt k = q * Real.pi
  · exact LemmaSAll.r0c D hA hN h4 h3
  have hirr : ∃ k, IrrPi (D.model.angleAt k) := by
    by_contra hc
    exact hA fun k => by_contra fun hk => hc ⟨k, hk⟩
  -- Case B: ABC ~ T.
  by_cases hB : SimilarTM D
  · obtain ⟨μ, τ, hs⟩ := hB
    rcases Row2.theoremS_perm D μ τ hs hN with h | h <;> omega
  -- Case C.
  rcases hC N D hN h4 h3 hirr hB with hR | hT | hS | hTP | h32
  · -- right tile: N even
    obtain ⟨α, h0, h2, hi, ⟨p, q, hpq, hp, hq⟩, γ, hγ, i, j, hij, hi', hj'⟩ := hR
    obtain ⟨m, hm⟩ := Row3.RP.row3_RP_even_any_label D h0 h2 hi hpq hp hq hγ hij hi' hj'
    omega
  · -- γ = 2α
    obtain ⟨α, a, b, c, hα, hd, i, j, hij, hi, hj⟩ := hT
    exact Row4.not_prime_any_label D hα hd hij hi hj hN
  · -- angle π/3: Lemma P, then Theorem E
    obtain ⟨α, a, b, c, hα, hd⟩ := hS
    exact Row5Hr0.Row5.theoremE_sixty_full D hα hd (hP N D hN h4 h3 α a b c hα hd hB) ⟨hN, h3⟩
  · -- angle 2π/3
    obtain ⟨α, a, b, c, hα, hd, hsh⟩ := hTP
    rcases hsh with he | hi | hf | hr
    · exact Row5TwoPiThreeFull.Row5.theoremE_twoPiThree_full D hα hd he ⟨hN, h3⟩
    · exact hIso N D hN h4 h3 α a b c hα hd hi
    · exact hF1 N D hN h4 h3 α a b c hα hd hf
    · exact hR8 N D hN h4 h3 α a b c hα hd hr
  · -- 3α + 2β = π
    obtain ⟨α, β, a, b, c, hα, hrel, hd, hsh⟩ := h32
    obtain ⟨σ, m0, o0, m1, o1, m2, o2⟩ := id hd
    have s01 : σ 0 ≠ σ 1 := σ.injective.ne (by decide)
    have s20 : σ 2 ≠ σ 0 := σ.injective.ne (by decide)
    have s21 : σ 2 ≠ σ 1 := σ.injective.ne (by decide)
    rcases hsh with ⟨τ, t0, t1, t2⟩ | ⟨τ, t0, t1, t2⟩ | ⟨τ, t0, t1, t2⟩ | ⟨τ, t0, t1, t2⟩ |
        ⟨τ, t0, t1, t2⟩
    · -- (β, β, 3α): Row 12 rationality, S1, I6
      obtain ⟨r, hr, hb⟩ := Row12.rational_any_label D hα hrel hd
        (τ.injective.ne (by decide : (0 : Fin 3) ≠ 1)) t0 t1
      exact not_baseBetaTiled (hS1 N D hN h4 h3 α β a b c r hα hrel hd hr hb ⟨τ, t0, t1, t2⟩)
    · -- (α+β, α+β, α): Row 13 rationality, R-A, I6
      obtain ⟨r, hr, hb⟩ := Row13.rational_any_label D hα hrel hd
        (τ.injective.ne (by decide : (0 : Fin 3) ≠ 1)) t0 t1
      exact not_baseBetaTiled (hRA N D hN h4 h3 α β a b c r hα hrel hd hr hb ⟨τ, t0, t1, t2⟩)
    · -- (2α, β, α+β): Row 14 rationality, R-W, I6
      obtain ⟨r, hr⟩ := Row14.rational_any_label D α β hα hrel s01 s20 s21 m0 m1
        (τ.injective.ne (by decide : (0 : Fin 3) ≠ 1)) t0 t1
      rw [o0, o2] at hr
      exact not_baseBetaTiled (hRW N D hN h4 h3 α β a b c r hα hrel hd hr
        (Rows11_13AnyLabel.b_of_rational hrel hd hr) ⟨τ, t0, t1, t2⟩)
    · -- (2α, α, 2β): Row 15 rationality, R-4
      obtain ⟨r, hr, -⟩ := Row15.rational_any_label D α β hα hrel s01 s20 s21 m0 m1
        (τ.injective.ne (by decide : (0 : Fin 3) ≠ 1)) t0 t1
      rw [o0, o2] at hr
      exact hR4m N D hN h4 h3 α β a b c r hα hrel hd hr
        (Rows11_13AnyLabel.b_of_rational hrel hd hr) ⟨τ, t0, t1, t2⟩
    · -- (α, α, α+2β): Row 11 at prime N (Lean, unconditional)
      exact Row11.prime_excluded_any_label D hα hrel hd
        (τ.injective.ne (by decide : (0 : Fin 3) ≠ 1)) t0 t1 hN

/-! ## Non-vacuity controls

For each hypothesis `H = ∀ N D, N prime → … → premises → C`: a REAL certified dissection (non-prime
N) satisfies all `premises`, so `H` is not vacuously true; and where `C` is provably false
(`False` or `BaseBetaTiled`), the prime-free variant of `H` is REFUTED by that dissection, i.e. the
restriction to prime N is exactly what `H` rests on and no real dissection in the corpus refutes `H`
itself.  (None of this proves an unproved hypothesis.) -/

section Controls

open Erdos634.Draft.FluxGridWitness (α44 β44 α44_irr three_α_two_β t_angle0 t_angle1 t_angle2)

/-- The certified 44-tiling (target (16,16,22)-scaled base-β, tile (2,3,4)·8). -/
noncomputable abbrev D44 := Erdos634.Tiling44Bridge.dissection

/-- **LemmaC's conclusion holds on a real dissection** with an irrational angle: at N = 44 the
3α+2β disjunct with the base-β shape. -/
theorem lemmaC_conclusion_real_44 : ThreeTwoCase D44 ∧ ∃ k, IrrPi (D44.model.angleAt k) :=
  ⟨⟨α44, β44, 16, 24, 32, α44_irr, three_α_two_β, Erdos634.Draft.FluxRow11Witness.data44,
    Or.inl ⟨1, t_angle0, t_angle1, t_angle2⟩⟩, ⟨2, α44_irr⟩⟩

/-- **S1 control.** Every non-arithmetic premise of `ScaleBaseBetaStatement` holds on the real
44-tiling (with r = 1/2), so the prime-free variant of S1 is refuted: S1 rests on primality
(at N = 44 = 2²·11, k = 2). -/
theorem scaleBaseBeta_premises_44 :
    IrrPi α44 ∧ 3 * α44 + 2 * β44 = Real.pi ∧ D44.model.ThreeAlphaData α44 β44 16 24 32 ∧
      (16 : ℝ) = ((1 / 2 : ℚ) : ℝ) * 32 ∧ (24 : ℝ) = (1 - ((1 / 2 : ℚ) : ℝ) ^ 2) * 32 ∧
      TgtAngles D44 β44 β44 (3 * α44) :=
  ⟨α44_irr, three_α_two_β, Erdos634.Draft.FluxRow11Witness.data44, by norm_num, by norm_num,
    ⟨1, t_angle0, t_angle1, t_angle2⟩⟩

theorem scaleBaseBeta_primeFree_refuted :
    ¬ (∀ (N : ℕ) (D : CongruentDissection N) (α β a b c : ℝ) (r : ℚ), IrrPi α →
        3 * α + 2 * β = Real.pi → D.model.ThreeAlphaData α β a b c → a = (r : ℝ) * c →
        b = (1 - (r : ℝ) ^ 2) * c → TgtAngles D β β (3 * α) → BaseBetaTiled) := by
  intro h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := scaleBaseBeta_premises_44
  exact not_baseBetaTiled (h _ D44 α44 β44 16 24 32 (1 / 2) h1 h2 h3 h4 h5 h6)

/-- `TgtAngles` from two known target angles (third by the angle sum). -/
theorem tgtAngles_of_two {N : ℕ} (D : CongruentDissection N) (σ : Equiv.Perm (Fin 3)) {x y z : ℝ}
    (h0 : D.target.angleAt (σ 0) = x) (h1 : D.target.angleAt (σ 1) = y) (hz : x + y + z = Real.pi) :
    TgtAngles D x y z := by
  refine ⟨σ, h0, h1, ?_⟩
  have := Row3.RP.angle_third (T := D.target) (p := σ 0) (q := σ 1) (r := σ 2)
    (σ.injective.ne (by decide)) (σ.injective.ne (by decide)) (σ.injective.ne (by decide))
  rw [h0, h1] at this
  linarith

/-- `ThreeAlphaData` from `α` at vertex 0, `β` at vertex 2 and the three opposite sides. -/
theorem threeAlpha_of_02 (T : Tri) {α β a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (h0 : T.angleAt 0 = α) (h2 : T.angleAt 2 = β)
    (o0 : T.oppLen 0 = a) (o2 : T.oppLen 2 = b) (o1 : T.oppLen 1 = c) :
    T.ThreeAlphaData α β a b c := by
  have hs := Row3.RP.angle_third (T := T) (p := 0) (q := 2) (r := 1) (by decide) (by decide)
    (by decide)
  refine ⟨Equiv.swap 1 2, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Equiv.swap_apply_of_ne_of_ne (show (0 : Fin 3) ≠ 1 by decide)
      (show (0 : Fin 3) ≠ 2 by decide), Equiv.swap_apply_left, Equiv.swap_apply_right]
  · exact h0
  · exact o0
  · exact h2
  · exact o2
  · rw [h0, h2] at hs; linarith
  · exact o1

/-- The certified 63-tiling (target (6,7,8)·24, tile (2,3,4)·8): shape (2α, β, α+β). -/
noncomputable abbrev D63 := Erdos634.CevianTiling63Bridge.dissection

theorem d63_opp2 : D63.model.oppLen 2 = 24 := by
  unfold Tri.oppLen
  simp only [show (2:Fin 3) + 1 = 0 from rfl, show (2:Fin 3) + 2 = 1 from rfl]
  exact Erdos634.Draft.Row14JointWitness.m_d01

/-- **R-W control.** Every non-arithmetic premise of `RWStatement` holds on the real 63-tiling
(r = 1/2), so the prime-free variant of R-W is refuted (at N = 63 the target is 3·W₁(1,2), k = 3). -/
theorem rw_premises_63 :
    IrrPi α44 ∧ 3 * α44 + 2 * β44 = Real.pi ∧ D63.model.ThreeAlphaData α44 β44 16 24 32 ∧
      (16 : ℝ) = ((1 / 2 : ℚ) : ℝ) * 32 ∧ (24 : ℝ) = (1 - ((1 / 2 : ℚ) : ℝ) ^ 2) * 32 ∧
      TgtAngles D63 (2 * α44) β44 (α44 + β44) := by
  refine ⟨α44_irr, three_α_two_β, threeAlpha_of_02 _ three_α_two_β
    Erdos634.Draft.Row14JointWitness.model_angle0 Erdos634.Draft.Row14JointWitness.model_angle2
    Erdos634.Draft.Row14JointWitness.model_opp.1 d63_opp2
    Erdos634.Draft.Row14JointWitness.model_opp.2, by norm_num, by norm_num, ?_⟩
  refine tgtAngles_of_two D63 (Equiv.swap 0 2) ?_ ?_ (by linarith [three_α_two_β])
  · rw [Equiv.swap_apply_left]; exact Erdos634.Draft.Row14JointWitness.target_angle2
  · rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
    exact Erdos634.Draft.Row14JointWitness.target_angle1

theorem rw_primeFree_refuted :
    ¬ (∀ (N : ℕ) (D : CongruentDissection N) (α β a b c : ℝ) (r : ℚ), IrrPi α →
        3 * α + 2 * β = Real.pi → D.model.ThreeAlphaData α β a b c → a = (r : ℝ) * c →
        b = (1 - (r : ℝ) ^ 2) * c → TgtAngles D (2 * α) β (α + β) → BaseBetaTiled) := by
  intro h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := rw_premises_63
  exact not_baseBetaTiled (h _ D63 α44 β44 16 24 32 (1 / 2) h1 h2 h3 h4 h5 h6)

/-- The certified 77-tiling (tile (3,2,4)·16): shape (2α, α, 2β). -/
noncomputable abbrev D77 := Erdos634.Tiling77Bridge.dissection

/-- **R-4 control.** Every non-arithmetic premise of `RMinus4Statement` holds on the real
77-tiling (r = 1/2), so the prime-free variant of R-4 (conclusion `False`) is refuted; at N = 77 =
(2f²−e²)(3f²−e²) with (e,f) = (1,2), k = 1 — exactly R-4's composite count. -/
theorem rMinus4_premises_77 :
    IrrPi α44 ∧ 3 * α44 + 2 * β44 = Real.pi ∧ D77.model.ThreeAlphaData α44 β44 32 48 64 ∧
      (32 : ℝ) = ((1 / 2 : ℚ) : ℝ) * 64 ∧ (48 : ℝ) = (1 - ((1 / 2 : ℚ) : ℝ) ^ 2) * 64 ∧
      TgtAngles D77 (2 * α44) α44 (2 * β44) := by
  refine ⟨α44_irr, three_α_two_β, threeAlpha_of_02 _ three_α_two_β
    Erdos634.Draft.Row15JointWitness.model_angle0 Erdos634.Draft.Row15JointWitness.model_angle2
    Erdos634.Draft.Row15JointWitness.model_opp.1 Erdos634.Draft.Row15JointWitness.model_opp.2.2
    Erdos634.Draft.Row15JointWitness.model_opp.2.1, by norm_num, by norm_num, ?_⟩
  exact tgtAngles_of_two D77 1 Erdos634.Draft.Row15JointWitness.target_angle0
    Erdos634.Draft.Row15JointWitness.target_angle1 (by linarith [three_α_two_β])

theorem rMinus4_primeFree_refuted :
    ¬ (∀ (N : ℕ) (D : CongruentDissection N) (α β a b c : ℝ) (r : ℚ), IrrPi α →
        3 * α + 2 * β = Real.pi → D.model.ThreeAlphaData α β a b c → a = (r : ℝ) * c →
        b = (1 - (r : ℝ) ^ 2) * c → TgtAngles D (2 * α) α (2 * β) → False) := by
  intro h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := rMinus4_premises_77
  exact h _ D77 α44 β44 32 48 64 (1 / 2) h1 h2 h3 h4 h5 h6

end Controls

end Erdos634.Draft.TheoremPConditional

#print axioms Erdos634.Draft.TheoremPConditional.theoremP_conditional
#print axioms Erdos634.Draft.TheoremPConditional.not_baseBetaTiled
#print axioms Erdos634.Draft.TheoremPConditional.lemmaC_conclusion_real_44
#print axioms Erdos634.Draft.TheoremPConditional.scaleBaseBeta_primeFree_refuted
#print axioms Erdos634.Draft.TheoremPConditional.rw_primeFree_refuted
#print axioms Erdos634.Draft.TheoremPConditional.rMinus4_primeFree_refuted

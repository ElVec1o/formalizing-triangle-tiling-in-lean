-- Draft/BeesonH1UncL28.lean -- NEW wrapper theorems (no in-place edits): H1 (`¬ ∃ r : ℚ, α = r π`) of the cited Beeson consumers DERIVED from
-- `BeesonH1.lemma1_unconditional`; each `*_h1unc` takes the extra hypothesis `hns` (target NOT similar to the tile, i.e. NotSim as
-- ¬ Triple3 ...), the hypothesis of lemma1_unconditional.  Statements are the originals with hα/hirr/hδ replaced by hns.
-- NOTE, UNAUDITED (depends on the unaudited lacz51_all).  Credit: Beeson (arXiv 1206.2229 v4), Beeson-Zhang, Laczkovich (Discrete Math. 140 (1995)).
import Erdos634.Draft.LaczFormal51Lemma1
import Erdos634.Draft.BeesonL28e2
import Erdos634.Draft.BeesonL28e1
import Erdos634.Draft.BeesonL28c3
import Erdos634.Draft.BeesonL28c2
import Erdos634.Draft.BeesonColoringThm1Colour

open scoped Classical

namespace Erdos634.BeesonColoring

open Erdos634.Geometry Erdos634.Geometry.A1Field Erdos634.BeesonH1

variable {N : ℕ} {α β a b c : ℝ}

theorem boundary_gen_h1unc (D : CongruentDissection N) {α β a b c : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β)) (p0 q0 p1 q1 p2 q2 : ℤ)
    (h0 : D.target.angleAt 0 = (p0 : ℝ) * α + (q0 : ℝ) * β)
    (h1 : D.target.angleAt 1 = (p1 : ℝ) * α + (q1 : ℝ) * β)
    (h2 : D.target.angleAt 2 = (p2 : ℝ) * α + (q2 : ℝ) * β) :
    ∃ ε : Fin N → ℤ, D.toDissection.ProperColouring ε ∧ ∃ e : ℝ, (e = 1 ∨ e = -1) ∧
      ((∑ i, ε i : ℤ) : ℝ) * (a + b + c) =
        e * (sg p0 q0 * D.target.oppLen 0 + sg p1 q1 * D.target.oppLen 1 + sg p2 q2 * D.target.oppLen 2) :=
  boundary_gen (D := D) (hα := (lemma1_unconditional D hrel h hns)) (hrel := hrel) (h := h) (p0 := p0) (q0 := q0) (p1 := p1) (q1 := q1) (p2 := p2) (q2 := q2) (h0 := h0) (h1 := h1) (h2 := h2)

theorem thm1_colouring_h1unc (D : CongruentDissection N) {α β a b c : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β)) :
    (let P : ℝ → Prop := fun R => ∃ ε' : Fin N → ℤ, D.toDissection.ProperColouring ε' ∧
        ∃ M : ℤ, M = ((Finset.univ.filter fun i => ε' i = 1).card : ℤ)
          - ((Finset.univ.filter fun i => ε' i = -1).card : ℤ) ∧ 0 < M ∧ (M : ℝ) * (a + b + c) = R
     ((D.target.angleAt 0 = α ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = α + 2 * β) →
        P (D.target.oppLen 0 + D.target.oppLen 1 + D.target.oppLen 2)) ∧
     ((D.target.angleAt 0 = β ∧ D.target.angleAt 1 = β ∧ D.target.angleAt 2 = 3 * α) →
        P (D.target.oppLen 0 + D.target.oppLen 1 + D.target.oppLen 2)) ∧
     ((D.target.angleAt 0 = α + β ∧ D.target.angleAt 1 = α + β ∧ D.target.angleAt 2 = α) →
        P (D.target.oppLen 0 + D.target.oppLen 1 - D.target.oppLen 2)) ∧
     ((D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = 2 * β) →
        P (D.target.oppLen 0 - D.target.oppLen 1 + D.target.oppLen 2)) ∧
     ((D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = β ∧ D.target.angleAt 2 = α + β) →
        P (D.target.oppLen 0 - D.target.oppLen 1 + D.target.oppLen 2))) :=
  thm1_colouring (D := D) (hα := (lemma1_unconditional D hrel h hns)) (hrel := hrel) (h := h)

theorem lemma28_printed_h1unc (D : CongruentDissection N) {α β a b c : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β)) :
    -- triquadratic (2α, β, α+β): M1 = M2, so κ is undefined
    ((D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = β ∧ D.target.angleAt 2 = α + β) →
      ∃ M1 M2 : ℤ, M1 = M2) ∧
    -- (β, 3α, β): κ = -s
    ((D.target.angleAt 0 = β ∧ D.target.angleAt 1 = 3 * α ∧ D.target.angleAt 2 = β) →
      ∃ M1 M2 : ℤ, (M2 : ℝ) - M1 ≠ 0 ∧ ((M1 : ℝ) + M2) / ((M2 : ℝ) - M1) = -(a / c)) ∧
    -- (α+β, α, α+β): κ = s
    ((D.target.angleAt 0 = α + β ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = α + β) →
      ∃ M1 M2 : ℤ, (M2 : ℝ) - M1 ≠ 0 ∧ ((M1 : ℝ) + M2) / ((M2 : ℝ) - M1) = a / c) ∧
    -- (α, α+2β, α) and (2α, α, 2β): κ = s/(2-s²), 0 < κ < 1, s = κ(2-s²), quartic
    (∀ (_ : (D.target.angleAt 0 = α ∧ D.target.angleAt 1 = α + 2 * β ∧ D.target.angleAt 2 = α) ∨
        (D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = 2 * β)),
      ∃ M1 M2 : ℤ, (M2 : ℝ) - M1 ≠ 0 ∧
        ∃ κ : ℝ, κ = ((M1 : ℝ) + M2) / ((M2 : ℝ) - M1) ∧ κ = (a / c) / (2 - (a / c) ^ 2) ∧
          0 < κ ∧ κ < 1 ∧ a / c = κ * (2 - (a / c) ^ 2) ∧
          κ ^ 2 * (a / c) ^ 4 - (4 * κ ^ 2 + 1) * (a / c) ^ 2 + 4 * κ ^ 2 = 0) :=
  lemma28_printed (D := D) (hδ := ((delta_irr_iff hrel).mp (lemma1_unconditional D hrel h hns))) (hrel := hrel) (h := h)

theorem phi1_sum_h1unc (D : CongruentDissection N) {α β a b c : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β)) (p0 q0 p1 q1 p2 q2 : ℤ)
    (h0 : D.target.angleAt 0 = (p0 : ℝ) * α + (q0 : ℝ) * β)
    (h1 : D.target.angleAt 1 = (p1 : ℝ) * α + (q1 : ℝ) * β)
    (h2 : D.target.angleAt 2 = (p2 : ℝ) * α + (q2 : ℝ) * β)
    (ε : Fin N → ℤ) (hε : SignsFor D (Phi1 D α (lemma1_unconditional D hrel h hns)) ε) :
    ((∑ i, ε i : ℤ) : ℝ) * (a + b + c)
      = sg p2 q2 * (sg p0 q0 * D.target.oppLen 0 + sg p1 q1 * D.target.oppLen 1
          + sg p2 q2 * D.target.oppLen 2) :=
  phi1_sum (D := D) (hα := (lemma1_unconditional D hrel h hns)) (hrel := hrel) (h := h) (p0 := p0) (q0 := q0) (p1 := p1) (q1 := q1) (p2 := p2) (q2 := q2) (h0 := h0) (h1 := h1) (h2 := h2) (ε := ε) (hε := hε)

theorem phi2_sum_h1unc (D : CongruentDissection N) {α β a b c : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β)) (p0 q0 p1 q1 p2 q2 : ℤ)
    (h0 : D.target.angleAt 0 = (p0 : ℝ) * α + (q0 : ℝ) * β)
    (h1 : D.target.angleAt 1 = (p1 : ℝ) * α + (q1 : ℝ) * β)
    (h2 : D.target.angleAt 2 = (p2 : ℝ) * α + (q2 : ℝ) * β)
    (ε : Fin N → ℤ) (hε : SignsFor D (Phi2 D α (lemma1_unconditional D hrel h hns)) ε) :
    ((∑ i, ε i : ℤ) : ℝ) * (a - b - c)
      = sg0 p2 * (sg0 p0 * D.target.oppLen 0 + sg0 p1 * D.target.oppLen 1
          + sg0 p2 * D.target.oppLen 2) :=
  phi2_sum (D := D) (hα := (lemma1_unconditional D hrel h hns)) (hrel := hrel) (h := h) (p0 := p0) (q0 := q0) (p1 := p1) (q1 := q1) (p2 := p2) (q2 := q2) (h0 := h0) (h1 := h1) (h2 := h2) (ε := ε) (hε := hε)

theorem val_tri_h1unc (D : CongruentDissection N) {α β a b c : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β)) (ε1 ε2 : Fin N → ℤ)
    (hε1 : SignsFor D (Phi1 D α (lemma1_unconditional D hrel h hns)) ε1) (hε2 : SignsFor D (Phi2 D α (lemma1_unconditional D hrel h hns)) ε2)
    (e0 : D.target.angleAt 0 = 2 * α) (e1 : D.target.angleAt 1 = β)
    (e2 : D.target.angleAt 2 = α + β) :
    ((∑ i, ε1 i : ℤ) : ℝ) = (circD D.target / circD D.model) * (a / c) ∧
    ((∑ i, ε2 i : ℤ) : ℝ) = (circD D.target / circD D.model) * (a / c) :=
  val_tri (D := D) (hα := (lemma1_unconditional D hrel h hns)) (hrel := hrel) (h := h) (ε1 := ε1) (ε2 := ε2) (hε1 := hε1) (hε2 := hε2) (e0 := e0) (e1 := e1) (e2 := e2)

theorem val_beta3_h1unc (D : CongruentDissection N) {α β a b c : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β)) (ε1 ε2 : Fin N → ℤ)
    (hε1 : SignsFor D (Phi1 D α (lemma1_unconditional D hrel h hns)) ε1) (hε2 : SignsFor D (Phi2 D α (lemma1_unconditional D hrel h hns)) ε2)
    (e0 : D.target.angleAt 0 = β) (e1 : D.target.angleAt 1 = 3 * α)
    (e2 : D.target.angleAt 2 = β) :
    ((∑ i, ε1 i : ℤ) : ℝ) = (circD D.target / circD D.model) * ((1 - (a / c)) * (1 + (a / c)) ^ 2) ∧
    ((∑ i, ε2 i : ℤ) : ℝ) = -((circD D.target / circD D.model) * ((1 - (a / c)) ^ 2 * (1 + (a / c)))) :=
  val_beta3 (D := D) (hα := (lemma1_unconditional D hrel h hns)) (hrel := hrel) (h := h) (ε1 := ε1) (ε2 := ε2) (hε1 := hε1) (hε2 := hε2) (e0 := e0) (e1 := e1) (e2 := e2)

theorem val_apb_h1unc (D : CongruentDissection N) {α β a b c : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β)) (ε1 ε2 : Fin N → ℤ)
    (hε1 : SignsFor D (Phi1 D α (lemma1_unconditional D hrel h hns)) ε1) (hε2 : SignsFor D (Phi2 D α (lemma1_unconditional D hrel h hns)) ε2)
    (e0 : D.target.angleAt 0 = α + β) (e1 : D.target.angleAt 1 = α)
    (e2 : D.target.angleAt 2 = α + β) :
    ((∑ i, ε1 i : ℤ) : ℝ) = (circD D.target / circD D.model) * (1 / (1 + (a / c))) ∧
    ((∑ i, ε2 i : ℤ) : ℝ) = -((circD D.target / circD D.model) * (1 / (1 - (a / c)))) :=
  val_apb (D := D) (hα := (lemma1_unconditional D hrel h hns)) (hrel := hrel) (h := h) (ε1 := ε1) (ε2 := ε2) (hε1 := hε1) (hε2 := hε2) (e0 := e0) (e1 := e1) (e2 := e2)

theorem val_a2b_h1unc (D : CongruentDissection N) {α β a b c : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β)) (ε1 ε2 : Fin N → ℤ)
    (hε1 : SignsFor D (Phi1 D α (lemma1_unconditional D hrel h hns)) ε1) (hε2 : SignsFor D (Phi2 D α (lemma1_unconditional D hrel h hns)) ε2)
    (e0 : D.target.angleAt 0 = α) (e1 : D.target.angleAt 1 = α + 2 * β)
    (e2 : D.target.angleAt 2 = α) :
    ((∑ i, ε1 i : ℤ) : ℝ) = (circD D.target / circD D.model) * ((a / c) * (2 + (a / c)) / (1 + (a / c))) ∧
    ((∑ i, ε2 i : ℤ) : ℝ) = -((circD D.target / circD D.model) * ((a / c) * (2 - (a / c)) / (1 - (a / c)))) :=
  val_a2b (D := D) (hα := (lemma1_unconditional D hrel h hns)) (hrel := hrel) (h := h) (ε1 := ε1) (ε2 := ε2) (hε1 := hε1) (hε2 := hε2) (e0 := e0) (e1 := e1) (e2 := e2)

theorem val_2a2b_h1unc (D : CongruentDissection N) {α β a b c : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β)) (ε1 ε2 : Fin N → ℤ)
    (hε1 : SignsFor D (Phi1 D α (lemma1_unconditional D hrel h hns)) ε1) (hε2 : SignsFor D (Phi2 D α (lemma1_unconditional D hrel h hns)) ε2)
    (e0 : D.target.angleAt 0 = 2 * α) (e1 : D.target.angleAt 1 = α)
    (e2 : D.target.angleAt 2 = 2 * β) :
    ((∑ i, ε1 i : ℤ) : ℝ) = (circD D.target / circD D.model) * ((a / c) * (1 - (a / c)) * (2 + (a / c))) ∧
    ((∑ i, ε2 i : ℤ) : ℝ) = -((circD D.target / circD D.model) * ((a / c) * (2 - (a / c)) * (1 + (a / c)))) :=
  val_2a2b (D := D) (hα := (lemma1_unconditional D hrel h hns)) (hrel := hrel) (h := h) (ε1 := ε1) (ε2 := ε2) (hε1 := hε1) (hε2 := hε2) (e0 := e0) (e1 := e1) (e2 := e2)

theorem exists_signs1_h1unc (D : CongruentDissection N) {α β a b c : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β)) :
    ∃ ε1 : Fin N → ℤ, SignsFor D (Phi1 D α (lemma1_unconditional D hrel h hns)) ε1 ∧ D.toDissection.ProperColouring ε1 :=
  exists_signs1 (D := D) (hα := (lemma1_unconditional D hrel h hns)) (hrel := hrel) (h := h)

theorem exists_signs2_h1unc (D : CongruentDissection N) {α β a b c : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β)) :
    ∃ ε2 : Fin N → ℤ, SignsFor D (Phi2 D α (lemma1_unconditional D hrel h hns)) ε2 ∧ ∀ i, ε2 i = 1 ∨ ε2 i = -1 :=
  exists_signs2 (D := D) (hα := (lemma1_unconditional D hrel h hns)) (hrel := hrel) (h := h)

theorem lemma28_printed2_h1unc (D : CongruentDissection N) {α β a b c : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β)) (ε1 ε2 : Fin N → ℤ)
    (hε1 : SignsFor D (Phi1 D α ((delta_irr_iff hrel).mpr ((delta_irr_iff hrel).mp (lemma1_unconditional D hrel h hns)))) ε1)
    (hε2 : SignsFor D (Phi2 D α ((delta_irr_iff hrel).mpr ((delta_irr_iff hrel).mp (lemma1_unconditional D hrel h hns)))) ε2)
    (M1 M2 : ℤ) (hM1 : M1 = ∑ i, ε1 i) (hM2 : M2 = ∑ i, ε2 i) :
    -- triquadratic (2α, β, α+β): M1 = M2 (= Λ s), so κ is undefined
    ((D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = β ∧ D.target.angleAt 2 = α + β) →
      M1 = M2 ∧ (M1 : ℝ) = (circD D.target / circD D.model) * (a / c)) ∧
    -- (β, 3α, β): κ = -s
    ((D.target.angleAt 0 = β ∧ D.target.angleAt 1 = 3 * α ∧ D.target.angleAt 2 = β) →
      (M2 : ℝ) - M1 ≠ 0 ∧ ((M1 : ℝ) + M2) / ((M2 : ℝ) - M1) = -(a / c)) ∧
    -- (α+β, α, α+β): κ = s
    ((D.target.angleAt 0 = α + β ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = α + β) →
      (M2 : ℝ) - M1 ≠ 0 ∧ ((M1 : ℝ) + M2) / ((M2 : ℝ) - M1) = a / c) ∧
    -- (α, α+2β, α) and (2α, α, 2β): κ = s/(2-s²), 0 < κ < 1, s = κ(2-s²), quartic
    ((D.target.angleAt 0 = α ∧ D.target.angleAt 1 = α + 2 * β ∧ D.target.angleAt 2 = α) ∨
        (D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = 2 * β) →
      (M2 : ℝ) - M1 ≠ 0 ∧ ∀ κ : ℝ, κ = ((M1 : ℝ) + M2) / ((M2 : ℝ) - M1) →
        κ = (a / c) / (2 - (a / c) ^ 2) ∧ 0 < κ ∧ κ < 1 ∧ a / c = κ * (2 - (a / c) ^ 2) ∧
          κ ^ 2 * (a / c) ^ 4 - (4 * κ ^ 2 + 1) * (a / c) ^ 2 + 4 * κ ^ 2 = 0) :=
  lemma28_printed2 (D := D) (hδ := ((delta_irr_iff hrel).mp (lemma1_unconditional D hrel h hns))) (hrel := hrel) (h := h) (ε1 := ε1) (ε2 := ε2) (hε1 := hε1) (hε2 := hε2) (M1 := M1) (M2 := M2) (hM1 := hM1) (hM2 := hM2)

theorem eps_eq_edgeWeight_h1unc (D : CongruentDissection N) {α β a b c : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β)) (bb : ZMod 2) (anc : Real.Angle)
    (hK : (chiAt α (lemma1_unconditional D hrel h hns) bb anc).tileValue D.model ≠ 0) (ε : Fin N → ℤ)
    (hε : SignsFor D (chiAt α (lemma1_unconditional D hrel h hns) bb anc) ε) (i : Fin N) (k : Fin 3)
    (hk : (D.tile i).angleAt (k + 2) = α) :
    (ε i : ℝ) = (chiAt α (lemma1_unconditional D hrel h hns) bb anc).weight ((D.tile i).leftUnit k) :=
  eps_eq_edgeWeight (D := D) (hα := (lemma1_unconditional D hrel h hns)) (hrel := hrel) (h := h) (bb := bb) (anc := anc) (hK := hK) (ε := ε) (hε := hε) (i := i) (k := k) (hk := hk)

theorem tv_plus_ne_h1unc (D : CongruentDissection N) (hrel : 3 * α + 2 * β = Real.pi) (h : D.model.ThreeAlphaData α β a b c)
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β)) (anc : Real.Angle) :
    (chiAt α (lemma1_unconditional D hrel h hns) 0 anc).tileValue D.model ≠ 0 :=
  tv_plus_ne (D := D) (hα := (lemma1_unconditional D hrel h hns)) (hrel := hrel) (h := h) (anc := anc)

theorem tv_minus_ne_h1unc (D : CongruentDissection N) (hrel : 3 * α + 2 * β = Real.pi) (h : D.model.ThreeAlphaData α β a b c)
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β)) (anc : Real.Angle) :
    (chiAt α (lemma1_unconditional D hrel h hns) 1 anc).tileValue D.model ≠ 0 :=
  tv_minus_ne (D := D) (hα := (lemma1_unconditional D hrel h hns)) (hrel := hrel) (h := h) (anc := anc)

theorem eps2_printed_h1unc (D : CongruentDissection N) (hrel : 3 * α + 2 * β = Real.pi) (h : D.model.ThreeAlphaData α β a b c)
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β))
    (ε2 : Fin N → ℤ) (hε2 : SignsFor D (Phi2 D α (lemma1_unconditional D hrel h hns)) ε2) (i : Fin N) (k : Fin 3)
    (hk : (D.tile i).angleAt (k + 2) = α) (n e : ℤ)
    (hdir : ((D.tile i).leftUnit k).angle
      = (D.target.leftUnit 0).angle + (((n : ℝ) * (α + β) + (e : ℝ) * Real.pi : ℝ) : Real.Angle)) :
    (ε2 i : ℝ) = (-1 : ℝ) ^ (n + e) :=
  eps2_printed (D := D) (hα := (lemma1_unconditional D hrel h hns)) (hrel := hrel) (h := h) (ε2 := ε2) (hε2 := hε2) (i := i) (k := k) (hk := hk) (n := n) (e := e) (hdir := hdir)

theorem eps1_printed_h1unc (D : CongruentDissection N) (hrel : 3 * α + 2 * β = Real.pi) (h : D.model.ThreeAlphaData α β a b c)
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β))
    (ε1 : Fin N → ℤ) (hε1 : SignsFor D (Phi1 D α (lemma1_unconditional D hrel h hns)) ε1) (i : Fin N) (k : Fin 3)
    (hk : (D.tile i).angleAt (k + 2) = α) (n e : ℤ)
    (hdir : ((D.tile i).leftUnit k).angle
      = (D.target.leftUnit 0).angle + (((n : ℝ) * (α + β) + (e : ℝ) * Real.pi : ℝ) : Real.Angle)) :
    (ε1 i : ℝ) = (-1 : ℝ) ^ e :=
  eps1_printed (D := D) (hα := (lemma1_unconditional D hrel h hns)) (hrel := hrel) (h := h) (ε1 := ε1) (hε1 := hε1) (i := i) (k := k) (hk := hk) (n := n) (e := e) (hdir := hdir)

theorem exists_printed_h1unc (D : CongruentDissection N) (hrel : 3 * α + 2 * β = Real.pi) (h : D.model.ThreeAlphaData α β a b c)
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β))
    (hc : AnchorCoset D α (lemma1_unconditional D hrel h hns)) :
    ∀ i : Fin N, ∃ (k : Fin 3) (n e : ℤ), (D.tile i).angleAt (k + 2) = α ∧
      ((D.tile i).leftUnit k).angle
        = (D.target.leftUnit 0).angle + (((n : ℝ) * (α + β) + (e : ℝ) * Real.pi : ℝ) : Real.Angle) :=
  exists_printed (D := D) (hα := (lemma1_unconditional D hrel h hns)) (hrel := hrel) (h := h) (hc := hc)

theorem printed_sums_h1unc (D : CongruentDissection N) (hrel : 3 * α + 2 * β = Real.pi) (h : D.model.ThreeAlphaData α β a b c)
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β))
    (ε1 ε2 : Fin N → ℤ) (hε1 : SignsFor D (Phi1 D α (lemma1_unconditional D hrel h hns)) ε1) (hε2 : SignsFor D (Phi2 D α (lemma1_unconditional D hrel h hns)) ε2)
    (k : Fin N → Fin 3) (n e : Fin N → ℤ)
    (hk : ∀ i, (D.tile i).angleAt (k i + 2) = α)
    (hdir : ∀ i, ((D.tile i).leftUnit (k i)).angle
      = (D.target.leftUnit 0).angle + (((n i : ℝ) * (α + β) + (e i : ℝ) * Real.pi : ℝ) : Real.Angle)) :
    (((∑ i, ε1 i : ℤ)) : ℝ) = ∑ i, (-1 : ℝ) ^ (e i) ∧
      (((∑ i, ε2 i : ℤ)) : ℝ) = ∑ i, (-1 : ℝ) ^ (n i + e i) :=
  printed_sums (D := D) (hα := (lemma1_unconditional D hrel h hns)) (hrel := hrel) (h := h) (ε1 := ε1) (ε2 := ε2) (hε1 := hε1) (hε2 := hε2) (k := k) (n := n) (e := e) (hk := hk) (hdir := hdir)

theorem lemma28_printed3_h1unc (D : CongruentDissection N) {α β a b c : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β))
    (k : Fin N → Fin 3) (n e : Fin N → ℤ)
    (hk : ∀ i, (D.tile i).angleAt (k i + 2) = α)
    (hdir : ∀ i, ((D.tile i).leftUnit (k i)).angle
      = (D.target.leftUnit 0).angle + (((n i : ℝ) * (α + β) + (e i : ℝ) * Real.pi : ℝ) : Real.Angle))
    (M1 M2 : ℤ) (hM1 : (M1 : ℝ) = ∑ i, (-1 : ℝ) ^ (e i))
    (hM2 : (M2 : ℝ) = ∑ i, (-1 : ℝ) ^ (n i + e i)) :
    -- triquadratic (2α, β, α+β): M1 = M2 (= Λ s), so κ is undefined
    ((D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = β ∧ D.target.angleAt 2 = α + β) →
      M1 = M2 ∧ (M1 : ℝ) = (circD D.target / circD D.model) * (a / c)) ∧
    -- (β, 3α, β): κ = -s
    ((D.target.angleAt 0 = β ∧ D.target.angleAt 1 = 3 * α ∧ D.target.angleAt 2 = β) →
      (M2 : ℝ) - M1 ≠ 0 ∧ ((M1 : ℝ) + M2) / ((M2 : ℝ) - M1) = -(a / c)) ∧
    -- (α+β, α, α+β): κ = s
    ((D.target.angleAt 0 = α + β ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = α + β) →
      (M2 : ℝ) - M1 ≠ 0 ∧ ((M1 : ℝ) + M2) / ((M2 : ℝ) - M1) = a / c) ∧
    -- (α, α+2β, α) and (2α, α, 2β): κ = s/(2-s²), 0 < κ < 1, s = κ(2-s²), quartic
    ((D.target.angleAt 0 = α ∧ D.target.angleAt 1 = α + 2 * β ∧ D.target.angleAt 2 = α) ∨
        (D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = 2 * β) →
      (M2 : ℝ) - M1 ≠ 0 ∧ ∀ κ : ℝ, κ = ((M1 : ℝ) + M2) / ((M2 : ℝ) - M1) →
        κ = (a / c) / (2 - (a / c) ^ 2) ∧ 0 < κ ∧ κ < 1 ∧ a / c = κ * (2 - (a / c) ^ 2) ∧
          κ ^ 2 * (a / c) ^ 4 - (4 * κ ^ 2 + 1) * (a / c) ^ 2 + 4 * κ ^ 2 = 0) :=
  lemma28_printed3 (D := D) (hδ := ((delta_irr_iff hrel).mp (lemma1_unconditional D hrel h hns))) (hrel := hrel) (h := h) (k := k) (n := n) (e := e) (hk := hk) (hdir := hdir) (M1 := M1) (M2 := M2) (hM1 := hM1) (hM2 := hM2)

theorem anchorCoset_of_threeAlpha_h1unc (D : CongruentDissection N) {α β a b c : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β)) : AnchorCoset D α (lemma1_unconditional D hrel h hns) :=
  anchorCoset_of_threeAlpha (D := D) (hα := (lemma1_unconditional D hrel h hns)) (hrel := hrel) (h := h)

theorem exists_printed_unc_h1unc (D : CongruentDissection N) {α β a b c : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β)) :
    ∃ (k : Fin N → Fin 3) (n e : Fin N → ℤ), (∀ i, (D.tile i).angleAt (k i + 2) = α) ∧
      ∀ i, ((D.tile i).leftUnit (k i)).angle
        = (D.target.leftUnit 0).angle + (((n i : ℝ) * (α + β) + (e i : ℝ) * Real.pi : ℝ) : Real.Angle) :=
  exists_printed_unc (D := D) (hδ := ((delta_irr_iff hrel).mp (lemma1_unconditional D hrel h hns))) (hrel := hrel) (h := h)

end Erdos634.BeesonColoring
#print axioms Erdos634.BeesonColoring.boundary_gen_h1unc
#print axioms Erdos634.BeesonColoring.thm1_colouring_h1unc
#print axioms Erdos634.BeesonColoring.lemma28_printed_h1unc
#print axioms Erdos634.BeesonColoring.phi1_sum_h1unc
#print axioms Erdos634.BeesonColoring.phi2_sum_h1unc
#print axioms Erdos634.BeesonColoring.val_tri_h1unc
#print axioms Erdos634.BeesonColoring.val_beta3_h1unc
#print axioms Erdos634.BeesonColoring.val_apb_h1unc
#print axioms Erdos634.BeesonColoring.val_a2b_h1unc
#print axioms Erdos634.BeesonColoring.val_2a2b_h1unc
#print axioms Erdos634.BeesonColoring.exists_signs1_h1unc
#print axioms Erdos634.BeesonColoring.exists_signs2_h1unc
#print axioms Erdos634.BeesonColoring.lemma28_printed2_h1unc
#print axioms Erdos634.BeesonColoring.eps_eq_edgeWeight_h1unc
#print axioms Erdos634.BeesonColoring.tv_plus_ne_h1unc
#print axioms Erdos634.BeesonColoring.tv_minus_ne_h1unc
#print axioms Erdos634.BeesonColoring.eps2_printed_h1unc
#print axioms Erdos634.BeesonColoring.eps1_printed_h1unc
#print axioms Erdos634.BeesonColoring.exists_printed_h1unc
#print axioms Erdos634.BeesonColoring.printed_sums_h1unc
#print axioms Erdos634.BeesonColoring.lemma28_printed3_h1unc
#print axioms Erdos634.BeesonColoring.anchorCoset_of_threeAlpha_h1unc
#print axioms Erdos634.BeesonColoring.exists_printed_unc_h1unc

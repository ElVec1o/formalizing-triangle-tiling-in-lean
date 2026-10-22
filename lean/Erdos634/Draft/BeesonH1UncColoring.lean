-- Draft/BeesonH1UncColoring.lean -- NEW wrapper theorems (no in-place edits): H1 (`¬ ∃ r : ℚ, α = r π`) of the cited Beeson consumers DERIVED from
-- `BeesonH1.lemma1_unconditional`; each `*_h1unc` takes the extra hypothesis `hns` (target NOT similar to the tile, i.e. NotSim as
-- ¬ Triple3 ...), the hypothesis of lemma1_unconditional.  Statements are the originals with hα/hirr/hδ replaced by hns.
-- NOTE, UNAUDITED (depends on the unaudited lacz51_all).  Credit: Beeson (arXiv 1206.2229 v4), Beeson-Zhang, Laczkovich (Discrete Math. 140 (1995)).
import Erdos634.Draft.LaczFormal51Lemma1
import Erdos634.Draft.BeesonT25ii
import Erdos634.Draft.BeesonT25
import Erdos634.Draft.BeesonT4Final
import Erdos634.Draft.BeesonT17Eq
import Erdos634.Draft.BeesonL28
import Erdos634.Draft.BeesonL10
import Erdos634.Draft.BeesonColoringThm15
import Erdos634.Draft.BeesonColoringThm21
import Erdos634.Draft.BeesonShapesL5L6L11
import Erdos634.Draft.BeesonColoringCor7

open scoped Classical

namespace Erdos634.BeesonColoring

open Erdos634.Geometry Erdos634.Geometry.A1Field Erdos634.BeesonH1

variable {N : ℕ} {α β a b c : ℝ}

theorem thm1_h1unc (D : CongruentDissection N) {α β a b c : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β)) :
    -- base angles alpha: `+`
    ((D.target.angleAt 0 = α ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = α + 2 * β) →
      ∃ M : ℤ, 0 < M ∧ (M : ℝ) * (a + b + c) =
        D.target.oppLen 0 + D.target.oppLen 1 + D.target.oppLen 2) ∧
    -- base angles beta: `+`
    ((D.target.angleAt 0 = β ∧ D.target.angleAt 1 = β ∧ D.target.angleAt 2 = 3 * α) →
      ∃ M : ℤ, 0 < M ∧ (M : ℝ) * (a + b + c) =
        D.target.oppLen 0 + D.target.oppLen 1 + D.target.oppLen 2) ∧
    -- base angles alpha + beta: `-` on the base
    ((D.target.angleAt 0 = α + β ∧ D.target.angleAt 1 = α + β ∧ D.target.angleAt 2 = α) →
      ∃ M : ℤ, 0 < M ∧ (M : ℝ) * (a + b + c) =
        D.target.oppLen 0 + D.target.oppLen 1 - D.target.oppLen 2) ∧
    -- (2 alpha, alpha, 2 beta): `X - Y + Z`
    ((D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = 2 * β) →
      ∃ M : ℤ, 0 < M ∧ (M : ℝ) * (a + b + c) =
        D.target.oppLen 0 - D.target.oppLen 1 + D.target.oppLen 2) ∧
    -- (2 alpha, beta, alpha + beta): `X - Y + Z`
    ((D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = β ∧ D.target.angleAt 2 = α + β) →
      ∃ M : ℤ, 0 < M ∧ (M : ℝ) * (a + b + c) =
        D.target.oppLen 0 - D.target.oppLen 1 + D.target.oppLen 2) :=
  thm1 (D := D) (hα := (lemma1_unconditional D hrel h hns)) (hrel := hrel) (h := h)

theorem thm13_h1unc (D : CongruentDissection N) {α β a b c : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β))
    (hP0 : D.target.angleAt 0 = 2 * α) (hP1 : D.target.angleAt 1 = α)
    (hP2 : D.target.angleAt 2 = 2 * β) :
    ∃ (M : ℤ) (s : ℚ), 0 < M ∧ (s : ℝ) = a / c ∧ (s : ℝ) = 2 * Real.sin (α / 2) ∧
      b = (1 - (s : ℝ) ^ 2) * c ∧ 0 < s ∧ s < 1 ∧
      (N : ℚ) * ((1 - s) ^ 2 * (2 + s) ^ 2) = (M : ℚ) ^ 2 * ((2 - s ^ 2) * (3 - s ^ 2)) ∧
      (N : ℚ) / (M : ℚ) ^ 2 = (2 - s ^ 2) * (3 - s ^ 2) / ((1 - s) ^ 2 * (2 + s) ^ 2) :=
  thm13 (D := D) (hα := (lemma1_unconditional D hrel h hns)) (hrel := hrel) (h := h) (hP0 := hP0) (hP1 := hP1) (hP2 := hP2)

theorem thm15_only_if_h1unc (D : CongruentDissection N) {α β k : ℝ} (a b c : ℤ) (hk : 0 < k)
    (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β (k * a) (k * b) (k * c))
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β))
    (hP0 : D.target.angleAt 0 = 2 * α) (hP1 : D.target.angleAt 1 = α)
    (hP2 : D.target.angleAt 2 = 2 * β) :
    0 < c ∧ (2 * Real.sin (α / 2) : ℝ) = (a : ℝ) / c ∧ b * c = c ^ 2 - a ^ 2 ∧ c ∣ a ^ 2 ∧
      ∃ M : ℤ, 0 < M ∧ (N : ℤ) * (b + c - a) ^ 2 = (b + c) * (b + 2 * c) * M ^ 2 :=
  thm15_only_if (D := D) (a := a) (b := b) (c := c) (hk := hk) (hα := (lemma1_unconditional D hrel h hns)) (hrel := hrel) (h := h) (hP0 := hP0) (hP1 := hP1) (hP2 := hP2)

theorem thm21_h1unc (D : CongruentDissection N) {α β a b c : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β))
    (hP0 : D.target.angleAt 0 = α + β) (hP1 : D.target.angleAt 1 = α + β)
    (hP2 : D.target.angleAt 2 = α) :
    ∃ (M : ℤ) (s : ℚ), 0 < M ∧ (s : ℝ) = a / c ∧ (s : ℝ) = 2 * Real.sin (α / 2) ∧
      0 < s ∧ s < 1 ∧ b = (1 - (s : ℝ) ^ 2) * c ∧
      (N : ℚ) * (1 - s) = (M : ℚ) ^ 2 * (1 + s) ∧
      (N : ℚ) / (M : ℚ) ^ 2 = (1 + s) / (1 - s) ∧
      s = ((N : ℚ) - (M : ℚ) ^ 2) / ((N : ℚ) + (M : ℚ) ^ 2) ∧
      D.target.oppLen 0 = (M : ℝ) * (1 + (s : ℝ)) * c ∧
      D.target.oppLen 1 = (M : ℝ) * (1 + (s : ℝ)) * c ∧
      D.target.oppLen 2 = (M : ℝ) * (1 + (s : ℝ)) * a ∧
      ((M : ℝ) * (1 + (s : ℝ))) ^ 2 * c = N * b ∧
      (M : ℚ) ^ 2 = N * ((1 - s) / (1 + s)) ∧
      (s : ℝ) = D.target.oppLen 2 / D.target.oppLen 0 :=
  thm21 (D := D) (hα := (lemma1_unconditional D hrel h hns)) (hrel := hrel) (h := h) (hP0 := hP0) (hP1 := hP1) (hP2 := hP2)

theorem cor7_only_if_h1unc {N : ℕ} (D : CongruentDissection N) {α β A B C : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β A B C)
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β))
    (hP0 : D.target.angleAt 0 = 2 * α) (hP1 : D.target.angleAt 1 = α) (hP2 : D.target.angleAt 2 = 2 * β) :
    ∃ q : ℚ, 2 * Real.sin (α / 2) = (q : ℝ) :=
  Cor7.cor7_only_if (D := D) (hα := (lemma1_unconditional D hrel h hns)) (hrel := hrel) (h := h) (hP0 := hP0) (hP1 := hP1) (hP2 := hP2)

theorem corner_fig_h1unc {N : ℕ} (D : CongruentDissection N) {α β a b c : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β)) (k : Fin 3) :
    vcount D k Real.pi = 0 ∧
    (vcount D k α : ℝ) * α + (vcount D k β : ℝ) * β + (vcount D k (2 * α + β) : ℝ) * (2 * α + β)
      = D.target.angleAt k :=
  corner_fig (D := D) (hirr := (lemma1_unconditional D hrel h hns)) (hrel := hrel) (h := h) (k := k)

theorem corner_totals_h1unc {N : ℕ} (D : CongruentDissection N) {α β a b c : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β)) :
    (∑ k, vcount D k α) + 2 * (∑ k, vcount D k (2 * α + β)) = 3 ∧
    (∑ k, vcount D k β) + (∑ k, vcount D k (2 * α + β)) = 2 :=
  corner_totals (D := D) (hirr := (lemma1_unconditional D hrel h hns)) (hrel := hrel) (h := h)

theorem lemma11_h1unc {N : ℕ} (D : CongruentDissection N) {α β a b c : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β)) :
    FiveShapes (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β ∧
    (∑ k, vcount D k α) = 3 ∧ (∑ k, vcount D k β) = 2 ∧ (∀ k, vcount D k (2 * α + β) = 0) ∧
    (∀ k, 1 ≤ vcount D k α + vcount D k β) :=
  lemma11 (D := D) (hirr := (lemma1_unconditional D hrel h hns)) (hrel := hrel) (h := h) (hns := hns)

theorem lemma10_h1unc {N : ℕ} (D : CongruentDissection N) {α β a b c : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β)) :
    (∀ v ∈ cornerPts D.toDissection, v ∉ Set.range D.target.pts →
      vecAt D α β v = (3, 2, 0) ∨ vecAt D α β v = (1, 1, 1) ∨ vecAt D α β v = (2, 2, 2) ∨
      vecAt D α β v = (6, 4, 0) ∨ vecAt D α β v = (4, 3, 1) ∨ vecAt D α β v = (0, 1, 3)) ∧
    ((cornerPts D.toDissection).filter (fun v => vecAt D α β v = (0, 1, 3))).card
      = 1 + ((cornerPts D.toDissection).filter (fun v => vecAt D α β v = (3, 2, 0))).card
        + 2 * ((cornerPts D.toDissection).filter (fun v => vecAt D α β v = (6, 4, 0))).card
        + ((cornerPts D.toDissection).filter (fun v => vecAt D α β v = (4, 3, 1))).card :=
  lemma10 (D := D) (hirr := (lemma1_unconditional D hrel h hns)) (hrel := hrel) (h := h) (hns := hns)

theorem t4_M1_h1unc (D : CongruentDissection N) {α β a b c : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β)) :
    ((D.target.angleAt 0 = α ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = α + 2 * β) →
      ∃ M : ℤ, 0 < M ∧ (M : ℝ) = (circD D.target / circD D.model) * ((a / c) * (2 + a / c) / (1 + a / c))) ∧
    ((D.target.angleAt 0 = β ∧ D.target.angleAt 1 = β ∧ D.target.angleAt 2 = 3 * α) →
      ∃ M : ℤ, 0 < M ∧ (M : ℝ) = (circD D.target / circD D.model) * ((1 - a / c) * (1 + a / c) ^ 2)) ∧
    ((D.target.angleAt 0 = α + β ∧ D.target.angleAt 1 = α + β ∧ D.target.angleAt 2 = α) →
      ∃ M : ℤ, 0 < M ∧ (M : ℝ) = (circD D.target / circD D.model) * (1 / (1 + a / c))) ∧
    ((D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = 2 * β) →
      ∃ M : ℤ, 0 < M ∧ (M : ℝ) = (circD D.target / circD D.model) *
        ((a / c) * (1 - a / c) * (2 + a / c))) ∧
    ((D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = β ∧ D.target.angleAt 2 = α + β) →
      ∃ M : ℤ, 0 < M ∧ (M : ℝ) = (circD D.target / circD D.model) * (a / c)) :=
  t4_M1 (D := D) (hα := (lemma1_unconditional D hrel h hns)) (hrel := hrel) (h := h)

theorem t4_M2_T5_h1unc (D : CongruentDissection N) {α β a b c : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β)) :
    ((D.target.angleAt 0 = α ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = α + 2 * β) →
      ∃ M1 M2 : ℤ, (M1 : ℝ) = (circD D.target / circD D.model) * ((a / c) * (2 + a / c) / (1 + a / c)) ∧
        (M2 : ℝ) = -((circD D.target / circD D.model) * ((a / c) * (2 - a / c) / (1 - a / c)))) ∧
    ((D.target.angleAt 0 = β ∧ D.target.angleAt 1 = β ∧ D.target.angleAt 2 = 3 * α) →
      ∃ M1 M2 : ℤ, (M1 : ℝ) = (circD D.target / circD D.model) * ((1 - a / c) * (1 + a / c) ^ 2) ∧
        (M2 : ℝ) = -((circD D.target / circD D.model) * ((1 - a / c) ^ 2 * (1 + a / c))) ∧
        a / c = ((M1 : ℝ) + M2) / ((M1 : ℝ) - M2) ∧ ∃ q : ℚ, a / c = (q : ℝ)) ∧
    ((D.target.angleAt 0 = α + β ∧ D.target.angleAt 1 = α + β ∧ D.target.angleAt 2 = α) →
      ∃ M1 M2 : ℤ, (M1 : ℝ) = (circD D.target / circD D.model) * (1 / (1 + a / c)) ∧
        (M2 : ℝ) = -((circD D.target / circD D.model) * (1 / (1 - a / c))) ∧
        a / c = ((M1 : ℝ) + M2) / ((M2 : ℝ) - M1) ∧ ∃ q : ℚ, a / c = (q : ℝ)) :=
  t4_M2_T5 (D := D) (hα := (lemma1_unconditional D hrel h hns)) (hrel := hrel) (h := h)

theorem t4_M2_rows45_h1unc (D : CongruentDissection N) {α β a b c : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β)) :
    ((D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = 2 * β) →
      ∃ M1 M2 : ℤ, (M1 : ℝ) = (circD D.target / circD D.model) * ((a / c) * (1 - a / c) * (2 + a / c)) ∧
        (M2 : ℝ) = -((circD D.target / circD D.model) * ((a / c) * (2 - a / c) * (1 + a / c)))) ∧
    ((D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = β ∧ D.target.angleAt 2 = α + β) →
      ∃ M1 M2 : ℤ, (M1 : ℝ) = (circD D.target / circD D.model) * (a / c) ∧
        (M2 : ℝ) = (circD D.target / circD D.model) * (a / c)) :=
  t4_M2_rows45 (D := D) (hα := (lemma1_unconditional D hrel h hns)) (hrel := hrel) (h := h)

theorem t4_final_h1unc (D : CongruentDissection N) {α β a b c : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β)) :
    ((D.target.angleAt 0 = α ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = α + 2 * β) →
      ∃ M1 M2 : ℤ, (M1 : ℝ) = (circD D.target / circD D.model) * ((a / c) * (2 + a / c) / (1 + a / c)) ∧
        (M2 : ℝ) = -((circD D.target / circD D.model) * ((a / c) * (2 - a / c) / (1 - a / c))) ∧
        M1 ≠ 0 ∧ M2 ≠ 0) ∧
    ((D.target.angleAt 0 = β ∧ D.target.angleAt 1 = β ∧ D.target.angleAt 2 = 3 * α) →
      ∃ M1 M2 : ℤ, (M1 : ℝ) = (circD D.target / circD D.model) * ((1 - a / c) * (1 + a / c) ^ 2) ∧
        (M2 : ℝ) = -((circD D.target / circD D.model) * ((1 - a / c) ^ 2 * (1 + a / c))) ∧
        M1 ≠ 0 ∧ M2 ≠ 0) ∧
    ((D.target.angleAt 0 = α + β ∧ D.target.angleAt 1 = α + β ∧ D.target.angleAt 2 = α) →
      ∃ M1 M2 : ℤ, (M1 : ℝ) = (circD D.target / circD D.model) * (1 / (1 + a / c)) ∧
        (M2 : ℝ) = -((circD D.target / circD D.model) * (1 / (1 - a / c))) ∧ M1 ≠ 0 ∧ M2 ≠ 0) ∧
    ((D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = 2 * β) →
      ∃ M1 M2 : ℤ, (M1 : ℝ) = (circD D.target / circD D.model) * ((a / c) * (1 - a / c) * (2 + a / c)) ∧
        (M2 : ℝ) = -((circD D.target / circD D.model) * ((a / c) * (2 - a / c) * (1 + a / c))) ∧
        M1 ≠ 0 ∧ M2 ≠ 0) ∧
    ((D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = β ∧ D.target.angleAt 2 = α + β) →
      ∃ M1 M2 : ℤ, (M1 : ℝ) = (circD D.target / circD D.model) * (a / c) ∧
        (M2 : ℝ) = (circD D.target / circD D.model) * (a / c) ∧ M1 ≠ 0 ∧ M2 ≠ 0 ∧
        circD D.target / circD D.model = (M1 : ℝ) / (a / c)) :=
  t4_final (D := D) (hα := (lemma1_unconditional D hrel h hns)) (hrel := hrel) (h := h)

theorem t6_h1unc (D : CongruentDissection N) {α β a b c : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β)) :
    ((D.target.angleAt 0 = α ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = α + 2 * β) →
      ∃ M1 M2 : ℤ, (M1 : ℝ) = (circD D.target / circD D.model) * ((a / c) * (2 + a / c) / (1 + a / c)) ∧
        (M2 : ℝ) = -((circD D.target / circD D.model) * ((a / c) * (2 - a / c) / (1 - a / c))) ∧
        (N : ℝ) + M1 * M2 ≠ 0 ∧
        (a / c) ^ 2 = 2 * (2 * N + M1 * M2) / (N + M1 * M2) ∧ ∃ q : ℚ, (q : ℝ) = a / c) ∧
    ((D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = 2 * β) →
      ∃ M1 M2 : ℤ, (M1 : ℝ) = (circD D.target / circD D.model) * ((a / c) * (1 - a / c) * (2 + a / c)) ∧
        (M2 : ℝ) = -((circD D.target / circD D.model) * ((a / c) * (2 - a / c) * (1 + a / c))) ∧
        (N : ℝ) + M1 * M2 ≠ 0 ∧
        (a / c) ^ 2 = ((M1 : ℝ) + M2) ^ 2 / (2 * (N + M1 * M2)) ∧ ∃ q : ℚ, (q : ℝ) = a / c) :=
  t6 (D := D) (hα := (lemma1_unconditional D hrel h hns)) (hrel := hrel) (h := h)

theorem t25_i_h1unc (D : CongruentDissection N) {α β a b c : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β))
    (e0 : D.target.angleAt 0 = α) (e1 : D.target.angleAt 1 = α)
    (e2 : D.target.angleAt 2 = α + 2 * β) :
    ∃ M : ℤ, 0 < M ∧ 0 < a / c ∧ a / c < 1 ∧
      (N : ℝ) * ((1 - a / c) * (2 + a / c) ^ 2) = (M : ℝ) ^ 2 * ((1 + a / c) * (2 - (a / c) ^ 2)) ∧
      (M : ℝ) ^ 2 ≤ 2 * N :=
  t25_i (D := D) (hα := (lemma1_unconditional D hrel h hns)) (hrel := hrel) (h := h) (e0 := e0) (e1 := e1) (e2 := e2)

theorem t25_ii_h1unc (D : CongruentDissection N) {α β a b c : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β))
    (e0 : D.target.angleAt 0 = α) (e1 : D.target.angleAt 1 = α)
    (e2 : D.target.angleAt 2 = α + 2 * β)
    (g k m : ℕ) (hg : 0 < g) (hcop : Nat.Coprime k m)
    (ha : a = (g : ℝ) * ((m : ℝ) * k)) (hb : b = (g : ℝ) * ((k : ℝ) ^ 2 - (m : ℝ) ^ 2))
    (hc : c = (g : ℝ) * (k : ℝ) ^ 2) :
    ∃ M j : ℤ, 0 < M ∧ M = ((2 * k + m : ℕ) : ℤ) * j ∧
      (N : ℤ) * ((k : ℤ) - m) = j ^ 2 * ((m : ℤ) + k) * (2 * (k : ℤ) ^ 2 - (m : ℤ) ^ 2) :=
  t25_ii (D := D) (hα := (lemma1_unconditional D hrel h hns)) (hrel := hrel) (h := h) (e0 := e0) (e1 := e1) (e2 := e2) (g := g) (k := k) (m := m) (hg := hg) (hcop := hcop) (ha := ha) (hb := hb) (hc := hc)

theorem second_tiling_eq_h1unc (D : CongruentDissection N) {α β a b c : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β))
    (e0 : D.target.angleAt 0 = 2 * α) (e1 : D.target.angleAt 1 = α) (e2 : D.target.angleAt 2 = 2 * β) :
    ∃ (M : ℤ) (q : ℚ), 0 < M ∧ (q : ℝ) = a / c ∧ 0 < a / c ∧ a / c < 1 ∧
      (N : ℝ) * ((1 - a / c) ^ 2 * (2 + a / c) ^ 2) = (M : ℝ) ^ 2 * ((2 - (a / c) ^ 2) * (3 - (a / c) ^ 2)) :=
  second_tiling_eq (D := D) (hα := (lemma1_unconditional D hrel h hns)) (hrel := hrel) (h := h) (e0 := e0) (e1 := e1) (e2 := e2)

theorem lemma28_h1unc (D : CongruentDissection N) {α β a b c : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β)) :
    -- triquadratic: M1 = M2 (kappa undefined)
    ((D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = β ∧ D.target.angleAt 2 = α + β) →
      ∃ M1 M2 : ℤ, M1 = M2 ∧ M1 ≠ 0) ∧
    -- (beta, 3 alpha, beta): kappa = -s
    ((D.target.angleAt 0 = β ∧ D.target.angleAt 1 = β ∧ D.target.angleAt 2 = 3 * α) →
      ∃ M1 M2 : ℤ, (M2 : ℝ) - M1 ≠ 0 ∧ ((M1 : ℝ) + M2) / ((M2 : ℝ) - M1) = -(a / c)) ∧
    -- (alpha+beta, alpha, alpha+beta): kappa = s
    ((D.target.angleAt 0 = α + β ∧ D.target.angleAt 1 = α + β ∧ D.target.angleAt 2 = α) →
      ∃ M1 M2 : ℤ, (M2 : ℝ) - M1 ≠ 0 ∧ ((M1 : ℝ) + M2) / ((M2 : ℝ) - M1) = a / c) ∧
    -- (alpha, alpha+2beta, alpha) [t4_final order (alpha,alpha,alpha+2beta)] and (2alpha, alpha, 2beta):
    -- kappa = s/(2-s^2), 0 < kappa < 1, s = kappa (2-s^2), quartic
    (∀ (_ : (D.target.angleAt 0 = α ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = α + 2 * β) ∨
        (D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = 2 * β)),
      ∃ M1 M2 : ℤ, (M2 : ℝ) - M1 ≠ 0 ∧
        ∃ κ : ℝ, κ = ((M1 : ℝ) + M2) / ((M2 : ℝ) - M1) ∧ κ = (a / c) / (2 - (a / c) ^ 2) ∧
          0 < κ ∧ κ < 1 ∧ a / c = κ * (2 - (a / c) ^ 2) ∧
          κ ^ 2 * (a / c) ^ 4 - (4 * κ ^ 2 + 1) * (a / c) ^ 2 + 4 * κ ^ 2 = 0) :=
  lemma28 (D := D) (hα := (lemma1_unconditional D hrel h hns)) (hrel := hrel) (h := h)

end Erdos634.BeesonColoring
#print axioms Erdos634.BeesonColoring.thm1_h1unc
#print axioms Erdos634.BeesonColoring.thm13_h1unc
#print axioms Erdos634.BeesonColoring.thm15_only_if_h1unc
#print axioms Erdos634.BeesonColoring.thm21_h1unc
#print axioms Erdos634.BeesonColoring.cor7_only_if_h1unc
#print axioms Erdos634.BeesonColoring.corner_fig_h1unc
#print axioms Erdos634.BeesonColoring.corner_totals_h1unc
#print axioms Erdos634.BeesonColoring.lemma11_h1unc
#print axioms Erdos634.BeesonColoring.lemma10_h1unc
#print axioms Erdos634.BeesonColoring.t4_M1_h1unc
#print axioms Erdos634.BeesonColoring.t4_M2_T5_h1unc
#print axioms Erdos634.BeesonColoring.t4_M2_rows45_h1unc
#print axioms Erdos634.BeesonColoring.t4_final_h1unc
#print axioms Erdos634.BeesonColoring.t6_h1unc
#print axioms Erdos634.BeesonColoring.t25_i_h1unc
#print axioms Erdos634.BeesonColoring.t25_ii_h1unc
#print axioms Erdos634.BeesonColoring.second_tiling_eq_h1unc
#print axioms Erdos634.BeesonColoring.lemma28_h1unc

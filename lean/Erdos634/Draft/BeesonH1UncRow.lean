-- Draft/BeesonH1UncRow.lean -- NEW wrapper theorems (no in-place edits): the consumers of H1 ("alpha is not a rational multiple of pi")
-- in BeesonRowSect10, BeesonRow2Trig, BeesonCol2L31, with H1 DERIVED from `BeesonH1.lemma1_unconditional`.
-- Extra hypotheses (these are exactly the hypotheses of `lemma1_unconditional`): a CongruentDissection D whose model has
-- `ThreeAlphaData alpha beta a b c`, `3 alpha + 2 beta = pi`, and NotSim: `hns : ¬ Triple3 (target angles) alpha beta (2 alpha + beta)`.
-- NOTE, UNAUDITED (depends on the unaudited `lacz51_all`).  Credit: Beeson (arXiv 1206.2229 v4, Lemmas 17, 23, 24, 31, 38), Laczkovich
-- (Discrete Math. 140 (1995) Thm 5.1, 5.3), Beeson-Zhang.
import Erdos634.Draft.LaczFormal51Lemma1
import Erdos634.Draft.BeesonRow2Trig
import Erdos634.Draft.BeesonCol2L31

namespace Erdos634.BeesonH1Unc

open Erdos634 Erdos634.Geometry Erdos634.BeesonColoring Erdos634.BeesonH1

section
variable {N : ℕ} (D : CongruentDissection N) {α β a b c : ℝ}
  (hrel : 3 * α + 2 * β = Real.pi) (h : D.model.ThreeAlphaData α β a b c)
  (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β))

include hrel h hns

theorem lemma23_unique_h1unc (p q u v : ℤ) (hpq : (p : ℝ) * α + q * β = u * α + v * β) : p = u ∧ q = v :=
  Erdos634.BeesonRow.lemma23_unique α β hrel (lemma1_unconditional D hrel h hns) p q u v hpq

theorem lemma23_sector_h1unc (x y z p q : ℕ) (hh : (x : ℝ) * α + y * β + z * (2 * α + β) = p * α + q * β) :
    x + 2 * z = p ∧ y + z = q :=
  Erdos634.BeesonRow.lemma23_sector α β hrel (lemma1_unconditional D hrel h hns) x y z p q hh

theorem lemma23_items_h1unc (x y z : ℕ) :
    ((x : ℝ) * α + y * β + z * (2 * α + β) = α → x = 1 ∧ y = 0 ∧ z = 0) ∧
    ((x : ℝ) * α + y * β + z * (2 * α + β) = β → x = 0 ∧ y = 1 ∧ z = 0) ∧
    ((x : ℝ) * α + y * β + z * (2 * α + β) = α + β → x = 1 ∧ y = 1 ∧ z = 0) ∧
    ((x : ℝ) * α + y * β + z * (2 * α + β) = 3 * α → x = 3 ∧ y = 0 ∧ z = 0) ∧
    ((x : ℝ) * α + y * β + z * (2 * α + β) = α + 2 * β → x = 1 ∧ y = 2 ∧ z = 0) :=
  Erdos634.BeesonRow.lemma23_items α β hrel (lemma1_unconditional D hrel h hns) x y z

theorem lemma24_core_h1unc (p q r s : ℕ) (hpq : 2 ≤ p + q)
    (hsum : ((2 * α + β) + (r * α + s * β)) + (p * α + q * β) = Real.pi) :
    p = 1 ∧ q = 1 ∧ r = 0 ∧ s = 0 :=
  Erdos634.BeesonRow.lemma24_core α β hrel (lemma1_unconditional D hrel h hns) p q r s hpq hsum

theorem lemma24_rest_h1unc (u2 v2 u3 v3 : ℕ) (h2 : 1 ≤ u2 + v2) (h3' : 1 ≤ u3 + v3)
    (hh : ((u2 : ℝ) * α + v2 * β) + (u3 * α + v3 * β) = α + β) :
    (u2 = 1 ∧ v2 = 0 ∧ u3 = 0 ∧ v3 = 1) ∨ (u2 = 0 ∧ v2 = 1 ∧ u3 = 1 ∧ v3 = 0) :=
  Erdos634.BeesonRow.lemma24_rest α β hrel (lemma1_unconditional D hrel h hns) u2 v2 u3 v3 h2 h3' hh

theorem lemma17_h1unc (δ : ℝ) (hδ : δ = α + β) : ¬ ∃ r : ℚ, δ = (r : ℝ) * Real.pi :=
  Erdos634.BeesonRow2.lemma17 α β δ hδ hrel (lemma1_unconditional D hrel h hns)

theorem lemma38_arith_h1unc (hβ : 0 < β) :
    (¬ ∃ r : ℚ, β = (r : ℝ) * Real.pi) ∧ (¬ ∃ r : ℚ, α = (r : ℝ) * β) :=
  Erdos634.BeesonRow2.lemma38_arith α β hrel hβ (lemma1_unconditional D hrel h hns)

theorem l31_irr_of_h1_h1unc : ¬ ∃ q : ℚ, α = (q : ℝ) * β :=
  Erdos634.BeesonCol2L31.l31_irr_of_h1 hrel (lemma1_unconditional D hrel h hns)

end

end Erdos634.BeesonH1Unc

#print axioms Erdos634.BeesonH1Unc.lemma23_unique_h1unc
#print axioms Erdos634.BeesonH1Unc.lemma23_items_h1unc
#print axioms Erdos634.BeesonH1Unc.lemma24_core_h1unc
#print axioms Erdos634.BeesonH1Unc.lemma24_rest_h1unc
#print axioms Erdos634.BeesonH1Unc.lemma17_h1unc
#print axioms Erdos634.BeesonH1Unc.lemma38_arith_h1unc
#print axioms Erdos634.BeesonH1Unc.l31_irr_of_h1_h1unc

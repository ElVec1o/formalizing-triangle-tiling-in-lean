/-
Draft/CompositeFinal8.lean — `GapE120 N` and `GapE60 N` PROVED for N = 35, 39, 51, 55 and `GapE120 87` PROVED; `GapE60 87`
reduced to the single pair `E60Pair 87 29 9` (D = 52 non-square but `2·87 = 3·38 + 3·20` has a side solution (p,q,r) = (3,3,3)).
All via `CompositeE5Gen` (irrational-part side matching + E7b at the pin), by finite arithmetic on the pairs `(s,t)`, `s t = 3N`.
Then the conditional chains with the equilateral leaves discharged.
*** CONDITIONAL.  UNAUDITED.  Formalization debt, NOT /goal progress.  No sorry, no native_decide. ***
-/
import Erdos634.Draft.CompositeE5Gen

set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000
set_option maxRecDepth 4000

namespace Erdos634.Draft.CompositeFinal8

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.Chain15 Erdos634.Draft.ChainComposite
open Erdos634.Draft.CompositeGen2 Erdos634.Draft.CompositeFinal6 Erdos634.Draft.CompositeFinal7
open Erdos634.Draft.CompositeE5Gen

theorem pairs120_35 : ∀ s t : ℤ, 1 ≤ s → s ≤ ((35 : ℕ) : ℤ) → 1 ≤ t → t ≤ ((35 : ℕ) : ℤ) → s * t = 3 * ((35 : ℕ) : ℤ) →
    ¬ IsSquare ((t - s) ^ 2 + 16 * ((35 : ℕ) : ℤ)) ∧ ∀ r : ℤ, 0 ≤ r → 2 * ((35 : ℕ) : ℤ) ≠ r * (s + t) := by
  intro s t h1 h2 h3 h4 h5
  push_cast at *
  interval_cases s <;>
    first
    | (exfalso; omega)
    | (interval_cases t <;> first | (exfalso; omega) | exact ⟨by decide +kernel, fun r hr => by omega⟩)

theorem gapE120_35 : GapE120 35 := gapE120_of_pairs 35 (by norm_num) pairs120_35

theorem pairs120_39 : ∀ s t : ℤ, 1 ≤ s → s ≤ ((39 : ℕ) : ℤ) → 1 ≤ t → t ≤ ((39 : ℕ) : ℤ) → s * t = 3 * ((39 : ℕ) : ℤ) →
    ¬ IsSquare ((t - s) ^ 2 + 16 * ((39 : ℕ) : ℤ)) ∧ ∀ r : ℤ, 0 ≤ r → 2 * ((39 : ℕ) : ℤ) ≠ r * (s + t) := by
  intro s t h1 h2 h3 h4 h5
  push_cast at *
  interval_cases s <;>
    first
    | (exfalso; omega)
    | (interval_cases t <;> first | (exfalso; omega) | exact ⟨by decide +kernel, fun r hr => by omega⟩)

theorem gapE120_39 : GapE120 39 := gapE120_of_pairs 39 (by norm_num) pairs120_39

theorem pairs120_51 : ∀ s t : ℤ, 1 ≤ s → s ≤ ((51 : ℕ) : ℤ) → 1 ≤ t → t ≤ ((51 : ℕ) : ℤ) → s * t = 3 * ((51 : ℕ) : ℤ) →
    ¬ IsSquare ((t - s) ^ 2 + 16 * ((51 : ℕ) : ℤ)) ∧ ∀ r : ℤ, 0 ≤ r → 2 * ((51 : ℕ) : ℤ) ≠ r * (s + t) := by
  intro s t h1 h2 h3 h4 h5
  push_cast at *
  interval_cases s <;>
    first
    | (exfalso; omega)
    | (interval_cases t <;> first | (exfalso; omega) | exact ⟨by decide +kernel, fun r hr => by omega⟩)

theorem gapE120_51 : GapE120 51 := gapE120_of_pairs 51 (by norm_num) pairs120_51

theorem pairs120_55 : ∀ s t : ℤ, 1 ≤ s → s ≤ ((55 : ℕ) : ℤ) → 1 ≤ t → t ≤ ((55 : ℕ) : ℤ) → s * t = 3 * ((55 : ℕ) : ℤ) →
    ¬ IsSquare ((t - s) ^ 2 + 16 * ((55 : ℕ) : ℤ)) ∧ ∀ r : ℤ, 0 ≤ r → 2 * ((55 : ℕ) : ℤ) ≠ r * (s + t) := by
  intro s t h1 h2 h3 h4 h5
  push_cast at *
  interval_cases s <;>
    first
    | (exfalso; omega)
    | (interval_cases t <;> first | (exfalso; omega) | exact ⟨by decide +kernel, fun r hr => by omega⟩)

theorem gapE120_55 : GapE120 55 := gapE120_of_pairs 55 (by norm_num) pairs120_55

theorem pairs120_87 : ∀ s t : ℤ, 1 ≤ s → s ≤ ((87 : ℕ) : ℤ) → 1 ≤ t → t ≤ ((87 : ℕ) : ℤ) → s * t = 3 * ((87 : ℕ) : ℤ) →
    ¬ IsSquare ((t - s) ^ 2 + 16 * ((87 : ℕ) : ℤ)) ∧ ∀ r : ℤ, 0 ≤ r → 2 * ((87 : ℕ) : ℤ) ≠ r * (s + t) := by
  intro s t h1 h2 h3 h4 h5
  push_cast at *
  interval_cases s <;>
    first
    | (exfalso; omega)
    | (interval_cases t <;> first | (exfalso; omega) | exact ⟨by decide +kernel, fun r hr => by omega⟩)

theorem gapE120_87 : GapE120 87 := gapE120_of_pairs 87 (by norm_num) pairs120_87

theorem pairs60_35 : ∀ m₁ m₂ : ℤ, 1 ≤ m₁ → m₁ ≤ ((35 : ℕ) : ℤ) → 1 ≤ m₂ → m₂ ≤ ((35 : ℕ) : ℤ) →
    m₁ * m₂ = 3 * ((35 : ℕ) : ℤ) → m₂ < m₁ →
    (m₁ = ((35 : ℕ) : ℤ) ∧ m₂ = 3) ∨ (¬ IsSquare ((m₁ + m₂) ^ 2 - 16 * ((35 : ℕ) : ℤ)) ∧
      (0 ≤ (m₁ + m₂) ^ 2 - 16 * ((35 : ℕ) : ℤ) →
        ∀ p r : ℤ, 0 ≤ p → 0 ≤ r → 2 * ((35 : ℕ) : ℤ) ≠ p * (m₁ + m₂) + r * (m₁ - m₂))) := by
  intro m₁ m₂ h1 h2 h3 h4 h5 h6
  push_cast at *
  interval_cases m₁ <;>
    first
    | (exfalso; omega)
    | (interval_cases m₂ <;> first | (exfalso; omega) | (left; omega) |
        (right; exact ⟨by decide +kernel, fun hnn p r hp hr => by
          first | (exfalso; norm_num at hnn; done) | omega⟩))

theorem gapE60_35 : GapE60 35 := gapE60_of_pairs 35 (by norm_num) pairs60_35

theorem pairs60_39 : ∀ m₁ m₂ : ℤ, 1 ≤ m₁ → m₁ ≤ ((39 : ℕ) : ℤ) → 1 ≤ m₂ → m₂ ≤ ((39 : ℕ) : ℤ) →
    m₁ * m₂ = 3 * ((39 : ℕ) : ℤ) → m₂ < m₁ →
    (m₁ = ((39 : ℕ) : ℤ) ∧ m₂ = 3) ∨ (¬ IsSquare ((m₁ + m₂) ^ 2 - 16 * ((39 : ℕ) : ℤ)) ∧
      (0 ≤ (m₁ + m₂) ^ 2 - 16 * ((39 : ℕ) : ℤ) →
        ∀ p r : ℤ, 0 ≤ p → 0 ≤ r → 2 * ((39 : ℕ) : ℤ) ≠ p * (m₁ + m₂) + r * (m₁ - m₂))) := by
  intro m₁ m₂ h1 h2 h3 h4 h5 h6
  push_cast at *
  interval_cases m₁ <;>
    first
    | (exfalso; omega)
    | (interval_cases m₂ <;> first | (exfalso; omega) | (left; omega) |
        (right; exact ⟨by decide +kernel, fun hnn p r hp hr => by
          first | (exfalso; norm_num at hnn; done) | omega⟩))

theorem gapE60_39 : GapE60 39 := gapE60_of_pairs 39 (by norm_num) pairs60_39

theorem pairs60_51 : ∀ m₁ m₂ : ℤ, 1 ≤ m₁ → m₁ ≤ ((51 : ℕ) : ℤ) → 1 ≤ m₂ → m₂ ≤ ((51 : ℕ) : ℤ) →
    m₁ * m₂ = 3 * ((51 : ℕ) : ℤ) → m₂ < m₁ →
    (m₁ = ((51 : ℕ) : ℤ) ∧ m₂ = 3) ∨ (¬ IsSquare ((m₁ + m₂) ^ 2 - 16 * ((51 : ℕ) : ℤ)) ∧
      (0 ≤ (m₁ + m₂) ^ 2 - 16 * ((51 : ℕ) : ℤ) →
        ∀ p r : ℤ, 0 ≤ p → 0 ≤ r → 2 * ((51 : ℕ) : ℤ) ≠ p * (m₁ + m₂) + r * (m₁ - m₂))) := by
  intro m₁ m₂ h1 h2 h3 h4 h5 h6
  push_cast at *
  interval_cases m₁ <;>
    first
    | (exfalso; omega)
    | (interval_cases m₂ <;> first | (exfalso; omega) | (left; omega) |
        (right; exact ⟨by decide +kernel, fun hnn p r hp hr => by
          first | (exfalso; norm_num at hnn; done) | omega⟩))

theorem gapE60_51 : GapE60 51 := gapE60_of_pairs 51 (by norm_num) pairs60_51

theorem pairs60_55 : ∀ m₁ m₂ : ℤ, 1 ≤ m₁ → m₁ ≤ ((55 : ℕ) : ℤ) → 1 ≤ m₂ → m₂ ≤ ((55 : ℕ) : ℤ) →
    m₁ * m₂ = 3 * ((55 : ℕ) : ℤ) → m₂ < m₁ →
    (m₁ = ((55 : ℕ) : ℤ) ∧ m₂ = 3) ∨ (¬ IsSquare ((m₁ + m₂) ^ 2 - 16 * ((55 : ℕ) : ℤ)) ∧
      (0 ≤ (m₁ + m₂) ^ 2 - 16 * ((55 : ℕ) : ℤ) →
        ∀ p r : ℤ, 0 ≤ p → 0 ≤ r → 2 * ((55 : ℕ) : ℤ) ≠ p * (m₁ + m₂) + r * (m₁ - m₂))) := by
  intro m₁ m₂ h1 h2 h3 h4 h5 h6
  push_cast at *
  interval_cases m₁ <;>
    first
    | (exfalso; omega)
    | (interval_cases m₂ <;> first | (exfalso; omega) | (left; omega) |
        (right; exact ⟨by decide +kernel, fun hnn p r hp hr => by
          first | (exfalso; norm_num at hnn; done) | omega⟩))

theorem gapE60_55 : GapE60 55 := gapE60_of_pairs 55 (by norm_num) pairs60_55

/-- N = 87: the pair `(29, 9)` is NOT killed by side matching (negative control for the pair machinery):
`2·87 = 3·(29+9) + 3·(29−9)`. -/
theorem not_pairs60_87_noexc : ¬ (∀ p r : ℤ, 0 ≤ p → 0 ≤ r → 2 * (((87 : ℕ)) : ℤ) ≠ p * (29 + 9) + r * (29 - 9)) :=
  fun h => h 3 3 (by norm_num) (by norm_num) (by norm_num)

theorem pairs60_87 : ∀ m₁ m₂ : ℤ, 1 ≤ m₁ → m₁ ≤ ((87 : ℕ) : ℤ) → 1 ≤ m₂ → m₂ ≤ ((87 : ℕ) : ℤ) →
    m₁ * m₂ = 3 * ((87 : ℕ) : ℤ) → m₂ < m₁ →
    (m₁ = ((87 : ℕ) : ℤ) ∧ m₂ = 3) ∨ (m₁ = 29 ∧ m₂ = 9) ∨ (¬ IsSquare ((m₁ + m₂) ^ 2 - 16 * ((87 : ℕ) : ℤ)) ∧
      (0 ≤ (m₁ + m₂) ^ 2 - 16 * ((87 : ℕ) : ℤ) →
        ∀ p r : ℤ, 0 ≤ p → 0 ≤ r → 2 * ((87 : ℕ) : ℤ) ≠ p * (m₁ + m₂) + r * (m₁ - m₂))) := by
  intro m₁ m₂ h1 h2 h3 h4 h5 h6
  push_cast at *
  interval_cases m₁ <;>
    first
    | (exfalso; omega)
    | (interval_cases m₂ <;> first | (exfalso; omega) | (left; omega) | (right; left; omega) |
        (right; right; exact ⟨by decide +kernel, fun hnn p r hp hr => by
          first | (exfalso; norm_num at hnn; done) | omega⟩))

/-- **`GapE60 87` modulo the single pair `E60Pair 87 29 9`.** -/
theorem gapE60_87 (gx : E60Pair 87 29 9) : GapE60 87 := gapE60_of_pairs_exc 87 (by norm_num) 29 9 gx pairs60_87

/-! ## Conditional chains with the equilateral leaves discharged -/

/-- **N = 35, modulo `GapF1 35` only.** -/
theorem chain_35_F1only (gF1 : GapF1 35) (D : CongruentDissection 35) : False :=
  chain_cond_35 gapE60_35 gapE120_35 gF1 D
/-- **N = 55, modulo `GapF1 55` only.** -/
theorem chain_55_F1only (gF1 : GapF1 55) (D : CongruentDissection 55) : False :=
  chain_cond_55 gapE60_55 gapE120_55 gF1 D
/-- **N = 39, modulo `GammaTwoAlphaClosed 39` and `GapF1 39`.** -/
theorem chain_39_GF1 (gG : GammaTwoAlphaClosed 39) (gF1 : GapF1 39) (D : CongruentDissection 39) : False :=
  chain_cond_39 gG gapE60_39 gapE120_39 gF1 D
/-- **N = 51, modulo `GammaTwoAlphaClosed 51` and `GapF1 51`.** -/
theorem chain_51_GF1 (gG : GammaTwoAlphaClosed 51) (gF1 : GapF1 51) (D : CongruentDissection 51) : False :=
  chain_cond_51 gG gapE60_51 gapE120_51 gF1 D
/-- **N = 87, modulo `GammaTwoAlphaClosed 87`, `E60Pair 87 29 9` and `GapF1 87`.** -/
theorem chain_87_GE60F1 (gG : GammaTwoAlphaClosed 87) (gx : E60Pair 87 29 9) (gF1 : GapF1 87)
    (D : CongruentDissection 87) : False :=
  chain_cond_87 gG (gapE60_87 gx) gapE120_87 gF1 D

end Erdos634.Draft.CompositeFinal8

#print axioms Erdos634.Draft.CompositeFinal8.gapE120_35
#print axioms Erdos634.Draft.CompositeFinal8.gapE60_35
#print axioms Erdos634.Draft.CompositeFinal8.gapE120_39
#print axioms Erdos634.Draft.CompositeFinal8.gapE60_39
#print axioms Erdos634.Draft.CompositeFinal8.gapE120_51
#print axioms Erdos634.Draft.CompositeFinal8.gapE60_51
#print axioms Erdos634.Draft.CompositeFinal8.gapE120_55
#print axioms Erdos634.Draft.CompositeFinal8.gapE60_55
#print axioms Erdos634.Draft.CompositeFinal8.gapE120_87
#print axioms Erdos634.Draft.CompositeFinal8.gapE60_87
#print axioms Erdos634.Draft.CompositeFinal8.chain_35_F1only
#print axioms Erdos634.Draft.CompositeFinal8.chain_55_F1only
#print axioms Erdos634.Draft.CompositeFinal8.chain_39_GF1
#print axioms Erdos634.Draft.CompositeFinal8.chain_51_GF1
#print axioms Erdos634.Draft.CompositeFinal8.chain_87_GE60F1

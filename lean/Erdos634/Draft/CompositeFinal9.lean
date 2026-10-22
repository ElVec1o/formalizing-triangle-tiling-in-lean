/-
Draft/CompositeFinal9.lean — the F1 leaf `GapF1 N` PROVED for N = 35, 39, 51, 55, 87 (`F1KappaSide3.f1MaGt1_of_list` +
`CompositeF1Gen.gapF1_of_MaGt1`), and the resulting chains.
  N = 35, 55 :  `chain_N_final`  has NO residual hypothesis.
  N = 39, 51 :  residual `GammaTwoAlphaClosed N` only.
  N = 87     :  residual `GammaTwoAlphaClosed 87` and `E60Pair 87 29 9`.
Each `chain_N_final` is a Lean theorem `... → CongruentDissection N → False`.  UNAUDITED.  Formalization debt, NOT /goal progress.
No sorry, no native_decide.  The only residual hypotheses are the named ones above.
-/
import Erdos634.Draft.F1KappaSide3

set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.CompositeFinal9

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.Chain15 Erdos634.Draft.ChainComposite
open Erdos634.Draft.CompositeFinal6 Erdos634.Draft.CompositeFinal7 Erdos634.Draft.CompositeFinal8
open Erdos634.Draft.CompositeE5Gen Erdos634.Draft.CompositeF1Gen Erdos634.Draft.F1KappaSide

theorem f1MaGt1_35 : F1MaGt1 35 := by
  refine f1MaGt1_of_list 35 ?_
  intro Ma Mb h1 h2 h3
  have hMa : Ma ≤ 9 := by nlinarith
  interval_cases Ma <;> first | (exfalso; omega) | skip
  obtain rfl : Mb = 7 := by omega
  exact ⟨1, by norm_num, by norm_num, by decide +kernel, by norm_num⟩

theorem gapF1_35 : GapF1 35 := gapF1_of_MaGt1 35 (by norm_num) f1MaGt1_35

theorem f1MaGt1_39 : F1MaGt1 39 := by
  refine f1MaGt1_of_list 39 ?_
  intro Ma Mb h1 h2 h3
  have hMa : Ma ≤ 9 := by nlinarith
  interval_cases Ma <;> first | (exfalso; omega) | skip
  obtain rfl : Mb = 13 := by omega
  exact ⟨5, by norm_num, by norm_num, by decide +kernel, by norm_num⟩

theorem gapF1_39 : GapF1 39 := gapF1_of_MaGt1 39 (by norm_num) f1MaGt1_39

theorem f1MaGt1_51 : F1MaGt1 51 := by
  refine f1MaGt1_of_list 51 ?_
  intro Ma Mb h1 h2 h3
  have hMa : Ma ≤ 9 := by nlinarith
  interval_cases Ma <;> first | (exfalso; omega) | skip
  obtain rfl : Mb = 17 := by omega
  exact ⟨7, by norm_num, by norm_num, by decide +kernel, by norm_num⟩

theorem gapF1_51 : GapF1 51 := gapF1_of_MaGt1 51 (by norm_num) f1MaGt1_51

theorem f1MaGt1_55 : F1MaGt1 55 := by
  refine f1MaGt1_of_list 55 ?_
  intro Ma Mb h1 h2 h3
  have hMa : Ma ≤ 9 := by nlinarith
  interval_cases Ma <;> first | (exfalso; omega) | skip
  obtain rfl : Mb = 11 := by omega
  exact ⟨3, by norm_num, by norm_num, by decide +kernel, by norm_num⟩

theorem gapF1_55 : GapF1 55 := gapF1_of_MaGt1 55 (by norm_num) f1MaGt1_55

theorem f1MaGt1_87 : F1MaGt1 87 := by
  refine f1MaGt1_of_list 87 ?_
  intro Ma Mb h1 h2 h3
  have hMa : Ma ≤ 9 := by nlinarith
  interval_cases Ma <;> first | (exfalso; omega) | skip
  obtain rfl : Mb = 29 := by omega
  exact ⟨13, by norm_num, by norm_num, by decide +kernel, by norm_num⟩

theorem gapF1_87 : GapF1 87 := gapF1_of_MaGt1 87 (by norm_num) f1MaGt1_87

/-! ## Final theorems -/

/-- **N = 35: no residual hypothesis.**  (UNAUDITED; see (private working notes, not included).) -/
theorem chain_35_final (D : CongruentDissection 35) : False := chain_35_F1only gapF1_35 D
/-- **N = 55: no residual hypothesis.** -/
theorem chain_55_final (D : CongruentDissection 55) : False := chain_55_F1only gapF1_55 D
/-- **N = 39, modulo `GammaTwoAlphaClosed 39`.** -/
theorem chain_39_final (gG : GammaTwoAlphaClosed 39) (D : CongruentDissection 39) : False :=
  chain_39_GF1 gG gapF1_39 D
/-- **N = 51, modulo `GammaTwoAlphaClosed 51`.** -/
theorem chain_51_final (gG : GammaTwoAlphaClosed 51) (D : CongruentDissection 51) : False :=
  chain_51_GF1 gG gapF1_51 D
/-- **N = 87, modulo `GammaTwoAlphaClosed 87` and `E60Pair 87 29 9`.** -/
theorem chain_87_final (gG : GammaTwoAlphaClosed 87) (gx : E60Pair 87 29 9) (D : CongruentDissection 87) : False :=
  chain_87_GE60F1 gG gx gapF1_87 D

/-! ## Negative controls (the finite hypotheses are not trivially true) -/

/-- The E120 pair table FAILS at N = 15: the pair `(5, 9)` has `D = 4² + 16·15 = 256 = 16²` (the (3,5,7) tile, side 15). -/
theorem not_pairs120_15 : ¬ (∀ s t : ℤ, 1 ≤ s → s ≤ ((15 : ℕ) : ℤ) → 1 ≤ t → t ≤ ((15 : ℕ) : ℤ) →
    s * t = 3 * ((15 : ℕ) : ℤ) →
    ¬ IsSquare ((t - s) ^ 2 + 16 * ((15 : ℕ) : ℤ)) ∧ ∀ r : ℤ, 0 ≤ r → 2 * ((15 : ℕ) : ℤ) ≠ r * (s + t)) := by
  intro h
  have := (h 5 9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1
  exact this ⟨16, by norm_num⟩

/-- The F1 pair list FAILS at N = 105: `(Ma, Mb) = (3, 35)` has `(Ma+Mb)² + 12 N = 38² + 1260 = 2704 = 52²`
(rational tile `b/a`), so the `b^κ` word argument does not apply there. -/
theorem not_f1list_105 : ¬ (∀ Ma Mb : ℕ, 1 < Ma → Ma < Mb → Ma * Mb = 105 →
      ∃ κ : ℕ, 0 < κ ∧ Mb = Ma + 2 * κ ∧ ¬ IsSquare (((Ma : ℤ) + Mb) ^ 2 + 12 * ((105 : ℕ) : ℤ)) ∧
        Ma ^ 2 + Mb ^ 2 ≠ 4 * Ma * Mb) := by
  intro h
  obtain ⟨κ, -, -, hns, -⟩ := h 3 35 (by norm_num) (by norm_num) (by norm_num)
  exact hns ⟨52, by norm_num⟩

end Erdos634.Draft.CompositeFinal9

#print axioms Erdos634.Draft.CompositeFinal9.chain_35_final
#print axioms Erdos634.Draft.CompositeFinal9.chain_55_final
#print axioms Erdos634.Draft.CompositeFinal9.chain_39_final
#print axioms Erdos634.Draft.CompositeFinal9.chain_51_final
#print axioms Erdos634.Draft.CompositeFinal9.chain_87_final
#print axioms Erdos634.Draft.CompositeFinal9.not_pairs120_15
#print axioms Erdos634.Draft.CompositeFinal9.not_f1list_105

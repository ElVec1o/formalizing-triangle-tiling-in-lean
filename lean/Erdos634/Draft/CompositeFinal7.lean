/-
Draft/CompositeFinal7.lean — `GapR8 N` PROVED for N = 35, 39, 51, 55, 87 (`R8Gen2.gapR8_of_arith2`: NoF2, NoF3, NoF4z by
finite arithmetic), and the conditional dispatch `chain_cond_N` of each of the five odd composites with EXACTLY the residual
hypotheses `GapE60 N`, `GapE120 N`, `GapF1 N` (+ `GammaTwoAlphaClosed N` at 39, 51, 87).
*** CONDITIONAL.  UNAUDITED.  Formalization debt, NOT /goal progress.  No sorry, no native_decide. ***
-/
import Erdos634.Draft.CompositeFinal6

set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.CompositeFinal7

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.Chain15 Erdos634.Draft.ChainComposite
open Erdos634.Draft.CompositeGen2 Erdos634.Draft.CompositeArith Erdos634.Draft.CompositeS2Arith
open Erdos634.Draft.CompositeS1Arith Erdos634.Draft.CompositeIsoB Erdos634.Draft.CompositeFinal2
open Erdos634.Draft.CompositeFinal3 Erdos634.Draft.CompositeFinal6
open Erdos634.Draft.R8Gen2

theorem noF3_35 : NoF3 35 := by
  intro s j hj hjs h
  push_cast at h
  have h1 : j ≤ 4 := by nlinarith
  have h2 : s ≤ 12 := by nlinarith
  interval_cases j <;> interval_cases s <;> omega

theorem noF2_35 : NoF2 35 := by
  apply noF2_of_int
  · intro z hz
    push_cast at hz
    have h1 : z ≤ 6 := by nlinarith
    have h2 : -6 ≤ z := by nlinarith
    interval_cases z <;> omega
  · intro x r hx hr h z hz
    push_cast at hz
    have hx7 : x ≤ 6 := by nlinarith
    have hr9 : r ≤ 9 := by nlinarith
    interval_cases x <;> interval_cases r <;>
      first
      | omega
      | (norm_num at hz
         have h1 : z ≤ 9 := by nlinarith
         have h2 : -9 ≤ z := by nlinarith
         interval_cases z <;> omega)

theorem noF4z_35 : NoF4z 35 := by
  apply noF4z_of_int
  intro x r hx hr h z hz
  have hx7 : x ≤ 6 := by nlinarith
  have hr9 : r ≤ 9 := by nlinarith
  interval_cases x <;> interval_cases r <;>
    first
    | omega
    | (norm_num at hz
       have h1 : z ≤ 9 := by nlinarith
       have h2 : -9 ≤ z := by nlinarith
       interval_cases z <;> omega)

theorem gapR8_35 : GapR8 35 := gapR8_of_arith2 35 noF2_35 noF3_35 noF4z_35

theorem noF3_39 : NoF3 39 := by
  intro s j hj hjs h
  push_cast at h
  have h1 : j ≤ 4 := by nlinarith
  have h2 : s ≤ 12 := by nlinarith
  interval_cases j <;> interval_cases s <;> omega

theorem noF2_39 : NoF2 39 := by
  apply noF2_of_int
  · intro z hz
    push_cast at hz
    have h1 : z ≤ 6 := by nlinarith
    have h2 : -6 ≤ z := by nlinarith
    interval_cases z <;> omega
  · intro x r hx hr h z hz
    push_cast at hz
    have hx7 : x ≤ 6 := by nlinarith
    have hr9 : r ≤ 9 := by nlinarith
    interval_cases x <;> interval_cases r <;>
      first
      | omega
      | (norm_num at hz
         have h1 : z ≤ 9 := by nlinarith
         have h2 : -9 ≤ z := by nlinarith
         interval_cases z <;> omega)

theorem noF4z_39 : NoF4z 39 := by
  apply noF4z_of_int
  intro x r hx hr h z hz
  have hx7 : x ≤ 6 := by nlinarith
  have hr9 : r ≤ 9 := by nlinarith
  interval_cases x <;> interval_cases r <;>
    first
    | omega
    | (norm_num at hz
       have h1 : z ≤ 9 := by nlinarith
       have h2 : -9 ≤ z := by nlinarith
       interval_cases z <;> omega)

theorem gapR8_39 : GapR8 39 := gapR8_of_arith2 39 noF2_39 noF3_39 noF4z_39

theorem noF3_51 : NoF3 51 := by
  intro s j hj hjs h
  push_cast at h
  have h1 : j ≤ 4 := by nlinarith
  have h2 : s ≤ 12 := by nlinarith
  interval_cases j <;> interval_cases s <;> omega

theorem noF2_51 : NoF2 51 := by
  apply noF2_of_int
  · intro z hz
    push_cast at hz
    have h1 : z ≤ 6 := by nlinarith
    have h2 : -6 ≤ z := by nlinarith
    interval_cases z <;> omega
  · intro x r hx hr h z hz
    push_cast at hz
    have hx7 : x ≤ 6 := by nlinarith
    have hr9 : r ≤ 9 := by nlinarith
    interval_cases x <;> interval_cases r <;>
      first
      | omega
      | (norm_num at hz
         have h1 : z ≤ 9 := by nlinarith
         have h2 : -9 ≤ z := by nlinarith
         interval_cases z <;> omega)

theorem noF4z_51 : NoF4z 51 := by
  apply noF4z_of_int
  intro x r hx hr h z hz
  have hx7 : x ≤ 6 := by nlinarith
  have hr9 : r ≤ 9 := by nlinarith
  interval_cases x <;> interval_cases r <;>
    first
    | omega
    | (norm_num at hz
       have h1 : z ≤ 9 := by nlinarith
       have h2 : -9 ≤ z := by nlinarith
       interval_cases z <;> omega)

theorem gapR8_51 : GapR8 51 := gapR8_of_arith2 51 noF2_51 noF3_51 noF4z_51

theorem noF3_55 : NoF3 55 := by
  intro s j hj hjs h
  push_cast at h
  have h1 : j ≤ 4 := by nlinarith
  have h2 : s ≤ 12 := by nlinarith
  interval_cases j <;> interval_cases s <;> omega

theorem noF2_55 : NoF2 55 := by
  apply noF2_of_int
  · intro z hz
    push_cast at hz
    have h1 : z ≤ 6 := by nlinarith
    have h2 : -6 ≤ z := by nlinarith
    interval_cases z <;> omega
  · intro x r hx hr h z hz
    push_cast at hz
    have hx7 : x ≤ 6 := by nlinarith
    have hr9 : r ≤ 9 := by nlinarith
    interval_cases x <;> interval_cases r <;>
      first
      | omega
      | (norm_num at hz
         have h1 : z ≤ 9 := by nlinarith
         have h2 : -9 ≤ z := by nlinarith
         interval_cases z <;> omega)

theorem noF4z_55 : NoF4z 55 := by
  apply noF4z_of_int
  intro x r hx hr h z hz
  have hx7 : x ≤ 6 := by nlinarith
  have hr9 : r ≤ 9 := by nlinarith
  interval_cases x <;> interval_cases r <;>
    first
    | omega
    | (norm_num at hz
       have h1 : z ≤ 9 := by nlinarith
       have h2 : -9 ≤ z := by nlinarith
       interval_cases z <;> omega)

theorem gapR8_55 : GapR8 55 := gapR8_of_arith2 55 noF2_55 noF3_55 noF4z_55

theorem noF3_87 : NoF3 87 := by
  intro s j hj hjs h
  push_cast at h
  have h1 : j ≤ 4 := by nlinarith
  have h2 : s ≤ 12 := by nlinarith
  interval_cases j <;> interval_cases s <;> omega

theorem noF2_87 : NoF2 87 := by
  apply noF2_of_int
  · intro z hz
    push_cast at hz
    have h1 : z ≤ 6 := by nlinarith
    have h2 : -6 ≤ z := by nlinarith
    interval_cases z <;> omega
  · intro x r hx hr h z hz
    push_cast at hz
    have hx7 : x ≤ 6 := by nlinarith
    have hr9 : r ≤ 9 := by nlinarith
    interval_cases x <;> interval_cases r <;>
      first
      | omega
      | (norm_num at hz
         have h1 : z ≤ 9 := by nlinarith
         have h2 : -9 ≤ z := by nlinarith
         interval_cases z <;> omega)

theorem noF4z_87 : NoF4z 87 := by
  apply noF4z_of_int
  intro x r hx hr h z hz
  have hx7 : x ≤ 6 := by nlinarith
  have hr9 : r ≤ 9 := by nlinarith
  interval_cases x <;> interval_cases r <;>
    first
    | omega
    | (norm_num at hz
       have h1 : z ≤ 9 := by nlinarith
       have h2 : -9 ≤ z := by nlinarith
       interval_cases z <;> omega)

theorem gapR8_87 : GapR8 87 := gapR8_of_arith2 87 noF2_87 noF3_87 noF4z_87


/-! ## Conditional dispatch, one per N -/

/-- **N = 35, modulo `GapE60 35`, `GapE120 35`, `GapF1 35`.** -/
theorem chain_cond_35 (gE60 : GapE60 35) (gE120 : GapE120 35) (gF1 : GapF1 35) (D : CongruentDissection 35) : False :=
  chain_gen3 35 sqfree_35 s1Closed_35 s2Closed_35 (s3Closed_of_isoQRef 35 isoQRef_35) isoH9b_35
    gapAcomp_35 caseB_35 caseR_35 gamma_35 gE60 gE120 gF1 gapR8_35 D

/-- **N = 55, modulo `GapE60 55`, `GapE120 55`, `GapF1 55`.** -/
theorem chain_cond_55 (gE60 : GapE60 55) (gE120 : GapE120 55) (gF1 : GapF1 55) (D : CongruentDissection 55) : False :=
  chain_gen3 55 sqfree_55 s1Closed_55 s2Closed_55 (s3Closed_of_isoQRef 55 isoQRef_55) isoH9b_55
    gapAcomp_55 caseB_55 caseR_55 gamma_55 gE60 gE120 gF1 gapR8_55 D

/-- **N = 39, modulo `GammaTwoAlphaClosed 39`, `GapE60 39`, `GapE120 39`, `GapF1 39`.** -/
theorem chain_cond_39 (gG : GammaTwoAlphaClosed 39) (gE60 : GapE60 39) (gE120 : GapE120 39) (gF1 : GapF1 39)
    (D : CongruentDissection 39) : False :=
  chain_gen3 39 sqfree_39 s1Closed_39 s2Closed_39 (s3Closed_of_isoQRef 39 isoQRef_39) isoH9b_39
    gapAcomp_39 caseB_39 caseR_39 gG gE60 gE120 gF1 gapR8_39 D

/-- **N = 51, modulo `GammaTwoAlphaClosed 51`, `GapE60 51`, `GapE120 51`, `GapF1 51`.** -/
theorem chain_cond_51 (gG : GammaTwoAlphaClosed 51) (gE60 : GapE60 51) (gE120 : GapE120 51) (gF1 : GapF1 51)
    (D : CongruentDissection 51) : False :=
  chain_gen3 51 sqfree_51 s1Closed_51 s2Closed_51 (s3Closed_of_isoQRef 51 isoQRef_51) isoH9b_51
    gapAcomp_51 caseB_51 caseR_51 gG gE60 gE120 gF1 gapR8_51 D

/-- **N = 87, modulo `GammaTwoAlphaClosed 87`, `GapE60 87`, `GapE120 87`, `GapF1 87`.** -/
theorem chain_cond_87 (gG : GammaTwoAlphaClosed 87) (gE60 : GapE60 87) (gE120 : GapE120 87) (gF1 : GapF1 87)
    (D : CongruentDissection 87) : False :=
  chain_gen3 87 sqfree_87 s1Closed_87 s2Closed_87 (s3Closed_of_isoQRef 87 isoQRef_87) isoH9b_87
    gapAcomp_87 caseB_87 caseR_87 gG gE60 gE120 gF1 gapR8_87 D

end Erdos634.Draft.CompositeFinal7

#print axioms Erdos634.Draft.CompositeFinal7.gapR8_35
#print axioms Erdos634.Draft.CompositeFinal7.gapR8_39
#print axioms Erdos634.Draft.CompositeFinal7.gapR8_51
#print axioms Erdos634.Draft.CompositeFinal7.gapR8_55
#print axioms Erdos634.Draft.CompositeFinal7.gapR8_87
#print axioms Erdos634.Draft.CompositeFinal7.chain_cond_35
#print axioms Erdos634.Draft.CompositeFinal7.chain_cond_39
#print axioms Erdos634.Draft.CompositeFinal7.chain_cond_51
#print axioms Erdos634.Draft.CompositeFinal7.chain_cond_55
#print axioms Erdos634.Draft.CompositeFinal7.chain_cond_87

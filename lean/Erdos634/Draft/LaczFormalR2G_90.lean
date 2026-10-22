-- Draft/LaczFormalR2G_90.lean -- glue: `allCert 90 = true` from the chunks of `LaczFormalR2L_90`.  UNAUDITED.
import Erdos634.Draft.LaczFormalR2Bridge
import Erdos634.Draft.LaczFormalR2L_90

namespace Erdos634.Draft.LaczFormal
open Erdos634.LemmaS

theorem allCert_90 : allCert 90 = true := by
  refine allCert_of_lite_chunks 90 3 [0, 3, 6, 9, 12, 15, 18, 21, 24, 27, 30, 33, 36, 39, 42, 45, 48, 51, 54, 57, 60, 63, 66, 69, 72, 75, 78, 81, 84, 87] ?_ ?_
  · intro lo hlo
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlo
    rcases hlo with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Erdos634.Lite.c90_0
    · exact Erdos634.Lite.c90_3
    · exact Erdos634.Lite.c90_6
    · exact Erdos634.Lite.c90_9
    · exact Erdos634.Lite.c90_12
    · exact Erdos634.Lite.c90_15
    · exact Erdos634.Lite.c90_18
    · exact Erdos634.Lite.c90_21
    · exact Erdos634.Lite.c90_24
    · exact Erdos634.Lite.c90_27
    · exact Erdos634.Lite.c90_30
    · exact Erdos634.Lite.c90_33
    · exact Erdos634.Lite.c90_36
    · exact Erdos634.Lite.c90_39
    · exact Erdos634.Lite.c90_42
    · exact Erdos634.Lite.c90_45
    · exact Erdos634.Lite.c90_48
    · exact Erdos634.Lite.c90_51
    · exact Erdos634.Lite.c90_54
    · exact Erdos634.Lite.c90_57
    · exact Erdos634.Lite.c90_60
    · exact Erdos634.Lite.c90_63
    · exact Erdos634.Lite.c90_66
    · exact Erdos634.Lite.c90_69
    · exact Erdos634.Lite.c90_72
    · exact Erdos634.Lite.c90_75
    · exact Erdos634.Lite.c90_78
    · exact Erdos634.Lite.c90_81
    · exact Erdos634.Lite.c90_84
    · exact Erdos634.Lite.c90_87
  · decide +kernel

end Erdos634.Draft.LaczFormal

-- Draft/LaczFormalR2G_81.lean -- glue: `allCert 81 = true` from the chunks of `LaczFormalR2L_81`.  UNAUDITED.
import Erdos634.Draft.LaczFormalR2Bridge
import Erdos634.Draft.LaczFormalR2L_81

namespace Erdos634.Draft.LaczFormal
open Erdos634.LemmaS

theorem allCert_81 : allCert 81 = true := by
  refine allCert_of_lite_chunks 81 3 [0, 3, 6, 9, 12, 15, 18, 21, 24, 27, 30, 33, 36, 39, 42, 45, 48, 51, 54, 57, 60, 63, 66, 69, 72, 75, 78] ?_ ?_
  · intro lo hlo
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlo
    rcases hlo with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Erdos634.Lite.c81_0
    · exact Erdos634.Lite.c81_3
    · exact Erdos634.Lite.c81_6
    · exact Erdos634.Lite.c81_9
    · exact Erdos634.Lite.c81_12
    · exact Erdos634.Lite.c81_15
    · exact Erdos634.Lite.c81_18
    · exact Erdos634.Lite.c81_21
    · exact Erdos634.Lite.c81_24
    · exact Erdos634.Lite.c81_27
    · exact Erdos634.Lite.c81_30
    · exact Erdos634.Lite.c81_33
    · exact Erdos634.Lite.c81_36
    · exact Erdos634.Lite.c81_39
    · exact Erdos634.Lite.c81_42
    · exact Erdos634.Lite.c81_45
    · exact Erdos634.Lite.c81_48
    · exact Erdos634.Lite.c81_51
    · exact Erdos634.Lite.c81_54
    · exact Erdos634.Lite.c81_57
    · exact Erdos634.Lite.c81_60
    · exact Erdos634.Lite.c81_63
    · exact Erdos634.Lite.c81_66
    · exact Erdos634.Lite.c81_69
    · exact Erdos634.Lite.c81_72
    · exact Erdos634.Lite.c81_75
    · exact Erdos634.Lite.c81_78
  · decide +kernel

end Erdos634.Draft.LaczFormal

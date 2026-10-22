-- Draft/LaczFormalR2G_80.lean -- glue: `allCert 80 = true` from the chunks of `LaczFormalR2L_80`.  UNAUDITED.
import Erdos634.Draft.LaczFormalR2Bridge
import Erdos634.Draft.LaczFormalR2L_80

namespace Erdos634.Draft.LaczFormal
open Erdos634.LemmaS

theorem allCert_80 : allCert 80 = true := by
  refine allCert_of_lite_chunks 80 3 [0, 3, 6, 9, 12, 15, 18, 21, 24, 27, 30, 33, 36, 39, 42, 45, 48, 51, 54, 57, 60, 63, 66, 69, 72, 75, 78] ?_ ?_
  · intro lo hlo
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlo
    rcases hlo with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Erdos634.Lite.c80_0
    · exact Erdos634.Lite.c80_3
    · exact Erdos634.Lite.c80_6
    · exact Erdos634.Lite.c80_9
    · exact Erdos634.Lite.c80_12
    · exact Erdos634.Lite.c80_15
    · exact Erdos634.Lite.c80_18
    · exact Erdos634.Lite.c80_21
    · exact Erdos634.Lite.c80_24
    · exact Erdos634.Lite.c80_27
    · exact Erdos634.Lite.c80_30
    · exact Erdos634.Lite.c80_33
    · exact Erdos634.Lite.c80_36
    · exact Erdos634.Lite.c80_39
    · exact Erdos634.Lite.c80_42
    · exact Erdos634.Lite.c80_45
    · exact Erdos634.Lite.c80_48
    · exact Erdos634.Lite.c80_51
    · exact Erdos634.Lite.c80_54
    · exact Erdos634.Lite.c80_57
    · exact Erdos634.Lite.c80_60
    · exact Erdos634.Lite.c80_63
    · exact Erdos634.Lite.c80_66
    · exact Erdos634.Lite.c80_69
    · exact Erdos634.Lite.c80_72
    · exact Erdos634.Lite.c80_75
    · exact Erdos634.Lite.c80_78
  · decide +kernel

end Erdos634.Draft.LaczFormal

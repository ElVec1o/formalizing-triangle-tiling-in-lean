-- Draft/LaczFormalR2G_96.lean -- glue: `allCert 96 = true` from the chunks of `LaczFormalR2L_96`.  UNAUDITED.
import Erdos634.Draft.LaczFormalR2Bridge
import Erdos634.Draft.LaczFormalR2L_96

namespace Erdos634.Draft.LaczFormal
open Erdos634.LemmaS

theorem allCert_96 : allCert 96 = true := by
  refine allCert_of_lite_chunks 96 3 [0, 3, 6, 9, 12, 15, 18, 21, 24, 27, 30, 33, 36, 39, 42, 45, 48, 51, 54, 57, 60, 63, 66, 69, 72, 75, 78, 81, 84, 87, 90, 93] ?_ ?_
  · intro lo hlo
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlo
    rcases hlo with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Erdos634.Lite.c96_0
    · exact Erdos634.Lite.c96_3
    · exact Erdos634.Lite.c96_6
    · exact Erdos634.Lite.c96_9
    · exact Erdos634.Lite.c96_12
    · exact Erdos634.Lite.c96_15
    · exact Erdos634.Lite.c96_18
    · exact Erdos634.Lite.c96_21
    · exact Erdos634.Lite.c96_24
    · exact Erdos634.Lite.c96_27
    · exact Erdos634.Lite.c96_30
    · exact Erdos634.Lite.c96_33
    · exact Erdos634.Lite.c96_36
    · exact Erdos634.Lite.c96_39
    · exact Erdos634.Lite.c96_42
    · exact Erdos634.Lite.c96_45
    · exact Erdos634.Lite.c96_48
    · exact Erdos634.Lite.c96_51
    · exact Erdos634.Lite.c96_54
    · exact Erdos634.Lite.c96_57
    · exact Erdos634.Lite.c96_60
    · exact Erdos634.Lite.c96_63
    · exact Erdos634.Lite.c96_66
    · exact Erdos634.Lite.c96_69
    · exact Erdos634.Lite.c96_72
    · exact Erdos634.Lite.c96_75
    · exact Erdos634.Lite.c96_78
    · exact Erdos634.Lite.c96_81
    · exact Erdos634.Lite.c96_84
    · exact Erdos634.Lite.c96_87
    · exact Erdos634.Lite.c96_90
    · exact Erdos634.Lite.c96_93
  · decide +kernel

end Erdos634.Draft.LaczFormal

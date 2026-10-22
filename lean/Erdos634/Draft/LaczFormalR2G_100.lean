-- Draft/LaczFormalR2G_100.lean -- glue: `allCert 100 = true` from the chunks of `LaczFormalR2L_100`.  UNAUDITED.
import Erdos634.Draft.LaczFormalR2Bridge
import Erdos634.Draft.LaczFormalR2L_100

namespace Erdos634.Draft.LaczFormal
open Erdos634.LemmaS

theorem allCert_100 : allCert 100 = true := by
  refine allCert_of_lite_chunks 100 3 [0, 3, 6, 9, 12, 15, 18, 21, 24, 27, 30, 33, 36, 39, 42, 45, 48, 51, 54, 57, 60, 63, 66, 69, 72, 75, 78, 81, 84, 87, 90, 93, 96, 99] ?_ ?_
  · intro lo hlo
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlo
    rcases hlo with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Erdos634.Lite.c100_0
    · exact Erdos634.Lite.c100_3
    · exact Erdos634.Lite.c100_6
    · exact Erdos634.Lite.c100_9
    · exact Erdos634.Lite.c100_12
    · exact Erdos634.Lite.c100_15
    · exact Erdos634.Lite.c100_18
    · exact Erdos634.Lite.c100_21
    · exact Erdos634.Lite.c100_24
    · exact Erdos634.Lite.c100_27
    · exact Erdos634.Lite.c100_30
    · exact Erdos634.Lite.c100_33
    · exact Erdos634.Lite.c100_36
    · exact Erdos634.Lite.c100_39
    · exact Erdos634.Lite.c100_42
    · exact Erdos634.Lite.c100_45
    · exact Erdos634.Lite.c100_48
    · exact Erdos634.Lite.c100_51
    · exact Erdos634.Lite.c100_54
    · exact Erdos634.Lite.c100_57
    · exact Erdos634.Lite.c100_60
    · exact Erdos634.Lite.c100_63
    · exact Erdos634.Lite.c100_66
    · exact Erdos634.Lite.c100_69
    · exact Erdos634.Lite.c100_72
    · exact Erdos634.Lite.c100_75
    · exact Erdos634.Lite.c100_78
    · exact Erdos634.Lite.c100_81
    · exact Erdos634.Lite.c100_84
    · exact Erdos634.Lite.c100_87
    · exact Erdos634.Lite.c100_90
    · exact Erdos634.Lite.c100_93
    · exact Erdos634.Lite.c100_96
    · exact Erdos634.Lite.c100_99
  · decide +kernel

end Erdos634.Draft.LaczFormal

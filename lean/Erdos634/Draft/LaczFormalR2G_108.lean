-- Draft/LaczFormalR2G_108.lean -- glue: `allCert 108 = true` from the chunks of `LaczFormalR2L_108`.  UNAUDITED.
import Erdos634.Draft.LaczFormalR2Bridge
import Erdos634.Draft.LaczFormalR2L_108

namespace Erdos634.Draft.LaczFormal
open Erdos634.LemmaS

theorem allCert_108 : allCert 108 = true := by
  refine allCert_of_lite_chunks 108 2 [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36, 38, 40, 42, 44, 46, 48, 50, 52, 54, 56, 58, 60, 62, 64, 66, 68, 70, 72, 74, 76, 78, 80, 82, 84, 86, 88, 90, 92, 94, 96, 98, 100, 102, 104, 106] ?_ ?_
  · intro lo hlo
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlo
    rcases hlo with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Erdos634.Lite.c108_0
    · exact Erdos634.Lite.c108_2
    · exact Erdos634.Lite.c108_4
    · exact Erdos634.Lite.c108_6
    · exact Erdos634.Lite.c108_8
    · exact Erdos634.Lite.c108_10
    · exact Erdos634.Lite.c108_12
    · exact Erdos634.Lite.c108_14
    · exact Erdos634.Lite.c108_16
    · exact Erdos634.Lite.c108_18
    · exact Erdos634.Lite.c108_20
    · exact Erdos634.Lite.c108_22
    · exact Erdos634.Lite.c108_24
    · exact Erdos634.Lite.c108_26
    · exact Erdos634.Lite.c108_28
    · exact Erdos634.Lite.c108_30
    · exact Erdos634.Lite.c108_32
    · exact Erdos634.Lite.c108_34
    · exact Erdos634.Lite.c108_36
    · exact Erdos634.Lite.c108_38
    · exact Erdos634.Lite.c108_40
    · exact Erdos634.Lite.c108_42
    · exact Erdos634.Lite.c108_44
    · exact Erdos634.Lite.c108_46
    · exact Erdos634.Lite.c108_48
    · exact Erdos634.Lite.c108_50
    · exact Erdos634.Lite.c108_52
    · exact Erdos634.Lite.c108_54
    · exact Erdos634.Lite.c108_56
    · exact Erdos634.Lite.c108_58
    · exact Erdos634.Lite.c108_60
    · exact Erdos634.Lite.c108_62
    · exact Erdos634.Lite.c108_64
    · exact Erdos634.Lite.c108_66
    · exact Erdos634.Lite.c108_68
    · exact Erdos634.Lite.c108_70
    · exact Erdos634.Lite.c108_72
    · exact Erdos634.Lite.c108_74
    · exact Erdos634.Lite.c108_76
    · exact Erdos634.Lite.c108_78
    · exact Erdos634.Lite.c108_80
    · exact Erdos634.Lite.c108_82
    · exact Erdos634.Lite.c108_84
    · exact Erdos634.Lite.c108_86
    · exact Erdos634.Lite.c108_88
    · exact Erdos634.Lite.c108_90
    · exact Erdos634.Lite.c108_92
    · exact Erdos634.Lite.c108_94
    · exact Erdos634.Lite.c108_96
    · exact Erdos634.Lite.c108_98
    · exact Erdos634.Lite.c108_100
    · exact Erdos634.Lite.c108_102
    · exact Erdos634.Lite.c108_104
    · exact Erdos634.Lite.c108_106
  · decide +kernel

end Erdos634.Draft.LaczFormal

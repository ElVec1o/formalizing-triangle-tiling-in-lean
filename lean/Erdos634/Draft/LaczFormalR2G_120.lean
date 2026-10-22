-- Draft/LaczFormalR2G_120.lean -- glue: `allCert 120 = true` from the chunks of `LaczFormalR2L_120`.  UNAUDITED.
import Erdos634.Draft.LaczFormalR2Bridge
import Erdos634.Draft.LaczFormalR2L_120

namespace Erdos634.Draft.LaczFormal
open Erdos634.LemmaS

theorem allCert_120 : allCert 120 = true := by
  refine allCert_of_lite_chunks 120 2 [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36, 38, 40, 42, 44, 46, 48, 50, 52, 54, 56, 58, 60, 62, 64, 66, 68, 70, 72, 74, 76, 78, 80, 82, 84, 86, 88, 90, 92, 94, 96, 98, 100, 102, 104, 106, 108, 110, 112, 114, 116, 118] ?_ ?_
  · intro lo hlo
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlo
    rcases hlo with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Erdos634.Lite.c120_0
    · exact Erdos634.Lite.c120_2
    · exact Erdos634.Lite.c120_4
    · exact Erdos634.Lite.c120_6
    · exact Erdos634.Lite.c120_8
    · exact Erdos634.Lite.c120_10
    · exact Erdos634.Lite.c120_12
    · exact Erdos634.Lite.c120_14
    · exact Erdos634.Lite.c120_16
    · exact Erdos634.Lite.c120_18
    · exact Erdos634.Lite.c120_20
    · exact Erdos634.Lite.c120_22
    · exact Erdos634.Lite.c120_24
    · exact Erdos634.Lite.c120_26
    · exact Erdos634.Lite.c120_28
    · exact Erdos634.Lite.c120_30
    · exact Erdos634.Lite.c120_32
    · exact Erdos634.Lite.c120_34
    · exact Erdos634.Lite.c120_36
    · exact Erdos634.Lite.c120_38
    · exact Erdos634.Lite.c120_40
    · exact Erdos634.Lite.c120_42
    · exact Erdos634.Lite.c120_44
    · exact Erdos634.Lite.c120_46
    · exact Erdos634.Lite.c120_48
    · exact Erdos634.Lite.c120_50
    · exact Erdos634.Lite.c120_52
    · exact Erdos634.Lite.c120_54
    · exact Erdos634.Lite.c120_56
    · exact Erdos634.Lite.c120_58
    · exact Erdos634.Lite.c120_60
    · exact Erdos634.Lite.c120_62
    · exact Erdos634.Lite.c120_64
    · exact Erdos634.Lite.c120_66
    · exact Erdos634.Lite.c120_68
    · exact Erdos634.Lite.c120_70
    · exact Erdos634.Lite.c120_72
    · exact Erdos634.Lite.c120_74
    · exact Erdos634.Lite.c120_76
    · exact Erdos634.Lite.c120_78
    · exact Erdos634.Lite.c120_80
    · exact Erdos634.Lite.c120_82
    · exact Erdos634.Lite.c120_84
    · exact Erdos634.Lite.c120_86
    · exact Erdos634.Lite.c120_88
    · exact Erdos634.Lite.c120_90
    · exact Erdos634.Lite.c120_92
    · exact Erdos634.Lite.c120_94
    · exact Erdos634.Lite.c120_96
    · exact Erdos634.Lite.c120_98
    · exact Erdos634.Lite.c120_100
    · exact Erdos634.Lite.c120_102
    · exact Erdos634.Lite.c120_104
    · exact Erdos634.Lite.c120_106
    · exact Erdos634.Lite.c120_108
    · exact Erdos634.Lite.c120_110
    · exact Erdos634.Lite.c120_112
    · exact Erdos634.Lite.c120_114
    · exact Erdos634.Lite.c120_116
    · exact Erdos634.Lite.c120_118
  · decide +kernel

end Erdos634.Draft.LaczFormal

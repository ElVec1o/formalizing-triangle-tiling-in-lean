-- Draft/LaczFormalR2G_125.lean -- glue: `allCert 125 = true` from the chunks of `LaczFormalR2L_125`.  UNAUDITED.
import Erdos634.Draft.LaczFormalR2Bridge
import Erdos634.Draft.LaczFormalR2L_125

namespace Erdos634.Draft.LaczFormal
open Erdos634.LemmaS

theorem allCert_125 : allCert 125 = true := by
  refine allCert_of_lite_chunks 125 2 [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36, 38, 40, 42, 44, 46, 48, 50, 52, 54, 56, 58, 60, 62, 64, 66, 68, 70, 72, 74, 76, 78, 80, 82, 84, 86, 88, 90, 92, 94, 96, 98, 100, 102, 104, 106, 108, 110, 112, 114, 116, 118, 120, 122, 124] ?_ ?_
  · intro lo hlo
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlo
    rcases hlo with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Erdos634.Lite.c125_0
    · exact Erdos634.Lite.c125_2
    · exact Erdos634.Lite.c125_4
    · exact Erdos634.Lite.c125_6
    · exact Erdos634.Lite.c125_8
    · exact Erdos634.Lite.c125_10
    · exact Erdos634.Lite.c125_12
    · exact Erdos634.Lite.c125_14
    · exact Erdos634.Lite.c125_16
    · exact Erdos634.Lite.c125_18
    · exact Erdos634.Lite.c125_20
    · exact Erdos634.Lite.c125_22
    · exact Erdos634.Lite.c125_24
    · exact Erdos634.Lite.c125_26
    · exact Erdos634.Lite.c125_28
    · exact Erdos634.Lite.c125_30
    · exact Erdos634.Lite.c125_32
    · exact Erdos634.Lite.c125_34
    · exact Erdos634.Lite.c125_36
    · exact Erdos634.Lite.c125_38
    · exact Erdos634.Lite.c125_40
    · exact Erdos634.Lite.c125_42
    · exact Erdos634.Lite.c125_44
    · exact Erdos634.Lite.c125_46
    · exact Erdos634.Lite.c125_48
    · exact Erdos634.Lite.c125_50
    · exact Erdos634.Lite.c125_52
    · exact Erdos634.Lite.c125_54
    · exact Erdos634.Lite.c125_56
    · exact Erdos634.Lite.c125_58
    · exact Erdos634.Lite.c125_60
    · exact Erdos634.Lite.c125_62
    · exact Erdos634.Lite.c125_64
    · exact Erdos634.Lite.c125_66
    · exact Erdos634.Lite.c125_68
    · exact Erdos634.Lite.c125_70
    · exact Erdos634.Lite.c125_72
    · exact Erdos634.Lite.c125_74
    · exact Erdos634.Lite.c125_76
    · exact Erdos634.Lite.c125_78
    · exact Erdos634.Lite.c125_80
    · exact Erdos634.Lite.c125_82
    · exact Erdos634.Lite.c125_84
    · exact Erdos634.Lite.c125_86
    · exact Erdos634.Lite.c125_88
    · exact Erdos634.Lite.c125_90
    · exact Erdos634.Lite.c125_92
    · exact Erdos634.Lite.c125_94
    · exact Erdos634.Lite.c125_96
    · exact Erdos634.Lite.c125_98
    · exact Erdos634.Lite.c125_100
    · exact Erdos634.Lite.c125_102
    · exact Erdos634.Lite.c125_104
    · exact Erdos634.Lite.c125_106
    · exact Erdos634.Lite.c125_108
    · exact Erdos634.Lite.c125_110
    · exact Erdos634.Lite.c125_112
    · exact Erdos634.Lite.c125_114
    · exact Erdos634.Lite.c125_116
    · exact Erdos634.Lite.c125_118
    · exact Erdos634.Lite.c125_120
    · exact Erdos634.Lite.c125_122
    · exact Erdos634.Lite.c125_124
  · decide +kernel

end Erdos634.Draft.LaczFormal

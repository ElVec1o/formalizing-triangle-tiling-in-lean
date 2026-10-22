-- Draft/LaczFormalR2G_135.lean -- glue: `allCert 135 = true` from the chunks of `LaczFormalR2L_135`.  UNAUDITED.
import Erdos634.Draft.LaczFormalR2Bridge
import Erdos634.Draft.LaczFormalR2L_135

namespace Erdos634.Draft.LaczFormal
open Erdos634.LemmaS

theorem allCert_135 : allCert 135 = true := by
  refine allCert_of_lite_chunks 135 2 [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36, 38, 40, 42, 44, 46, 48, 50, 52, 54, 56, 58, 60, 62, 64, 66, 68, 70, 72, 74, 76, 78, 80, 82, 84, 86, 88, 90, 92, 94, 96, 98, 100, 102, 104, 106, 108, 110, 112, 114, 116, 118, 120, 122, 124, 126, 128, 130, 132, 134] ?_ ?_
  · intro lo hlo
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlo
    rcases hlo with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Erdos634.Lite.c135_0
    · exact Erdos634.Lite.c135_2
    · exact Erdos634.Lite.c135_4
    · exact Erdos634.Lite.c135_6
    · exact Erdos634.Lite.c135_8
    · exact Erdos634.Lite.c135_10
    · exact Erdos634.Lite.c135_12
    · exact Erdos634.Lite.c135_14
    · exact Erdos634.Lite.c135_16
    · exact Erdos634.Lite.c135_18
    · exact Erdos634.Lite.c135_20
    · exact Erdos634.Lite.c135_22
    · exact Erdos634.Lite.c135_24
    · exact Erdos634.Lite.c135_26
    · exact Erdos634.Lite.c135_28
    · exact Erdos634.Lite.c135_30
    · exact Erdos634.Lite.c135_32
    · exact Erdos634.Lite.c135_34
    · exact Erdos634.Lite.c135_36
    · exact Erdos634.Lite.c135_38
    · exact Erdos634.Lite.c135_40
    · exact Erdos634.Lite.c135_42
    · exact Erdos634.Lite.c135_44
    · exact Erdos634.Lite.c135_46
    · exact Erdos634.Lite.c135_48
    · exact Erdos634.Lite.c135_50
    · exact Erdos634.Lite.c135_52
    · exact Erdos634.Lite.c135_54
    · exact Erdos634.Lite.c135_56
    · exact Erdos634.Lite.c135_58
    · exact Erdos634.Lite.c135_60
    · exact Erdos634.Lite.c135_62
    · exact Erdos634.Lite.c135_64
    · exact Erdos634.Lite.c135_66
    · exact Erdos634.Lite.c135_68
    · exact Erdos634.Lite.c135_70
    · exact Erdos634.Lite.c135_72
    · exact Erdos634.Lite.c135_74
    · exact Erdos634.Lite.c135_76
    · exact Erdos634.Lite.c135_78
    · exact Erdos634.Lite.c135_80
    · exact Erdos634.Lite.c135_82
    · exact Erdos634.Lite.c135_84
    · exact Erdos634.Lite.c135_86
    · exact Erdos634.Lite.c135_88
    · exact Erdos634.Lite.c135_90
    · exact Erdos634.Lite.c135_92
    · exact Erdos634.Lite.c135_94
    · exact Erdos634.Lite.c135_96
    · exact Erdos634.Lite.c135_98
    · exact Erdos634.Lite.c135_100
    · exact Erdos634.Lite.c135_102
    · exact Erdos634.Lite.c135_104
    · exact Erdos634.Lite.c135_106
    · exact Erdos634.Lite.c135_108
    · exact Erdos634.Lite.c135_110
    · exact Erdos634.Lite.c135_112
    · exact Erdos634.Lite.c135_114
    · exact Erdos634.Lite.c135_116
    · exact Erdos634.Lite.c135_118
    · exact Erdos634.Lite.c135_120
    · exact Erdos634.Lite.c135_122
    · exact Erdos634.Lite.c135_124
    · exact Erdos634.Lite.c135_126
    · exact Erdos634.Lite.c135_128
    · exact Erdos634.Lite.c135_130
    · exact Erdos634.Lite.c135_132
    · exact Erdos634.Lite.c135_134
  · decide +kernel

end Erdos634.Draft.LaczFormal

-- Draft/LaczFormalR2G_160.lean -- glue: `allCert 160 = true` from the chunks of `LaczFormalR2L_160`.  UNAUDITED.
import Erdos634.Draft.LaczFormalR2Bridge
import Erdos634.Draft.LaczFormalR2L_160

namespace Erdos634.Draft.LaczFormal
open Erdos634.LemmaS

theorem allCert_160 : allCert 160 = true := by
  refine allCert_of_lite_chunks 160 2 [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36, 38, 40, 42, 44, 46, 48, 50, 52, 54, 56, 58, 60, 62, 64, 66, 68, 70, 72, 74, 76, 78, 80, 82, 84, 86, 88, 90, 92, 94, 96, 98, 100, 102, 104, 106, 108, 110, 112, 114, 116, 118, 120, 122, 124, 126, 128, 130, 132, 134, 136, 138, 140, 142, 144, 146, 148, 150, 152, 154, 156, 158] ?_ ?_
  · intro lo hlo
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlo
    rcases hlo with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Erdos634.Lite.c160_0
    · exact Erdos634.Lite.c160_2
    · exact Erdos634.Lite.c160_4
    · exact Erdos634.Lite.c160_6
    · exact Erdos634.Lite.c160_8
    · exact Erdos634.Lite.c160_10
    · exact Erdos634.Lite.c160_12
    · exact Erdos634.Lite.c160_14
    · exact Erdos634.Lite.c160_16
    · exact Erdos634.Lite.c160_18
    · exact Erdos634.Lite.c160_20
    · exact Erdos634.Lite.c160_22
    · exact Erdos634.Lite.c160_24
    · exact Erdos634.Lite.c160_26
    · exact Erdos634.Lite.c160_28
    · exact Erdos634.Lite.c160_30
    · exact Erdos634.Lite.c160_32
    · exact Erdos634.Lite.c160_34
    · exact Erdos634.Lite.c160_36
    · exact Erdos634.Lite.c160_38
    · exact Erdos634.Lite.c160_40
    · exact Erdos634.Lite.c160_42
    · exact Erdos634.Lite.c160_44
    · exact Erdos634.Lite.c160_46
    · exact Erdos634.Lite.c160_48
    · exact Erdos634.Lite.c160_50
    · exact Erdos634.Lite.c160_52
    · exact Erdos634.Lite.c160_54
    · exact Erdos634.Lite.c160_56
    · exact Erdos634.Lite.c160_58
    · exact Erdos634.Lite.c160_60
    · exact Erdos634.Lite.c160_62
    · exact Erdos634.Lite.c160_64
    · exact Erdos634.Lite.c160_66
    · exact Erdos634.Lite.c160_68
    · exact Erdos634.Lite.c160_70
    · exact Erdos634.Lite.c160_72
    · exact Erdos634.Lite.c160_74
    · exact Erdos634.Lite.c160_76
    · exact Erdos634.Lite.c160_78
    · exact Erdos634.Lite.c160_80
    · exact Erdos634.Lite.c160_82
    · exact Erdos634.Lite.c160_84
    · exact Erdos634.Lite.c160_86
    · exact Erdos634.Lite.c160_88
    · exact Erdos634.Lite.c160_90
    · exact Erdos634.Lite.c160_92
    · exact Erdos634.Lite.c160_94
    · exact Erdos634.Lite.c160_96
    · exact Erdos634.Lite.c160_98
    · exact Erdos634.Lite.c160_100
    · exact Erdos634.Lite.c160_102
    · exact Erdos634.Lite.c160_104
    · exact Erdos634.Lite.c160_106
    · exact Erdos634.Lite.c160_108
    · exact Erdos634.Lite.c160_110
    · exact Erdos634.Lite.c160_112
    · exact Erdos634.Lite.c160_114
    · exact Erdos634.Lite.c160_116
    · exact Erdos634.Lite.c160_118
    · exact Erdos634.Lite.c160_120
    · exact Erdos634.Lite.c160_122
    · exact Erdos634.Lite.c160_124
    · exact Erdos634.Lite.c160_126
    · exact Erdos634.Lite.c160_128
    · exact Erdos634.Lite.c160_130
    · exact Erdos634.Lite.c160_132
    · exact Erdos634.Lite.c160_134
    · exact Erdos634.Lite.c160_136
    · exact Erdos634.Lite.c160_138
    · exact Erdos634.Lite.c160_140
    · exact Erdos634.Lite.c160_142
    · exact Erdos634.Lite.c160_144
    · exact Erdos634.Lite.c160_146
    · exact Erdos634.Lite.c160_148
    · exact Erdos634.Lite.c160_150
    · exact Erdos634.Lite.c160_152
    · exact Erdos634.Lite.c160_154
    · exact Erdos634.Lite.c160_156
    · exact Erdos634.Lite.c160_158
  · decide +kernel

end Erdos634.Draft.LaczFormal

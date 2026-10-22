-- Draft/LaczFormalR2G_162.lean -- glue: `allCert 162 = true` from the chunks of `LaczFormalR2L_162`.  UNAUDITED.
import Erdos634.Draft.LaczFormalR2Bridge
import Erdos634.Draft.LaczFormalR2L_162

namespace Erdos634.Draft.LaczFormal
open Erdos634.LemmaS

theorem allCert_162 : allCert 162 = true := by
  refine allCert_of_lite_chunks 162 2 [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36, 38, 40, 42, 44, 46, 48, 50, 52, 54, 56, 58, 60, 62, 64, 66, 68, 70, 72, 74, 76, 78, 80, 82, 84, 86, 88, 90, 92, 94, 96, 98, 100, 102, 104, 106, 108, 110, 112, 114, 116, 118, 120, 122, 124, 126, 128, 130, 132, 134, 136, 138, 140, 142, 144, 146, 148, 150, 152, 154, 156, 158, 160] ?_ ?_
  · intro lo hlo
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlo
    rcases hlo with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Erdos634.Lite.c162_0
    · exact Erdos634.Lite.c162_2
    · exact Erdos634.Lite.c162_4
    · exact Erdos634.Lite.c162_6
    · exact Erdos634.Lite.c162_8
    · exact Erdos634.Lite.c162_10
    · exact Erdos634.Lite.c162_12
    · exact Erdos634.Lite.c162_14
    · exact Erdos634.Lite.c162_16
    · exact Erdos634.Lite.c162_18
    · exact Erdos634.Lite.c162_20
    · exact Erdos634.Lite.c162_22
    · exact Erdos634.Lite.c162_24
    · exact Erdos634.Lite.c162_26
    · exact Erdos634.Lite.c162_28
    · exact Erdos634.Lite.c162_30
    · exact Erdos634.Lite.c162_32
    · exact Erdos634.Lite.c162_34
    · exact Erdos634.Lite.c162_36
    · exact Erdos634.Lite.c162_38
    · exact Erdos634.Lite.c162_40
    · exact Erdos634.Lite.c162_42
    · exact Erdos634.Lite.c162_44
    · exact Erdos634.Lite.c162_46
    · exact Erdos634.Lite.c162_48
    · exact Erdos634.Lite.c162_50
    · exact Erdos634.Lite.c162_52
    · exact Erdos634.Lite.c162_54
    · exact Erdos634.Lite.c162_56
    · exact Erdos634.Lite.c162_58
    · exact Erdos634.Lite.c162_60
    · exact Erdos634.Lite.c162_62
    · exact Erdos634.Lite.c162_64
    · exact Erdos634.Lite.c162_66
    · exact Erdos634.Lite.c162_68
    · exact Erdos634.Lite.c162_70
    · exact Erdos634.Lite.c162_72
    · exact Erdos634.Lite.c162_74
    · exact Erdos634.Lite.c162_76
    · exact Erdos634.Lite.c162_78
    · exact Erdos634.Lite.c162_80
    · exact Erdos634.Lite.c162_82
    · exact Erdos634.Lite.c162_84
    · exact Erdos634.Lite.c162_86
    · exact Erdos634.Lite.c162_88
    · exact Erdos634.Lite.c162_90
    · exact Erdos634.Lite.c162_92
    · exact Erdos634.Lite.c162_94
    · exact Erdos634.Lite.c162_96
    · exact Erdos634.Lite.c162_98
    · exact Erdos634.Lite.c162_100
    · exact Erdos634.Lite.c162_102
    · exact Erdos634.Lite.c162_104
    · exact Erdos634.Lite.c162_106
    · exact Erdos634.Lite.c162_108
    · exact Erdos634.Lite.c162_110
    · exact Erdos634.Lite.c162_112
    · exact Erdos634.Lite.c162_114
    · exact Erdos634.Lite.c162_116
    · exact Erdos634.Lite.c162_118
    · exact Erdos634.Lite.c162_120
    · exact Erdos634.Lite.c162_122
    · exact Erdos634.Lite.c162_124
    · exact Erdos634.Lite.c162_126
    · exact Erdos634.Lite.c162_128
    · exact Erdos634.Lite.c162_130
    · exact Erdos634.Lite.c162_132
    · exact Erdos634.Lite.c162_134
    · exact Erdos634.Lite.c162_136
    · exact Erdos634.Lite.c162_138
    · exact Erdos634.Lite.c162_140
    · exact Erdos634.Lite.c162_142
    · exact Erdos634.Lite.c162_144
    · exact Erdos634.Lite.c162_146
    · exact Erdos634.Lite.c162_148
    · exact Erdos634.Lite.c162_150
    · exact Erdos634.Lite.c162_152
    · exact Erdos634.Lite.c162_154
    · exact Erdos634.Lite.c162_156
    · exact Erdos634.Lite.c162_158
    · exact Erdos634.Lite.c162_160
  · decide +kernel

end Erdos634.Draft.LaczFormal

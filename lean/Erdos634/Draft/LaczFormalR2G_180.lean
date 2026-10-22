-- Draft/LaczFormalR2G_180.lean -- glue: `allCert 180 = true` from the chunks of `LaczFormalR2L_180`.  UNAUDITED.
import Erdos634.Draft.LaczFormalR2Bridge
import Erdos634.Draft.LaczFormalR2L_180

namespace Erdos634.Draft.LaczFormal
open Erdos634.LemmaS

theorem allCert_180 : allCert 180 = true := by
  refine allCert_of_lite_chunks 180 2 [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36, 38, 40, 42, 44, 46, 48, 50, 52, 54, 56, 58, 60, 62, 64, 66, 68, 70, 72, 74, 76, 78, 80, 82, 84, 86, 88, 90, 92, 94, 96, 98, 100, 102, 104, 106, 108, 110, 112, 114, 116, 118, 120, 122, 124, 126, 128, 130, 132, 134, 136, 138, 140, 142, 144, 146, 148, 150, 152, 154, 156, 158, 160, 162, 164, 166, 168, 170, 172, 174, 176, 178] ?_ ?_
  · intro lo hlo
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlo
    rcases hlo with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Erdos634.Lite.c180_0
    · exact Erdos634.Lite.c180_2
    · exact Erdos634.Lite.c180_4
    · exact Erdos634.Lite.c180_6
    · exact Erdos634.Lite.c180_8
    · exact Erdos634.Lite.c180_10
    · exact Erdos634.Lite.c180_12
    · exact Erdos634.Lite.c180_14
    · exact Erdos634.Lite.c180_16
    · exact Erdos634.Lite.c180_18
    · exact Erdos634.Lite.c180_20
    · exact Erdos634.Lite.c180_22
    · exact Erdos634.Lite.c180_24
    · exact Erdos634.Lite.c180_26
    · exact Erdos634.Lite.c180_28
    · exact Erdos634.Lite.c180_30
    · exact Erdos634.Lite.c180_32
    · exact Erdos634.Lite.c180_34
    · exact Erdos634.Lite.c180_36
    · exact Erdos634.Lite.c180_38
    · exact Erdos634.Lite.c180_40
    · exact Erdos634.Lite.c180_42
    · exact Erdos634.Lite.c180_44
    · exact Erdos634.Lite.c180_46
    · exact Erdos634.Lite.c180_48
    · exact Erdos634.Lite.c180_50
    · exact Erdos634.Lite.c180_52
    · exact Erdos634.Lite.c180_54
    · exact Erdos634.Lite.c180_56
    · exact Erdos634.Lite.c180_58
    · exact Erdos634.Lite.c180_60
    · exact Erdos634.Lite.c180_62
    · exact Erdos634.Lite.c180_64
    · exact Erdos634.Lite.c180_66
    · exact Erdos634.Lite.c180_68
    · exact Erdos634.Lite.c180_70
    · exact Erdos634.Lite.c180_72
    · exact Erdos634.Lite.c180_74
    · exact Erdos634.Lite.c180_76
    · exact Erdos634.Lite.c180_78
    · exact Erdos634.Lite.c180_80
    · exact Erdos634.Lite.c180_82
    · exact Erdos634.Lite.c180_84
    · exact Erdos634.Lite.c180_86
    · exact Erdos634.Lite.c180_88
    · exact Erdos634.Lite.c180_90
    · exact Erdos634.Lite.c180_92
    · exact Erdos634.Lite.c180_94
    · exact Erdos634.Lite.c180_96
    · exact Erdos634.Lite.c180_98
    · exact Erdos634.Lite.c180_100
    · exact Erdos634.Lite.c180_102
    · exact Erdos634.Lite.c180_104
    · exact Erdos634.Lite.c180_106
    · exact Erdos634.Lite.c180_108
    · exact Erdos634.Lite.c180_110
    · exact Erdos634.Lite.c180_112
    · exact Erdos634.Lite.c180_114
    · exact Erdos634.Lite.c180_116
    · exact Erdos634.Lite.c180_118
    · exact Erdos634.Lite.c180_120
    · exact Erdos634.Lite.c180_122
    · exact Erdos634.Lite.c180_124
    · exact Erdos634.Lite.c180_126
    · exact Erdos634.Lite.c180_128
    · exact Erdos634.Lite.c180_130
    · exact Erdos634.Lite.c180_132
    · exact Erdos634.Lite.c180_134
    · exact Erdos634.Lite.c180_136
    · exact Erdos634.Lite.c180_138
    · exact Erdos634.Lite.c180_140
    · exact Erdos634.Lite.c180_142
    · exact Erdos634.Lite.c180_144
    · exact Erdos634.Lite.c180_146
    · exact Erdos634.Lite.c180_148
    · exact Erdos634.Lite.c180_150
    · exact Erdos634.Lite.c180_152
    · exact Erdos634.Lite.c180_154
    · exact Erdos634.Lite.c180_156
    · exact Erdos634.Lite.c180_158
    · exact Erdos634.Lite.c180_160
    · exact Erdos634.Lite.c180_162
    · exact Erdos634.Lite.c180_164
    · exact Erdos634.Lite.c180_166
    · exact Erdos634.Lite.c180_168
    · exact Erdos634.Lite.c180_170
    · exact Erdos634.Lite.c180_172
    · exact Erdos634.Lite.c180_174
    · exact Erdos634.Lite.c180_176
    · exact Erdos634.Lite.c180_178
  · decide +kernel

end Erdos634.Draft.LaczFormal

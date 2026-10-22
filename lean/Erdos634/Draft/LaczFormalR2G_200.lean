-- Draft/LaczFormalR2G_200.lean -- glue: `allCert 200 = true` from the chunks of `LaczFormalR2L_200`.  UNAUDITED.
import Erdos634.Draft.LaczFormalR2Bridge
import Erdos634.Draft.LaczFormalR2L_200

namespace Erdos634.Draft.LaczFormal
open Erdos634.LemmaS

theorem allCert_200 : allCert 200 = true := by
  refine allCert_of_lite_chunks 200 2 [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36, 38, 40, 42, 44, 46, 48, 50, 52, 54, 56, 58, 60, 62, 64, 66, 68, 70, 72, 74, 76, 78, 80, 82, 84, 86, 88, 90, 92, 94, 96, 98, 100, 102, 104, 106, 108, 110, 112, 114, 116, 118, 120, 122, 124, 126, 128, 130, 132, 134, 136, 138, 140, 142, 144, 146, 148, 150, 152, 154, 156, 158, 160, 162, 164, 166, 168, 170, 172, 174, 176, 178, 180, 182, 184, 186, 188, 190, 192, 194, 196, 198] ?_ ?_
  · intro lo hlo
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlo
    rcases hlo with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Erdos634.Lite.c200_0
    · exact Erdos634.Lite.c200_2
    · exact Erdos634.Lite.c200_4
    · exact Erdos634.Lite.c200_6
    · exact Erdos634.Lite.c200_8
    · exact Erdos634.Lite.c200_10
    · exact Erdos634.Lite.c200_12
    · exact Erdos634.Lite.c200_14
    · exact Erdos634.Lite.c200_16
    · exact Erdos634.Lite.c200_18
    · exact Erdos634.Lite.c200_20
    · exact Erdos634.Lite.c200_22
    · exact Erdos634.Lite.c200_24
    · exact Erdos634.Lite.c200_26
    · exact Erdos634.Lite.c200_28
    · exact Erdos634.Lite.c200_30
    · exact Erdos634.Lite.c200_32
    · exact Erdos634.Lite.c200_34
    · exact Erdos634.Lite.c200_36
    · exact Erdos634.Lite.c200_38
    · exact Erdos634.Lite.c200_40
    · exact Erdos634.Lite.c200_42
    · exact Erdos634.Lite.c200_44
    · exact Erdos634.Lite.c200_46
    · exact Erdos634.Lite.c200_48
    · exact Erdos634.Lite.c200_50
    · exact Erdos634.Lite.c200_52
    · exact Erdos634.Lite.c200_54
    · exact Erdos634.Lite.c200_56
    · exact Erdos634.Lite.c200_58
    · exact Erdos634.Lite.c200_60
    · exact Erdos634.Lite.c200_62
    · exact Erdos634.Lite.c200_64
    · exact Erdos634.Lite.c200_66
    · exact Erdos634.Lite.c200_68
    · exact Erdos634.Lite.c200_70
    · exact Erdos634.Lite.c200_72
    · exact Erdos634.Lite.c200_74
    · exact Erdos634.Lite.c200_76
    · exact Erdos634.Lite.c200_78
    · exact Erdos634.Lite.c200_80
    · exact Erdos634.Lite.c200_82
    · exact Erdos634.Lite.c200_84
    · exact Erdos634.Lite.c200_86
    · exact Erdos634.Lite.c200_88
    · exact Erdos634.Lite.c200_90
    · exact Erdos634.Lite.c200_92
    · exact Erdos634.Lite.c200_94
    · exact Erdos634.Lite.c200_96
    · exact Erdos634.Lite.c200_98
    · exact Erdos634.Lite.c200_100
    · exact Erdos634.Lite.c200_102
    · exact Erdos634.Lite.c200_104
    · exact Erdos634.Lite.c200_106
    · exact Erdos634.Lite.c200_108
    · exact Erdos634.Lite.c200_110
    · exact Erdos634.Lite.c200_112
    · exact Erdos634.Lite.c200_114
    · exact Erdos634.Lite.c200_116
    · exact Erdos634.Lite.c200_118
    · exact Erdos634.Lite.c200_120
    · exact Erdos634.Lite.c200_122
    · exact Erdos634.Lite.c200_124
    · exact Erdos634.Lite.c200_126
    · exact Erdos634.Lite.c200_128
    · exact Erdos634.Lite.c200_130
    · exact Erdos634.Lite.c200_132
    · exact Erdos634.Lite.c200_134
    · exact Erdos634.Lite.c200_136
    · exact Erdos634.Lite.c200_138
    · exact Erdos634.Lite.c200_140
    · exact Erdos634.Lite.c200_142
    · exact Erdos634.Lite.c200_144
    · exact Erdos634.Lite.c200_146
    · exact Erdos634.Lite.c200_148
    · exact Erdos634.Lite.c200_150
    · exact Erdos634.Lite.c200_152
    · exact Erdos634.Lite.c200_154
    · exact Erdos634.Lite.c200_156
    · exact Erdos634.Lite.c200_158
    · exact Erdos634.Lite.c200_160
    · exact Erdos634.Lite.c200_162
    · exact Erdos634.Lite.c200_164
    · exact Erdos634.Lite.c200_166
    · exact Erdos634.Lite.c200_168
    · exact Erdos634.Lite.c200_170
    · exact Erdos634.Lite.c200_172
    · exact Erdos634.Lite.c200_174
    · exact Erdos634.Lite.c200_176
    · exact Erdos634.Lite.c200_178
    · exact Erdos634.Lite.c200_180
    · exact Erdos634.Lite.c200_182
    · exact Erdos634.Lite.c200_184
    · exact Erdos634.Lite.c200_186
    · exact Erdos634.Lite.c200_188
    · exact Erdos634.Lite.c200_190
    · exact Erdos634.Lite.c200_192
    · exact Erdos634.Lite.c200_194
    · exact Erdos634.Lite.c200_196
    · exact Erdos634.Lite.c200_198
  · decide +kernel

end Erdos634.Draft.LaczFormal

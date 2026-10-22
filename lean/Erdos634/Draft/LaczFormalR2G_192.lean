-- Draft/LaczFormalR2G_192.lean -- glue: `allCert 192 = true` from the chunks of `LaczFormalR2L_192`.  UNAUDITED.
import Erdos634.Draft.LaczFormalR2Bridge
import Erdos634.Draft.LaczFormalR2L_192

namespace Erdos634.Draft.LaczFormal
open Erdos634.LemmaS

theorem allCert_192 : allCert 192 = true := by
  refine allCert_of_lite_chunks 192 2 [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36, 38, 40, 42, 44, 46, 48, 50, 52, 54, 56, 58, 60, 62, 64, 66, 68, 70, 72, 74, 76, 78, 80, 82, 84, 86, 88, 90, 92, 94, 96, 98, 100, 102, 104, 106, 108, 110, 112, 114, 116, 118, 120, 122, 124, 126, 128, 130, 132, 134, 136, 138, 140, 142, 144, 146, 148, 150, 152, 154, 156, 158, 160, 162, 164, 166, 168, 170, 172, 174, 176, 178, 180, 182, 184, 186, 188, 190] ?_ ?_
  · intro lo hlo
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlo
    rcases hlo with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Erdos634.Lite.c192_0
    · exact Erdos634.Lite.c192_2
    · exact Erdos634.Lite.c192_4
    · exact Erdos634.Lite.c192_6
    · exact Erdos634.Lite.c192_8
    · exact Erdos634.Lite.c192_10
    · exact Erdos634.Lite.c192_12
    · exact Erdos634.Lite.c192_14
    · exact Erdos634.Lite.c192_16
    · exact Erdos634.Lite.c192_18
    · exact Erdos634.Lite.c192_20
    · exact Erdos634.Lite.c192_22
    · exact Erdos634.Lite.c192_24
    · exact Erdos634.Lite.c192_26
    · exact Erdos634.Lite.c192_28
    · exact Erdos634.Lite.c192_30
    · exact Erdos634.Lite.c192_32
    · exact Erdos634.Lite.c192_34
    · exact Erdos634.Lite.c192_36
    · exact Erdos634.Lite.c192_38
    · exact Erdos634.Lite.c192_40
    · exact Erdos634.Lite.c192_42
    · exact Erdos634.Lite.c192_44
    · exact Erdos634.Lite.c192_46
    · exact Erdos634.Lite.c192_48
    · exact Erdos634.Lite.c192_50
    · exact Erdos634.Lite.c192_52
    · exact Erdos634.Lite.c192_54
    · exact Erdos634.Lite.c192_56
    · exact Erdos634.Lite.c192_58
    · exact Erdos634.Lite.c192_60
    · exact Erdos634.Lite.c192_62
    · exact Erdos634.Lite.c192_64
    · exact Erdos634.Lite.c192_66
    · exact Erdos634.Lite.c192_68
    · exact Erdos634.Lite.c192_70
    · exact Erdos634.Lite.c192_72
    · exact Erdos634.Lite.c192_74
    · exact Erdos634.Lite.c192_76
    · exact Erdos634.Lite.c192_78
    · exact Erdos634.Lite.c192_80
    · exact Erdos634.Lite.c192_82
    · exact Erdos634.Lite.c192_84
    · exact Erdos634.Lite.c192_86
    · exact Erdos634.Lite.c192_88
    · exact Erdos634.Lite.c192_90
    · exact Erdos634.Lite.c192_92
    · exact Erdos634.Lite.c192_94
    · exact Erdos634.Lite.c192_96
    · exact Erdos634.Lite.c192_98
    · exact Erdos634.Lite.c192_100
    · exact Erdos634.Lite.c192_102
    · exact Erdos634.Lite.c192_104
    · exact Erdos634.Lite.c192_106
    · exact Erdos634.Lite.c192_108
    · exact Erdos634.Lite.c192_110
    · exact Erdos634.Lite.c192_112
    · exact Erdos634.Lite.c192_114
    · exact Erdos634.Lite.c192_116
    · exact Erdos634.Lite.c192_118
    · exact Erdos634.Lite.c192_120
    · exact Erdos634.Lite.c192_122
    · exact Erdos634.Lite.c192_124
    · exact Erdos634.Lite.c192_126
    · exact Erdos634.Lite.c192_128
    · exact Erdos634.Lite.c192_130
    · exact Erdos634.Lite.c192_132
    · exact Erdos634.Lite.c192_134
    · exact Erdos634.Lite.c192_136
    · exact Erdos634.Lite.c192_138
    · exact Erdos634.Lite.c192_140
    · exact Erdos634.Lite.c192_142
    · exact Erdos634.Lite.c192_144
    · exact Erdos634.Lite.c192_146
    · exact Erdos634.Lite.c192_148
    · exact Erdos634.Lite.c192_150
    · exact Erdos634.Lite.c192_152
    · exact Erdos634.Lite.c192_154
    · exact Erdos634.Lite.c192_156
    · exact Erdos634.Lite.c192_158
    · exact Erdos634.Lite.c192_160
    · exact Erdos634.Lite.c192_162
    · exact Erdos634.Lite.c192_164
    · exact Erdos634.Lite.c192_166
    · exact Erdos634.Lite.c192_168
    · exact Erdos634.Lite.c192_170
    · exact Erdos634.Lite.c192_172
    · exact Erdos634.Lite.c192_174
    · exact Erdos634.Lite.c192_176
    · exact Erdos634.Lite.c192_178
    · exact Erdos634.Lite.c192_180
    · exact Erdos634.Lite.c192_182
    · exact Erdos634.Lite.c192_184
    · exact Erdos634.Lite.c192_186
    · exact Erdos634.Lite.c192_188
    · exact Erdos634.Lite.c192_190
  · decide +kernel

end Erdos634.Draft.LaczFormal

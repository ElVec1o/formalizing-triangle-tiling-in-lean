-- Draft/LaczFormalR2G_150.lean -- glue: `allCert 150 = true` from the chunks of `LaczFormalR2L_150`.  UNAUDITED.
import Erdos634.Draft.LaczFormalR2Bridge
import Erdos634.Draft.LaczFormalR2L_150

namespace Erdos634.Draft.LaczFormal
open Erdos634.LemmaS

theorem allCert_150 : allCert 150 = true := by
  refine allCert_of_lite_chunks 150 2 [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36, 38, 40, 42, 44, 46, 48, 50, 52, 54, 56, 58, 60, 62, 64, 66, 68, 70, 72, 74, 76, 78, 80, 82, 84, 86, 88, 90, 92, 94, 96, 98, 100, 102, 104, 106, 108, 110, 112, 114, 116, 118, 120, 122, 124, 126, 128, 130, 132, 134, 136, 138, 140, 142, 144, 146, 148] ?_ ?_
  · intro lo hlo
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlo
    rcases hlo with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Erdos634.Lite.c150_0
    · exact Erdos634.Lite.c150_2
    · exact Erdos634.Lite.c150_4
    · exact Erdos634.Lite.c150_6
    · exact Erdos634.Lite.c150_8
    · exact Erdos634.Lite.c150_10
    · exact Erdos634.Lite.c150_12
    · exact Erdos634.Lite.c150_14
    · exact Erdos634.Lite.c150_16
    · exact Erdos634.Lite.c150_18
    · exact Erdos634.Lite.c150_20
    · exact Erdos634.Lite.c150_22
    · exact Erdos634.Lite.c150_24
    · exact Erdos634.Lite.c150_26
    · exact Erdos634.Lite.c150_28
    · exact Erdos634.Lite.c150_30
    · exact Erdos634.Lite.c150_32
    · exact Erdos634.Lite.c150_34
    · exact Erdos634.Lite.c150_36
    · exact Erdos634.Lite.c150_38
    · exact Erdos634.Lite.c150_40
    · exact Erdos634.Lite.c150_42
    · exact Erdos634.Lite.c150_44
    · exact Erdos634.Lite.c150_46
    · exact Erdos634.Lite.c150_48
    · exact Erdos634.Lite.c150_50
    · exact Erdos634.Lite.c150_52
    · exact Erdos634.Lite.c150_54
    · exact Erdos634.Lite.c150_56
    · exact Erdos634.Lite.c150_58
    · exact Erdos634.Lite.c150_60
    · exact Erdos634.Lite.c150_62
    · exact Erdos634.Lite.c150_64
    · exact Erdos634.Lite.c150_66
    · exact Erdos634.Lite.c150_68
    · exact Erdos634.Lite.c150_70
    · exact Erdos634.Lite.c150_72
    · exact Erdos634.Lite.c150_74
    · exact Erdos634.Lite.c150_76
    · exact Erdos634.Lite.c150_78
    · exact Erdos634.Lite.c150_80
    · exact Erdos634.Lite.c150_82
    · exact Erdos634.Lite.c150_84
    · exact Erdos634.Lite.c150_86
    · exact Erdos634.Lite.c150_88
    · exact Erdos634.Lite.c150_90
    · exact Erdos634.Lite.c150_92
    · exact Erdos634.Lite.c150_94
    · exact Erdos634.Lite.c150_96
    · exact Erdos634.Lite.c150_98
    · exact Erdos634.Lite.c150_100
    · exact Erdos634.Lite.c150_102
    · exact Erdos634.Lite.c150_104
    · exact Erdos634.Lite.c150_106
    · exact Erdos634.Lite.c150_108
    · exact Erdos634.Lite.c150_110
    · exact Erdos634.Lite.c150_112
    · exact Erdos634.Lite.c150_114
    · exact Erdos634.Lite.c150_116
    · exact Erdos634.Lite.c150_118
    · exact Erdos634.Lite.c150_120
    · exact Erdos634.Lite.c150_122
    · exact Erdos634.Lite.c150_124
    · exact Erdos634.Lite.c150_126
    · exact Erdos634.Lite.c150_128
    · exact Erdos634.Lite.c150_130
    · exact Erdos634.Lite.c150_132
    · exact Erdos634.Lite.c150_134
    · exact Erdos634.Lite.c150_136
    · exact Erdos634.Lite.c150_138
    · exact Erdos634.Lite.c150_140
    · exact Erdos634.Lite.c150_142
    · exact Erdos634.Lite.c150_144
    · exact Erdos634.Lite.c150_146
    · exact Erdos634.Lite.c150_148
  · decide +kernel

end Erdos634.Draft.LaczFormal

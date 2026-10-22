-- Draft/LaczFormalR2G_144.lean -- glue: `allCert 144 = true` from the chunks of `LaczFormalR2L_144`.  UNAUDITED.
import Erdos634.Draft.LaczFormalR2Bridge
import Erdos634.Draft.LaczFormalR2L_144

namespace Erdos634.Draft.LaczFormal
open Erdos634.LemmaS

theorem allCert_144 : allCert 144 = true := by
  refine allCert_of_lite_chunks 144 2 [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36, 38, 40, 42, 44, 46, 48, 50, 52, 54, 56, 58, 60, 62, 64, 66, 68, 70, 72, 74, 76, 78, 80, 82, 84, 86, 88, 90, 92, 94, 96, 98, 100, 102, 104, 106, 108, 110, 112, 114, 116, 118, 120, 122, 124, 126, 128, 130, 132, 134, 136, 138, 140, 142] ?_ ?_
  · intro lo hlo
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlo
    rcases hlo with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Erdos634.Lite.c144_0
    · exact Erdos634.Lite.c144_2
    · exact Erdos634.Lite.c144_4
    · exact Erdos634.Lite.c144_6
    · exact Erdos634.Lite.c144_8
    · exact Erdos634.Lite.c144_10
    · exact Erdos634.Lite.c144_12
    · exact Erdos634.Lite.c144_14
    · exact Erdos634.Lite.c144_16
    · exact Erdos634.Lite.c144_18
    · exact Erdos634.Lite.c144_20
    · exact Erdos634.Lite.c144_22
    · exact Erdos634.Lite.c144_24
    · exact Erdos634.Lite.c144_26
    · exact Erdos634.Lite.c144_28
    · exact Erdos634.Lite.c144_30
    · exact Erdos634.Lite.c144_32
    · exact Erdos634.Lite.c144_34
    · exact Erdos634.Lite.c144_36
    · exact Erdos634.Lite.c144_38
    · exact Erdos634.Lite.c144_40
    · exact Erdos634.Lite.c144_42
    · exact Erdos634.Lite.c144_44
    · exact Erdos634.Lite.c144_46
    · exact Erdos634.Lite.c144_48
    · exact Erdos634.Lite.c144_50
    · exact Erdos634.Lite.c144_52
    · exact Erdos634.Lite.c144_54
    · exact Erdos634.Lite.c144_56
    · exact Erdos634.Lite.c144_58
    · exact Erdos634.Lite.c144_60
    · exact Erdos634.Lite.c144_62
    · exact Erdos634.Lite.c144_64
    · exact Erdos634.Lite.c144_66
    · exact Erdos634.Lite.c144_68
    · exact Erdos634.Lite.c144_70
    · exact Erdos634.Lite.c144_72
    · exact Erdos634.Lite.c144_74
    · exact Erdos634.Lite.c144_76
    · exact Erdos634.Lite.c144_78
    · exact Erdos634.Lite.c144_80
    · exact Erdos634.Lite.c144_82
    · exact Erdos634.Lite.c144_84
    · exact Erdos634.Lite.c144_86
    · exact Erdos634.Lite.c144_88
    · exact Erdos634.Lite.c144_90
    · exact Erdos634.Lite.c144_92
    · exact Erdos634.Lite.c144_94
    · exact Erdos634.Lite.c144_96
    · exact Erdos634.Lite.c144_98
    · exact Erdos634.Lite.c144_100
    · exact Erdos634.Lite.c144_102
    · exact Erdos634.Lite.c144_104
    · exact Erdos634.Lite.c144_106
    · exact Erdos634.Lite.c144_108
    · exact Erdos634.Lite.c144_110
    · exact Erdos634.Lite.c144_112
    · exact Erdos634.Lite.c144_114
    · exact Erdos634.Lite.c144_116
    · exact Erdos634.Lite.c144_118
    · exact Erdos634.Lite.c144_120
    · exact Erdos634.Lite.c144_122
    · exact Erdos634.Lite.c144_124
    · exact Erdos634.Lite.c144_126
    · exact Erdos634.Lite.c144_128
    · exact Erdos634.Lite.c144_130
    · exact Erdos634.Lite.c144_132
    · exact Erdos634.Lite.c144_134
    · exact Erdos634.Lite.c144_136
    · exact Erdos634.Lite.c144_138
    · exact Erdos634.Lite.c144_140
    · exact Erdos634.Lite.c144_142
  · decide +kernel

end Erdos634.Draft.LaczFormal

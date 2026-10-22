-- Draft/LaczFormalR2G_128.lean -- glue: `allCert 128 = true` from the chunks of `LaczFormalR2L_128`.  UNAUDITED.
import Erdos634.Draft.LaczFormalR2Bridge
import Erdos634.Draft.LaczFormalR2L_128

namespace Erdos634.Draft.LaczFormal
open Erdos634.LemmaS

theorem allCert_128 : allCert 128 = true := by
  refine allCert_of_lite_chunks 128 2 [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36, 38, 40, 42, 44, 46, 48, 50, 52, 54, 56, 58, 60, 62, 64, 66, 68, 70, 72, 74, 76, 78, 80, 82, 84, 86, 88, 90, 92, 94, 96, 98, 100, 102, 104, 106, 108, 110, 112, 114, 116, 118, 120, 122, 124, 126] ?_ ?_
  · intro lo hlo
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlo
    rcases hlo with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Erdos634.Lite.c128_0
    · exact Erdos634.Lite.c128_2
    · exact Erdos634.Lite.c128_4
    · exact Erdos634.Lite.c128_6
    · exact Erdos634.Lite.c128_8
    · exact Erdos634.Lite.c128_10
    · exact Erdos634.Lite.c128_12
    · exact Erdos634.Lite.c128_14
    · exact Erdos634.Lite.c128_16
    · exact Erdos634.Lite.c128_18
    · exact Erdos634.Lite.c128_20
    · exact Erdos634.Lite.c128_22
    · exact Erdos634.Lite.c128_24
    · exact Erdos634.Lite.c128_26
    · exact Erdos634.Lite.c128_28
    · exact Erdos634.Lite.c128_30
    · exact Erdos634.Lite.c128_32
    · exact Erdos634.Lite.c128_34
    · exact Erdos634.Lite.c128_36
    · exact Erdos634.Lite.c128_38
    · exact Erdos634.Lite.c128_40
    · exact Erdos634.Lite.c128_42
    · exact Erdos634.Lite.c128_44
    · exact Erdos634.Lite.c128_46
    · exact Erdos634.Lite.c128_48
    · exact Erdos634.Lite.c128_50
    · exact Erdos634.Lite.c128_52
    · exact Erdos634.Lite.c128_54
    · exact Erdos634.Lite.c128_56
    · exact Erdos634.Lite.c128_58
    · exact Erdos634.Lite.c128_60
    · exact Erdos634.Lite.c128_62
    · exact Erdos634.Lite.c128_64
    · exact Erdos634.Lite.c128_66
    · exact Erdos634.Lite.c128_68
    · exact Erdos634.Lite.c128_70
    · exact Erdos634.Lite.c128_72
    · exact Erdos634.Lite.c128_74
    · exact Erdos634.Lite.c128_76
    · exact Erdos634.Lite.c128_78
    · exact Erdos634.Lite.c128_80
    · exact Erdos634.Lite.c128_82
    · exact Erdos634.Lite.c128_84
    · exact Erdos634.Lite.c128_86
    · exact Erdos634.Lite.c128_88
    · exact Erdos634.Lite.c128_90
    · exact Erdos634.Lite.c128_92
    · exact Erdos634.Lite.c128_94
    · exact Erdos634.Lite.c128_96
    · exact Erdos634.Lite.c128_98
    · exact Erdos634.Lite.c128_100
    · exact Erdos634.Lite.c128_102
    · exact Erdos634.Lite.c128_104
    · exact Erdos634.Lite.c128_106
    · exact Erdos634.Lite.c128_108
    · exact Erdos634.Lite.c128_110
    · exact Erdos634.Lite.c128_112
    · exact Erdos634.Lite.c128_114
    · exact Erdos634.Lite.c128_116
    · exact Erdos634.Lite.c128_118
    · exact Erdos634.Lite.c128_120
    · exact Erdos634.Lite.c128_122
    · exact Erdos634.Lite.c128_124
    · exact Erdos634.Lite.c128_126
  · decide +kernel

end Erdos634.Draft.LaczFormal

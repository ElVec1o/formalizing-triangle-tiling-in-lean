-- Draft/LaczFormalR2G_5.lean -- glue: `allCert 5 = true` from the chunks of `LaczFormalR2L_5`.  UNAUDITED.
import Erdos634.Draft.LaczFormalR2Bridge
import Erdos634.Draft.LaczFormalR2L_5

namespace Erdos634.Draft.LaczFormal
open Erdos634.LemmaS

theorem allCert_5 : allCert 5 = true := by
  refine allCert_of_lite_chunks 5 3 [0, 3] ?_ ?_
  · intro lo hlo
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlo
    rcases hlo with rfl | rfl
    · exact Erdos634.Lite.c5_0
    · exact Erdos634.Lite.c5_3
  · decide +kernel

end Erdos634.Draft.LaczFormal

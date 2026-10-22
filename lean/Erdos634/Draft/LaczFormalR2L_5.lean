-- Draft/LaczFormalR2L_5.lean -- chunked LIGHT kernel certificate for n = 5: `Erdos634.Lite.allCertR 5 lo 3` for lo = 0, 3, ... (each chunk its own `decide +kernel`,
-- so the process stays small).  Glued to `allCert 5` in `LaczFormalR2G_5`.  UNAUDITED.  Credit: Laczkovich (1995, Lemma S); our CaseACorF.
import Erdos634.Draft.LaczFormalR2Lite

namespace Erdos634.Lite

set_option maxHeartbeats 0 in
theorem c5_0 : allCertR 5 0 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem c5_3 : allCertR 5 3 3 = true := by decide +kernel

end Erdos634.Lite

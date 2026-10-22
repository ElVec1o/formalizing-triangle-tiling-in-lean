-- Draft/LaczFormalR2CertD.lean -- stage R2 (part 1, piece D): kernel certificates `allCert n = true` (CaseACorF) for 5-smooth n = [64, 72].
-- (R(a) = R0(a) for every primitive a with sum n; n outside the exceptional set {6,8,10,12,18,24,30,60}.)  UNAUDITED.
import Erdos634.Draft.CaseACorF

namespace Erdos634.Draft.LaczFormal
open Erdos634.LemmaS

theorem allCert_64 : allCert 64 = true := by decide +kernel
theorem allCert_72 : allCert 72 = true := by decide +kernel

end Erdos634.Draft.LaczFormal

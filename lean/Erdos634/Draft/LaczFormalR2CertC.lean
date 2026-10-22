-- Draft/LaczFormalR2CertC.lean -- stage R2 (part 1, piece C): kernel certificates `allCert n = true` (CaseACorF) for 5-smooth n = [48, 50, 54].
-- (R(a) = R0(a) for every primitive a with sum n; n outside the exceptional set {6,8,10,12,18,24,30,60}.)  UNAUDITED.
import Erdos634.Draft.CaseACorF

namespace Erdos634.Draft.LaczFormal
open Erdos634.LemmaS

theorem allCert_48 : allCert 48 = true := by decide +kernel
theorem allCert_50 : allCert 50 = true := by decide +kernel
theorem allCert_54 : allCert 54 = true := by decide +kernel

end Erdos634.Draft.LaczFormal

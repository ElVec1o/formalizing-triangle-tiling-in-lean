-- Draft/LaczFormalR2CertB.lean -- stage R2 (part 1, piece B): kernel certificates `allCert n = true` (CaseACorF) for 5-smooth n = [32, 36, 40, 45].
-- (R(a) = R0(a) for every primitive a with sum n; n outside the exceptional set {6,8,10,12,18,24,30,60}.)  UNAUDITED.
import Erdos634.Draft.CaseACorF

namespace Erdos634.Draft.LaczFormal
open Erdos634.LemmaS

theorem allCert_32 : allCert 32 = true := by decide +kernel
theorem allCert_36 : allCert 36 = true := by decide +kernel
theorem allCert_40 : allCert 40 = true := by decide +kernel
theorem allCert_45 : allCert 45 = true := by decide +kernel

end Erdos634.Draft.LaczFormal

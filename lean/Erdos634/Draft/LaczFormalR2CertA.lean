-- Draft/LaczFormalR2CertA.lean -- stage R2 (part 1, piece A): kernel certificates `allCert n = true` (CaseACorF) for 5-smooth n = [9, 15, 16, 20, 25, 27].
-- (R(a) = R0(a) for every primitive a with sum n; n outside the exceptional set {6,8,10,12,18,24,30,60}.)  UNAUDITED.
import Erdos634.Draft.CaseACorF

namespace Erdos634.Draft.LaczFormal
open Erdos634.LemmaS

theorem allCert_9 : allCert 9 = true := by decide +kernel
theorem allCert_15 : allCert 15 = true := by decide +kernel
theorem allCert_16 : allCert 16 = true := by decide +kernel
theorem allCert_20 : allCert 20 = true := by decide +kernel
theorem allCert_25 : allCert 25 = true := by decide +kernel
theorem allCert_27 : allCert 27 = true := by decide +kernel

end Erdos634.Draft.LaczFormal

-- Draft/LaczFormalR2CertE.lean -- stage R2 (part 1, piece E): kernel certificates `allCert n = true` (CaseACorF) for 5-smooth n = [75].
-- (R(a) = R0(a) for every primitive a with sum n; n outside the exceptional set {6,8,10,12,18,24,30,60}.)  UNAUDITED.
import Erdos634.Draft.CaseACorF

namespace Erdos634.Draft.LaczFormal
open Erdos634.LemmaS

theorem allCert_75 : allCert 75 = true := by decide +kernel

end Erdos634.Draft.LaczFormal

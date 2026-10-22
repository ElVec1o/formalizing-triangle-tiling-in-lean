-- Draft/LaczFormalIIcIsoWitL.lean -- NON-VACUITY of `IIcIsoCore` (Laczkovich, DCG 48 (2012), Thm 2.1, Case IIc, alpha = beta): the hypothesis block of `IIcIsoCore` is satisfied by the REGULAR OCTAGON cut into 8 isosceles triangles from its centre
-- (tile angles 3pi/8, 3pi/8, pi/4; sides 1, 1, s with s irrational), and `iic_iso_core` applies to it.  The conclusion is the printed one: `Concl7 \/ Concl5` (both hold for the regular octagon).
-- NOTE, UNAUDITED.  This shows the hypothesis block is consistent (not vacuous); it does not prove anything new about Erdos 634.  Credit: Laczkovich (DCG 48 (2012), Sect. 6), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcIsoWitK
import Erdos634.Draft.LaczFormalIIcIsoK

open Erdos634.Geometry Erdos634.CertCoord Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Thm21 Erdos634.Draft.LaczFormal.RG Erdos634.Draft.LaczFormal.Graph

namespace Erdos634.Draft.LaczFormal.IsoWit

instance octDiss_fans : HasFansC octDiss.toRegionDissection := hasFansC_poly octDiss.toRegionDissection oct rfl

/-- **Non-vacuity of `IIcIsoCore`**: every hypothesis is instantiated by the regular octagon (`N = 8`, `M = 8`), and `iic_iso_core` returns its conclusion. -/
theorem iic_iso_core_octagon : Concl7 octDiss oct ∨ Concl5 octDiss oct :=
  iic_iso_core 8 8 octDiss oct rfl idx octDiss_caseC octDiss_comm octDiss_notComm octDiss_angle2_lt octDiss_angle2_ne octDiss_angle01
    (fun j => ⟨octDiss_cnt0 j, octDiss_cnt1 j, octDiss_cnt2 j⟩) (fun _ => mkPt 0 0) (fun j => gexc_at j)

end Erdos634.Draft.LaczFormal.IsoWit

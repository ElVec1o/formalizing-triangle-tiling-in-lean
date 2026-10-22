-- Draft/LaczFormalCondE4.lean -- Condition (E) applied at n = 60: the four exceptional primitive triples (1,10,49), (7,10,43), (10,13,37), (10,19,31)
-- (the n = 60 members of the census of triples with R(a) != R0(a)) admit no congruent dissection of a triangle with angle triple
-- (10,10,40), (10,20,30) or (20,20,20) (x pi/60).  The only other K1/K2-admissible target is the tile's own shape (similar case, `reptile_SWW`).
-- Farkas certificates Y as in `E_kill`; found by exact LP ((private working notes, not included)), checked by omega.  UNAUDITED.
-- Credit: Laczkovich (Condition (E), classification); Beeson-Rosu.
import Erdos634.Draft.LaczFormalCondE3

open scoped BigOperators Classical
open Erdos634.Geometry Erdos634.KConj Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional

namespace Erdos634.Draft.LaczFormal

variable {N : ℕ}

/-- No congruent dissection has tile angles `(1,10,49)π/60` and target angles `(10,10,40)π/60` (Condition (E), `Y = (1,10,-11)`). -/
theorem kill_60_1_10_49_t10_10_40 (D : CongruentDissection N)
    (hT : TileAngles D (1 * Real.pi / 60) (10 * Real.pi / 60) (49 * Real.pi / 60))
    (hG : TgtAngles D (10 * Real.pi / 60) (10 * Real.pi / 60) (40 * Real.pi / 60)) : False := by
  refine E_kill_tri D 60 (by norm_num) 1 10 49 10 10 40 (1) (10) (-11) (by exact_mod_cast hT) (by exact_mod_cast hG) ?_ (by norm_num) ?_
  · intro c0 c1 c2 h
    have hb : c2 ≤ 2 := by omega
    interval_cases c2 <;> omega
  · intro f00 f01 f02 f10 f11 f12 f20 f21 f22 e0 e1 e2
    have b0 : f02 ≤ 0 := by omega
    have b1 : f12 ≤ 0 := by omega
    have b2 : f22 ≤ 0 := by omega
    interval_cases f02 <;> interval_cases f12 <;> interval_cases f22 <;> omega

/-- No congruent dissection has tile angles `(1,10,49)π/60` and target angles `(10,20,30)π/60` (Condition (E), `Y = (1,10,-11)`). -/
theorem kill_60_1_10_49_t10_20_30 (D : CongruentDissection N)
    (hT : TileAngles D (1 * Real.pi / 60) (10 * Real.pi / 60) (49 * Real.pi / 60))
    (hG : TgtAngles D (10 * Real.pi / 60) (20 * Real.pi / 60) (30 * Real.pi / 60)) : False := by
  refine E_kill_tri D 60 (by norm_num) 1 10 49 10 20 30 (1) (10) (-11) (by exact_mod_cast hT) (by exact_mod_cast hG) ?_ (by norm_num) ?_
  · intro c0 c1 c2 h
    have hb : c2 ≤ 2 := by omega
    interval_cases c2 <;> omega
  · intro f00 f01 f02 f10 f11 f12 f20 f21 f22 e0 e1 e2
    have b0 : f02 ≤ 0 := by omega
    have b1 : f12 ≤ 0 := by omega
    have b2 : f22 ≤ 0 := by omega
    interval_cases f02 <;> interval_cases f12 <;> interval_cases f22 <;> omega

/-- No congruent dissection has tile angles `(1,10,49)π/60` and target angles `(20,20,20)π/60` (Condition (E), `Y = (1,10,-11)`). -/
theorem kill_60_1_10_49_t20_20_20 (D : CongruentDissection N)
    (hT : TileAngles D (1 * Real.pi / 60) (10 * Real.pi / 60) (49 * Real.pi / 60))
    (hG : TgtAngles D (20 * Real.pi / 60) (20 * Real.pi / 60) (20 * Real.pi / 60)) : False := by
  refine E_kill_tri D 60 (by norm_num) 1 10 49 20 20 20 (1) (10) (-11) (by exact_mod_cast hT) (by exact_mod_cast hG) ?_ (by norm_num) ?_
  · intro c0 c1 c2 h
    have hb : c2 ≤ 2 := by omega
    interval_cases c2 <;> omega
  · intro f00 f01 f02 f10 f11 f12 f20 f21 f22 e0 e1 e2
    have b0 : f02 ≤ 0 := by omega
    have b1 : f12 ≤ 0 := by omega
    have b2 : f22 ≤ 0 := by omega
    interval_cases f02 <;> interval_cases f12 <;> interval_cases f22 <;> omega

/-- No congruent dissection has tile angles `(7,10,43)π/60` and target angles `(10,10,40)π/60` (Condition (E), `Y = (1,10,-11)`). -/
theorem kill_60_7_10_43_t10_10_40 (D : CongruentDissection N)
    (hT : TileAngles D (7 * Real.pi / 60) (10 * Real.pi / 60) (43 * Real.pi / 60))
    (hG : TgtAngles D (10 * Real.pi / 60) (10 * Real.pi / 60) (40 * Real.pi / 60)) : False := by
  refine E_kill_tri D 60 (by norm_num) 7 10 43 10 10 40 (1) (10) (-11) (by exact_mod_cast hT) (by exact_mod_cast hG) ?_ (by norm_num) ?_
  · intro c0 c1 c2 h
    have hb : c2 ≤ 2 := by omega
    interval_cases c2 <;> omega
  · intro f00 f01 f02 f10 f11 f12 f20 f21 f22 e0 e1 e2
    have b0 : f02 ≤ 0 := by omega
    have b1 : f12 ≤ 0 := by omega
    have b2 : f22 ≤ 0 := by omega
    interval_cases f02 <;> interval_cases f12 <;> interval_cases f22 <;> omega

/-- No congruent dissection has tile angles `(7,10,43)π/60` and target angles `(10,20,30)π/60` (Condition (E), `Y = (1,10,-11)`). -/
theorem kill_60_7_10_43_t10_20_30 (D : CongruentDissection N)
    (hT : TileAngles D (7 * Real.pi / 60) (10 * Real.pi / 60) (43 * Real.pi / 60))
    (hG : TgtAngles D (10 * Real.pi / 60) (20 * Real.pi / 60) (30 * Real.pi / 60)) : False := by
  refine E_kill_tri D 60 (by norm_num) 7 10 43 10 20 30 (1) (10) (-11) (by exact_mod_cast hT) (by exact_mod_cast hG) ?_ (by norm_num) ?_
  · intro c0 c1 c2 h
    have hb : c2 ≤ 2 := by omega
    interval_cases c2 <;> omega
  · intro f00 f01 f02 f10 f11 f12 f20 f21 f22 e0 e1 e2
    have b0 : f02 ≤ 0 := by omega
    have b1 : f12 ≤ 0 := by omega
    have b2 : f22 ≤ 0 := by omega
    interval_cases f02 <;> interval_cases f12 <;> interval_cases f22 <;> omega

/-- No congruent dissection has tile angles `(7,10,43)π/60` and target angles `(20,20,20)π/60` (Condition (E), `Y = (1,10,-11)`). -/
theorem kill_60_7_10_43_t20_20_20 (D : CongruentDissection N)
    (hT : TileAngles D (7 * Real.pi / 60) (10 * Real.pi / 60) (43 * Real.pi / 60))
    (hG : TgtAngles D (20 * Real.pi / 60) (20 * Real.pi / 60) (20 * Real.pi / 60)) : False := by
  refine E_kill_tri D 60 (by norm_num) 7 10 43 20 20 20 (1) (10) (-11) (by exact_mod_cast hT) (by exact_mod_cast hG) ?_ (by norm_num) ?_
  · intro c0 c1 c2 h
    have hb : c2 ≤ 2 := by omega
    interval_cases c2 <;> omega
  · intro f00 f01 f02 f10 f11 f12 f20 f21 f22 e0 e1 e2
    have b0 : f02 ≤ 0 := by omega
    have b1 : f12 ≤ 0 := by omega
    have b2 : f22 ≤ 0 := by omega
    interval_cases f02 <;> interval_cases f12 <;> interval_cases f22 <;> omega

/-- No congruent dissection has tile angles `(10,13,37)π/60` and target angles `(10,10,40)π/60` (Condition (E), `Y = (1,-1,0)`). -/
theorem kill_60_10_13_37_t10_10_40 (D : CongruentDissection N)
    (hT : TileAngles D (10 * Real.pi / 60) (13 * Real.pi / 60) (37 * Real.pi / 60))
    (hG : TgtAngles D (10 * Real.pi / 60) (10 * Real.pi / 60) (40 * Real.pi / 60)) : False := by
  refine E_kill_tri D 60 (by norm_num) 10 13 37 10 10 40 (1) (-1) (0) (by exact_mod_cast hT) (by exact_mod_cast hG) ?_ (by norm_num) ?_
  · intro c0 c1 c2 h
    have hb : c2 ≤ 3 := by omega
    interval_cases c2 <;> omega
  · intro f00 f01 f02 f10 f11 f12 f20 f21 f22 e0 e1 e2
    have b0 : f02 ≤ 1 := by omega
    have b1 : f12 ≤ 1 := by omega
    have b2 : f22 ≤ 1 := by omega
    interval_cases f02 <;> interval_cases f12 <;> interval_cases f22 <;> omega

/-- No congruent dissection has tile angles `(10,13,37)π/60` and target angles `(10,20,30)π/60` (Condition (E), `Y = (1,-1,0)`). -/
theorem kill_60_10_13_37_t10_20_30 (D : CongruentDissection N)
    (hT : TileAngles D (10 * Real.pi / 60) (13 * Real.pi / 60) (37 * Real.pi / 60))
    (hG : TgtAngles D (10 * Real.pi / 60) (20 * Real.pi / 60) (30 * Real.pi / 60)) : False := by
  refine E_kill_tri D 60 (by norm_num) 10 13 37 10 20 30 (1) (-1) (0) (by exact_mod_cast hT) (by exact_mod_cast hG) ?_ (by norm_num) ?_
  · intro c0 c1 c2 h
    have hb : c2 ≤ 3 := by omega
    interval_cases c2 <;> omega
  · intro f00 f01 f02 f10 f11 f12 f20 f21 f22 e0 e1 e2
    have b0 : f02 ≤ 1 := by omega
    have b1 : f12 ≤ 1 := by omega
    have b2 : f22 ≤ 1 := by omega
    interval_cases f02 <;> interval_cases f12 <;> interval_cases f22 <;> omega

/-- No congruent dissection has tile angles `(10,13,37)π/60` and target angles `(20,20,20)π/60` (Condition (E), `Y = (1,-1,0)`). -/
theorem kill_60_10_13_37_t20_20_20 (D : CongruentDissection N)
    (hT : TileAngles D (10 * Real.pi / 60) (13 * Real.pi / 60) (37 * Real.pi / 60))
    (hG : TgtAngles D (20 * Real.pi / 60) (20 * Real.pi / 60) (20 * Real.pi / 60)) : False := by
  refine E_kill_tri D 60 (by norm_num) 10 13 37 20 20 20 (1) (-1) (0) (by exact_mod_cast hT) (by exact_mod_cast hG) ?_ (by norm_num) ?_
  · intro c0 c1 c2 h
    have hb : c2 ≤ 3 := by omega
    interval_cases c2 <;> omega
  · intro f00 f01 f02 f10 f11 f12 f20 f21 f22 e0 e1 e2
    have b0 : f02 ≤ 1 := by omega
    have b1 : f12 ≤ 1 := by omega
    have b2 : f22 ≤ 1 := by omega
    interval_cases f02 <;> interval_cases f12 <;> interval_cases f22 <;> omega

/-- No congruent dissection has tile angles `(10,19,31)π/60` and target angles `(10,10,40)π/60` (Condition (E), `Y = (1,-1,0)`). -/
theorem kill_60_10_19_31_t10_10_40 (D : CongruentDissection N)
    (hT : TileAngles D (10 * Real.pi / 60) (19 * Real.pi / 60) (31 * Real.pi / 60))
    (hG : TgtAngles D (10 * Real.pi / 60) (10 * Real.pi / 60) (40 * Real.pi / 60)) : False := by
  refine E_kill_tri D 60 (by norm_num) 10 19 31 10 10 40 (1) (-1) (0) (by exact_mod_cast hT) (by exact_mod_cast hG) ?_ (by norm_num) ?_
  · intro c0 c1 c2 h
    have hb : c2 ≤ 3 := by omega
    interval_cases c2 <;> omega
  · intro f00 f01 f02 f10 f11 f12 f20 f21 f22 e0 e1 e2
    have b0 : f02 ≤ 1 := by omega
    have b1 : f12 ≤ 1 := by omega
    have b2 : f22 ≤ 1 := by omega
    interval_cases f02 <;> interval_cases f12 <;> interval_cases f22 <;> omega

/-- No congruent dissection has tile angles `(10,19,31)π/60` and target angles `(10,20,30)π/60` (Condition (E), `Y = (1,-1,0)`). -/
theorem kill_60_10_19_31_t10_20_30 (D : CongruentDissection N)
    (hT : TileAngles D (10 * Real.pi / 60) (19 * Real.pi / 60) (31 * Real.pi / 60))
    (hG : TgtAngles D (10 * Real.pi / 60) (20 * Real.pi / 60) (30 * Real.pi / 60)) : False := by
  refine E_kill_tri D 60 (by norm_num) 10 19 31 10 20 30 (1) (-1) (0) (by exact_mod_cast hT) (by exact_mod_cast hG) ?_ (by norm_num) ?_
  · intro c0 c1 c2 h
    have hb : c2 ≤ 3 := by omega
    interval_cases c2 <;> omega
  · intro f00 f01 f02 f10 f11 f12 f20 f21 f22 e0 e1 e2
    have b0 : f02 ≤ 1 := by omega
    have b1 : f12 ≤ 1 := by omega
    have b2 : f22 ≤ 1 := by omega
    interval_cases f02 <;> interval_cases f12 <;> interval_cases f22 <;> omega

/-- No congruent dissection has tile angles `(10,19,31)π/60` and target angles `(20,20,20)π/60` (Condition (E), `Y = (1,-1,0)`). -/
theorem kill_60_10_19_31_t20_20_20 (D : CongruentDissection N)
    (hT : TileAngles D (10 * Real.pi / 60) (19 * Real.pi / 60) (31 * Real.pi / 60))
    (hG : TgtAngles D (20 * Real.pi / 60) (20 * Real.pi / 60) (20 * Real.pi / 60)) : False := by
  refine E_kill_tri D 60 (by norm_num) 10 19 31 20 20 20 (1) (-1) (0) (by exact_mod_cast hT) (by exact_mod_cast hG) ?_ (by norm_num) ?_
  · intro c0 c1 c2 h
    have hb : c2 ≤ 3 := by omega
    interval_cases c2 <;> omega
  · intro f00 f01 f02 f10 f11 f12 f20 f21 f22 e0 e1 e2
    have b0 : f02 ≤ 1 := by omega
    have b1 : f12 ≤ 1 := by omega
    have b2 : f22 ≤ 1 := by omega
    interval_cases f02 <;> interval_cases f12 <;> interval_cases f22 <;> omega

end Erdos634.Draft.LaczFormal

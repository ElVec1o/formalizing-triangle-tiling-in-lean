-- Draft/LaczFormalK1Kill2.lean -- K1-failing (tile, target) pairs at the exceptional n (instances of `K1_kill_tri`).  UNAUDITED.  Credit: Laczkovich (1995), Beeson-Rosu.
import Erdos634.Draft.LaczFormalK1Kill

open scoped BigOperators Classical
open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional

namespace Erdos634.Draft.LaczFormal

variable {N : ℕ}

/-- No congruent dissection has tile angles `(1,2,5)π/8` and target angles `(1,1,6)π/8`: K1 fails at `k = 3`
(`s_T = 2`, `s_ABC = 1`). -/
theorem k1kill_8_1_2_5_t1_1_6 (D : CongruentDissection N)
    (hT : TileAngles D (1 * Real.pi / 8) (2 * Real.pi / 8) (5 * Real.pi / 8))
    (hG : TgtAngles D (1 * Real.pi / 8) (1 * Real.pi / 8) (6 * Real.pi / 8)) : False := by
  have hT' : TileAngles D ((1 : ℕ) * Real.pi / (8 : ℕ)) ((2 : ℕ) * Real.pi / (8 : ℕ)) ((5 : ℕ) * Real.pi / (8 : ℕ)) := by
    simpa using hT
  have hG' : TgtAngles D ((1 : ℕ) * Real.pi / (8 : ℕ)) ((1 : ℕ) * Real.pi / (8 : ℕ)) ((6 : ℕ) * Real.pi / (8 : ℕ)) := by
    simpa using hG
  exact K1_kill_tri D 8 (by norm_num) 1 2 5 1 1 6 hT' hG' (k := 3) (by norm_num) (2/1) (1/1) (by norm_num)
    (by norm_num [Int.emod_emod_of_dvd]) (by norm_num [Int.emod_emod_of_dvd])

/-- No congruent dissection has tile angles `(1,2,5)π/8` and target angles `(1,3,4)π/8`: K1 fails at `k = 3`
(`s_T = 2`, `s_ABC = 1`). -/
theorem k1kill_8_1_2_5_t1_3_4 (D : CongruentDissection N)
    (hT : TileAngles D (1 * Real.pi / 8) (2 * Real.pi / 8) (5 * Real.pi / 8))
    (hG : TgtAngles D (1 * Real.pi / 8) (3 * Real.pi / 8) (4 * Real.pi / 8)) : False := by
  have hT' : TileAngles D ((1 : ℕ) * Real.pi / (8 : ℕ)) ((2 : ℕ) * Real.pi / (8 : ℕ)) ((5 : ℕ) * Real.pi / (8 : ℕ)) := by
    simpa using hT
  have hG' : TgtAngles D ((1 : ℕ) * Real.pi / (8 : ℕ)) ((3 : ℕ) * Real.pi / (8 : ℕ)) ((4 : ℕ) * Real.pi / (8 : ℕ)) := by
    simpa using hG
  exact K1_kill_tri D 8 (by norm_num) 1 2 5 1 3 4 hT' hG' (k := 3) (by norm_num) (2/1) (1/1) (by norm_num)
    (by norm_num [Int.emod_emod_of_dvd]) (by norm_num [Int.emod_emod_of_dvd])

/-- No congruent dissection has tile angles `(1,2,5)π/8` and target angles `(2,3,3)π/8`: K1 fails at `k = 3`
(`s_T = 2`, `s_ABC = 1`). -/
theorem k1kill_8_1_2_5_t2_3_3 (D : CongruentDissection N)
    (hT : TileAngles D (1 * Real.pi / 8) (2 * Real.pi / 8) (5 * Real.pi / 8))
    (hG : TgtAngles D (2 * Real.pi / 8) (3 * Real.pi / 8) (3 * Real.pi / 8)) : False := by
  have hT' : TileAngles D ((1 : ℕ) * Real.pi / (8 : ℕ)) ((2 : ℕ) * Real.pi / (8 : ℕ)) ((5 : ℕ) * Real.pi / (8 : ℕ)) := by
    simpa using hT
  have hG' : TgtAngles D ((2 : ℕ) * Real.pi / (8 : ℕ)) ((3 : ℕ) * Real.pi / (8 : ℕ)) ((3 : ℕ) * Real.pi / (8 : ℕ)) := by
    simpa using hG
  exact K1_kill_tri D 8 (by norm_num) 1 2 5 2 3 3 hT' hG' (k := 3) (by norm_num) (2/1) (1/1) (by norm_num)
    (by norm_num [Int.emod_emod_of_dvd]) (by norm_num [Int.emod_emod_of_dvd])

/-- No congruent dissection has tile angles `(1,2,9)π/12` and target angles `(1,1,10)π/12`: K1 fails at `k = 5`
(`s_T = 2`, `s_ABC = 1`). -/
theorem k1kill_12_1_2_9_t1_1_10 (D : CongruentDissection N)
    (hT : TileAngles D (1 * Real.pi / 12) (2 * Real.pi / 12) (9 * Real.pi / 12))
    (hG : TgtAngles D (1 * Real.pi / 12) (1 * Real.pi / 12) (10 * Real.pi / 12)) : False := by
  have hT' : TileAngles D ((1 : ℕ) * Real.pi / (12 : ℕ)) ((2 : ℕ) * Real.pi / (12 : ℕ)) ((9 : ℕ) * Real.pi / (12 : ℕ)) := by
    simpa using hT
  have hG' : TgtAngles D ((1 : ℕ) * Real.pi / (12 : ℕ)) ((1 : ℕ) * Real.pi / (12 : ℕ)) ((10 : ℕ) * Real.pi / (12 : ℕ)) := by
    simpa using hG
  exact K1_kill_tri D 12 (by norm_num) 1 2 9 1 1 10 hT' hG' (k := 5) (by norm_num) (2/1) (1/1) (by norm_num)
    (by norm_num [Int.emod_emod_of_dvd]) (by norm_num [Int.emod_emod_of_dvd])

/-- No congruent dissection has tile angles `(1,3,8)π/12` and target angles `(1,2,9)π/12`: K1 fails at `k = 5`
(`s_T = 1`, `s_ABC = 2`). -/
theorem k1kill_12_1_3_8_t1_2_9 (D : CongruentDissection N)
    (hT : TileAngles D (1 * Real.pi / 12) (3 * Real.pi / 12) (8 * Real.pi / 12))
    (hG : TgtAngles D (1 * Real.pi / 12) (2 * Real.pi / 12) (9 * Real.pi / 12)) : False := by
  have hT' : TileAngles D ((1 : ℕ) * Real.pi / (12 : ℕ)) ((3 : ℕ) * Real.pi / (12 : ℕ)) ((8 : ℕ) * Real.pi / (12 : ℕ)) := by
    simpa using hT
  have hG' : TgtAngles D ((1 : ℕ) * Real.pi / (12 : ℕ)) ((2 : ℕ) * Real.pi / (12 : ℕ)) ((9 : ℕ) * Real.pi / (12 : ℕ)) := by
    simpa using hG
  exact K1_kill_tri D 12 (by norm_num) 1 3 8 1 2 9 hT' hG' (k := 5) (by norm_num) (1/1) (2/1) (by norm_num)
    (by norm_num [Int.emod_emod_of_dvd]) (by norm_num [Int.emod_emod_of_dvd])

/-- No congruent dissection has tile angles `(1,3,8)π/12` and target angles `(1,4,7)π/12`: K1 fails at `k = 5`
(`s_T = 1`, `s_ABC = 2`). -/
theorem k1kill_12_1_3_8_t1_4_7 (D : CongruentDissection N)
    (hT : TileAngles D (1 * Real.pi / 12) (3 * Real.pi / 12) (8 * Real.pi / 12))
    (hG : TgtAngles D (1 * Real.pi / 12) (4 * Real.pi / 12) (7 * Real.pi / 12)) : False := by
  have hT' : TileAngles D ((1 : ℕ) * Real.pi / (12 : ℕ)) ((3 : ℕ) * Real.pi / (12 : ℕ)) ((8 : ℕ) * Real.pi / (12 : ℕ)) := by
    simpa using hT
  have hG' : TgtAngles D ((1 : ℕ) * Real.pi / (12 : ℕ)) ((4 : ℕ) * Real.pi / (12 : ℕ)) ((7 : ℕ) * Real.pi / (12 : ℕ)) := by
    simpa using hG
  exact K1_kill_tri D 12 (by norm_num) 1 3 8 1 4 7 hT' hG' (k := 5) (by norm_num) (1/1) (2/1) (by norm_num)
    (by norm_num [Int.emod_emod_of_dvd]) (by norm_num [Int.emod_emod_of_dvd])

/-- No congruent dissection has tile angles `(1,3,8)π/12` and target angles `(2,2,8)π/12`: K1 fails at `k = 5`
(`s_T = 1`, `s_ABC = 2`). -/
theorem k1kill_12_1_3_8_t2_2_8 (D : CongruentDissection N)
    (hT : TileAngles D (1 * Real.pi / 12) (3 * Real.pi / 12) (8 * Real.pi / 12))
    (hG : TgtAngles D (2 * Real.pi / 12) (2 * Real.pi / 12) (8 * Real.pi / 12)) : False := by
  have hT' : TileAngles D ((1 : ℕ) * Real.pi / (12 : ℕ)) ((3 : ℕ) * Real.pi / (12 : ℕ)) ((8 : ℕ) * Real.pi / (12 : ℕ)) := by
    simpa using hT
  have hG' : TgtAngles D ((2 : ℕ) * Real.pi / (12 : ℕ)) ((2 : ℕ) * Real.pi / (12 : ℕ)) ((8 : ℕ) * Real.pi / (12 : ℕ)) := by
    simpa using hG
  exact K1_kill_tri D 12 (by norm_num) 1 3 8 2 2 8 hT' hG' (k := 5) (by norm_num) (1/1) (2/1) (by norm_num)
    (by norm_num [Int.emod_emod_of_dvd]) (by norm_num [Int.emod_emod_of_dvd])

/-- No congruent dissection has tile angles `(1,3,8)π/12` and target angles `(2,3,7)π/12`: K1 fails at `k = 5`
(`s_T = 1`, `s_ABC = 2`). -/
theorem k1kill_12_1_3_8_t2_3_7 (D : CongruentDissection N)
    (hT : TileAngles D (1 * Real.pi / 12) (3 * Real.pi / 12) (8 * Real.pi / 12))
    (hG : TgtAngles D (2 * Real.pi / 12) (3 * Real.pi / 12) (7 * Real.pi / 12)) : False := by
  have hT' : TileAngles D ((1 : ℕ) * Real.pi / (12 : ℕ)) ((3 : ℕ) * Real.pi / (12 : ℕ)) ((8 : ℕ) * Real.pi / (12 : ℕ)) := by
    simpa using hT
  have hG' : TgtAngles D ((2 : ℕ) * Real.pi / (12 : ℕ)) ((3 : ℕ) * Real.pi / (12 : ℕ)) ((7 : ℕ) * Real.pi / (12 : ℕ)) := by
    simpa using hG
  exact K1_kill_tri D 12 (by norm_num) 1 3 8 2 3 7 hT' hG' (k := 5) (by norm_num) (1/1) (2/1) (by norm_num)
    (by norm_num [Int.emod_emod_of_dvd]) (by norm_num [Int.emod_emod_of_dvd])

/-- No congruent dissection has tile angles `(1,3,8)π/12` and target angles `(2,4,6)π/12`: K1 fails at `k = 5`
(`s_T = 1`, `s_ABC = 2`). -/
theorem k1kill_12_1_3_8_t2_4_6 (D : CongruentDissection N)
    (hT : TileAngles D (1 * Real.pi / 12) (3 * Real.pi / 12) (8 * Real.pi / 12))
    (hG : TgtAngles D (2 * Real.pi / 12) (4 * Real.pi / 12) (6 * Real.pi / 12)) : False := by
  have hT' : TileAngles D ((1 : ℕ) * Real.pi / (12 : ℕ)) ((3 : ℕ) * Real.pi / (12 : ℕ)) ((8 : ℕ) * Real.pi / (12 : ℕ)) := by
    simpa using hT
  have hG' : TgtAngles D ((2 : ℕ) * Real.pi / (12 : ℕ)) ((4 : ℕ) * Real.pi / (12 : ℕ)) ((6 : ℕ) * Real.pi / (12 : ℕ)) := by
    simpa using hG
  exact K1_kill_tri D 12 (by norm_num) 1 3 8 2 4 6 hT' hG' (k := 5) (by norm_num) (1/1) (2/1) (by norm_num)
    (by norm_num [Int.emod_emod_of_dvd]) (by norm_num [Int.emod_emod_of_dvd])

/-- No congruent dissection has tile angles `(1,3,8)π/12` and target angles `(4,4,4)π/12`: K1 fails at `k = 5`
(`s_T = 1`, `s_ABC = 2`). -/
theorem k1kill_12_1_3_8_t4_4_4 (D : CongruentDissection N)
    (hT : TileAngles D (1 * Real.pi / 12) (3 * Real.pi / 12) (8 * Real.pi / 12))
    (hG : TgtAngles D (4 * Real.pi / 12) (4 * Real.pi / 12) (4 * Real.pi / 12)) : False := by
  have hT' : TileAngles D ((1 : ℕ) * Real.pi / (12 : ℕ)) ((3 : ℕ) * Real.pi / (12 : ℕ)) ((8 : ℕ) * Real.pi / (12 : ℕ)) := by
    simpa using hT
  have hG' : TgtAngles D ((4 : ℕ) * Real.pi / (12 : ℕ)) ((4 : ℕ) * Real.pi / (12 : ℕ)) ((4 : ℕ) * Real.pi / (12 : ℕ)) := by
    simpa using hG
  exact K1_kill_tri D 12 (by norm_num) 1 3 8 4 4 4 hT' hG' (k := 5) (by norm_num) (1/1) (2/1) (by norm_num)
    (by norm_num [Int.emod_emod_of_dvd]) (by norm_num [Int.emod_emod_of_dvd])

/-- No congruent dissection has tile angles `(2,3,7)π/12` and target angles `(2,5,5)π/12`: K1 fails at `k = 5`
(`s_T = 2`, `s_ABC = 1`). -/
theorem k1kill_12_2_3_7_t2_5_5 (D : CongruentDissection N)
    (hT : TileAngles D (2 * Real.pi / 12) (3 * Real.pi / 12) (7 * Real.pi / 12))
    (hG : TgtAngles D (2 * Real.pi / 12) (5 * Real.pi / 12) (5 * Real.pi / 12)) : False := by
  have hT' : TileAngles D ((2 : ℕ) * Real.pi / (12 : ℕ)) ((3 : ℕ) * Real.pi / (12 : ℕ)) ((7 : ℕ) * Real.pi / (12 : ℕ)) := by
    simpa using hT
  have hG' : TgtAngles D ((2 : ℕ) * Real.pi / (12 : ℕ)) ((5 : ℕ) * Real.pi / (12 : ℕ)) ((5 : ℕ) * Real.pi / (12 : ℕ)) := by
    simpa using hG
  exact K1_kill_tri D 12 (by norm_num) 2 3 7 2 5 5 hT' hG' (k := 5) (by norm_num) (2/1) (1/1) (by norm_num)
    (by norm_num [Int.emod_emod_of_dvd]) (by norm_num [Int.emod_emod_of_dvd])

/-- No congruent dissection has tile angles `(2,3,7)π/12` and target angles `(3,3,6)π/12`: K1 fails at `k = 5`
(`s_T = 2`, `s_ABC = 1`). -/
theorem k1kill_12_2_3_7_t3_3_6 (D : CongruentDissection N)
    (hT : TileAngles D (2 * Real.pi / 12) (3 * Real.pi / 12) (7 * Real.pi / 12))
    (hG : TgtAngles D (3 * Real.pi / 12) (3 * Real.pi / 12) (6 * Real.pi / 12)) : False := by
  have hT' : TileAngles D ((2 : ℕ) * Real.pi / (12 : ℕ)) ((3 : ℕ) * Real.pi / (12 : ℕ)) ((7 : ℕ) * Real.pi / (12 : ℕ)) := by
    simpa using hT
  have hG' : TgtAngles D ((3 : ℕ) * Real.pi / (12 : ℕ)) ((3 : ℕ) * Real.pi / (12 : ℕ)) ((6 : ℕ) * Real.pi / (12 : ℕ)) := by
    simpa using hG
  exact K1_kill_tri D 12 (by norm_num) 2 3 7 3 3 6 hT' hG' (k := 5) (by norm_num) (2/1) (1/1) (by norm_num)
    (by norm_num [Int.emod_emod_of_dvd]) (by norm_num [Int.emod_emod_of_dvd])

/-- No congruent dissection has tile angles `(2,3,7)π/12` and target angles `(3,4,5)π/12`: K1 fails at `k = 5`
(`s_T = 2`, `s_ABC = 1`). -/
theorem k1kill_12_2_3_7_t3_4_5 (D : CongruentDissection N)
    (hT : TileAngles D (2 * Real.pi / 12) (3 * Real.pi / 12) (7 * Real.pi / 12))
    (hG : TgtAngles D (3 * Real.pi / 12) (4 * Real.pi / 12) (5 * Real.pi / 12)) : False := by
  have hT' : TileAngles D ((2 : ℕ) * Real.pi / (12 : ℕ)) ((3 : ℕ) * Real.pi / (12 : ℕ)) ((7 : ℕ) * Real.pi / (12 : ℕ)) := by
    simpa using hT
  have hG' : TgtAngles D ((3 : ℕ) * Real.pi / (12 : ℕ)) ((4 : ℕ) * Real.pi / (12 : ℕ)) ((5 : ℕ) * Real.pi / (12 : ℕ)) := by
    simpa using hG
  exact K1_kill_tri D 12 (by norm_num) 2 3 7 3 4 5 hT' hG' (k := 5) (by norm_num) (2/1) (1/1) (by norm_num)
    (by norm_num [Int.emod_emod_of_dvd]) (by norm_num [Int.emod_emod_of_dvd])

/-- No congruent dissection has tile angles `(3,4,5)π/12` and target angles `(4,4,4)π/12`: K1 fails at `k = 5`
(`s_T = 1`, `s_ABC = 2`). -/
theorem k1kill_12_3_4_5_t4_4_4 (D : CongruentDissection N)
    (hT : TileAngles D (3 * Real.pi / 12) (4 * Real.pi / 12) (5 * Real.pi / 12))
    (hG : TgtAngles D (4 * Real.pi / 12) (4 * Real.pi / 12) (4 * Real.pi / 12)) : False := by
  have hT' : TileAngles D ((3 : ℕ) * Real.pi / (12 : ℕ)) ((4 : ℕ) * Real.pi / (12 : ℕ)) ((5 : ℕ) * Real.pi / (12 : ℕ)) := by
    simpa using hT
  have hG' : TgtAngles D ((4 : ℕ) * Real.pi / (12 : ℕ)) ((4 : ℕ) * Real.pi / (12 : ℕ)) ((4 : ℕ) * Real.pi / (12 : ℕ)) := by
    simpa using hG
  exact K1_kill_tri D 12 (by norm_num) 3 4 5 4 4 4 hT' hG' (k := 5) (by norm_num) (1/1) (2/1) (by norm_num)
    (by norm_num [Int.emod_emod_of_dvd]) (by norm_num [Int.emod_emod_of_dvd])

end Erdos634.Draft.LaczFormal

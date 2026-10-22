-- Draft/LaczFormalCondE3.lean -- Condition (E) of Laczkovich (arXiv 2002.12013, Sect. 1.3) applied: the surviving non-similar triples of the
-- classification at n = 12, 18, 24, 30 (tile angles a_i pi/n, target angles u_j pi/n) admit NO congruent dissection.  Each theorem is stand-alone;
-- the certificate is the integer Farkas vector Y of `E_kill`, checked by omega.  UNAUDITED.  Credit: Laczkovich (Condition (E), classification);
-- Beeson-Rosu / Beeson (the tile lists); the Farkas certificates are ours.
import Erdos634.Draft.LaczFormalCondE2
import Erdos634.Draft.LaczFormalBase
import Erdos634.Draft.TheoremPConditional

open scoped BigOperators Classical
open Erdos634.Geometry Erdos634.KConj Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional

namespace Erdos634.Draft.LaczFormal

variable {N : ℕ}

/-- `E_kill` in the `TileAngles`/`TgtAngles` format, with all data as explicit scalars. -/
theorem E_kill_tri (D : CongruentDissection N) (n : ℕ) (hn : 0 < n) (a0 a1 a2 u0 u1 u2 : ℕ) (Y0 Y1 Y2 : ℤ)
    (hT : TileAngles D (a0 * Real.pi / n) (a1 * Real.pi / n) (a2 * Real.pi / n))
    (hG : TgtAngles D (u0 * Real.pi / n) (u1 * Real.pi / n) (u2 * Real.pi / n))
    (cert1 : ∀ c0 c1 c2 : ℕ, (a0 * c0 + a1 * c1 + a2 * c2 = n ∨ a0 * c0 + a1 * c1 + a2 * c2 = 2 * n) →
      0 ≤ Y0 * c0 + Y1 * c1 + Y2 * c2)
    (cert2 : Y0 + Y1 + Y2 ≤ 0)
    (cert3 : ∀ f00 f01 f02 f10 f11 f12 f20 f21 f22 : ℕ,
      a0 * f00 + a1 * f01 + a2 * f02 = u0 → a0 * f10 + a1 * f11 + a2 * f12 = u1 →
      a0 * f20 + a1 * f21 + a2 * f22 = u2 →
      0 < Y0 * (f00 + f10 + f20) + Y1 * (f01 + f11 + f21) + Y2 * (f02 + f12 + f22)) : False := by
  obtain ⟨σ, h0, h1, h2⟩ := hT
  obtain ⟨τ, g0, g1, g2⟩ := hG
  let a : Fin 3 → ℕ := fun i => match i with | 0 => a0 | 1 => a1 | 2 => a2
  let u : Fin 3 → ℕ := fun i => match i with | 0 => u0 | 1 => u1 | 2 => u2
  let Y : Fin 3 → ℤ := fun i => match i with | 0 => Y0 | 1 => Y1 | 2 => Y2
  refine E_kill D n hn a u Y σ τ ?_ ?_ ?_ ?_ ?_
  · intro i; fin_cases i <;> simp [a, h0, h1, h2]
  · intro j; fin_cases j <;> simp [u, g0, g1, g2]
  · intro c h
    have := cert1 (c 0) (c 1) (c 2)
    simp only [Fin.sum_univ_three, a, Y] at h ⊢
    push_cast
    exact this h
  · simpa [Fin.sum_univ_three, Y] using cert2
  · intro f hf
    have := cert3 (f 0 0) (f 0 1) (f 0 2) (f 1 0) (f 1 1) (f 1 2) (f 2 0) (f 2 1) (f 2 2)
      (by simpa [Fin.sum_univ_three, a, u] using hf 0) (by simpa [Fin.sum_univ_three, a, u] using hf 1)
      (by simpa [Fin.sum_univ_three, a, u] using hf 2)
    simp only [Fin.sum_univ_three, Y]
    push_cast
    linarith

/-- No congruent dissection has tile angles `(1,2,9)π/12` and target angles `(2,2,8)π/12` (Condition (E), `Y = (1,2,-3)`). -/
theorem kill_12_1_2_9_t2_2_8 (D : CongruentDissection N)
    (hT : TileAngles D (1 * Real.pi / 12) (2 * Real.pi / 12) (9 * Real.pi / 12))
    (hG : TgtAngles D (2 * Real.pi / 12) (2 * Real.pi / 12) (8 * Real.pi / 12)) : False := by
  refine E_kill_tri D 12 (by norm_num) 1 2 9 2 2 8 (1) (2) (-3) (by exact_mod_cast hT) (by exact_mod_cast hG) ?_ (by norm_num) ?_
  · intro c0 c1 c2 h
    omega
  · intro f00 f01 f02 f10 f11 f12 f20 f21 f22 e0 e1 e2
    omega

/-- No congruent dissection has tile angles `(1,2,9)π/12` and target angles `(2,4,6)π/12` (Condition (E), `Y = (1,2,-3)`). -/
theorem kill_12_1_2_9_t2_4_6 (D : CongruentDissection N)
    (hT : TileAngles D (1 * Real.pi / 12) (2 * Real.pi / 12) (9 * Real.pi / 12))
    (hG : TgtAngles D (2 * Real.pi / 12) (4 * Real.pi / 12) (6 * Real.pi / 12)) : False := by
  refine E_kill_tri D 12 (by norm_num) 1 2 9 2 4 6 (1) (2) (-3) (by exact_mod_cast hT) (by exact_mod_cast hG) ?_ (by norm_num) ?_
  · intro c0 c1 c2 h
    omega
  · intro f00 f01 f02 f10 f11 f12 f20 f21 f22 e0 e1 e2
    omega

/-- No congruent dissection has tile angles `(1,2,9)π/12` and target angles `(4,4,4)π/12` (Condition (E), `Y = (1,2,-3)`). -/
theorem kill_12_1_2_9_t4_4_4 (D : CongruentDissection N)
    (hT : TileAngles D (1 * Real.pi / 12) (2 * Real.pi / 12) (9 * Real.pi / 12))
    (hG : TgtAngles D (4 * Real.pi / 12) (4 * Real.pi / 12) (4 * Real.pi / 12)) : False := by
  refine E_kill_tri D 12 (by norm_num) 1 2 9 4 4 4 (1) (2) (-3) (by exact_mod_cast hT) (by exact_mod_cast hG) ?_ (by norm_num) ?_
  · intro c0 c1 c2 h
    omega
  · intro f00 f01 f02 f10 f11 f12 f20 f21 f22 e0 e1 e2
    omega

/-- No congruent dissection has tile angles `(1,3,14)π/18` and target angles `(3,3,12)π/18` (Condition (E), `Y = (1,3,-4)`). -/
theorem kill_18_1_3_14_t3_3_12 (D : CongruentDissection N)
    (hT : TileAngles D (1 * Real.pi / 18) (3 * Real.pi / 18) (14 * Real.pi / 18))
    (hG : TgtAngles D (3 * Real.pi / 18) (3 * Real.pi / 18) (12 * Real.pi / 18)) : False := by
  refine E_kill_tri D 18 (by norm_num) 1 3 14 3 3 12 (1) (3) (-4) (by exact_mod_cast hT) (by exact_mod_cast hG) ?_ (by norm_num) ?_
  · intro c0 c1 c2 h
    omega
  · intro f00 f01 f02 f10 f11 f12 f20 f21 f22 e0 e1 e2
    omega

/-- No congruent dissection has tile angles `(1,3,14)π/18` and target angles `(3,6,9)π/18` (Condition (E), `Y = (1,3,-4)`). -/
theorem kill_18_1_3_14_t3_6_9 (D : CongruentDissection N)
    (hT : TileAngles D (1 * Real.pi / 18) (3 * Real.pi / 18) (14 * Real.pi / 18))
    (hG : TgtAngles D (3 * Real.pi / 18) (6 * Real.pi / 18) (9 * Real.pi / 18)) : False := by
  refine E_kill_tri D 18 (by norm_num) 1 3 14 3 6 9 (1) (3) (-4) (by exact_mod_cast hT) (by exact_mod_cast hG) ?_ (by norm_num) ?_
  · intro c0 c1 c2 h
    omega
  · intro f00 f01 f02 f10 f11 f12 f20 f21 f22 e0 e1 e2
    omega

/-- No congruent dissection has tile angles `(1,3,14)π/18` and target angles `(6,6,6)π/18` (Condition (E), `Y = (1,3,-4)`). -/
theorem kill_18_1_3_14_t6_6_6 (D : CongruentDissection N)
    (hT : TileAngles D (1 * Real.pi / 18) (3 * Real.pi / 18) (14 * Real.pi / 18))
    (hG : TgtAngles D (6 * Real.pi / 18) (6 * Real.pi / 18) (6 * Real.pi / 18)) : False := by
  refine E_kill_tri D 18 (by norm_num) 1 3 14 6 6 6 (1) (3) (-4) (by exact_mod_cast hT) (by exact_mod_cast hG) ?_ (by norm_num) ?_
  · intro c0 c1 c2 h
    omega
  · intro f00 f01 f02 f10 f11 f12 f20 f21 f22 e0 e1 e2
    omega

/-- No congruent dissection has tile angles `(2,3,13)π/18` and target angles `(3,3,12)π/18` (Condition (E), `Y = (2,3,-5)`). -/
theorem kill_18_2_3_13_t3_3_12 (D : CongruentDissection N)
    (hT : TileAngles D (2 * Real.pi / 18) (3 * Real.pi / 18) (13 * Real.pi / 18))
    (hG : TgtAngles D (3 * Real.pi / 18) (3 * Real.pi / 18) (12 * Real.pi / 18)) : False := by
  refine E_kill_tri D 18 (by norm_num) 2 3 13 3 3 12 (2) (3) (-5) (by exact_mod_cast hT) (by exact_mod_cast hG) ?_ (by norm_num) ?_
  · intro c0 c1 c2 h
    omega
  · intro f00 f01 f02 f10 f11 f12 f20 f21 f22 e0 e1 e2
    omega

/-- No congruent dissection has tile angles `(2,3,13)π/18` and target angles `(3,6,9)π/18` (Condition (E), `Y = (2,3,-5)`). -/
theorem kill_18_2_3_13_t3_6_9 (D : CongruentDissection N)
    (hT : TileAngles D (2 * Real.pi / 18) (3 * Real.pi / 18) (13 * Real.pi / 18))
    (hG : TgtAngles D (3 * Real.pi / 18) (6 * Real.pi / 18) (9 * Real.pi / 18)) : False := by
  refine E_kill_tri D 18 (by norm_num) 2 3 13 3 6 9 (2) (3) (-5) (by exact_mod_cast hT) (by exact_mod_cast hG) ?_ (by norm_num) ?_
  · intro c0 c1 c2 h
    omega
  · intro f00 f01 f02 f10 f11 f12 f20 f21 f22 e0 e1 e2
    omega

/-- No congruent dissection has tile angles `(2,3,13)π/18` and target angles `(6,6,6)π/18` (Condition (E), `Y = (2,3,-5)`). -/
theorem kill_18_2_3_13_t6_6_6 (D : CongruentDissection N)
    (hT : TileAngles D (2 * Real.pi / 18) (3 * Real.pi / 18) (13 * Real.pi / 18))
    (hG : TgtAngles D (6 * Real.pi / 18) (6 * Real.pi / 18) (6 * Real.pi / 18)) : False := by
  refine E_kill_tri D 18 (by norm_num) 2 3 13 6 6 6 (2) (3) (-5) (by exact_mod_cast hT) (by exact_mod_cast hG) ?_ (by norm_num) ?_
  · intro c0 c1 c2 h
    omega
  · intro f00 f01 f02 f10 f11 f12 f20 f21 f22 e0 e1 e2
    omega

/-- No congruent dissection has tile angles `(3,7,8)π/18` and target angles `(3,3,12)π/18` (Condition (E), `Y = (3,1,-4)`). -/
theorem kill_18_3_7_8_t3_3_12 (D : CongruentDissection N)
    (hT : TileAngles D (3 * Real.pi / 18) (7 * Real.pi / 18) (8 * Real.pi / 18))
    (hG : TgtAngles D (3 * Real.pi / 18) (3 * Real.pi / 18) (12 * Real.pi / 18)) : False := by
  refine E_kill_tri D 18 (by norm_num) 3 7 8 3 3 12 (3) (1) (-4) (by exact_mod_cast hT) (by exact_mod_cast hG) ?_ (by norm_num) ?_
  · intro c0 c1 c2 h
    have hb : c2 ≤ 4 := by omega
    interval_cases c2 <;> omega
  · intro f00 f01 f02 f10 f11 f12 f20 f21 f22 e0 e1 e2
    have b0 : f02 ≤ 1 := by omega
    have b1 : f12 ≤ 1 := by omega
    have b2 : f22 ≤ 1 := by omega
    interval_cases f02 <;> interval_cases f12 <;> interval_cases f22 <;> omega

/-- No congruent dissection has tile angles `(3,7,8)π/18` and target angles `(3,6,9)π/18` (Condition (E), `Y = (3,1,-4)`). -/
theorem kill_18_3_7_8_t3_6_9 (D : CongruentDissection N)
    (hT : TileAngles D (3 * Real.pi / 18) (7 * Real.pi / 18) (8 * Real.pi / 18))
    (hG : TgtAngles D (3 * Real.pi / 18) (6 * Real.pi / 18) (9 * Real.pi / 18)) : False := by
  refine E_kill_tri D 18 (by norm_num) 3 7 8 3 6 9 (3) (1) (-4) (by exact_mod_cast hT) (by exact_mod_cast hG) ?_ (by norm_num) ?_
  · intro c0 c1 c2 h
    have hb : c2 ≤ 4 := by omega
    interval_cases c2 <;> omega
  · intro f00 f01 f02 f10 f11 f12 f20 f21 f22 e0 e1 e2
    have b0 : f02 ≤ 1 := by omega
    have b1 : f12 ≤ 1 := by omega
    have b2 : f22 ≤ 1 := by omega
    interval_cases f02 <;> interval_cases f12 <;> interval_cases f22 <;> omega

/-- No congruent dissection has tile angles `(3,7,8)π/18` and target angles `(6,6,6)π/18` (Condition (E), `Y = (3,1,-4)`). -/
theorem kill_18_3_7_8_t6_6_6 (D : CongruentDissection N)
    (hT : TileAngles D (3 * Real.pi / 18) (7 * Real.pi / 18) (8 * Real.pi / 18))
    (hG : TgtAngles D (6 * Real.pi / 18) (6 * Real.pi / 18) (6 * Real.pi / 18)) : False := by
  refine E_kill_tri D 18 (by norm_num) 3 7 8 6 6 6 (3) (1) (-4) (by exact_mod_cast hT) (by exact_mod_cast hG) ?_ (by norm_num) ?_
  · intro c0 c1 c2 h
    have hb : c2 ≤ 4 := by omega
    interval_cases c2 <;> omega
  · intro f00 f01 f02 f10 f11 f12 f20 f21 f22 e0 e1 e2
    have b0 : f02 ≤ 1 := by omega
    have b1 : f12 ≤ 1 := by omega
    have b2 : f22 ≤ 1 := by omega
    interval_cases f02 <;> interval_cases f12 <;> interval_cases f22 <;> omega

/-- No congruent dissection has tile angles `(1,4,19)π/24` and target angles `(4,4,16)π/24` (Condition (E), `Y = (1,4,-5)`). -/
theorem kill_24_1_4_19_t4_4_16 (D : CongruentDissection N)
    (hT : TileAngles D (1 * Real.pi / 24) (4 * Real.pi / 24) (19 * Real.pi / 24))
    (hG : TgtAngles D (4 * Real.pi / 24) (4 * Real.pi / 24) (16 * Real.pi / 24)) : False := by
  refine E_kill_tri D 24 (by norm_num) 1 4 19 4 4 16 (1) (4) (-5) (by exact_mod_cast hT) (by exact_mod_cast hG) ?_ (by norm_num) ?_
  · intro c0 c1 c2 h
    omega
  · intro f00 f01 f02 f10 f11 f12 f20 f21 f22 e0 e1 e2
    omega

/-- No congruent dissection has tile angles `(1,4,19)π/24` and target angles `(4,8,12)π/24` (Condition (E), `Y = (1,4,-5)`). -/
theorem kill_24_1_4_19_t4_8_12 (D : CongruentDissection N)
    (hT : TileAngles D (1 * Real.pi / 24) (4 * Real.pi / 24) (19 * Real.pi / 24))
    (hG : TgtAngles D (4 * Real.pi / 24) (8 * Real.pi / 24) (12 * Real.pi / 24)) : False := by
  refine E_kill_tri D 24 (by norm_num) 1 4 19 4 8 12 (1) (4) (-5) (by exact_mod_cast hT) (by exact_mod_cast hG) ?_ (by norm_num) ?_
  · intro c0 c1 c2 h
    omega
  · intro f00 f01 f02 f10 f11 f12 f20 f21 f22 e0 e1 e2
    omega

/-- No congruent dissection has tile angles `(1,4,19)π/24` and target angles `(8,8,8)π/24` (Condition (E), `Y = (1,4,-5)`). -/
theorem kill_24_1_4_19_t8_8_8 (D : CongruentDissection N)
    (hT : TileAngles D (1 * Real.pi / 24) (4 * Real.pi / 24) (19 * Real.pi / 24))
    (hG : TgtAngles D (8 * Real.pi / 24) (8 * Real.pi / 24) (8 * Real.pi / 24)) : False := by
  refine E_kill_tri D 24 (by norm_num) 1 4 19 8 8 8 (1) (4) (-5) (by exact_mod_cast hT) (by exact_mod_cast hG) ?_ (by norm_num) ?_
  · intro c0 c1 c2 h
    omega
  · intro f00 f01 f02 f10 f11 f12 f20 f21 f22 e0 e1 e2
    omega

/-- No congruent dissection has tile angles `(1,6,17)π/24` and target angles `(6,6,12)π/24` (Condition (E), `Y = (1,6,-7)`). -/
theorem kill_24_1_6_17_t6_6_12 (D : CongruentDissection N)
    (hT : TileAngles D (1 * Real.pi / 24) (6 * Real.pi / 24) (17 * Real.pi / 24))
    (hG : TgtAngles D (6 * Real.pi / 24) (6 * Real.pi / 24) (12 * Real.pi / 24)) : False := by
  refine E_kill_tri D 24 (by norm_num) 1 6 17 6 6 12 (1) (6) (-7) (by exact_mod_cast hT) (by exact_mod_cast hG) ?_ (by norm_num) ?_
  · intro c0 c1 c2 h
    omega
  · intro f00 f01 f02 f10 f11 f12 f20 f21 f22 e0 e1 e2
    omega

/-- No congruent dissection has tile angles `(4,7,13)π/24` and target angles `(4,4,16)π/24` (Condition (E), `Y = (4,1,-5)`). -/
theorem kill_24_4_7_13_t4_4_16 (D : CongruentDissection N)
    (hT : TileAngles D (4 * Real.pi / 24) (7 * Real.pi / 24) (13 * Real.pi / 24))
    (hG : TgtAngles D (4 * Real.pi / 24) (4 * Real.pi / 24) (16 * Real.pi / 24)) : False := by
  refine E_kill_tri D 24 (by norm_num) 4 7 13 4 4 16 (4) (1) (-5) (by exact_mod_cast hT) (by exact_mod_cast hG) ?_ (by norm_num) ?_
  · intro c0 c1 c2 h
    omega
  · intro f00 f01 f02 f10 f11 f12 f20 f21 f22 e0 e1 e2
    omega

/-- No congruent dissection has tile angles `(4,7,13)π/24` and target angles `(4,8,12)π/24` (Condition (E), `Y = (4,1,-5)`). -/
theorem kill_24_4_7_13_t4_8_12 (D : CongruentDissection N)
    (hT : TileAngles D (4 * Real.pi / 24) (7 * Real.pi / 24) (13 * Real.pi / 24))
    (hG : TgtAngles D (4 * Real.pi / 24) (8 * Real.pi / 24) (12 * Real.pi / 24)) : False := by
  refine E_kill_tri D 24 (by norm_num) 4 7 13 4 8 12 (4) (1) (-5) (by exact_mod_cast hT) (by exact_mod_cast hG) ?_ (by norm_num) ?_
  · intro c0 c1 c2 h
    omega
  · intro f00 f01 f02 f10 f11 f12 f20 f21 f22 e0 e1 e2
    omega

/-- No congruent dissection has tile angles `(4,7,13)π/24` and target angles `(8,8,8)π/24` (Condition (E), `Y = (4,1,-5)`). -/
theorem kill_24_4_7_13_t8_8_8 (D : CongruentDissection N)
    (hT : TileAngles D (4 * Real.pi / 24) (7 * Real.pi / 24) (13 * Real.pi / 24))
    (hG : TgtAngles D (8 * Real.pi / 24) (8 * Real.pi / 24) (8 * Real.pi / 24)) : False := by
  refine E_kill_tri D 24 (by norm_num) 4 7 13 8 8 8 (4) (1) (-5) (by exact_mod_cast hT) (by exact_mod_cast hG) ?_ (by norm_num) ?_
  · intro c0 c1 c2 h
    omega
  · intro f00 f01 f02 f10 f11 f12 f20 f21 f22 e0 e1 e2
    omega

/-- No congruent dissection has tile angles `(5,6,13)π/24` and target angles `(6,6,12)π/24` (Condition (E), `Y = (1,6,-7)`). -/
theorem kill_24_5_6_13_t6_6_12 (D : CongruentDissection N)
    (hT : TileAngles D (5 * Real.pi / 24) (6 * Real.pi / 24) (13 * Real.pi / 24))
    (hG : TgtAngles D (6 * Real.pi / 24) (6 * Real.pi / 24) (12 * Real.pi / 24)) : False := by
  refine E_kill_tri D 24 (by norm_num) 5 6 13 6 6 12 (1) (6) (-7) (by exact_mod_cast hT) (by exact_mod_cast hG) ?_ (by norm_num) ?_
  · intro c0 c1 c2 h
    omega
  · intro f00 f01 f02 f10 f11 f12 f20 f21 f22 e0 e1 e2
    omega

/-- No congruent dissection has tile angles `(1,5,24)π/30` and target angles `(5,5,20)π/30` (Condition (E), `Y = (1,5,-6)`). -/
theorem kill_30_1_5_24_t5_5_20 (D : CongruentDissection N)
    (hT : TileAngles D (1 * Real.pi / 30) (5 * Real.pi / 30) (24 * Real.pi / 30))
    (hG : TgtAngles D (5 * Real.pi / 30) (5 * Real.pi / 30) (20 * Real.pi / 30)) : False := by
  refine E_kill_tri D 30 (by norm_num) 1 5 24 5 5 20 (1) (5) (-6) (by exact_mod_cast hT) (by exact_mod_cast hG) ?_ (by norm_num) ?_
  · intro c0 c1 c2 h
    omega
  · intro f00 f01 f02 f10 f11 f12 f20 f21 f22 e0 e1 e2
    omega

/-- No congruent dissection has tile angles `(1,5,24)π/30` and target angles `(5,10,15)π/30` (Condition (E), `Y = (1,5,-6)`). -/
theorem kill_30_1_5_24_t5_10_15 (D : CongruentDissection N)
    (hT : TileAngles D (1 * Real.pi / 30) (5 * Real.pi / 30) (24 * Real.pi / 30))
    (hG : TgtAngles D (5 * Real.pi / 30) (10 * Real.pi / 30) (15 * Real.pi / 30)) : False := by
  refine E_kill_tri D 30 (by norm_num) 1 5 24 5 10 15 (1) (5) (-6) (by exact_mod_cast hT) (by exact_mod_cast hG) ?_ (by norm_num) ?_
  · intro c0 c1 c2 h
    omega
  · intro f00 f01 f02 f10 f11 f12 f20 f21 f22 e0 e1 e2
    omega

/-- No congruent dissection has tile angles `(1,5,24)π/30` and target angles `(10,10,10)π/30` (Condition (E), `Y = (1,5,-6)`). -/
theorem kill_30_1_5_24_t10_10_10 (D : CongruentDissection N)
    (hT : TileAngles D (1 * Real.pi / 30) (5 * Real.pi / 30) (24 * Real.pi / 30))
    (hG : TgtAngles D (10 * Real.pi / 30) (10 * Real.pi / 30) (10 * Real.pi / 30)) : False := by
  refine E_kill_tri D 30 (by norm_num) 1 5 24 10 10 10 (1) (5) (-6) (by exact_mod_cast hT) (by exact_mod_cast hG) ?_ (by norm_num) ?_
  · intro c0 c1 c2 h
    omega
  · intro f00 f01 f02 f10 f11 f12 f20 f21 f22 e0 e1 e2
    omega

/-- No congruent dissection has tile angles `(5,6,19)π/30` and target angles `(5,5,20)π/30` (Condition (E), `Y = (1,0,-1)`). -/
theorem kill_30_5_6_19_t5_5_20 (D : CongruentDissection N)
    (hT : TileAngles D (5 * Real.pi / 30) (6 * Real.pi / 30) (19 * Real.pi / 30))
    (hG : TgtAngles D (5 * Real.pi / 30) (5 * Real.pi / 30) (20 * Real.pi / 30)) : False := by
  refine E_kill_tri D 30 (by norm_num) 5 6 19 5 5 20 (1) (0) (-1) (by exact_mod_cast hT) (by exact_mod_cast hG) ?_ (by norm_num) ?_
  · intro c0 c1 c2 h
    omega
  · intro f00 f01 f02 f10 f11 f12 f20 f21 f22 e0 e1 e2
    omega

/-- No congruent dissection has tile angles `(5,6,19)π/30` and target angles `(5,10,15)π/30` (Condition (E), `Y = (1,0,-1)`). -/
theorem kill_30_5_6_19_t5_10_15 (D : CongruentDissection N)
    (hT : TileAngles D (5 * Real.pi / 30) (6 * Real.pi / 30) (19 * Real.pi / 30))
    (hG : TgtAngles D (5 * Real.pi / 30) (10 * Real.pi / 30) (15 * Real.pi / 30)) : False := by
  refine E_kill_tri D 30 (by norm_num) 5 6 19 5 10 15 (1) (0) (-1) (by exact_mod_cast hT) (by exact_mod_cast hG) ?_ (by norm_num) ?_
  · intro c0 c1 c2 h
    omega
  · intro f00 f01 f02 f10 f11 f12 f20 f21 f22 e0 e1 e2
    omega

/-- No congruent dissection has tile angles `(5,6,19)π/30` and target angles `(10,10,10)π/30` (Condition (E), `Y = (1,0,-1)`). -/
theorem kill_30_5_6_19_t10_10_10 (D : CongruentDissection N)
    (hT : TileAngles D (5 * Real.pi / 30) (6 * Real.pi / 30) (19 * Real.pi / 30))
    (hG : TgtAngles D (10 * Real.pi / 30) (10 * Real.pi / 30) (10 * Real.pi / 30)) : False := by
  refine E_kill_tri D 30 (by norm_num) 5 6 19 10 10 10 (1) (0) (-1) (by exact_mod_cast hT) (by exact_mod_cast hG) ?_ (by norm_num) ?_
  · intro c0 c1 c2 h
    omega
  · intro f00 f01 f02 f10 f11 f12 f20 f21 f22 e0 e1 e2
    omega

/-- No congruent dissection has tile angles `(5,7,18)π/30` and target angles `(5,5,20)π/30` (Condition (E), `Y = (5,1,-6)`). -/
theorem kill_30_5_7_18_t5_5_20 (D : CongruentDissection N)
    (hT : TileAngles D (5 * Real.pi / 30) (7 * Real.pi / 30) (18 * Real.pi / 30))
    (hG : TgtAngles D (5 * Real.pi / 30) (5 * Real.pi / 30) (20 * Real.pi / 30)) : False := by
  refine E_kill_tri D 30 (by norm_num) 5 7 18 5 5 20 (5) (1) (-6) (by exact_mod_cast hT) (by exact_mod_cast hG) ?_ (by norm_num) ?_
  · intro c0 c1 c2 h
    omega
  · intro f00 f01 f02 f10 f11 f12 f20 f21 f22 e0 e1 e2
    omega

/-- No congruent dissection has tile angles `(5,7,18)π/30` and target angles `(5,10,15)π/30` (Condition (E), `Y = (5,1,-6)`). -/
theorem kill_30_5_7_18_t5_10_15 (D : CongruentDissection N)
    (hT : TileAngles D (5 * Real.pi / 30) (7 * Real.pi / 30) (18 * Real.pi / 30))
    (hG : TgtAngles D (5 * Real.pi / 30) (10 * Real.pi / 30) (15 * Real.pi / 30)) : False := by
  refine E_kill_tri D 30 (by norm_num) 5 7 18 5 10 15 (5) (1) (-6) (by exact_mod_cast hT) (by exact_mod_cast hG) ?_ (by norm_num) ?_
  · intro c0 c1 c2 h
    omega
  · intro f00 f01 f02 f10 f11 f12 f20 f21 f22 e0 e1 e2
    omega

/-- No congruent dissection has tile angles `(5,7,18)π/30` and target angles `(10,10,10)π/30` (Condition (E), `Y = (5,1,-6)`). -/
theorem kill_30_5_7_18_t10_10_10 (D : CongruentDissection N)
    (hT : TileAngles D (5 * Real.pi / 30) (7 * Real.pi / 30) (18 * Real.pi / 30))
    (hG : TgtAngles D (10 * Real.pi / 30) (10 * Real.pi / 30) (10 * Real.pi / 30)) : False := by
  refine E_kill_tri D 30 (by norm_num) 5 7 18 10 10 10 (5) (1) (-6) (by exact_mod_cast hT) (by exact_mod_cast hG) ?_ (by norm_num) ?_
  · intro c0 c1 c2 h
    omega
  · intro f00 f01 f02 f10 f11 f12 f20 f21 f22 e0 e1 e2
    omega

/-- No congruent dissection has tile angles `(5,12,13)π/30` and target angles `(5,5,20)π/30` (Condition (E), `Y = (1,0,-1)`). -/
theorem kill_30_5_12_13_t5_5_20 (D : CongruentDissection N)
    (hT : TileAngles D (5 * Real.pi / 30) (12 * Real.pi / 30) (13 * Real.pi / 30))
    (hG : TgtAngles D (5 * Real.pi / 30) (5 * Real.pi / 30) (20 * Real.pi / 30)) : False := by
  refine E_kill_tri D 30 (by norm_num) 5 12 13 5 5 20 (1) (0) (-1) (by exact_mod_cast hT) (by exact_mod_cast hG) ?_ (by norm_num) ?_
  · intro c0 c1 c2 h
    omega
  · intro f00 f01 f02 f10 f11 f12 f20 f21 f22 e0 e1 e2
    omega

/-- No congruent dissection has tile angles `(5,12,13)π/30` and target angles `(5,10,15)π/30` (Condition (E), `Y = (1,0,-1)`). -/
theorem kill_30_5_12_13_t5_10_15 (D : CongruentDissection N)
    (hT : TileAngles D (5 * Real.pi / 30) (12 * Real.pi / 30) (13 * Real.pi / 30))
    (hG : TgtAngles D (5 * Real.pi / 30) (10 * Real.pi / 30) (15 * Real.pi / 30)) : False := by
  refine E_kill_tri D 30 (by norm_num) 5 12 13 5 10 15 (1) (0) (-1) (by exact_mod_cast hT) (by exact_mod_cast hG) ?_ (by norm_num) ?_
  · intro c0 c1 c2 h
    omega
  · intro f00 f01 f02 f10 f11 f12 f20 f21 f22 e0 e1 e2
    omega

/-- No congruent dissection has tile angles `(5,12,13)π/30` and target angles `(10,10,10)π/30` (Condition (E), `Y = (1,0,-1)`). -/
theorem kill_30_5_12_13_t10_10_10 (D : CongruentDissection N)
    (hT : TileAngles D (5 * Real.pi / 30) (12 * Real.pi / 30) (13 * Real.pi / 30))
    (hG : TgtAngles D (10 * Real.pi / 30) (10 * Real.pi / 30) (10 * Real.pi / 30)) : False := by
  refine E_kill_tri D 30 (by norm_num) 5 12 13 10 10 10 (1) (0) (-1) (by exact_mod_cast hT) (by exact_mod_cast hG) ?_ (by norm_num) ?_
  · intro c0 c1 c2 h
    omega
  · intro f00 f01 f02 f10 f11 f12 f20 f21 f22 e0 e1 e2
    omega

/-- **Satisfiability of the arithmetic of Condition (E).**  The vertex data of the `N = 4` ladder (equilateral tile `(1,1,1)π/3`, target
`(1,1,1)π/3` corners; three corner vertices carrying one tile corner each, three midpoints carrying the vectors `(1,1,1)`) satisfies every clause of
Condition (E): corner sums equal the target angles, non-corner sums equal `π` (`a·c = n = 3`), and the column sums are `N = 4`.  (The geometric `N = 4`
dissection itself is `ladderDissection`; this lemma shows the Farkas hypotheses of `E_kill` are not vacuous in the sense that (E) has solutions.) -/
theorem condE_arith_witness_N4 :
    ∃ (corner : Fin 3 → Fin 3 → ℕ) (mid : Fin 3 → Fin 3 → ℕ),
      (∀ j, ∑ i, corner j i = 1) ∧ (∀ k, ∑ i, mid k i = 3) ∧
      (∀ i, ∑ j, corner j i + ∑ k, mid k i = 4) := by
  refine ⟨fun j i => if i = j then 1 else 0, fun _ _ => 1, ?_, ?_, ?_⟩
  · intro j; simp [Finset.sum_ite_eq']
  · intro k; simp
  · intro i; simp [Finset.sum_ite_eq]

end Erdos634.Draft.LaczFormal

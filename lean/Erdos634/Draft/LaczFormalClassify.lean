-- Draft/LaczFormalClassify.lean -- CLASSIFICATION of the exceptional n = 6, 8, 10, 12, 18, 24, 30, 60 for tiles with rational angles (Laczkovich 1995 Thm 5.1 / 5.3, congruent case):
-- for each of the 28 primitive triples a with R(a) != R0(a), the target angle triple u of any congruent dissection is the tile's own triple (similar target)
-- or one of a short explicit list of valid/pending shapes; every other target is excluded.  The exclusions are: plain Condition (E) (643 targets, table-checked), K1, K2,
-- conjugate (E) for (2,3,7)/12, and the geometric cases (iv) (v) (vi) (vii).  Remaining NON-excluded entries: valid equilateral tilings of the rational tiles of n = 6
-- (equilateral targets, N = 3 resp. 2) and the isosceles 120-target of the 30-60-90 tile, and three tiles with an EQUILATERAL target left open
-- (12:(1,4,7), 30:(1,10,19), 30:(7,10,13); Laczkovich 2012 Thm 3.3 (iii) kills them via his Thm 2.1, not formalized).  UNAUDITED.
-- Credit: Laczkovich (1995, 2012, 2020), Beeson-Rosu, Beeson.
import Erdos634.Draft.LaczFormalWireData1
import Erdos634.Draft.LaczFormalWireData2
import Erdos634.Draft.LaczFormalWireData3
import Erdos634.Draft.LaczFormalWireData4
import Erdos634.Draft.LaczFormalWireData5
import Erdos634.Draft.LaczFormalK2Kill
import Erdos634.Draft.LaczFormalViiKill
import Erdos634.Draft.LaczFormalTailVGlue
import Erdos634.Draft.LaczFormalTailIV

open scoped BigOperators Classical
open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional

namespace Erdos634.Draft.LaczFormal

variable {N : ℕ}

/-- `wire_tile` in `TileAngles` form. -/
theorem wire_tileA (D : CongruentDissection N) (n : ℕ) (hn : 0 < n) (a : ℕ × ℕ × ℕ)
    (h0 : 0 < a.1) (h1 : 0 < a.2.1) (h2 : 0 < a.2.2) (surv : List (ℕ × ℕ × ℕ))
    (entries : List ((ℕ × ℕ × ℕ) × (ℤ × ℤ × ℤ))) (hc : Cover n a surv entries)
    (hM : TileAngles D (a.1 * Real.pi / n) (a.2.1 * Real.pi / n) (a.2.2 * Real.pi / n)) :
    ∃ u : ℕ × ℕ × ℕ, TgtAngles D (u.1 * Real.pi / n) (u.2.1 * Real.pi / n) (u.2.2 * Real.pi / n) ∧
      (u = a ∨ u ∈ surv) := by
  obtain ⟨σ, m0, m1, m2⟩ := hM
  obtain ⟨u, hT, -, -, -, -, hu⟩ := wire_tile D n hn a h0 h1 h2 surv entries hc σ
    (by intro i; fin_cases i <;> simp [m0, m1, m2])
  exact ⟨u, hT, hu⟩

/-- Case (vi) in `TgtAngles` numerator form. -/
theorem case_vi_kill {N : ℕ} (D : CongruentDissection N)
    (hM : TileAngles D (1 * Real.pi / 10) (2 * Real.pi / 10) (7 * Real.pi / 10))
    (hT : TgtAngles D (1 * Real.pi / 10) (1 * Real.pi / 10) (8 * Real.pi / 10)) : False :=
  case_vi D (hM.of_eq (by ring) rfl rfl) (tgt_of_eq hT (by ring) (by ring) rfl)

theorem tail_iv_kill {N : ℕ} (D : CongruentDissection N)
    (hM : TileAngles D (1 * Real.pi / 6) (1 * Real.pi / 6) (4 * Real.pi / 6))
    (hT : TgtAngles D (1 * Real.pi / 6) (2 * Real.pi / 6) (3 * Real.pi / 6)) : False :=
  tail_iv D (hM.of_eq (by ring) (by ring) (by ring)) (tgt_of_eq hT (by ring) (by ring) (by ring))

theorem tail_v_kill {N : ℕ} (D : CongruentDissection N)
    (hM : TileAngles D (1 * Real.pi / 10) (3 * Real.pi / 10) (6 * Real.pi / 10))
    (hT : TgtAngles D (3 * Real.pi / 10) (3 * Real.pi / 10) (4 * Real.pi / 10)) : False :=
  tail_v D (hM.of_eq (by ring) rfl rfl) hT

/-- Exceptional tile `(1,1,1)π/3`: the target angle triple (numerators over `3`) is in [(1, 1, 1)]. -/
theorem classify_3_1_1_1 (D : CongruentDissection N)
    (hM : TileAngles D (1 * Real.pi / 3) (1 * Real.pi / 3) (1 * Real.pi / 3)) :
    ∃ u : ℕ × ℕ × ℕ, u ∈ [(1, 1, 1)] ∧
      TgtAngles D (u.1 * Real.pi / 3) (u.2.1 * Real.pi / 3) (u.2.2 * Real.pi / 3) := by
  obtain ⟨u, hT, hu⟩ := wire_tileA D 3 (by norm_num) (1, 1, 1) (by norm_num) (by norm_num) (by norm_num)
    surv_3_1_1_1 ent_3_1_1_1 cover_3_1_1_1 (by simpa using hM)
  rcases hu with rfl | hs
  · exact ⟨_, by simp, hT⟩
  · simp [surv_3_1_1_1] at hs

/-- Exceptional tile `(1,1,2)π/4`: the target angle triple (numerators over `4`) is in [(1, 1, 2)]. -/
theorem classify_4_1_1_2 (D : CongruentDissection N)
    (hM : TileAngles D (1 * Real.pi / 4) (1 * Real.pi / 4) (2 * Real.pi / 4)) :
    ∃ u : ℕ × ℕ × ℕ, u ∈ [(1, 1, 2)] ∧
      TgtAngles D (u.1 * Real.pi / 4) (u.2.1 * Real.pi / 4) (u.2.2 * Real.pi / 4) := by
  obtain ⟨u, hT, hu⟩ := wire_tileA D 4 (by norm_num) (1, 1, 2) (by norm_num) (by norm_num) (by norm_num)
    surv_4_1_1_2 ent_4_1_1_2 cover_4_1_1_2 (by simpa using hM)
  rcases hu with rfl | hs
  · exact ⟨_, by simp, hT⟩
  · simp [surv_4_1_1_2] at hs

/-- Exceptional tile `(1,1,4)π/6`: the target angle triple (numerators over `6`) is in [(1, 1, 4), (2, 2, 2)]. -/
theorem classify_6_1_1_4 (D : CongruentDissection N)
    (hM : TileAngles D (1 * Real.pi / 6) (1 * Real.pi / 6) (4 * Real.pi / 6)) :
    ∃ u : ℕ × ℕ × ℕ, u ∈ [(1, 1, 4), (2, 2, 2)] ∧
      TgtAngles D (u.1 * Real.pi / 6) (u.2.1 * Real.pi / 6) (u.2.2 * Real.pi / 6) := by
  obtain ⟨u, hT, hu⟩ := wire_tileA D 6 (by norm_num) (1, 1, 4) (by norm_num) (by norm_num) (by norm_num)
    surv_6_1_1_4 ent_6_1_1_4 cover_6_1_1_4 (by simpa using hM)
  rcases hu with rfl | hs
  · exact ⟨_, by simp, hT⟩
  · simp only [surv_6_1_1_4, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exfalso
      exact tail_iv_kill D hM (by simpa using hT)
    · exact ⟨_, by simp, hT⟩

/-- Exceptional tile `(1,2,3)π/6`: the target angle triple (numerators over `6`) is in [(1, 2, 3), (1, 1, 4), (2, 2, 2)]. -/
theorem classify_6_1_2_3 (D : CongruentDissection N)
    (hM : TileAngles D (1 * Real.pi / 6) (2 * Real.pi / 6) (3 * Real.pi / 6)) :
    ∃ u : ℕ × ℕ × ℕ, u ∈ [(1, 2, 3), (1, 1, 4), (2, 2, 2)] ∧
      TgtAngles D (u.1 * Real.pi / 6) (u.2.1 * Real.pi / 6) (u.2.2 * Real.pi / 6) := by
  obtain ⟨u, hT, hu⟩ := wire_tileA D 6 (by norm_num) (1, 2, 3) (by norm_num) (by norm_num) (by norm_num)
    surv_6_1_2_3 ent_6_1_2_3 cover_6_1_2_3 (by simpa using hM)
  rcases hu with rfl | hs
  · exact ⟨_, by simp, hT⟩
  · simp only [surv_6_1_2_3, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact ⟨_, by simp, hT⟩
    · exact ⟨_, by simp, hT⟩

/-- Exceptional tile `(1,2,5)π/8`: the target angle triple (numerators over `8`) is in [(1, 2, 5)]. -/
theorem classify_8_1_2_5 (D : CongruentDissection N)
    (hM : TileAngles D (1 * Real.pi / 8) (2 * Real.pi / 8) (5 * Real.pi / 8)) :
    ∃ u : ℕ × ℕ × ℕ, u ∈ [(1, 2, 5)] ∧
      TgtAngles D (u.1 * Real.pi / 8) (u.2.1 * Real.pi / 8) (u.2.2 * Real.pi / 8) := by
  obtain ⟨u, hT, hu⟩ := wire_tileA D 8 (by norm_num) (1, 2, 5) (by norm_num) (by norm_num) (by norm_num)
    surv_8_1_2_5 ent_8_1_2_5 cover_8_1_2_5 (by simpa using hM)
  rcases hu with rfl | hs
  · exact ⟨_, by simp, hT⟩
  · simp only [surv_8_1_2_5, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exfalso
      exact k1kill_8_1_2_5_t1_1_6 D hM (by simpa using hT)
    · exfalso
      exact k1kill_8_1_2_5_t1_3_4 D hM (by simpa using hT)
    · exfalso
      exact case_vii_8 D hM (by simpa using hT)
    · exfalso
      exact k1kill_8_1_2_5_t2_3_3 D hM (by simpa using hT)

/-- Exceptional tile `(1,2,7)π/10`: the target angle triple (numerators over `10`) is in [(1, 2, 7)]. -/
theorem classify_10_1_2_7 (D : CongruentDissection N)
    (hM : TileAngles D (1 * Real.pi / 10) (2 * Real.pi / 10) (7 * Real.pi / 10)) :
    ∃ u : ℕ × ℕ × ℕ, u ∈ [(1, 2, 7)] ∧
      TgtAngles D (u.1 * Real.pi / 10) (u.2.1 * Real.pi / 10) (u.2.2 * Real.pi / 10) := by
  obtain ⟨u, hT, hu⟩ := wire_tileA D 10 (by norm_num) (1, 2, 7) (by norm_num) (by norm_num) (by norm_num)
    surv_10_1_2_7 ent_10_1_2_7 cover_10_1_2_7 (by simpa using hM)
  rcases hu with rfl | hs
  · exact ⟨_, by simp, hT⟩
  · simp only [surv_10_1_2_7, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl
    · exfalso
      exact case_vi_kill D hM (by simpa using hT)

/-- Exceptional tile `(1,3,6)π/10`: the target angle triple (numerators over `10`) is in [(1, 3, 6)]. -/
theorem classify_10_1_3_6 (D : CongruentDissection N)
    (hM : TileAngles D (1 * Real.pi / 10) (3 * Real.pi / 10) (6 * Real.pi / 10)) :
    ∃ u : ℕ × ℕ × ℕ, u ∈ [(1, 3, 6)] ∧
      TgtAngles D (u.1 * Real.pi / 10) (u.2.1 * Real.pi / 10) (u.2.2 * Real.pi / 10) := by
  obtain ⟨u, hT, hu⟩ := wire_tileA D 10 (by norm_num) (1, 3, 6) (by norm_num) (by norm_num) (by norm_num)
    surv_10_1_3_6 ent_10_1_3_6 cover_10_1_3_6 (by simpa using hM)
  rcases hu with rfl | hs
  · exact ⟨_, by simp, hT⟩
  · simp only [surv_10_1_3_6, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl
    · exfalso
      exact tail_v_kill D hM (by simpa using hT)

/-- Exceptional tile `(1,2,9)π/12`: the target angle triple (numerators over `12`) is in [(1, 2, 9)]. -/
theorem classify_12_1_2_9 (D : CongruentDissection N)
    (hM : TileAngles D (1 * Real.pi / 12) (2 * Real.pi / 12) (9 * Real.pi / 12)) :
    ∃ u : ℕ × ℕ × ℕ, u ∈ [(1, 2, 9)] ∧
      TgtAngles D (u.1 * Real.pi / 12) (u.2.1 * Real.pi / 12) (u.2.2 * Real.pi / 12) := by
  obtain ⟨u, hT, hu⟩ := wire_tileA D 12 (by norm_num) (1, 2, 9) (by norm_num) (by norm_num) (by norm_num)
    surv_12_1_2_9 ent_12_1_2_9 cover_12_1_2_9 (by simpa using hM)
  rcases hu with rfl | hs
  · exact ⟨_, by simp, hT⟩
  · simp only [surv_12_1_2_9, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl
    · exfalso
      exact k1kill_12_1_2_9_t1_1_10 D hM (by simpa using hT)

/-- Exceptional tile `(1,3,8)π/12`: the target angle triple (numerators over `12`) is in [(1, 3, 8)]. -/
theorem classify_12_1_3_8 (D : CongruentDissection N)
    (hM : TileAngles D (1 * Real.pi / 12) (3 * Real.pi / 12) (8 * Real.pi / 12)) :
    ∃ u : ℕ × ℕ × ℕ, u ∈ [(1, 3, 8)] ∧
      TgtAngles D (u.1 * Real.pi / 12) (u.2.1 * Real.pi / 12) (u.2.2 * Real.pi / 12) := by
  obtain ⟨u, hT, hu⟩ := wire_tileA D 12 (by norm_num) (1, 3, 8) (by norm_num) (by norm_num) (by norm_num)
    surv_12_1_3_8 ent_12_1_3_8 cover_12_1_3_8 (by simpa using hM)
  rcases hu with rfl | hs
  · exact ⟨_, by simp, hT⟩
  · simp only [surv_12_1_3_8, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exfalso
      exact k2kill_12_1_3_8_t1_1_10 D hM (by simpa using hT)
    · exfalso
      exact k1kill_12_1_3_8_t1_2_9 D hM (by simpa using hT)
    · exfalso
      exact k1kill_12_1_3_8_t1_4_7 D hM (by simpa using hT)
    · exfalso
      exact k2kill_12_1_3_8_t1_5_6 D hM (by simpa using hT)
    · exfalso
      exact k1kill_12_1_3_8_t2_2_8 D hM (by simpa using hT)
    · exfalso
      exact k1kill_12_1_3_8_t2_3_7 D hM (by simpa using hT)
    · exfalso
      exact k1kill_12_1_3_8_t2_4_6 D hM (by simpa using hT)
    · exfalso
      exact k2kill_12_1_3_8_t2_5_5 D hM (by simpa using hT)
    · exfalso
      exact case_vii_12_138 D hM (by simpa using hT)
    · exfalso
      exact k2kill_12_1_3_8_t3_4_5 D hM (by simpa using hT)
    · exfalso
      exact k1kill_12_1_3_8_t4_4_4 D hM (by simpa using hT)

/-- Exceptional tile `(1,4,7)π/12`: the target angle triple (numerators over `12`) is in [(1, 4, 7), (4, 4, 4)]. -/
theorem classify_12_1_4_7 (D : CongruentDissection N)
    (hM : TileAngles D (1 * Real.pi / 12) (4 * Real.pi / 12) (7 * Real.pi / 12)) :
    ∃ u : ℕ × ℕ × ℕ, u ∈ [(1, 4, 7), (4, 4, 4)] ∧
      TgtAngles D (u.1 * Real.pi / 12) (u.2.1 * Real.pi / 12) (u.2.2 * Real.pi / 12) := by
  obtain ⟨u, hT, hu⟩ := wire_tileA D 12 (by norm_num) (1, 4, 7) (by norm_num) (by norm_num) (by norm_num)
    surv_12_1_4_7 ent_12_1_4_7 cover_12_1_4_7 (by simpa using hM)
  rcases hu with rfl | hs
  · exact ⟨_, by simp, hT⟩
  · simp only [surv_12_1_4_7, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl
    · exact ⟨_, by simp, hT⟩

/-- Exceptional tile `(2,3,7)π/12`: the target angle triple (numerators over `12`) is in [(2, 3, 7)]. -/
theorem classify_12_2_3_7 (D : CongruentDissection N)
    (hM : TileAngles D (2 * Real.pi / 12) (3 * Real.pi / 12) (7 * Real.pi / 12)) :
    ∃ u : ℕ × ℕ × ℕ, u ∈ [(2, 3, 7)] ∧
      TgtAngles D (u.1 * Real.pi / 12) (u.2.1 * Real.pi / 12) (u.2.2 * Real.pi / 12) := by
  obtain ⟨u, hT, hu⟩ := wire_tileA D 12 (by norm_num) (2, 3, 7) (by norm_num) (by norm_num) (by norm_num)
    surv_12_2_3_7 ent_12_2_3_7 cover_12_2_3_7 (by simpa using hM)
  rcases hu with rfl | hs
  · exact ⟨_, by simp, hT⟩
  · simp only [surv_12_2_3_7, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
    · exfalso
      exact kill_12_2_3_7_t2_2_8 D hM (by simpa using hT)
    · exfalso
      exact kill_12_2_3_7_t2_4_6 D hM (by simpa using hT)
    · exfalso
      exact k1kill_12_2_3_7_t2_5_5 D hM (by simpa using hT)
    · exfalso
      exact k1kill_12_2_3_7_t3_3_6 D hM (by simpa using hT)
    · exfalso
      exact k1kill_12_2_3_7_t3_4_5 D hM (by simpa using hT)
    · exfalso
      exact kill_12_2_3_7_t4_4_4 D hM (by simpa using hT)

/-- Exceptional tile `(3,4,5)π/12`: the target angle triple (numerators over `12`) is in [(3, 4, 5)]. -/
theorem classify_12_3_4_5 (D : CongruentDissection N)
    (hM : TileAngles D (3 * Real.pi / 12) (4 * Real.pi / 12) (5 * Real.pi / 12)) :
    ∃ u : ℕ × ℕ × ℕ, u ∈ [(3, 4, 5)] ∧
      TgtAngles D (u.1 * Real.pi / 12) (u.2.1 * Real.pi / 12) (u.2.2 * Real.pi / 12) := by
  obtain ⟨u, hT, hu⟩ := wire_tileA D 12 (by norm_num) (3, 4, 5) (by norm_num) (by norm_num) (by norm_num)
    surv_12_3_4_5 ent_12_3_4_5 cover_12_3_4_5 (by simpa using hM)
  rcases hu with rfl | hs
  · exact ⟨_, by simp, hT⟩
  · simp only [surv_12_3_4_5, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exfalso
      exact case_vii_12_345 D hM (by simpa using hT)
    · exfalso
      exact k1kill_12_3_4_5_t4_4_4 D hM (by simpa using hT)

/-- Exceptional tile `(1,3,14)π/18`: the target angle triple (numerators over `18`) is in [(1, 3, 14)]. -/
theorem classify_18_1_3_14 (D : CongruentDissection N)
    (hM : TileAngles D (1 * Real.pi / 18) (3 * Real.pi / 18) (14 * Real.pi / 18)) :
    ∃ u : ℕ × ℕ × ℕ, u ∈ [(1, 3, 14)] ∧
      TgtAngles D (u.1 * Real.pi / 18) (u.2.1 * Real.pi / 18) (u.2.2 * Real.pi / 18) := by
  obtain ⟨u, hT, hu⟩ := wire_tileA D 18 (by norm_num) (1, 3, 14) (by norm_num) (by norm_num) (by norm_num)
    surv_18_1_3_14 ent_18_1_3_14 cover_18_1_3_14 (by simpa using hM)
  rcases hu with rfl | hs
  · exact ⟨_, by simp, hT⟩
  · simp [surv_18_1_3_14] at hs

/-- Exceptional tile `(2,3,13)π/18`: the target angle triple (numerators over `18`) is in [(2, 3, 13)]. -/
theorem classify_18_2_3_13 (D : CongruentDissection N)
    (hM : TileAngles D (2 * Real.pi / 18) (3 * Real.pi / 18) (13 * Real.pi / 18)) :
    ∃ u : ℕ × ℕ × ℕ, u ∈ [(2, 3, 13)] ∧
      TgtAngles D (u.1 * Real.pi / 18) (u.2.1 * Real.pi / 18) (u.2.2 * Real.pi / 18) := by
  obtain ⟨u, hT, hu⟩ := wire_tileA D 18 (by norm_num) (2, 3, 13) (by norm_num) (by norm_num) (by norm_num)
    surv_18_2_3_13 ent_18_2_3_13 cover_18_2_3_13 (by simpa using hM)
  rcases hu with rfl | hs
  · exact ⟨_, by simp, hT⟩
  · simp [surv_18_2_3_13] at hs

/-- Exceptional tile `(3,7,8)π/18`: the target angle triple (numerators over `18`) is in [(3, 7, 8)]. -/
theorem classify_18_3_7_8 (D : CongruentDissection N)
    (hM : TileAngles D (3 * Real.pi / 18) (7 * Real.pi / 18) (8 * Real.pi / 18)) :
    ∃ u : ℕ × ℕ × ℕ, u ∈ [(3, 7, 8)] ∧
      TgtAngles D (u.1 * Real.pi / 18) (u.2.1 * Real.pi / 18) (u.2.2 * Real.pi / 18) := by
  obtain ⟨u, hT, hu⟩ := wire_tileA D 18 (by norm_num) (3, 7, 8) (by norm_num) (by norm_num) (by norm_num)
    surv_18_3_7_8 ent_18_3_7_8 cover_18_3_7_8 (by simpa using hM)
  rcases hu with rfl | hs
  · exact ⟨_, by simp, hT⟩
  · simp [surv_18_3_7_8] at hs

/-- Exceptional tile `(1,4,19)π/24`: the target angle triple (numerators over `24`) is in [(1, 4, 19)]. -/
theorem classify_24_1_4_19 (D : CongruentDissection N)
    (hM : TileAngles D (1 * Real.pi / 24) (4 * Real.pi / 24) (19 * Real.pi / 24)) :
    ∃ u : ℕ × ℕ × ℕ, u ∈ [(1, 4, 19)] ∧
      TgtAngles D (u.1 * Real.pi / 24) (u.2.1 * Real.pi / 24) (u.2.2 * Real.pi / 24) := by
  obtain ⟨u, hT, hu⟩ := wire_tileA D 24 (by norm_num) (1, 4, 19) (by norm_num) (by norm_num) (by norm_num)
    surv_24_1_4_19 ent_24_1_4_19 cover_24_1_4_19 (by simpa using hM)
  rcases hu with rfl | hs
  · exact ⟨_, by simp, hT⟩
  · simp [surv_24_1_4_19] at hs

/-- Exceptional tile `(1,6,17)π/24`: the target angle triple (numerators over `24`) is in [(1, 6, 17)]. -/
theorem classify_24_1_6_17 (D : CongruentDissection N)
    (hM : TileAngles D (1 * Real.pi / 24) (6 * Real.pi / 24) (17 * Real.pi / 24)) :
    ∃ u : ℕ × ℕ × ℕ, u ∈ [(1, 6, 17)] ∧
      TgtAngles D (u.1 * Real.pi / 24) (u.2.1 * Real.pi / 24) (u.2.2 * Real.pi / 24) := by
  obtain ⟨u, hT, hu⟩ := wire_tileA D 24 (by norm_num) (1, 6, 17) (by norm_num) (by norm_num) (by norm_num)
    surv_24_1_6_17 ent_24_1_6_17 cover_24_1_6_17 (by simpa using hM)
  rcases hu with rfl | hs
  · exact ⟨_, by simp, hT⟩
  · simp [surv_24_1_6_17] at hs

/-- Exceptional tile `(4,7,13)π/24`: the target angle triple (numerators over `24`) is in [(4, 7, 13)]. -/
theorem classify_24_4_7_13 (D : CongruentDissection N)
    (hM : TileAngles D (4 * Real.pi / 24) (7 * Real.pi / 24) (13 * Real.pi / 24)) :
    ∃ u : ℕ × ℕ × ℕ, u ∈ [(4, 7, 13)] ∧
      TgtAngles D (u.1 * Real.pi / 24) (u.2.1 * Real.pi / 24) (u.2.2 * Real.pi / 24) := by
  obtain ⟨u, hT, hu⟩ := wire_tileA D 24 (by norm_num) (4, 7, 13) (by norm_num) (by norm_num) (by norm_num)
    surv_24_4_7_13 ent_24_4_7_13 cover_24_4_7_13 (by simpa using hM)
  rcases hu with rfl | hs
  · exact ⟨_, by simp, hT⟩
  · simp [surv_24_4_7_13] at hs

/-- Exceptional tile `(5,6,13)π/24`: the target angle triple (numerators over `24`) is in [(5, 6, 13)]. -/
theorem classify_24_5_6_13 (D : CongruentDissection N)
    (hM : TileAngles D (5 * Real.pi / 24) (6 * Real.pi / 24) (13 * Real.pi / 24)) :
    ∃ u : ℕ × ℕ × ℕ, u ∈ [(5, 6, 13)] ∧
      TgtAngles D (u.1 * Real.pi / 24) (u.2.1 * Real.pi / 24) (u.2.2 * Real.pi / 24) := by
  obtain ⟨u, hT, hu⟩ := wire_tileA D 24 (by norm_num) (5, 6, 13) (by norm_num) (by norm_num) (by norm_num)
    surv_24_5_6_13 ent_24_5_6_13 cover_24_5_6_13 (by simpa using hM)
  rcases hu with rfl | hs
  · exact ⟨_, by simp, hT⟩
  · simp [surv_24_5_6_13] at hs

/-- Exceptional tile `(1,5,24)π/30`: the target angle triple (numerators over `30`) is in [(1, 5, 24)]. -/
theorem classify_30_1_5_24 (D : CongruentDissection N)
    (hM : TileAngles D (1 * Real.pi / 30) (5 * Real.pi / 30) (24 * Real.pi / 30)) :
    ∃ u : ℕ × ℕ × ℕ, u ∈ [(1, 5, 24)] ∧
      TgtAngles D (u.1 * Real.pi / 30) (u.2.1 * Real.pi / 30) (u.2.2 * Real.pi / 30) := by
  obtain ⟨u, hT, hu⟩ := wire_tileA D 30 (by norm_num) (1, 5, 24) (by norm_num) (by norm_num) (by norm_num)
    surv_30_1_5_24 ent_30_1_5_24 cover_30_1_5_24 (by simpa using hM)
  rcases hu with rfl | hs
  · exact ⟨_, by simp, hT⟩
  · simp [surv_30_1_5_24] at hs

/-- Exceptional tile `(1,10,19)π/30`: the target angle triple (numerators over `30`) is in [(1, 10, 19), (10, 10, 10)]. -/
theorem classify_30_1_10_19 (D : CongruentDissection N)
    (hM : TileAngles D (1 * Real.pi / 30) (10 * Real.pi / 30) (19 * Real.pi / 30)) :
    ∃ u : ℕ × ℕ × ℕ, u ∈ [(1, 10, 19), (10, 10, 10)] ∧
      TgtAngles D (u.1 * Real.pi / 30) (u.2.1 * Real.pi / 30) (u.2.2 * Real.pi / 30) := by
  obtain ⟨u, hT, hu⟩ := wire_tileA D 30 (by norm_num) (1, 10, 19) (by norm_num) (by norm_num) (by norm_num)
    surv_30_1_10_19 ent_30_1_10_19 cover_30_1_10_19 (by simpa using hM)
  rcases hu with rfl | hs
  · exact ⟨_, by simp, hT⟩
  · simp only [surv_30_1_10_19, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl
    · exact ⟨_, by simp, hT⟩

/-- Exceptional tile `(5,6,19)π/30`: the target angle triple (numerators over `30`) is in [(5, 6, 19)]. -/
theorem classify_30_5_6_19 (D : CongruentDissection N)
    (hM : TileAngles D (5 * Real.pi / 30) (6 * Real.pi / 30) (19 * Real.pi / 30)) :
    ∃ u : ℕ × ℕ × ℕ, u ∈ [(5, 6, 19)] ∧
      TgtAngles D (u.1 * Real.pi / 30) (u.2.1 * Real.pi / 30) (u.2.2 * Real.pi / 30) := by
  obtain ⟨u, hT, hu⟩ := wire_tileA D 30 (by norm_num) (5, 6, 19) (by norm_num) (by norm_num) (by norm_num)
    surv_30_5_6_19 ent_30_5_6_19 cover_30_5_6_19 (by simpa using hM)
  rcases hu with rfl | hs
  · exact ⟨_, by simp, hT⟩
  · simp [surv_30_5_6_19] at hs

/-- Exceptional tile `(5,7,18)π/30`: the target angle triple (numerators over `30`) is in [(5, 7, 18)]. -/
theorem classify_30_5_7_18 (D : CongruentDissection N)
    (hM : TileAngles D (5 * Real.pi / 30) (7 * Real.pi / 30) (18 * Real.pi / 30)) :
    ∃ u : ℕ × ℕ × ℕ, u ∈ [(5, 7, 18)] ∧
      TgtAngles D (u.1 * Real.pi / 30) (u.2.1 * Real.pi / 30) (u.2.2 * Real.pi / 30) := by
  obtain ⟨u, hT, hu⟩ := wire_tileA D 30 (by norm_num) (5, 7, 18) (by norm_num) (by norm_num) (by norm_num)
    surv_30_5_7_18 ent_30_5_7_18 cover_30_5_7_18 (by simpa using hM)
  rcases hu with rfl | hs
  · exact ⟨_, by simp, hT⟩
  · simp [surv_30_5_7_18] at hs

/-- Exceptional tile `(5,12,13)π/30`: the target angle triple (numerators over `30`) is in [(5, 12, 13)]. -/
theorem classify_30_5_12_13 (D : CongruentDissection N)
    (hM : TileAngles D (5 * Real.pi / 30) (12 * Real.pi / 30) (13 * Real.pi / 30)) :
    ∃ u : ℕ × ℕ × ℕ, u ∈ [(5, 12, 13)] ∧
      TgtAngles D (u.1 * Real.pi / 30) (u.2.1 * Real.pi / 30) (u.2.2 * Real.pi / 30) := by
  obtain ⟨u, hT, hu⟩ := wire_tileA D 30 (by norm_num) (5, 12, 13) (by norm_num) (by norm_num) (by norm_num)
    surv_30_5_12_13 ent_30_5_12_13 cover_30_5_12_13 (by simpa using hM)
  rcases hu with rfl | hs
  · exact ⟨_, by simp, hT⟩
  · simp [surv_30_5_12_13] at hs

/-- Exceptional tile `(7,10,13)π/30`: the target angle triple (numerators over `30`) is in [(7, 10, 13), (10, 10, 10)]. -/
theorem classify_30_7_10_13 (D : CongruentDissection N)
    (hM : TileAngles D (7 * Real.pi / 30) (10 * Real.pi / 30) (13 * Real.pi / 30)) :
    ∃ u : ℕ × ℕ × ℕ, u ∈ [(7, 10, 13), (10, 10, 10)] ∧
      TgtAngles D (u.1 * Real.pi / 30) (u.2.1 * Real.pi / 30) (u.2.2 * Real.pi / 30) := by
  obtain ⟨u, hT, hu⟩ := wire_tileA D 30 (by norm_num) (7, 10, 13) (by norm_num) (by norm_num) (by norm_num)
    surv_30_7_10_13 ent_30_7_10_13 cover_30_7_10_13 (by simpa using hM)
  rcases hu with rfl | hs
  · exact ⟨_, by simp, hT⟩
  · simp only [surv_30_7_10_13, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl
    · exact ⟨_, by simp, hT⟩

/-- Exceptional tile `(1,10,49)π/60`: the target angle triple (numerators over `60`) is in [(1, 10, 49)]. -/
theorem classify_60_1_10_49 (D : CongruentDissection N)
    (hM : TileAngles D (1 * Real.pi / 60) (10 * Real.pi / 60) (49 * Real.pi / 60)) :
    ∃ u : ℕ × ℕ × ℕ, u ∈ [(1, 10, 49)] ∧
      TgtAngles D (u.1 * Real.pi / 60) (u.2.1 * Real.pi / 60) (u.2.2 * Real.pi / 60) := by
  obtain ⟨u, hT, hu⟩ := wire_tileA D 60 (by norm_num) (1, 10, 49) (by norm_num) (by norm_num) (by norm_num)
    surv_60_1_10_49 ent_60_1_10_49 cover_60_1_10_49 (by simpa using hM)
  rcases hu with rfl | hs
  · exact ⟨_, by simp, hT⟩
  · simp [surv_60_1_10_49] at hs

/-- Exceptional tile `(7,10,43)π/60`: the target angle triple (numerators over `60`) is in [(7, 10, 43)]. -/
theorem classify_60_7_10_43 (D : CongruentDissection N)
    (hM : TileAngles D (7 * Real.pi / 60) (10 * Real.pi / 60) (43 * Real.pi / 60)) :
    ∃ u : ℕ × ℕ × ℕ, u ∈ [(7, 10, 43)] ∧
      TgtAngles D (u.1 * Real.pi / 60) (u.2.1 * Real.pi / 60) (u.2.2 * Real.pi / 60) := by
  obtain ⟨u, hT, hu⟩ := wire_tileA D 60 (by norm_num) (7, 10, 43) (by norm_num) (by norm_num) (by norm_num)
    surv_60_7_10_43 ent_60_7_10_43 cover_60_7_10_43 (by simpa using hM)
  rcases hu with rfl | hs
  · exact ⟨_, by simp, hT⟩
  · simp [surv_60_7_10_43] at hs

/-- Exceptional tile `(10,13,37)π/60`: the target angle triple (numerators over `60`) is in [(10, 13, 37)]. -/
theorem classify_60_10_13_37 (D : CongruentDissection N)
    (hM : TileAngles D (10 * Real.pi / 60) (13 * Real.pi / 60) (37 * Real.pi / 60)) :
    ∃ u : ℕ × ℕ × ℕ, u ∈ [(10, 13, 37)] ∧
      TgtAngles D (u.1 * Real.pi / 60) (u.2.1 * Real.pi / 60) (u.2.2 * Real.pi / 60) := by
  obtain ⟨u, hT, hu⟩ := wire_tileA D 60 (by norm_num) (10, 13, 37) (by norm_num) (by norm_num) (by norm_num)
    surv_60_10_13_37 ent_60_10_13_37 cover_60_10_13_37 (by simpa using hM)
  rcases hu with rfl | hs
  · exact ⟨_, by simp, hT⟩
  · simp [surv_60_10_13_37] at hs

/-- Exceptional tile `(10,19,31)π/60`: the target angle triple (numerators over `60`) is in [(10, 19, 31)]. -/
theorem classify_60_10_19_31 (D : CongruentDissection N)
    (hM : TileAngles D (10 * Real.pi / 60) (19 * Real.pi / 60) (31 * Real.pi / 60)) :
    ∃ u : ℕ × ℕ × ℕ, u ∈ [(10, 19, 31)] ∧
      TgtAngles D (u.1 * Real.pi / 60) (u.2.1 * Real.pi / 60) (u.2.2 * Real.pi / 60) := by
  obtain ⟨u, hT, hu⟩ := wire_tileA D 60 (by norm_num) (10, 19, 31) (by norm_num) (by norm_num) (by norm_num)
    surv_60_10_19_31 ent_60_10_19_31 cover_60_10_19_31 (by simpa using hM)
  rcases hu with rfl | hs
  · exact ⟨_, by simp, hT⟩
  · simp [surv_60_10_19_31] at hs

end Erdos634.Draft.LaczFormal

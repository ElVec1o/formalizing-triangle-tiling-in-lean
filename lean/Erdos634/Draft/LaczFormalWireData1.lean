-- Draft/LaczFormalWireData1.lean -- WIRING DATA: n = 3, 4, 6, 8, 10
-- Table-checked by `decide +kernel` (certificates found by exact LP, (private working notes, not included)).  UNAUDITED.
import Erdos634.Draft.LaczFormalWire

set_option maxHeartbeats 16000000

namespace Erdos634.Draft.LaczFormal

def surv_3_1_1_1 : List (ℕ × ℕ × ℕ) := []
def ent_3_1_1_1 : List ((ℕ × ℕ × ℕ) × (ℤ × ℤ × ℤ)) :=
  []

set_option maxHeartbeats 8000000 in
theorem cover_3_1_1_1 : Cover 3 (1, 1, 1) surv_3_1_1_1 ent_3_1_1_1 := by
  unfold surv_3_1_1_1 ent_3_1_1_1
  decide +kernel

def surv_4_1_1_2 : List (ℕ × ℕ × ℕ) := []
def ent_4_1_1_2 : List ((ℕ × ℕ × ℕ) × (ℤ × ℤ × ℤ)) :=
  []

set_option maxHeartbeats 8000000 in
theorem cover_4_1_1_2 : Cover 4 (1, 1, 2) surv_4_1_1_2 ent_4_1_1_2 := by
  unfold surv_4_1_1_2 ent_4_1_1_2
  decide +kernel

def surv_6_1_1_4 : List (ℕ × ℕ × ℕ) := [(1, 2, 3), (2, 2, 2)]
def ent_6_1_1_4 : List ((ℕ × ℕ × ℕ) × (ℤ × ℤ × ℤ)) :=
  []

set_option maxHeartbeats 8000000 in
theorem cover_6_1_1_4 : Cover 6 (1, 1, 4) surv_6_1_1_4 ent_6_1_1_4 := by
  unfold surv_6_1_1_4 ent_6_1_1_4
  decide +kernel

def surv_6_1_2_3 : List (ℕ × ℕ × ℕ) := [(1, 1, 4), (2, 2, 2)]
def ent_6_1_2_3 : List ((ℕ × ℕ × ℕ) × (ℤ × ℤ × ℤ)) :=
  []

set_option maxHeartbeats 8000000 in
theorem cover_6_1_2_3 : Cover 6 (1, 2, 3) surv_6_1_2_3 ent_6_1_2_3 := by
  unfold surv_6_1_2_3 ent_6_1_2_3
  decide +kernel

def surv_8_1_2_5 : List (ℕ × ℕ × ℕ) := [(1, 1, 6), (1, 3, 4), (2, 2, 4), (2, 3, 3)]
def ent_8_1_2_5 : List ((ℕ × ℕ × ℕ) × (ℤ × ℤ × ℤ)) :=
  []

set_option maxHeartbeats 8000000 in
theorem cover_8_1_2_5 : Cover 8 (1, 2, 5) surv_8_1_2_5 ent_8_1_2_5 := by
  unfold surv_8_1_2_5 ent_8_1_2_5
  decide +kernel

def surv_10_1_2_7 : List (ℕ × ℕ × ℕ) := [(1, 1, 8)]
def ent_10_1_2_7 : List ((ℕ × ℕ × ℕ) × (ℤ × ℤ × ℤ)) :=
  [((1, 3, 6), (1, 2, -3)),
   ((1, 4, 5), (1, 2, -3)),
   ((2, 2, 6), (1, 2, -3)),
   ((2, 3, 5), (1, 2, -3)),
   ((2, 4, 4), (1, 2, -3)),
   ((3, 3, 4), (1, 2, -3))]

set_option maxHeartbeats 8000000 in
theorem cover_10_1_2_7 : Cover 10 (1, 2, 7) surv_10_1_2_7 ent_10_1_2_7 := by
  unfold surv_10_1_2_7 ent_10_1_2_7
  decide +kernel

def surv_10_1_3_6 : List (ℕ × ℕ × ℕ) := [(3, 3, 4)]
def ent_10_1_3_6 : List ((ℕ × ℕ × ℕ) × (ℤ × ℤ × ℤ)) :=
  [((1, 1, 8), (3, -1, -2)),
   ((1, 2, 7), (3, -1, -2)),
   ((1, 4, 5), (3, -1, -2)),
   ((2, 2, 6), (3, -1, -2)),
   ((2, 3, 5), (3, -1, -2)),
   ((2, 4, 4), (3, -1, -2))]

set_option maxHeartbeats 8000000 in
theorem cover_10_1_3_6 : Cover 10 (1, 3, 6) surv_10_1_3_6 ent_10_1_3_6 := by
  unfold surv_10_1_3_6 ent_10_1_3_6
  decide +kernel

end Erdos634.Draft.LaczFormal

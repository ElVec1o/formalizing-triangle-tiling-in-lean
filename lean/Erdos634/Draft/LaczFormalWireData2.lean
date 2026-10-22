-- Draft/LaczFormalWireData2.lean -- WIRING DATA: n = 12
-- Table-checked by `decide +kernel` (certificates found by exact LP, (private working notes, not included)).  UNAUDITED.
import Erdos634.Draft.LaczFormalWire

set_option maxHeartbeats 16000000

namespace Erdos634.Draft.LaczFormal

def surv_12_1_2_9 : List (ℕ × ℕ × ℕ) := [(1, 1, 10)]
def ent_12_1_2_9 : List ((ℕ × ℕ × ℕ) × (ℤ × ℤ × ℤ)) :=
  [((1, 3, 8), (1, 2, -3)),
   ((1, 4, 7), (1, 2, -3)),
   ((1, 5, 6), (1, 2, -3)),
   ((2, 2, 8), (1, 2, -3)),
   ((2, 3, 7), (1, 2, -3)),
   ((2, 4, 6), (1, 2, -3)),
   ((2, 5, 5), (1, 2, -3)),
   ((3, 3, 6), (1, 2, -3)),
   ((3, 4, 5), (1, 2, -3)),
   ((4, 4, 4), (1, 2, -3))]

set_option maxHeartbeats 8000000 in
theorem cover_12_1_2_9 : Cover 12 (1, 2, 9) surv_12_1_2_9 ent_12_1_2_9 := by
  unfold surv_12_1_2_9 ent_12_1_2_9
  decide +kernel

def surv_12_1_3_8 : List (ℕ × ℕ × ℕ) := [(1, 1, 10), (1, 2, 9), (1, 4, 7), (1, 5, 6), (2, 2, 8), (2, 3, 7), (2, 4, 6), (2, 5, 5), (3, 3, 6), (3, 4, 5), (4, 4, 4)]
def ent_12_1_3_8 : List ((ℕ × ℕ × ℕ) × (ℤ × ℤ × ℤ)) :=
  []

set_option maxHeartbeats 8000000 in
theorem cover_12_1_3_8 : Cover 12 (1, 3, 8) surv_12_1_3_8 ent_12_1_3_8 := by
  unfold surv_12_1_3_8 ent_12_1_3_8
  decide +kernel

def surv_12_1_4_7 : List (ℕ × ℕ × ℕ) := [(4, 4, 4)]
def ent_12_1_4_7 : List ((ℕ × ℕ × ℕ) × (ℤ × ℤ × ℤ)) :=
  [((1, 1, 10), (1, 0, -1)),
   ((1, 2, 9), (1, 0, -1)),
   ((1, 3, 8), (1, 0, -1)),
   ((1, 5, 6), (1, 0, -1)),
   ((2, 2, 8), (1, 0, -1)),
   ((2, 3, 7), (1, 0, -1)),
   ((2, 4, 6), (1, 0, -1)),
   ((2, 5, 5), (1, 0, -1)),
   ((3, 3, 6), (1, 0, -1)),
   ((3, 4, 5), (1, 0, -1))]

set_option maxHeartbeats 8000000 in
theorem cover_12_1_4_7 : Cover 12 (1, 4, 7) surv_12_1_4_7 ent_12_1_4_7 := by
  unfold surv_12_1_4_7 ent_12_1_4_7
  decide +kernel

def surv_12_2_3_7 : List (ℕ × ℕ × ℕ) := [(2, 2, 8), (2, 4, 6), (2, 5, 5), (3, 3, 6), (3, 4, 5), (4, 4, 4)]
def ent_12_2_3_7 : List ((ℕ × ℕ × ℕ) × (ℤ × ℤ × ℤ)) :=
  []

set_option maxHeartbeats 8000000 in
theorem cover_12_2_3_7 : Cover 12 (2, 3, 7) surv_12_2_3_7 ent_12_2_3_7 := by
  unfold surv_12_2_3_7 ent_12_2_3_7
  decide +kernel

def surv_12_3_4_5 : List (ℕ × ℕ × ℕ) := [(3, 3, 6), (4, 4, 4)]
def ent_12_3_4_5 : List ((ℕ × ℕ × ℕ) × (ℤ × ℤ × ℤ)) :=
  []

set_option maxHeartbeats 8000000 in
theorem cover_12_3_4_5 : Cover 12 (3, 4, 5) surv_12_3_4_5 ent_12_3_4_5 := by
  unfold surv_12_3_4_5 ent_12_3_4_5
  decide +kernel

end Erdos634.Draft.LaczFormal

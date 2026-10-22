import Erdos634.Draft.LaczFormalColumnArith
import Erdos634.Draft.LaczFormalColumnLat
import Erdos634.Draft.LaczFormalColumnMain
import Erdos634.Draft.LaczFormalColumnWit
import Erdos634.Draft.LaczFormalColumnGrid
import Erdos634.Draft.LaczFormalColumnStmt
import Erdos634.Draft.LaczFormalColumnCtl
import Erdos634.Draft.LaczFormalColumnWall
import Erdos634.Draft.LaczFormalColumnC2
import Erdos634.Draft.LaczFormalColumnBoundary
import Erdos634.Draft.LaczFormalColumnBase

/-!
# Aggregate: the Column Lemma layer (C1–C4), UNAUDITED

Credit: AI assistant (Column Lemma proposal), Beeson–Roșu, Beeson, Laczkovich.  New modules only; `LaczFormalMJ*` and
`LaczFormalWall*` are untouched.  Add `import Erdos634.Draft.LaczFormalAllColumn` to `AllLaczWalk` (one line) when the
audit has passed.
-/

#print axioms Erdos634.LaczCol.WFrame.MJ_main
#print axioms Erdos634.LaczCol.wall_T_rule
#print axioms Erdos634.LaczCol.C1_c_row
#print axioms Erdos634.LaczCol.C1_a_row
#print axioms Erdos634.LaczCol.C3_b_row
#print axioms Erdos634.LaczCol.C1_between_walls
#print axioms Erdos634.LaczCol.C1_c_cells
#print axioms Erdos634.LaczCol.C4_events
#print axioms Erdos634.LaczCol.C4_sharp
#print axioms Erdos634.LaczCol.ofLFrame
#print axioms Erdos634.LaczCol.control_wall_207
#print axioms Erdos634.LaczCol.grid_wallHyps
#print axioms Erdos634.LaczCol.grid_betaWall
#print axioms Erdos634.LaczCol.grid_C1_c
#print axioms Erdos634.LaczCol.grid_C1_a
#print axioms Erdos634.LaczCol.grid_C1_c_fails_at_e
#print axioms Erdos634.LaczCol.grid_C3_b
#print axioms Erdos634.LaczColumn.meet_param
#print axioms Erdos634.LaczColumn.wall_first_common
#print axioms Erdos634.LaczColumn.MJ_ka_unique
#print axioms Erdos634.LaczColumn.bfree_cover_c
#print axioms Erdos634.LaczColumn.bfree_cover_a
#print axioms Erdos634.LaczColumn.chord_second_cover
#print axioms Erdos634.LaczCol.C2_wall_segment
#print axioms Erdos634.LaczCol.C2_counts
#print axioms Erdos634.LaczCol.C2_no_common_below
#print axioms Erdos634.LaczCol.grid_TRule_exercised
#print axioms Erdos634.LaczCol.WFrame.TRule_iff
#print axioms Erdos634.LaczCol.boundary_T_rule
#print axioms Erdos634.LaczCol.grid_boundaryWall
#print axioms Erdos634.LaczCol.BoundaryWall.of_leg
#print axioms Erdos634.LaczCol.C4_bfree_counts
#print axioms Erdos634.LaczCol.grid_C4_hyps
#print axioms Erdos634.LaczCol.C1_counts_invariant
#print axioms Erdos634.LaczCol.grid_C1_counts
#print axioms Erdos634.LaczCol.FaultSeg.dist_counts
#print axioms Erdos634.LaczColumn.bfree_unique_below
#print axioms Erdos634.LaczCol.WFrame.MJ_main0

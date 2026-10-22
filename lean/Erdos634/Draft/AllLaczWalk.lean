-- Draft/AllLaczWalk.lean -- aggregate of the base-walk formalization of the band rules and Theorem U
-- (room LEAN_TAIL_2026-10-21).  Its closure contains SideRunGMain (AllThreshold): NOT imported by AllLacz or All.
import Erdos634.Draft.LaczFormalBandLemma
import Erdos634.Draft.LaczFormalWalkBase
import Erdos634.Draft.LaczFormalWalkTok
import Erdos634.Draft.LaczFormalWalkAssemble
import Erdos634.Draft.LaczFormalWalkCount
import Erdos634.Draft.LaczFormalWalkCorner
import Erdos634.Draft.LaczFormalWalkRun
import Erdos634.Draft.LaczFormalWalkRules
import Erdos634.Draft.LaczFormalUDims
import Erdos634.Draft.LaczFormalBand
import Erdos634.Draft.LaczFormalW2Interfaces
-- (room LEAN_W2_2026-10-21): fan successor lemma, I4 (wedge at G1), rule W2 (chord version), W2Rule_holds.
import Erdos634.Draft.LaczFormalFanSucc
import Erdos634.Draft.LaczFormalFanVertex
import Erdos634.Draft.LaczFormalFanFill
import Erdos634.Draft.LaczFormalW2Fan
import Erdos634.Draft.LaczFormalW2Tri
import Erdos634.Draft.LaczFormalW2G1
import Erdos634.Draft.LaczFormalW2Bridge
import Erdos634.Draft.LaczFormalW2Step1Tok
import Erdos634.Draft.LaczFormalW2Lines
import Erdos634.Draft.LaczFormalW2Chords
import Erdos634.Draft.LaczFormalW2P2
import Erdos634.Draft.LaczFormalW2Vec
import Erdos634.Draft.LaczFormalW2More
import Erdos634.Draft.LaczFormalW2Oriented
import Erdos634.Draft.LaczFormalW2Mirror
import Erdos634.Draft.LaczFormalW2Final
import Erdos634.Draft.LaczFormalW2Walk
import Erdos634.Draft.LaczFormalM2
import Erdos634.Draft.LaczFormalMJArith
import Erdos634.Draft.LaczFormalAllColumn
-- (room LEAN_MJ_2026-10-21): the rule M(j) for all j: lattice frame, rows, Claims Z and A, token bridge, MRule_holds, band_theorem_free.
import Erdos634.Draft.LaczFormalMJLat
import Erdos634.Draft.LaczFormalMJCell
import Erdos634.Draft.LaczFormalMJCover
import Erdos634.Draft.LaczFormalMJChord
import Erdos634.Draft.LaczFormalMJFig
import Erdos634.Draft.LaczFormalMJTile
import Erdos634.Draft.LaczFormalMJGround
import Erdos634.Draft.LaczFormalMJRow
import Erdos634.Draft.LaczFormalMJStage1
import Erdos634.Draft.LaczFormalMJStage2
import Erdos634.Draft.LaczFormalMJAdv
import Erdos634.Draft.LaczFormalMJBits
import Erdos634.Draft.LaczFormalMJZ
import Erdos634.Draft.LaczFormalMJZA
import Erdos634.Draft.LaczFormalMJZA2
import Erdos634.Draft.LaczFormalMJZA3
import Erdos634.Draft.LaczFormalMJMain
import Erdos634.Draft.LaczFormalMJBridge
import Erdos634.Draft.LaczFormalMJWalk
import Erdos634.Draft.LaczFormalMJFinal
-- (audit room band_gaps_2026-10-21): non-vacuity control for the rule M(j): genuine tilings satisfy the hypothesis package; tokOf default unused.
import Erdos634.Draft.LaczFormalMJControl
-- (room LEAN_CTRL2_2026-10-21): non-vacuity control for the cell predicates UpCell/DownCell/Ground/Std/TRule/ARule (bare lattice, grid dissection, explicit coordinates)
import Erdos634.Draft.LaczFormalMJBare
import Erdos634.Draft.LaczFormalMJGrid
import Erdos634.Draft.LaczFormalMJCellCtl
-- (room LEAN_WALL_2026-10-21): Wall Lemma layer: one-sided vertex figure at a wall, transversal non-straddling, grid control.
import Erdos634.Draft.LaczFormalWall
import Erdos634.Draft.LaczFormalWallCtl
-- (room LEAN_A_2026-10-21): Lemma A(j), the aBG^j run rule (thick analogue of M(j)): lattice induction, token bridge, AARule_holds. UNAUDITED.
import Erdos634.Draft.AllLaczA

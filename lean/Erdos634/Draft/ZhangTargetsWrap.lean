import Mathlib.Tactic
import Erdos634.ZhangTargets

/-!
Credit: the constructions are those of Y. X. Zhang, 'Tiling triangles with 2 pi/3 angles' (arXiv:2512.22696); the versions uniform in the tile are ours.
# rem:zhangsmall / rem:zhangsharp — Zhang target arithmetic: wrapper
   (PROVED, cited declarations VERIFIED)

Rows 60–61 of PAPER_MAP:
- `rem:zhangsmall`: each searched target holds exactly N tiles (Heron identities).
- `rem:zhangsharp`: the non-representable widths are exactly the gaps (Frobenius gaps).

All theorems in `ZhangTargets.lean` are `by decide`, kernel-certified, no axioms.
The paper's (3,5,7), (7,8,13), (5,16,19) triangle identities are certified here.

**These are VERIFIED** (cited declarations VERIFIED per PAPER_MAP row 60-61).
This wrapper simply re-exposes them under the `Draft` namespace.
-/

namespace Erdos634.Draft.ZhangTargetsWrap

open Erdos634.ZhangTargets

/-- (3,5,7) tile identity: 7²=3²+3·5+5². -/
theorem zhang_tile_357 : (7:Int)*7 = 3*3 + 3*5 + 5*5 :=
  tile_357

/-- Heron scaling for (3,5,7): equilateral row. -/
theorem zhang_heron_357_eq : heron 15 15 15 = 15*15 * heron 3 5 7 :=
  heron_357_equilateral

/-- Heron scaling for (3,5,7): row 24. -/
theorem zhang_heron_357_r24 : heron 15 21 24 = 24*24 * heron 3 5 7 :=
  heron_357_row24

/-- Heron scaling for (3,5,7): row 33. -/
theorem zhang_heron_357_r33 : heron 21 21 33 = 33*33 * heron 3 5 7 :=
  heron_357_row33

/-- (7,8,13) tile identity: 13²=7²+7·8+8². -/
theorem zhang_tile_7813 : (13:Int)*13 = 7*7 + 7*8 + 8*8 :=
  tile_7813

/-- Heron scaling for (7,8,13): equilateral. -/
theorem zhang_heron_7813_eq : heron 56 56 56 = 56*56 * heron 7 8 13 :=
  heron_7813_equilateral

/-- Frobenius gap: 3x+5y ≠ 4. -/
theorem zhang_frob_35_gap4 (x y : Nat) : 3*x + 5*y ≠ 4 :=
  frob_35_gap4 x y

/-- Frobenius gap: 3x+5y ≠ 7. -/
theorem zhang_frob_35_gap7 (x y : Nat) : 3*x + 5*y ≠ 7 :=
  frob_35_gap7 x y

/-- Frobenius representation: 3·1+5·1=8. -/
theorem zhang_frob_35_rep8 : 3*1 + 5*1 = 8 :=
  frob_35_rep8

/-- Frobenius gap: 7x+8y ≠ 13. -/
theorem zhang_frob_78_gap13 (x y : Nat) : 7*x + 8*y ≠ 13 :=
  frob_78_gap13 x y

/-- Frobenius representation: 7·1+8·1=15. -/
theorem zhang_frob_78_rep15 : 7*1 + 8*1 = 15 :=
  frob_78_rep15

#print axioms zhang_tile_357
#print axioms zhang_heron_357_eq
#print axioms zhang_frob_35_gap4
#print axioms zhang_frob_78_gap13

end Erdos634.Draft.ZhangTargetsWrap

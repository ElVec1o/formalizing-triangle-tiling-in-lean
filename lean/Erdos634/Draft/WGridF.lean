-- Draft/WGridF.lean — L5 of (private working notes, not included) §3: the (k+1)×(l+1) grid of the unit W-parallelogram
-- of L4 (WPgramF.pgramF).  Phi_F[0, F(F²-1)(k+1)] × [0,(2F²-1)(l+1)] tiled by 2(2f²-1)(k+1)(l+1) tiles
-- congruent to MF f.  Direct instance of the generic BrickGridF.grid (A = F(F²-1), B = 2F²-1).
-- f=2: A=6, B=7, 14(k+1)(l+1) tiles (= WGrid.grid).  UNAUDITED.  Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).
import Erdos634.Draft.WPgramF

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Sh Tset Rect RTiling.cast RTiling.castN)

namespace Erdos634.Draft.WGridF
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WPgramF

theorem A_pos (f : ℕ) (hf : 2 ≤ f) : 0 < (f : ℝ) * ((f : ℝ) ^ 2 - 1) := by
  have h := hF f hf; have := Erdos634.Draft.WBrickF.hA_pos h; nlinarith

theorem B_pos (f : ℕ) (hf : 2 ≤ f) : 0 < 2 * (f : ℝ) ^ 2 - 1 := by
  have h := hF f hf; nlinarith

/-- **L5.** The `(k+1)×(l+1)` grid of L4. -/
noncomputable def gridF (f : ℕ) (hf : 2 ≤ f) (k l : ℕ) :
    RTiling (Phi (f : ℝ) '' Rect 0 ((f : ℝ) * ((f : ℝ) ^ 2 - 1) * ((k : ℝ) + 1)) 0
        ((2 * (f : ℝ) ^ 2 - 1) * ((l : ℝ) + 1)))
      (Erdos634.Draft.WBrickF.MF (f : ℝ) (hF f hf)) (2 * (2 * f ^ 2 - 1) * (k + 1) * (l + 1)) :=
  Erdos634.Draft.BrickGridF.grid (hF f hf) (A_pos f hf) (B_pos f hf) (pgramF f hf) k l

/-- f = 2 sanity: the same shape as `WGrid.grid` up to the frame scale 1/8: `A = 6`, `B = 7`,
`14(k+1)(l+1)` tiles. -/
noncomputable example (k l : ℕ) :
    RTiling (Phi ((2 : ℕ) : ℝ) '' Rect 0 (((2 : ℕ) : ℝ) * (((2 : ℕ) : ℝ) ^ 2 - 1) * ((k : ℝ) + 1)) 0
        ((2 * ((2 : ℕ) : ℝ) ^ 2 - 1) * ((l : ℝ) + 1)))
      (Erdos634.Draft.WBrickF.MF ((2 : ℕ) : ℝ) (hF 2 le_rfl)) (14 * (k + 1) * (l + 1)) :=
  RTiling.castN (by norm_num) (gridF 2 le_rfl k l)

end Erdos634.Draft.WGridF

#print axioms Erdos634.Draft.WGridF.gridF

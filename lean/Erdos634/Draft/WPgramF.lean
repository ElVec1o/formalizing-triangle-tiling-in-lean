-- Draft/WPgramF.lean — L4 of (private working notes, not included) §3: the unit W-parallelogram for general f.
-- f : ℕ, f ≥ 2, F = (f:ℝ), a = F²-1, b = F.  Bricks: A-brick (a wide, f tall), B-brick (f wide, a tall).
-- DIMENSIONS (checked by hand; the scope-plan wording "f slabs of height a / one slab of height b"
-- has the heights swapped): the parallelogram is Phi_F[0, F·(F²-1)] × [0, 2F²-1] (f=2: 6×7 ✓.).
--   * bottom: f slabs of height b=F, each f A-bricks (width a) across width f·a; grid (f)×(f) of the
--     A-brick = Phi[0,a·f]×[0,F·f]: height f² , 2f² tiles.
--   * top: ONE slab of height a=f²-1, made of a B-bricks (width F) across width a·F: height a,
--     2(f²-1) tiles.   Total height f²+(f²-1)=2f²-1; total tiles 2f²+2(f²-1)=2(2f²-1)  ✓.
-- f=2: bottom 2 rows of two 3x2 bricks (8 tiles), top 3 bricks 2x3 (6 tiles): 14 = 2(2*4-1)  ✓.  UNAUDITED.
-- Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).
import Erdos634.Draft.BrickGridF

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Sh Tset Rect RTiling.cast RTiling.castN)

namespace Erdos634.Draft.WPgramF
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.BrickGridF
open Erdos634.Draft.WBrickF

theorem cast_f1 (f : ℕ) (hf : 2 ≤ f) : (((f - 1 : ℕ) : ℝ) + 1) = (f : ℝ) := by
  have : (f - 1 : ℕ) + 1 = f := by omega
  exact_mod_cast this

theorem cast_f2 (f : ℕ) (hf : 2 ≤ f) : (((f ^ 2 - 2 : ℕ) : ℝ) + 1) = (f : ℝ) ^ 2 - 1 := by
  have h : 2 ≤ f ^ 2 := by nlinarith
  have : (f ^ 2 - 2 : ℕ) + 2 = f ^ 2 := by omega
  have h2 : (((f ^ 2 - 2 : ℕ) : ℝ)) + 2 = (f : ℝ) ^ 2 := by exact_mod_cast this
  linarith

theorem hF (f : ℕ) (hf : 2 ≤ f) : (1 : ℝ) < (f : ℝ) := by
  have : (2 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf
  linarith

/-- **L4.** The unit W-parallelogram `Φ_f[0,f(f²-1)]×[0,2f²-1]` tiled by `2(2f²-1)` tiles
congruent to `MF f`. -/
noncomputable def pgramF (f : ℕ) (hf : 2 ≤ f) :
    RTiling (Phi (f : ℝ) '' Rect 0 ((f : ℝ) * ((f : ℝ) ^ 2 - 1)) 0 (2 * (f : ℝ) ^ 2 - 1))
      (MF (f : ℝ) (hF f hf)) (2 * (2 * f ^ 2 - 1)) := by
  have h1 := hF f hf
  have c1 := cast_f1 f hf
  have c2 := cast_f2 f hf
  have hfpos : (0 : ℝ) < (f : ℝ) := by linarith
  have hapos : (0 : ℝ) < (f : ℝ) ^ 2 - 1 := by nlinarith
  have hf2 : 2 ≤ f ^ 2 := by nlinarith
  -- bottom block: f×f grid of the A-brick
  have Bot := gridA h1 (f - 1) (f - 1)
  rw [c1] at Bot
  -- top slab: (f²-1)×1 grid of the B-brick
  have Top := gridB h1 (f ^ 2 - 2) 0
  rw [c2] at Top
  have Top' := shift_rect Top 0 ((f : ℝ) * (f : ℝ)) ((f : ℝ) * ((f : ℝ) ^ 2 - 1) + 0)
    ((f : ℝ) * (f : ℝ) + ((f : ℝ) ^ 2 - 1) * (((0 : ℕ) : ℝ) + 1)) (by ring) (by push_cast; ring)
  have eB : Rect 0 (((f : ℝ) ^ 2 - 1) * (f : ℝ)) 0 ((f : ℝ) * (f : ℝ))
      = Rect 0 ((f : ℝ) * ((f : ℝ) ^ 2 - 1)) 0 ((f : ℝ) * (f : ℝ)) := by rw [mul_comm]
  have eT : Rect 0 ((f : ℝ) * ((f : ℝ) ^ 2 - 1) + 0) ((f : ℝ) * (f : ℝ))
        ((f : ℝ) * (f : ℝ) + ((f : ℝ) ^ 2 - 1) * (((0 : ℕ) : ℝ) + 1))
      = Rect 0 ((f : ℝ) * ((f : ℝ) ^ 2 - 1)) ((f : ℝ) * (f : ℝ)) (2 * (f : ℝ) ^ 2 - 1) := by
    have h : (f : ℝ) * (f : ℝ) + ((f : ℝ) ^ 2 - 1) * (((0 : ℕ) : ℝ) + 1) = 2 * (f : ℝ) ^ 2 - 1 := by
      push_cast; ring
    rw [h, add_zero]
  have V := vstack h1 (a := 0) (b := (f : ℝ) * ((f : ℝ) ^ 2 - 1)) (c := 0) (d := (f : ℝ) * (f : ℝ))
    (e := 2 * (f : ℝ) ^ 2 - 1) (by positivity) (by nlinarith)
    (RTiling.cast (congrArg _ eB) Bot) (RTiling.cast (congrArg _ eT) Top')
  refine RTiling.castN ?_ V
  have e1 : f - 1 + 1 = f := by omega
  have e2 : f ^ 2 - 2 + 1 = f ^ 2 - 1 := by omega
  have e3 : 2 * (2 * f ^ 2 - 1) = 2 * f * f + 2 * (f ^ 2 - 1) := by
    zify [show 1 ≤ f ^ 2 by omega, show 1 ≤ 2 * f ^ 2 by omega]; ring
  rw [e3]
  simp only [e1, e2, zero_add, mul_one]

end Erdos634.Draft.WPgramF

#print axioms Erdos634.Draft.WPgramF.pgramF

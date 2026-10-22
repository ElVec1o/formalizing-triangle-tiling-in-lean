-- Draft/BrickGridF.lean — L3 of (private working notes, not included) §3: for any tiling R of the brick
-- Phi_f[0,A]x[0,B] by n tiles congruent to M, the (k+1)x(l+1) grid of translates tiles
-- Phi_f[0,A(k+1)]x[0,B(l+1)] by n(k+1)(l+1) tiles.  Also the f-parametric shift/hstack/vstack
-- (the WPgram versions are tied to the f=2 frame).  Mirrors WGrid.strip/grid.  UNAUDITED.
-- Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).
import Erdos634.Draft.WBrickF
import Erdos634.Draft.WPgram

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Sh Tset Rect RTiling.cast RTiling.castN Sh_Rect
  interior_disj_fst interior_disj_snd)

namespace Erdos634.Draft.BrickGridF
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling

noncomputable def shift_rect {f : ℝ} {A B : ℝ} {M : Tri} {N : ℕ}
    (R : RTiling (Phi f '' Rect 0 A 0 B) M N)
    (x y x2 y2 : ℝ) (hx : x2 = A + x) (hy : y2 = B + y) : RTiling (Phi f '' Rect x x2 y y2) M N := by
  have h := shiftR R (x, y)
  rw [Sh_Rect] at h
  simp only [zero_add] at h
  subst hx hy
  exact h

noncomputable def hstack {f : ℝ} (hf : 1 < f) {a b e c d : ℝ} {M : Tri} {N₁ N₂ : ℕ}
    (hab : a ≤ b) (hbe : b ≤ e)
    (R₁ : RTiling (Phi f '' Rect a b c d) M N₁) (R₂ : RTiling (Phi f '' Rect b e c d) M N₂) :
    RTiling (Phi f '' Rect a e c d) M (N₁ + N₂) := by
  have hd : Disjoint (interior (Phi f '' Rect a b c d)) (interior (Phi f '' Rect b e c d)) :=
    disjoint_image hf (interior_disj_fst b (fun p hp => hp.2.1) (fun p hp => hp.1))
  refine RTiling.cast ?_ (union R₁ R₂ hd)
  rw [← Set.image_union, Erdos634.Draft.WPgram.Rect_union_fst a b e c d hab hbe]

noncomputable def vstack {f : ℝ} (hf : 1 < f) {a b c d e : ℝ} {M : Tri} {N₁ N₂ : ℕ}
    (hcd : c ≤ d) (hde : d ≤ e)
    (R₁ : RTiling (Phi f '' Rect a b c d) M N₁) (R₂ : RTiling (Phi f '' Rect a b d e) M N₂) :
    RTiling (Phi f '' Rect a b c e) M (N₁ + N₂) := by
  have hd : Disjoint (interior (Phi f '' Rect a b c d)) (interior (Phi f '' Rect a b d e)) :=
    disjoint_image hf (interior_disj_snd d (fun p hp => hp.2.2.2) (fun p hp => hp.2.2.1))
  refine RTiling.cast ?_ (union R₁ R₂ hd)
  rw [← Set.image_union, Erdos634.Draft.WPgram.Rect_union_snd a b c d e hcd hde]

variable {f : ℝ} (hf : 1 < f) {A B : ℝ} (hA : 0 < A) (hB : 0 < B) {M : Tri} {n : ℕ}
  (R : RTiling (Phi f '' Rect 0 A 0 B) M n)

include hf hA in
/-- A horizontal strip of `k+1` copies of the brick. -/
noncomputable def strip : (k : ℕ) → RTiling (Phi f '' Rect 0 (A * ((k : ℝ) + 1)) 0 B) M (n * (k + 1))
  | 0 => RTiling.cast (by norm_num) (RTiling.castN (by norm_num) R)
  | k + 1 => by
      have s := shift_rect R (A * ((k : ℝ) + 1)) 0 (A * (((k + 1 : ℕ) : ℝ) + 1)) B
        (by push_cast; ring) (by norm_num)
      have h := hstack hf (by positivity)
        (by push_cast; nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) (strip k) s
      exact RTiling.castN (by ring) h

include hf hA hB in
/-- **L3.** The `(k+1) × (l+1)` grid of one brick type. -/
noncomputable def grid (k : ℕ) : (l : ℕ) →
    RTiling (Phi f '' Rect 0 (A * ((k : ℝ) + 1)) 0 (B * ((l : ℝ) + 1))) M (n * (k + 1) * (l + 1))
  | 0 => RTiling.cast (by norm_num) (RTiling.castN (by ring) (strip hf hA R k))
  | l + 1 => by
      have s := shift_rect (strip hf hA R k) 0 (B * ((l : ℝ) + 1)) (A * ((k : ℝ) + 1) + 0)
        (B * (((l + 1 : ℕ) : ℝ) + 1)) (by ring) (by push_cast; ring)
      simp only [add_zero] at s
      have h := vstack hf (by positivity)
        (by push_cast; nlinarith [(Nat.cast_nonneg l : (0 : ℝ) ≤ l)])
        (grid k l) s
      exact RTiling.castN (by ring) h

/-- Instance: `(k+1)×(l+1)` grid of the `(f²-1)×f` brick, `2(k+1)(l+1)` tiles congruent to
`(f,f²-1,f²)`. -/
noncomputable def gridA (hf : 1 < f) (k l : ℕ) :
    RTiling (Phi f '' Rect 0 ((f ^ 2 - 1) * ((k : ℝ) + 1)) 0 (f * ((l : ℝ) + 1)))
      (Erdos634.Draft.WBrickF.MF f hf) (2 * (k + 1) * (l + 1)) :=
  grid hf (Erdos634.Draft.WBrickF.hA_pos hf) (Erdos634.Draft.WBrickF.hf_pos hf)
    (Erdos634.Draft.WBrickF.brickA f hf) k l

/-- Instance: grid of the `f×(f²-1)` brick. -/
noncomputable def gridB (hf : 1 < f) (k l : ℕ) :
    RTiling (Phi f '' Rect 0 (f * ((k : ℝ) + 1)) 0 ((f ^ 2 - 1) * ((l : ℝ) + 1)))
      (Erdos634.Draft.WBrickF.MF f hf) (2 * (k + 1) * (l + 1)) :=
  grid hf (Erdos634.Draft.WBrickF.hf_pos hf) (Erdos634.Draft.WBrickF.hA_pos hf)
    (Erdos634.Draft.WBrickF.brickB f hf) k l

/-- f = 2: the (1,2) strip/grid shape (`A=3`, `B=2`) is recovered: `gridA 2` tiles
`Φ_2[0,3(k+1)]×[0,2(l+1)]` by `2(k+1)(l+1)` tiles. -/
noncomputable example (k l : ℕ) : RTiling (Phi 2 '' Rect 0 ((2 ^ 2 - 1) * ((k : ℝ) + 1)) 0 (2 * ((l : ℝ) + 1)))
    (Erdos634.Draft.WBrickF.MF 2 (by norm_num)) (2 * (k + 1) * (l + 1)) := gridA (by norm_num) k l

end Erdos634.Draft.BrickGridF

#print axioms Erdos634.Draft.BrickGridF.grid
#print axioms Erdos634.Draft.BrickGridF.gridA
#print axioms Erdos634.Draft.BrickGridF.gridB

-- Draft/WPgram.lean — step (b) of the 7m² plan: the unit W-parallelogram Φ[0,6]×[0,7] tiled by
-- 14 tiles (7 bricks: 4 of 3×2 in two rows, 3 of 2×3 in the top slab).  UNAUDITED.
import Erdos634.Draft.WBrick

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (s15 s15_pos s15_sq Sh Tset Rect RTiling.cast RTiling.castN Sh_Rect
  interior_disj_fst interior_disj_snd)

namespace Erdos634.Draft.WPgram
open Erdos634.Draft.WFrame Erdos634.Draft.RegionTiling Erdos634.Draft.WBrick

/-- Translate a rectangle tiling. -/
noncomputable def shift_rect {A B : ℝ} {M : Tri} {N : ℕ} (R : RTiling (Phi '' Rect 0 A 0 B) M N)
    (x y x2 y2 : ℝ) (hx : x2 = A + x) (hy : y2 = B + y) : RTiling (Phi '' Rect x x2 y y2) M N := by
  have h := shiftR R (x, y)
  rw [show Erdos634.Draft.WFrame.Sh (x, y) (Rect 0 A 0 B) = Erdos634.Draft.CollarParam.Sh (x, y) (Rect 0 A 0 B) from rfl,
    Sh_Rect] at h
  simp only [zero_add] at h
  subst hx hy
  exact h

theorem Rect_union_fst (a b e c d : ℝ) (hab : a ≤ b) (hbe : b ≤ e) :
    Rect a b c d ∪ Rect b e c d = Rect a e c d := by
  ext p
  simp only [Rect, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro (⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩)
    · exact ⟨h1, by linarith, h3, h4⟩
    · exact ⟨by linarith, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    by_cases h : p.1 ≤ b
    · exact Or.inl ⟨h1, h, h3, h4⟩
    · exact Or.inr ⟨by linarith, h2, h3, h4⟩

theorem Rect_union_snd (a b c d e : ℝ) (hcd : c ≤ d) (hde : d ≤ e) :
    Rect a b c d ∪ Rect a b d e = Rect a b c e := by
  ext p
  simp only [Rect, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro (⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩)
    · exact ⟨h1, h2, h3, by linarith⟩
    · exact ⟨h1, h2, by linarith, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    by_cases h : p.2 ≤ d
    · exact Or.inl ⟨h1, h2, h3, h⟩
    · exact Or.inr ⟨h1, h2, by linarith, h4⟩

noncomputable def hstack {a b e c d : ℝ} {M : Tri} {N₁ N₂ : ℕ} (hab : a ≤ b) (hbe : b ≤ e)
    (R₁ : RTiling (Phi '' Rect a b c d) M N₁) (R₂ : RTiling (Phi '' Rect b e c d) M N₂) :
    RTiling (Phi '' Rect a e c d) M (N₁ + N₂) := by
  have hd : Disjoint (interior (Phi '' Rect a b c d)) (interior (Phi '' Rect b e c d)) :=
    disjoint_image (interior_disj_fst b (fun p hp => hp.2.1) (fun p hp => hp.1))
  refine RTiling.cast ?_ (union R₁ R₂ hd)
  rw [← Set.image_union, Rect_union_fst a b e c d hab hbe]

noncomputable def vstack {a b c d e : ℝ} {M : Tri} {N₁ N₂ : ℕ} (hcd : c ≤ d) (hde : d ≤ e)
    (R₁ : RTiling (Phi '' Rect a b c d) M N₁) (R₂ : RTiling (Phi '' Rect a b d e) M N₂) :
    RTiling (Phi '' Rect a b c e) M (N₁ + N₂) := by
  have hd : Disjoint (interior (Phi '' Rect a b c d)) (interior (Phi '' Rect a b d e)) :=
    disjoint_image (interior_disj_snd d (fun p hp => hp.2.2.2) (fun p hp => hp.2.2.1))
  refine RTiling.cast ?_ (union R₁ R₂ hd)
  rw [← Set.image_union, Rect_union_snd a b c d e hcd hde]

/-- **Step (b).** The unit W-parallelogram: 14 tiles. -/
noncomputable def pgram6x7 : RTiling (Phi '' Rect 0 6 0 7) MW 14 := by
  have s1 := shift_rect brick32 0 0 3 2 (by norm_num) (by norm_num)
  have s2 := shift_rect brick32 3 0 6 2 (by norm_num) (by norm_num)
  have s3 := shift_rect brick32 0 2 3 4 (by norm_num) (by norm_num)
  have s4 := shift_rect brick32 3 2 6 4 (by norm_num) (by norm_num)
  have t1 := shift_rect brick23 0 4 2 7 (by norm_num) (by norm_num)
  have t2 := shift_rect brick23 2 4 4 7 (by norm_num) (by norm_num)
  have t3 := shift_rect brick23 4 4 6 7 (by norm_num) (by norm_num)
  have row1 := hstack (by norm_num) (by norm_num) s1 s2
  have row2 := hstack (by norm_num) (by norm_num) s3 s4
  have top := hstack (by norm_num) (by norm_num) (hstack (by norm_num) (by norm_num) t1 t2) t3
  have low := vstack (by norm_num) (by norm_num) row1 row2
  exact RTiling.castN (by norm_num) (vstack (by norm_num) (by norm_num) low top)

end Erdos634.Draft.WPgram

#print axioms Erdos634.Draft.WPgram.pgram6x7

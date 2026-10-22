-- Draft/WAddF.lean — L6 of (private working notes, not included) §3: W-addition for general f.  With A = F(F²-1),
-- B = 2F²-1 (F = (f:ℝ)) and
--   Wt m = {p | p1 ≤ A m, p2 ≤ B m, A B m ≤ B p1 + A p2}   (vertices (Am,0),(Am,Bm),(0,Bm)),
--   Wt (m1+m2) = Sh(A m2,0)(Wt m1) ∪ Rect(A m2..A(m1+m2), B m1..B(m1+m2)) ∪ Sh(0,B m1)(Wt m2).
-- Count: N1 + 2B m1 m2 + N2, so N = B m² ((2f²-1)m²) is closed under sums.  f=2: A=6,B=7 (WAdd.Wt).
-- `WClosed` records the closure; NO base case is claimed here (W_1 itself is L7/L8).  UNAUDITED.
-- Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).
import Erdos634.Draft.WGridF

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Sh Tset Rect RTiling.cast RTiling.castN
  interior_disj_fst interior_disj_snd)

namespace Erdos634.Draft.WAddF
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WPgramF Erdos634.Draft.WGridF
open Erdos634.Draft.BrickGridF (shift_rect)

/-- The skew right triangle `W_m` with legs `A m`, `B m`. -/
def Wt (A B m : ℝ) : Set (ℝ × ℝ) := {p | p.1 ≤ A * m ∧ p.2 ≤ B * m ∧ A * B * m ≤ B * p.1 + A * p.2}

theorem Wt_add (A B m1 m2 : ℝ) (hA : 0 < A) (hB : 0 < B) (h1 : 0 ≤ m1) (h2 : 0 ≤ m2) :
    (Sh (A * m2, 0) (Wt A B m1) ∪ Rect (A * m2) (A * (m1 + m2)) (B * m1) (B * (m1 + m2)))
      ∪ Sh (0, B * m1) (Wt A B m2) = Wt A B (m1 + m2) := by
  have a1 : 0 ≤ A * m1 := by positivity
  have a2 : 0 ≤ A * m2 := by positivity
  have b1 : 0 ≤ B * m1 := by positivity
  have b2 : 0 ≤ B * m2 := by positivity
  ext p
  simp only [Sh, Wt, Rect, Set.mem_union, Set.mem_setOf_eq, Prod.fst_sub, Prod.snd_sub, sub_zero]
  constructor
  · rintro ((⟨a, b, c⟩ | ⟨a, b, c, d⟩) | ⟨a, b, c⟩)
    · refine ⟨by linarith, by linarith, by nlinarith⟩
    · have e1 : A * B * m2 ≤ B * p.1 := by nlinarith
      have e2 : A * B * m1 ≤ A * p.2 := by nlinarith
      exact ⟨b, d, by nlinarith⟩
    · refine ⟨by linarith, by linarith, by nlinarith⟩
  · rintro ⟨a, b, c⟩
    by_cases hp2 : p.2 ≤ B * m1
    · left; left; exact ⟨by linarith, hp2, by nlinarith⟩
    · by_cases hp1 : A * m2 ≤ p.1
      · left; right; exact ⟨hp1, a, by linarith, b⟩
      · right; refine ⟨by linarith, by linarith, by nlinarith⟩

/-- **L6 (region tiling).** `W_{m1+m2}` from `W_{m1}`, `W_{m2}` and the `(m1)×(m2)` grid, with
`m1 = k+1`, `m2 = l+1`. -/
noncomputable def waddF (f : ℕ) (hf : 2 ≤ f) (k l : ℕ) {N₁ N₂ : ℕ}
    (RA : RTiling (Phi (f : ℝ) '' Wt ((f : ℝ) * ((f : ℝ) ^ 2 - 1)) (2 * (f : ℝ) ^ 2 - 1) ((k : ℝ) + 1))
      (Erdos634.Draft.WBrickF.MF (f : ℝ) (hF f hf)) N₁)
    (RB : RTiling (Phi (f : ℝ) '' Wt ((f : ℝ) * ((f : ℝ) ^ 2 - 1)) (2 * (f : ℝ) ^ 2 - 1) ((l : ℝ) + 1))
      (Erdos634.Draft.WBrickF.MF (f : ℝ) (hF f hf)) N₂) :
    RTiling (Phi (f : ℝ) '' Wt ((f : ℝ) * ((f : ℝ) ^ 2 - 1)) (2 * (f : ℝ) ^ 2 - 1)
        (((k : ℝ) + 1) + ((l : ℝ) + 1)))
      (Erdos634.Draft.WBrickF.MF (f : ℝ) (hF f hf))
      (N₁ + 2 * (2 * f ^ 2 - 1) * (k + 1) * (l + 1) + N₂) := by
  have h1 := hF f hf
  set A : ℝ := (f : ℝ) * ((f : ℝ) ^ 2 - 1) with hAdef
  set B : ℝ := 2 * (f : ℝ) ^ 2 - 1 with hBdef
  have hA : 0 < A := A_pos f hf
  have hB : 0 < B := B_pos f hf
  set m1 : ℝ := (k : ℝ) + 1 with hm1
  set m2 : ℝ := (l : ℝ) + 1 with hm2
  have p1 : 0 ≤ m1 := by positivity
  have p2 : 0 ≤ m2 := by positivity
  have hAt := shiftR RA (A * m2, 0)
  have hG := shift_rect (gridF f hf k l) (A * m2) (B * m1) (A * (m1 + m2)) (B * (m1 + m2))
    (by rw [hm1, hm2]; ring) (by rw [hm1, hm2]; ring)
  have hC := shiftR RB (0, B * m1)
  have hd1 : Disjoint (interior (Phi (f : ℝ) '' Sh (A * m2, 0) (Wt A B m1)))
      (interior (Phi (f : ℝ) '' Rect (A * m2) (A * (m1 + m2)) (B * m1) (B * (m1 + m2)))) := by
    refine disjoint_image h1 (interior_disj_snd (B * m1) ?_ ?_)
    · rintro p ⟨a, b, c⟩; simp only [Prod.snd_sub, sub_zero] at b; exact b
    · rintro p ⟨a, b, c, d⟩; exact c
  have hd2 : Disjoint (interior (Phi (f : ℝ) '' Sh (A * m2, 0) (Wt A B m1) ∪
        Phi (f : ℝ) '' Rect (A * m2) (A * (m1 + m2)) (B * m1) (B * (m1 + m2))))
      (interior (Phi (f : ℝ) '' Sh (0, B * m1) (Wt A B m2))) := by
    rw [← Set.image_union]
    refine disjoint_image h1 (interior_disj_fst (A * m2) ?_ ?_).symm
    · rintro p ⟨a, b, c⟩; simp only [Prod.fst_sub, sub_zero] at a; exact a
    · rintro p (⟨a, b, c⟩ | ⟨a, b, c, d⟩)
      · simp only [Prod.fst_sub, Prod.snd_sub, sub_zero] at a b c; nlinarith
      · exact a
  have U := union (union hAt hG hd1) hC hd2
  refine RTiling.castN (by ring) (RTiling.cast ?_ U)
  rw [← Set.image_union, ← Set.image_union, Wt_add A B m1 m2 hA hB p1 p2]

/-- W-closure: `W_m` (`m ≥ 1` natural) admits a tiling by `(2f²-1) m²` tiles congruent to `MF f`. -/
def WClosed (f : ℕ) (hf : 2 ≤ f) (m : ℕ) : Prop :=
  Nonempty (RTiling (Phi (f : ℝ) '' Wt ((f : ℝ) * ((f : ℝ) ^ 2 - 1)) (2 * (f : ℝ) ^ 2 - 1) (m : ℝ))
    (Erdos634.Draft.WBrickF.MF (f : ℝ) (hF f hf)) ((2 * f ^ 2 - 1) * m ^ 2))

/-- **L6 (closure under sums).** -/
theorem WClosed_add (f : ℕ) (hf : 2 ≤ f) {m₁ m₂ : ℕ} (h1 : 1 ≤ m₁) (h2 : 1 ≤ m₂)
    (H1 : WClosed f hf m₁) (H2 : WClosed f hf m₂) : WClosed f hf (m₁ + m₂) := by
  obtain ⟨R1⟩ := H1
  obtain ⟨R2⟩ := H2
  obtain ⟨k, rfl⟩ : ∃ k, m₁ = k + 1 := ⟨m₁ - 1, by omega⟩
  obtain ⟨l, rfl⟩ : ∃ l, m₂ = l + 1 := ⟨m₂ - 1, by omega⟩
  have e1 : (((k + 1 : ℕ)) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  have e2 : (((l + 1 : ℕ)) : ℝ) = (l : ℝ) + 1 := by push_cast; ring
  rw [e1] at R1
  rw [e2] at R2
  have R := waddF f hf k l R1 R2
  have e : (((k + 1 + (l + 1) : ℕ)) : ℝ) = ((k : ℝ) + 1) + ((l : ℝ) + 1) := by push_cast; ring
  unfold WClosed
  rw [e]
  exact ⟨RTiling.castN (by ring) R⟩

end Erdos634.Draft.WAddF

#print axioms Erdos634.Draft.WAddF.Wt_add
#print axioms Erdos634.Draft.WAddF.waddF
#print axioms Erdos634.Draft.WAddF.WClosed_add

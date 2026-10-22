-- Draft/LaczFormalIIcSharp2.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2-6.3, repair of the hStrn gap (AI assistant plan IIC_STRN.md, S2): a point lies in the open side of at most one side of a triangle.
-- `tri_inner_side_unique`: `Y` in `openSegment (T.pts a) (T.pts b)` and in `openSegment (T.pts a') (T.pts b')` (`a != b`, `a' != b'`) gives `{a,b} = {a',b'}`.  Barycentric coordinates (`coord_lineSeg`): the coordinates of `Y` that are positive are exactly `a`, `b`.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2-6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG12GExcCapT1

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

set_option synthInstance.maxSize 4000 in
theorem fin3_pair_eq : ∀ a b a' b' : Fin 3, a ≠ b → a' ≠ b' → (∀ m : Fin 3, (m = a ∨ m = b) ↔ (m = a' ∨ m = b')) → (a = a' ∧ b = b') ∨ (a = b' ∧ b = a') := by decide

/-- The positive barycentric coordinates of an open-side point are exactly the two endpoints. -/
theorem coord_pos_iff (T : Tri) {A B Y : Plane} {a b : Fin 3} (hab : a ≠ b) (hA : T.pts a = A) (hB : T.pts b = B) (hY : Y ∈ openSegment ℝ A B) (m : Fin 3) :
    0 < T.basis.coord m Y ↔ (m = a ∨ m = b) := by
  obtain ⟨σ, h0, h1, hYσ⟩ := openSegment_param hY
  have hc := coord_lineSeg T m a b hA hB (σ := σ)
  rw [← hYσ] at hc
  by_cases hma : m = a
  · have hv : T.basis.coord m Y = 1 - σ := by
      rw [hc]; subst hma; simp [hab]; ring
    rw [hv]; exact ⟨fun _ => Or.inl hma, fun _ => by linarith⟩
  · by_cases hmb : m = b
    · have hv : T.basis.coord m Y = σ := by
        rw [hc]; subst hmb; simp [hma]
      rw [hv]; exact ⟨fun _ => Or.inr hmb, fun _ => h0⟩
    · have hv : T.basis.coord m Y = 0 := by
        rw [hc]; simp [hma, hmb]
      rw [hv]
      exact ⟨fun h => absurd h (lt_irrefl 0), fun h => by rcases h with h | h <;> contradiction⟩

/-- **S2.** Two open sides of one triangle containing the same point coincide (as unordered pairs of vertex indices). -/
theorem tri_inner_side_unique (T : Tri) {A B A' B' Y : Plane} {a b a' b' : Fin 3} (hab : a ≠ b) (hab' : a' ≠ b')
    (hA : T.pts a = A) (hB : T.pts b = B) (hA' : T.pts a' = A') (hB' : T.pts b' = B')
    (hY : Y ∈ openSegment ℝ A B) (hY' : Y ∈ openSegment ℝ A' B') :
    (a = a' ∧ b = b') ∨ (a = b' ∧ b = a') := by
  apply fin3_pair_eq a b a' b' hab hab'
  intro m
  rw [← coord_pos_iff T hab hA hB hY m, ← coord_pos_iff T hab' hA' hB' hY' m]

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.tri_inner_side_unique

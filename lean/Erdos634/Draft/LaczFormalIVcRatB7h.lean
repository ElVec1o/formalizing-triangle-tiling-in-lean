-- Draft/LaczFormalIVcRatB7h.lean -- Laczkovich DCG 48 (2012), Sect. 8.3 (Subcase IVc, rational branch), BLUEPRINT Part B, item B7, stage h: THE STEP LEMMA (core).
--   `Box F z`: z lies in the open box (-1,0) x (0,1) of the frame F = (U; p, q), i.e. in the interior of the rhombus U - p + [0,1] p + [0,1] q.
--   `VWTiling.step_core`: T a VWTiling of a convex A inside {fb >= 0}, U = F.pt 0 0 in A, a point of A with fa > 0 (so U is approached from the sector fa > 0), kites miss the box, every rhombus misses the box or
--   lies in {fa <= 0}, and U is a vertex of every cell through U that has a point with fa > 0 (`hvert`; supplied by `vertex_of_corner` for the corner X, or by `vertex_of_second_cell` along the side).
--   Then some rhombus piece of T is exactly Par U p q (the parallelogram U + [0,1] p + [0,1] q).  Route: `exists_cell_at` (B7g) gives the cell c0, `cell_labels` its frame triangle, `kite_cell_excluded` (B7f) excludes a kite,
--   `rhomb_cell0/1_identify` (B7e) identify the rhombus.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 8.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIVcRatB7g

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

/-- The open box `(-1,0) x (0,1)` of the frame. -/
def Box {b : ℝ} (F : Frame b) (z : Plane) : Prop := -1 < F.fa z ∧ F.fa z < 0 ∧ 0 < F.fb z ∧ F.fb z < 1

namespace VWTiling
variable {b : ℝ} {A : Set Plane} {ιK ιR : Type} [Fintype ιK] [Fintype ιR] (T : VWTiling b A ιK ιR)

theorem K_subset (k : ιK) : (T.K k).set ⊆ A := fun y hy => by rw [← T.cover]; exact Or.inl (Set.mem_iUnion.mpr ⟨k, hy⟩)
theorem R_subset (r : ιR) : (T.R r).set ⊆ A := fun y hy => by rw [← T.cover]; exact Or.inr (Set.mem_iUnion.mpr ⟨r, hy⟩)

/-- **B7h.** -/
theorem step_core (hb : 0 < b) (hconv : Convex ℝ A) (F : Frame b) (hbel : ∀ y ∈ A, 0 ≤ F.fb y) (hUA : F.pt 0 0 ∈ A)
    {y : Plane} (hyA : y ∈ A) (hya : 0 < F.fa y)
    (hPK : ∀ k, ∀ z ∈ (T.K k).set, ¬ Box F z)
    (hPR : ∀ r, (∀ z ∈ (T.R r).set, ¬ Box F z) ∨ (∀ z ∈ (T.R r).set, F.fa z ≤ 0))
    (hvert : ∀ c : CellIdx ιK ιR, F.pt 0 0 ∈ (T.cellT c).carrier → (∃ z ∈ (T.cellT c).carrier, 0 < F.fa z) →
      ∃ j, (T.cellT c).pts j = F.pt 0 0) :
    ∃ r, (T.R r).set = Par F.U0 F.U1 F.p0 F.p1 F.q0 F.q1 := by
  obtain ⟨c, hUc, z, hz, hzpos⟩ := T.exists_cell_at hb hconv F hUA hyA hya
  obtain ⟨j0, hj0⟩ := hvert c hUc ⟨z, hz, hzpos⟩
  have hcg := T.cell_congruent hb c
  rcases c with ⟨k, i⟩ | ⟨r, i⟩
  · exfalso
    have hsub : ((T.K k).cell i).carrier ⊆ (T.K k).set := (T.K k).cell_subset i
    obtain ⟨a0, b0, a1, b1, a2, b2, hl0, hl1, hl2, d01, d02, d12, hp0, hp1, hp2⟩ :=
      cell_labels F hb ((T.K k).cell i) hcg ⟨j0, hj0⟩ (fun y hy => hbel y (T.K_subset k (hsub hy)))
        (fun y hy hbox => hPK k y (hsub hy) hbox)
    have h10 : F.pt 1 0 ∈ ((T.K k).cell i).carrier := by
      rcases hl0 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hl1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        rcases hl2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        first | exact absurd ⟨rfl, rfl⟩ d01 | exact absurd ⟨rfl, rfl⟩ d02 | exact absurd ⟨rfl, rfl⟩ d12 |
          (have := pts_mem ((T.K k).cell i) 0; rwa [hp0] at this) | (have := pts_mem ((T.K k).cell i) 1; rwa [hp1] at this) |
          (have := pts_mem ((T.K k).cell i) 2; rwa [hp2] at this)
    exact T.kite_cell_excluded hb hconv F hbel k i hUc h10
  · have hsub : ((T.R r).cell i).carrier ⊆ (T.R r).set := (T.R r).cell_subset i
    have hmissR : ∀ y ∈ (T.R r).set, ¬ (-1 < F.fa y ∧ F.fa y < 0 ∧ 0 < F.fb y ∧ F.fb y < 1) := by
      rcases hPR r with h | h
      · exact h
      · exact absurd (h z (hsub hz)) (not_le.mpr hzpos)
    obtain ⟨a0, b0, a1, b1, a2, b2, hl0, hl1, hl2, d01, d02, d12, hp0, hp1, hp2⟩ :=
      cell_labels F hb ((T.R r).cell i) hcg ⟨j0, hj0⟩ (fun y hy => hbel y (T.R_subset r (hsub hy)))
        (fun y hy => hmissR y (hsub hy))
    refine ⟨r, ?_⟩
    have hbelR : ∀ y ∈ (T.R r).set, 0 ≤ F.fb y := fun y hy => hbel y (T.R_subset r hy)
    fin_cases i
    · exact rhomb_cell0_identify F hb (T.R r) hl0 hl1 hl2 d01 d02 d12 hp0 hp1 hp2 hbelR hmissR
    · exact rhomb_cell1_identify F hb (T.R r) hl0 hl1 hl2 d01 d02 d12 hp0 hp1 hp2 hbelR hmissR

end VWTiling

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.VWTiling.step_core

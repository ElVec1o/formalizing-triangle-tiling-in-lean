-- Draft/LaczFormalBZL7h6.lean -- Beeson (arXiv 1206.1974v7) Lemma 10.5 (G5), bridges: a tile STEP along a line `d` at a vertex `Q` is a SECTOR of the fan at `Q` (start arm / end arm, length of the side),
--   and the count of corner pairs at a boundary vertex equals the number of non-alpha corner sectors.  UNAUDITED.
-- Credit: Beeson (arXiv 1206.1974v7, Lemma 10.5), Laczkovich (DCG 48 (2012), Sect. 4: fans, half-fan lemma), Beeson-Zhang.
import Erdos634.Draft.LaczFormalBZL7h5
import Erdos634.Draft.LaczFormalRGHead2
import Erdos634.Draft.LaczFormalRGBdy2

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

theorem par_neg_neg {u v : V2} (h : Par u v) : Par (-u.1, -u.2) (-v.1, -v.2) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩ <;> [skip; skip] <;> unfold crs dt at * <;> simp only at * <;> nlinarith [h1, h2]

/-- A step starting at `Q` along `d` is the start arm of a corner sector of any fan at `Q`; the arm is the side. -/
theorem step_start_sector {D : RegionDissection N} {Q : Plane} {κ : Type} [Fintype κ] (F : ExtFan D Q κ) {j : Fin N} {d : V2} {U' : Plane}
    (hS : TriStep (D.tile j) d Q U') :
    ∃ s : AtV D Q, s.1 = j ∧ Par (F.p s) d ∧ 0 < crs (F.p s) (F.q s) ∧ F.p s = toV2 (U' - Q) := by
  classical
  obtain ⟨kk0, f, g, hk0, hf, hfk, hgk, hgf, hpar, hleft⟩ := id hS
  have hmem : Q ∈ (D.tile j).carrier := hk0 ▸ subset_convexHull ℝ _ ⟨kk0, rfl⟩
  set s : AtV D Q := ⟨j, hmem⟩
  have hvert : ∃ k, (D.tile j).pts k = Q := ⟨kk0, hk0⟩
  obtain ⟨kk2, fl2, hk2, hp2, hq2⟩ := spec_corner_data (F.hspec s) hvert
  have hps : Par (F.p s) d := triStep_start hS kk2 fl2 hk2 hp2 hq2 (F.hok s)
  refine ⟨s, rfl, hps, crs_pos_of_corner (F.hok s) (F.hspec s) hvert, ?_⟩
  have hkk : kk0 = kk2 := (D.tile j).indep.injective (hk0.trans hk2.symm)
  subst hkk
  have hff : armP kk0 fl2 = f := by
    apply arm_unique (D.tile j) Q kk0 hk0 (armP kk0 fl2) f (armP_ne kk0 fl2) hfk d
    · rw [← hp2]; exact hps
    · rw [hf]; exact hpar
  rw [hp2, hff, hf]

/-- A step ending at `Q` along `d` is the end arm of a corner sector of any fan at `Q`; the arm is the side. -/
theorem step_end_sector {D : RegionDissection N} {Q : Plane} {κ : Type} [Fintype κ] (F : ExtFan D Q κ) {j : Fin N} {d : V2} {U : Plane}
    (hS : TriStep (D.tile j) d U Q) :
    ∃ s : AtV D Q, s.1 = j ∧ Par (F.q s) (-d.1, -d.2) ∧ 0 < crs (F.p s) (F.q s) ∧ F.q s = toV2 (U - Q) := by
  classical
  obtain ⟨kk0, f, g, hk0, hf, hfk, hgk, hgf, hpar, hleft⟩ := id hS
  have hmem : Q ∈ (D.tile j).carrier := hf ▸ subset_convexHull ℝ _ ⟨f, rfl⟩
  set s : AtV D Q := ⟨j, hmem⟩
  have hvert : ∃ k, (D.tile j).pts k = Q := ⟨f, hf⟩
  obtain ⟨kk2, fl2, hk2, hp2, hq2⟩ := spec_corner_data (F.hspec s) hvert
  have hqs : Par (F.q s) (-d.1, -d.2) := triStep_end hS kk2 fl2 hk2 hp2 hq2 (F.hok s)
  refine ⟨s, rfl, hqs, crs_pos_of_corner (F.hok s) (F.hspec s) hvert, ?_⟩
  have hkk : f = kk2 := (D.tile j).indep.injective (hf.trans hk2.symm)
  subst hkk
  have hP : Par (toV2 (U - Q)) (-d.1, -d.2) := by
    have h1 := par_neg_neg hpar
    have e : toV2 (U - Q) = (-(toV2 (Q - U)).1, -(toV2 (Q - U)).2) := by unfold toV2; ext <;> simp
    rw [e]; exact h1
  have hff : armQ f fl2 = kk0 := by
    apply arm_unique (D.tile j) Q f hf (armQ f fl2) kk0 (armQ_ne f fl2) hfk.symm (-d.1, -d.2)
    · rw [← hq2]; exact hqs
    · rw [hk0]; exact hP
  rw [hq2, hff, hk0]

end Erdos634.Draft.LaczFormal.RG

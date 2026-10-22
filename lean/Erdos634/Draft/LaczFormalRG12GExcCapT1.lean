-- Draft/LaczFormalRG12GExcCapT1.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2, repair of the PRINT GAP of L9 (exceptional point inside a tile side): the sector of a tile with `V` inside a side of a step has a ray along the step direction.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG12GExcCapMain
import Erdos634.Draft.CentroidSplit

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

theorem coord_lineSeg (T : Tri) (m : Fin 3) {A B : Plane} {σ : ℝ} (kk f : Fin 3) (hk : T.pts kk = A) (hf : T.pts f = B) :
    T.basis.coord m (A + σ • (B - A)) = (if m = kk then 1 else 0) + σ * ((if m = f then 1 else 0) - (if m = kk then 1 else 0)) := by
  have h1 : A + σ • (B - A) = AffineMap.lineMap A B σ := by
    rw [AffineMap.lineMap_apply]; simp [vsub_eq_sub, vadd_eq_add, add_comm]
  have ca : T.basis.coord m A = if m = kk then 1 else 0 := by
    rw [← hk]; exact Erdos634.Draft.CentroidSplit.coord_pts T m kk
  have cb : T.basis.coord m B = if m = f then 1 else 0 := by
    rw [← hf]; exact Erdos634.Draft.CentroidSplit.coord_pts T m f
  rw [h1, AffineMap.apply_lineMap, ca, cb, AffineMap.lineMap_apply]
  simp [vsub_eq_sub, vadd_eq_add]
  ring

theorem side_of_opposite (T : Tri) (m kk f : Fin 3) (hmk : m ≠ kk) (hmf : m ≠ f) (hfk : f ≠ kk) :
    T.pts (m + 2) - T.pts (m + 1) = T.pts f - T.pts kk ∨ T.pts (m + 2) - T.pts (m + 1) = T.pts kk - T.pts f := by
  fin_cases m <;> fin_cases kk <;> fin_cases f <;> first | (exfalso; simp_all; done) | (left; rfl) | (right; rfl)

/-- A tile with `V` inside the side of one of its steps of direction `d` has a sector at `V` with a ray along `d`. -/
theorem sec_inner {D : RegionDissection N} {V : Plane} {κ : Type} [Fintype κ] (F : ExtFan D V κ) {i : Fin N} {d : V2} {A B : Plane}
    (hS : TriStep (D.tile i) d A B) (hY : V ∈ openSegment ℝ A B) :
    ∃ x : AtV D V, x.1 = i ∧ (Par (F.p x) d ∨ Par (F.q x) d) := by
  obtain ⟨σ, h0, h1, hVσ⟩ := openSegment_param hY
  obtain ⟨hmem, hnv, -⟩ := step_interior_pt hS h0 h1
  rw [← hVσ] at hmem hnv
  refine ⟨⟨i, hmem⟩, rfl, ?_⟩
  rcases F.hspec ⟨i, hmem⟩ with ⟨k, hk, -⟩ | ⟨-, m, hm0, -, hq, hp⟩
  · exact absurd hk (hnv k)
  · obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar, hleft⟩ := hS
    have hc := coord_lineSeg (D.tile i) m kk f hk hf (σ := σ)
    rw [← hVσ] at hc
    have hmk : m ≠ kk := by
      intro h; subst h
      have : (D.tile i).basis.coord m V = 1 + σ * ((if m = f then 1 else 0) - 1) := by simpa using hc
      rw [hm0] at this
      by_cases hmf : m = f
      · exact hfk hmf.symm
      · simp [hmf] at this; linarith
    have hmf : m ≠ f := by
      intro h; subst h
      have : (D.tile i).basis.coord m V = (if m = kk then 1 else 0) + σ * (1 - (if m = kk then 1 else 0)) := by simpa using hc
      rw [hm0] at this
      simp [hmk] at this; linarith
    have hside := side_of_opposite (D.tile i) m kk f hmk hmf hfk
    rw [hk, hf] at hside
    have hneg : ∀ X Y : Plane, ((-(toV2 (X - Y)).1, -(toV2 (X - Y)).2) : V2) = toV2 (Y - X) := by
      intro X Y; simp [toV2]
    have hneg' : ∀ X Y : Plane, toV2 (-(X - Y)) = toV2 (Y - X) := by intro X Y; rw [neg_sub]
    have hpar' := hpar
    simp only at hp hq
    rcases hp with hp | hp
    · rcases hside with hs | hs
      · rw [hs] at hp; left; rw [hp]; exact hpar'
      · rw [hs] at hp; right; rw [hq, hp, hneg]; exact hpar'
    · rw [← neg_sub] at hp
      rcases hside with hs | hs
      · rw [hs] at hp
        right; rw [hq, hp]
        have : ((-(toV2 (-(B - A))).1, -(toV2 (-(B - A))).2) : V2) = toV2 (B - A) := by simp [toV2]
        rw [this]; exact hpar'
      · rw [hs, neg_sub] at hp
        left; rw [hp]; exact hpar'

end Erdos634.Draft.LaczFormal.RG

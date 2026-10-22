-- Draft/LaczFormalIVcRatBr4b.lean -- Laczkovich DCG 48 (2012), Sect. 8.3 (Subcase IVc, rational branch): BRIDGE stage Br4b: `vwOf` / `bridge_vw` = `VWTiling.ofPolyTiling`.
--   From `BrHyp` (a congruent region dissection into 30-60-90 tiles, regular via `CaseC.hregc`, every c-edge with an interior open-segment point, tile type labels rho/pi/2)
--   a `VWTiling s D.region (KIdx h) (RIdx h x Fin 2)` with finite index types: kites = the kite pairs `{i, pOf i}`, rhombi = the two rhombi of each parallelogram pair; cover from the tile cover;
--   disjointness from the tile disjointness (`pieces_disj`); the V/W clauses from `vw_transfer`.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 8.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIVcRatBr4a
import Erdos634.Draft.LaczFormalIVcRatB9b

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M] {D : CongruentRegionDissection N} {P : ConvPoly M} {idx : Fin N → Equiv.Perm (Fin 3)} {s : ℝ} {ρ π : Fin 3}
variable [HasFansC D.toRegionDissection] (h : BrHyp D P idx s ρ π)

noncomputable instance : Fintype (KIdx h) := by unfold KIdx; infer_instance
noncomputable instance : Fintype (RIdx h) := by unfold RIdx; infer_instance

/-- A same-label pair of corners at `X` of partner tiles lies on a kite piece. -/
theorem kite_piece_at {i' j' : Fin N} {b b' : Fin 3} {X : Plane} (hPr : Pr D i' j') (hb : (D.tile i').pts b = X) (hb' : (D.tile j').pts b' = X)
    (hl : idx i' b = idx j' b') (hl2 : idx i' b ≠ 2) :
    ∃ k : KIdx h, ∃ a, (D.tile k.1).pts a = X ∧ idx k.1 a = idx i' b := by
  have hj : j' = pOf h i' := pOf_eq_of_Pr h hPr
  subst hj
  by_cases hlt : i' < pOf h i'
  · exact ⟨⟨i', kite_of_samelabel h hPr hb hb' hl hl2, hlt⟩, b, hb, rfl⟩
  · have hlt' : pOf h i' < i' := lt_of_le_of_ne (not_lt.1 hlt) (pOf_ne h i')
    have hK : IsK h (pOf h i') := by
      unfold IsK
      rw [pOf_pOf]
      exact kite_of_samelabel h (Pr_pOf h i').symm hb' hb hl.symm (by rw [← hl]; exact hl2)
    exact ⟨⟨pOf h i', hK, by rw [pOf_pOf]; exact hlt'⟩, b', hb', hl.symm⟩

theorem pieceSet_sub (i : Fin N) : pieceSet h i ⊆ D.region := by
  intro x hx
  rcases hx with hx | hx
  · exact tile_sub_region D.toRegionDissection i hx
  · exact tile_sub_region D.toRegionDissection _ hx

theorem exists_min (i : Fin N) : ∃ m, m < pOf h m ∧ (i = m ∨ i = pOf h m) := by
  by_cases hlt : i < pOf h i
  · exact ⟨i, hlt, Or.inl rfl⟩
  · have hlt' : pOf h i < i := lt_of_le_of_ne (not_lt.1 hlt) (pOf_ne h i)
    exact ⟨pOf h i, by rw [pOf_pOf]; exact hlt', Or.inr (pOf_pOf h i).symm⟩

set_option maxHeartbeats 1600000 in
/-- **`VWTiling.ofPolyTiling` (bridge).**  The V/W tiling of the region of `D` by kites and rhombi of side `s` built from the c-pairs. -/
noncomputable def vwOf : VWTiling s D.region (KIdx h) (RIdx h × Fin 2) where
  K := kd h
  R := rdd h
  cover := by
    apply Set.Subset.antisymm
    · rintro x (hx | hx)
      · obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hx
        rw [(kd_spec h k).2.2.2.2.1] at hk
        exact pieceSet_sub h _ hk
      · obtain ⟨r, hr⟩ := Set.mem_iUnion.1 hx
        exact pieceSet_sub h _ (rdd_sub h r hr)
    · intro x hx
      have hx' : x ∈ ⋃ i, (D.tile i).carrier := by rw [D.covers]; exact hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx'
      obtain ⟨m, hm, hmi⟩ := exists_min h i
      have hxm : x ∈ pieceSet h m := by
        rcases hmi with e | e
        · left; rw [← e]; exact hi
        · right; rw [← e]; exact hi
      by_cases hK : IsK h m
      · left
        exact Set.mem_iUnion.2 ⟨⟨m, hK, hm⟩, by rw [(kd_spec h ⟨m, hK, hm⟩).2.2.2.2.1]; exact hxm⟩
      · right
        rw [← (rd_spec h ⟨m, hK, hm⟩).2] at hxm
        rcases hxm with hx0 | hx1
        · exact Set.mem_iUnion.2 ⟨(⟨m, hK, hm⟩, 0), by simp only [rdd]; simpa using hx0⟩
        · exact Set.mem_iUnion.2 ⟨(⟨m, hK, hm⟩, 1), by simp only [rdd]; simpa using hx1⟩
  disjKK := by
    intro k k' hne
    have hne' : k.1 ≠ k'.1 := fun e => hne (Subtype.ext e)
    rw [(kd_spec h k).2.2.2.2.1, (kd_spec h k').2.2.2.2.1]
    exact pieces_disj h k.2.2 k'.2.2 hne'
  disjRR := by
    intro r r' hne
    obtain ⟨⟨i, hi⟩, e⟩ := r
    obtain ⟨⟨i', hi'⟩, e'⟩ := r'
    by_cases hii : i = i'
    · subst hii
      have he : e ≠ e' := fun he => hne (by rw [he])
      fin_cases e <;> fin_cases e' <;> simp at he ⊢ <;> simp only [rdd] <;> simp
      · exact (rd_spec h ⟨i, hi⟩).1
      · exact (rd_spec h ⟨i, hi⟩).1.symm
    · exact (pieces_disj h hi.2 hi'.2 hii).mono (interior_mono (rdd_sub h (⟨i, hi⟩, e))) (interior_mono (rdd_sub h (⟨i', hi'⟩, e')))
  disjKR := by
    intro k r
    have hne : k.1 ≠ r.1.1 := fun e => r.1.2.1 (e ▸ k.2.1)
    rw [(kd_spec h k).2.2.2.2.1]
    exact (pieces_disj h k.2.2 r.1.2.2 hne).mono le_rfl (interior_mono (rdd_sub h r))
  vwV := by
    intro k
    obtain ⟨⟨a, ha, hla⟩, ⟨a', ha', hla'⟩, -⟩ := kd_spec h k
    obtain ⟨i', j', b, b', hPr, hb, hlb, hb', hlb'⟩ := vw_transfer h (c := π) (d := ρ) h.hρπ.symm h.hπ h.hρ (Pr_pOf h k.1) ha ha' hla hla'
    obtain ⟨k', a'', hpt, hl⟩ := kite_piece_at h hPr hb hb' (hlb.trans hlb'.symm) (by rw [hlb]; exact h.hρ)
    refine ⟨k', ?_⟩
    obtain ⟨-, -, ⟨a0, ha0, hl0⟩, -⟩ := kd_spec h k'
    have : a0 = a'' := (idx k'.1).injective (hl0.trans (hl.trans hlb).symm)
    subst this
    exact ((ha0.symm.trans hpt)).symm
  vwW := by
    intro k
    obtain ⟨-, -, ⟨a, ha, hla⟩, ⟨a', ha', hla'⟩, -⟩ := kd_spec h k
    obtain ⟨i', j', b, b', hPr, hb, hlb, hb', hlb'⟩ := vw_transfer h (c := ρ) (d := π) h.hρπ h.hρ h.hπ (Pr_pOf h k.1) ha ha' hla hla'
    obtain ⟨k', a'', hpt, hl⟩ := kite_piece_at h hPr hb hb' (hlb.trans hlb'.symm) (by rw [hlb]; exact h.hπ)
    refine ⟨k', ?_⟩
    obtain ⟨⟨a0, ha0, hl0⟩, -⟩ := kd_spec h k'
    have : a0 = a'' := (idx k'.1).injective (hl0.trans (hl.trans hlb).symm)
    subst this
    exact ((ha0.symm.trans hpt)).symm

#print axioms Erdos634.Draft.LaczFormal.RG.kite_piece_at
#print axioms Erdos634.Draft.LaczFormal.RG.vwOf

end Erdos634.Draft.LaczFormal.RG

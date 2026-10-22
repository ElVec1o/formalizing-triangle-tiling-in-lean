-- Draft/LaczFormalIIcL8aa.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.3, LEMMA 6.3 for a polygon with an arbitrary number M of vertices:
--   `lemma63 : Concl7 D P  \/  exists k, Concl5Rest D P k /\ exists s rev a, Concl5Seq D P k s rev a`   (conclusion (v) WITHOUT its printed inequality, see `Concl5Rest`, `Concl5Seq`, `concl5_of_parts`).
-- With one value of `W` it is `lemma63_one` (Concl7); with two it is `lemma63_two`, and `M` is even: the angle relation `(r - p) gamma = (v - p) pi`, `M gamma = 2 pi` gives `2 a_E = (v - p) M`, `v - p in {1, 2}`;
-- the arrivals add up to `M` (`exc_census`) and each is positive, so both have `v - p = 1` and `M = 2 a_E`.
-- NOTE, UNAUDITED.  CONDITIONAL on `kiteB = empty` (NoKites, the output of Lemma 6.2 for generic angles `AngGen`) and on the Case IIc hypothesis block (witnessed by GenWitK (204-tile octagon, genTiling_thm21) and IsoWitM).
-- Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcL8z

open scoped Classical Fin.NatCast
open EuclideanGeometry Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

set_option maxHeartbeats 12800000 in
/-- two distinct values of `W` force `M` even. -/
theorem M_even_of_two [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (G : AngGen (fun l => D.model.angleAt l))
    (hcor : ∀ j : Fin M, cnt D idx (P.v j) 0 = 1 ∧ cnt D idx (P.v j) 1 = 1 ∧ cnt D idx (P.v j) 2 = 0)
    (hNK : kiteB D idx = ∅) (W : Fin M → Plane) (hW : ∀ j, GExc D idx (P.v j) (W j)) (hdiff : ∃ j, W j ≠ W 0) : ∃ k, M = 2 * k := by
  classical
  obtain ⟨j0, hj0⟩ := hdiff
  set E := W 0 with hEdef
  set F := W j0 with hFdef
  have hEF : E ≠ F := fun h => hj0 h.symm
  obtain ⟨hKB, hM1, hM3⟩ := gexc_matching' D P hreg idx hC hab hac h1 h3 G hcor
  have hWex : ∀ j, W j ∈ excVerts2 D idx P := by
    intro j
    rcases gexc_end_cls D P hreg idx hC hab hac h1 h3 G hcor (hW j) with h | h
    · rw [hNK] at h; exact absurd h (Finset.notMem_empty _)
    · exact h
  have hP0 : cntP0 D idx P = M := by
    unfold cntP0
    rw [Finset.sum_congr rfl (fun j _ => (hcor (j + 1)).1)]
    simp
  have hcard2 : (excVerts2 D idx P).card ≤ 2 := by
    obtain ⟨-, -, hc, -⟩ := caseII_exc_count D P hreg idx hC.hidxA hC.hregc h1 h3
    rw [hP0] at hc
    omega
  have hsub : ({E, F} : Finset Plane) ⊆ excVerts2 D idx P := by
    intro Z hZ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hZ
    rcases hZ with rfl | rfl <;> exact hWex _
  have hEx : excVerts2 D idx P = {E, F} := by
    symm
    apply Finset.eq_of_subset_of_card_le hsub
    rw [Finset.card_pair hEF]; exact hcard2
  have hcensus := exc_census D P hreg idx hC h1 h3 hcor
  rw [hEx, Finset.sum_pair hEF] at hcensus
  have hEmem : E ∈ excVerts2 D idx P := by rw [hEx]; simp
  have hFmem : F ∈ excVerts2 D idx P := by rw [hEx]; simp
  have hpi := Real.pi_pos
  have hγ0 := model_angle_pos' D 2
  obtain ⟨hang, hMγ⟩ := corner_angles_gamma D P hreg idx hC h1 h3 hcor
  have hval : ∀ Z ∈ excVerts2 D idx P, ∃ m : ℕ, m ∈ ({1, 2} : Finset ℕ) ∧ 2 * (cnt D idx Z 2 - cnt D idx Z 0) = m * M := by
    intro Z hZ
    have hZ' := hZ
    unfold excVerts2 at hZ'
    simp only [Finset.mem_filter, Finset.mem_sdiff] at hZ'
    obtain ⟨⟨hZv, hZp⟩, hlt⟩ := hZ'
    have hvert := mem_vtxSet.mp hZv
    have hnc : ∀ kk : Fin M, Z ≠ P.v (kk + 1) := fun kk hkk => hZp (mem_polyVerts.mpr ⟨kk, hkk⟩)
    obtain ⟨v, hv2, hrel⟩ := vertex_angle_rel D P hreg idx hC.hidxA hC.hregc hvert hnc
    have hp1 := exc_cnt0_le_one D P hreg idx hC.hidxA hC.hregc h1 h3 hvert hnc hlt
    obtain ⟨a, ha⟩ : ∃ a, a = cnt D idx Z 2 - cnt D idx Z 0 := ⟨_, rfl⟩
    rw [← ha]
    have haR : (a : ℝ) * D.model.angleAt 2 = ((v : ℝ) - cnt D idx Z 0) * Real.pi := by
      rw [ha, Nat.cast_sub hlt.le]; exact hrel
    have h2a : (2 * a : ℝ) = ((v : ℝ) - cnt D idx Z 0) * M := by
      have : ((2 * a : ℝ)) * D.model.angleAt 2 = (((v : ℝ) - cnt D idx Z 0) * M) * D.model.angleAt 2 := by
        linear_combination 2 * haR - ((v : ℝ) - cnt D idx Z 0) * hMγ
      exact mul_right_cancel₀ hγ0.ne' this
    have ha1 : 1 ≤ a := by omega
    have ha1R : (1 : ℝ) ≤ a := by exact_mod_cast ha1
    have hMR : (3 : ℝ) ≤ M := by exact_mod_cast P.three_le
    rcases (by omega : cnt D idx Z 0 = 0 ∨ cnt D idx Z 0 = 1) with hp | hp <;>
    rcases (by omega : v = 0 ∨ v = 1 ∨ v = 2) with hv | hv | hv <;>
    · rw [hp, hv] at h2a
      simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] at h2a
      first
        | (exfalso; nlinarith)
        | (have h' : (2 * a : ℝ) = ((1 : ℕ) : ℝ) * M := by push_cast; linarith
           exact ⟨1, by simp, by exact_mod_cast h'⟩)
        | (have h' : (2 * a : ℝ) = ((2 : ℕ) : ℝ) * M := by push_cast; linarith
           exact ⟨2, by simp, by exact_mod_cast h'⟩)
  obtain ⟨mE, hmE, hE2⟩ := hval E hEmem
  obtain ⟨mF, hmF, hF2⟩ := hval F hFmem
  have hEpos : 1 ≤ cnt D idx E 2 - cnt D idx E 0 := by
    have h := hEmem; unfold excVerts2 at h
    have := (Finset.mem_filter.mp h).2
    omega
  have hFpos : 1 ≤ cnt D idx F 2 - cnt D idx F 0 := by
    have h := hFmem; unfold excVerts2 at h
    have := (Finset.mem_filter.mp h).2
    omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmE hmF
  rcases hmE with rfl | rfl <;> rcases hmF with rfl | rfl
  · exact ⟨cnt D idx E 2 - cnt D idx E 0, by omega⟩
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega

end Erdos634.Draft.LaczFormal.RG

-- Draft/LaczFormalBZL7h11.lean -- Beeson (arXiv 1206.1974v7) Lemma 10.6 (G5c): at the corner A of angle alpha the two steps of the walks along the two sides at A cannot both have length c.
--   `corner_not_both_c`, then `g5c_of_corner` (the hypothesis G5c of `Thm107Open`, from the existence of an alpha corner).
-- NOTE, UNAUDITED.  Credit: Beeson (arXiv 1206.1974v7, Lemma 10.6: "the b edge of that tile lies on AC or on AB"), Laczkovich (DCG 48 (2012), Sect. 4), Beeson-Zhang.
import Erdos634.Draft.LaczFormalBZL7h10

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

theorem corner_not_both_c (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hβ : D.model.angleAt 1 = Real.pi - 3 * D.model.angleAt 0) (hγ : D.model.angleAt 2 = 2 * D.model.angleAt 0)
    (hα : ¬ ∃ r : ℚ, D.model.angleAt 0 = (r : ℝ) * Real.pi)
    (hne12 : slen D 2 ≠ slen D 1) (kA : Fin M) (hkA : P.angle (kA + 1) = D.model.angleAt 0)
    {j1 j2 : Fin N} {U1 U2 : Plane}
    (hS1 : TriStep (D.tile j1) (toV2 (P.e (kA + 1))) (P.v (kA + 1)) U1) (hS2 : TriStep (D.tile j2) (toV2 (P.e kA)) U2 (P.v (kA + 1))) :
    ¬ (dist (P.v (kA + 1)) U1 = slen D 2 ∧ dist U2 (P.v (kA + 1)) = slen D 2) := by
  classical
  rintro ⟨hc1, hc2⟩
  obtain ⟨hn0, hn1, hn2⟩ := corner_alpha_counts D P hreg idx hidxA hβ hγ hα kA hkA
  set A := P.v (kA + 1) with hA
  obtain ⟨kk1, f1, g1, hk1, hf1, hfk1, hgk1, hgf1, hd1⟩ := step_third D idx hidx hS1
  obtain ⟨kk2, f2, g2, hk2, hf2, hfk2, hgk2, hgf2, hd2⟩ := step_third D idx hidx hS2
  have hz : ∀ z : Fin 3, 1 ≤ cnt D idx A z → z = 0 := by
    intro z hz
    fin_cases z
    · rfl
    · simp at hz; omega
    · simp at hz; omega
  have h10 : idx j1 kk1 = 0 := hz _ (cnt_pos_of_corner_h1 D idx hk1 rfl)
  have h20 : idx j2 f2 = 0 := hz _ (cnt_pos_of_corner_h1 D idx hf2 rfl)
  have hj : j1 = j2 := corner_eq_of_cnt_le_one_h1 D idx (l := 0) (by omega) hk1 h10 hf2 h20
  subst hj
  have hkk : kk1 = f2 := (D.tile j1).indep.injective (hk1.trans hf2.symm)
  subst hkk
  by_cases hff : f1 = kk2
  · subst hff
    have hU : U1 = U2 := by rw [← hf1, ← hk2]
    subst hU
    obtain ⟨-, -, -, -, -, -, -, -, hp1, -⟩ := id hS1
    obtain ⟨-, -, -, -, -, -, -, -, hp2, -⟩ := id hS2
    obtain ⟨c1, hc1', hc1e⟩ := hp1.smul
    obtain ⟨c2, hc2', hc2e⟩ := hp2.smul
    have hneg : toV2 (A - U1) = (-(toV2 (U1 - A)).1, -(toV2 (U1 - A)).2) := by unfold toV2; ext <;> simp
    rw [hc2e, hc1e] at hneg
    have hcr := crs_consecutive_pos P kA
    set dk := toV2 (P.e kA) with hdk
    set dm := toV2 (P.e (kA + 1)) with hdm
    have e1 := congrArg Prod.fst hneg
    have e2 := congrArg Prod.snd hneg
    simp only at e1 e2
    unfold crs at hcr
    have : c2 * (dk.1 * dm.2 - dk.2 * dm.1) = 0 := by linear_combination dm.2 * e1 - dm.1 * e2
    have h0 : (dk.1 * dm.2 - dk.2 * dm.1) = 0 := by
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hc2'.ne'
      · exact h
    linarith
  · have hg1 : g1 = kk2 := fin3_g_eq kk1 f1 g1 kk2 hfk1 hgk1 hgf1 (Ne.symm hfk2) (Ne.symm hff)
    have hg2 : g2 = f1 := fin3_g2_eq kk1 f1 kk2 g2 hfk1 (Ne.symm hfk2) (Ne.symm hff) hgk2 hgf2
    rw [hg1] at hd1
    rw [hg2] at hd2
    have e1 : slen D (idx j1 kk2) = slen D 2 := by rw [← hd1]; exact hc1
    have e2 : slen D (idx j1 f1) = slen D 2 := by rw [← hd2]; exact hc2
    have hd01 : idx j1 f1 ≠ idx j1 kk2 := fun h => hff ((idx j1).injective h)
    rcases fin3_one_of (idx j1 kk1) (idx j1 f1) (idx j1 kk2) (fun h => hfk1 ((idx j1).injective h).symm)
      (fun h => hfk2 ((idx j1).injective h)) hd01 h10 with h | h
    · rw [h] at e2; exact hne12 (e2.symm)
    · rw [h] at e1; exact hne12 (e1.symm)

end Erdos634.Draft.LaczFormal.RG

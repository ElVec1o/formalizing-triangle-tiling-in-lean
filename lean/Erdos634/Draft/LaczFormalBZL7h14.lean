-- Draft/LaczFormalBZL7h14.lean -- Beeson (arXiv 1206.1974v7) Lemma 10.3 (G1), real fan at a CENTRE (corner counts (0,2,3)): the fan is a complete cycle of five corner sectors (`centre_fan`),
--   and no two of its rays are opposite (`centre_no_opp`: a block of sectors of total width pi would give n1 beta + n2 gamma = pi with n1 <= 2, n2 <= 3, impossible for alpha not in Q pi).
-- NOTE, UNAUDITED.  Credit: Beeson (arXiv 1206.1974v7, Lemma 10.3), Laczkovich (DCG 48 (2012), Lemma 8.1 proof: angle between rays, opposite ray iff block sum pi), Beeson-Zhang.
import Erdos634.Draft.LaczFormalBZL7h13
import Erdos634.Draft.LaczFormalRG4GkFan

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

/-- **The fan at a centre**: a complete cycle of five corner sectors. -/
theorem centre_fan (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hβ : D.model.angleAt 1 = Real.pi - 3 * D.model.angleAt 0) (hγ : D.model.angleAt 2 = 2 * D.model.angleAt 0)
    {X : Plane} (hX : ∃ i k, (D.tile i).pts k = X)
    (hc0 : cnt D idx X 0 = 0) (hc1 : cnt D idx X 1 = 2) (hc2 : cnt D idx X 2 = 3) :
    ∃ (F : ExtFan D.toRegionDissection X Empty),
      (∀ x : AtV D.toRegionDissection X, 0 < crs (F.p x) (F.q x)) ∧ Fintype.card (AtV D.toRegionDissection X) = 5 := by
  classical
  have hpi := Real.pi_pos
  have hS : ∑ l, (cnt D idx X l : ℝ) * D.model.angleAt l = 2 * Real.pi := by
    rw [Fin.sum_univ_three, hc0, hc1, hc2, hβ, hγ]; push_cast; ring
  have hint : X ∈ interior D.region := by
    by_contra hnot
    have := boundary_sum_le D P hreg idx hidxA hX hnot
    linarith
  obtain ⟨F⟩ := extFan_interior D.toRegionDissection X hX hint
  have hang := head_angle_sum D idx hidxA F inferInstance
  have hStr : (Strn D.toRegionDissection X).card = 0 := by
    by_contra hne
    have : (1 : ℝ) ≤ (Strn D.toRegionDissection X).card := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
    nlinarith
  refine ⟨F, ?_, ?_⟩
  · intro x
    rcases F.hspec x with ⟨k, hk, -⟩ | ⟨hnv, -⟩
    · exact crs_pos_of_corner (F.hok x) (F.hspec x) ⟨k, hk⟩
    · exfalso
      have : x.1 ∈ Strn D.toRegionDissection X := by
        simp only [Strn, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨x.2, hnv⟩
      have := Finset.card_pos.mpr ⟨x.1, this⟩
      omega
  · rw [card_atV, card_corn D idx X, hStr, Fin.sum_univ_three]
    omega

/-- **No opposite rays at a centre.**  If a sector `s` of the fan at a centre starts along the direction opposite to the ray between sectors `tl (b + (i+m-1) % m)` and `tl (b + i)`, we get a contradiction. -/
theorem centre_no_opp (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hβ : D.model.angleAt 1 = Real.pi - 3 * D.model.angleAt 0) (hγ : D.model.angleAt 2 = 2 * D.model.angleAt 0)
    (hα : ¬ ∃ r : ℚ, D.model.angleAt 0 = (r : ℝ) * Real.pi)
    {X : Plane} {κ : Type} [Fintype κ] (F : ExtFan D.toRegionDissection X κ) (hcor : ∀ x : AtV D.toRegionDissection X, 0 < crs (F.p x) (F.q x))
    (hemp : IsEmpty κ) (hc0 : cnt D idx X 0 = 0) (hc1 : cnt D idx X 1 = 2) (hc2 : cnt D idx X 2 = 3)
    (b i : ℕ) (hi : i < Fintype.card (AtV D.toRegionDissection X)) (s : AtV D.toRegionDissection X)
    (hs : Par (F.p s) (neg2 (F.q (tl F hemp (b + (i + Fintype.card (AtV D.toRegionDissection X) - 1) % Fintype.card (AtV D.toRegionDissection X)))))) :
    False := by
  classical
  obtain ⟨m', hm0, hm', hπ⟩ := opp_colG_aux D F hcor hemp b i hi s hs
  set m := Fintype.card (AtV D.toRegionDissection X) with hm
  have hpos : 0 < m := card_pos_atV F hemp
  set c := b + i with hc
  let typ : ℕ → Fin 3 := fun t => idx (tl F hemp (c + t)).1 (cd D F hcor (tl F hemp (c + t))).1
  have hwdt : ∀ t, wd (F.p (tl F hemp (c + t))) (F.q (tl F hemp (c + t))) = D.model.angleAt (typ t) :=
    fun t => wd_cd' D idx F hcor hidxA _
  have hbnd : ∀ j : Fin 3, ((Finset.range m').filter (fun t => typ t = j)).card ≤ cnt D idx X j := by
    intro j
    rw [cnt_atv D idx (fun x => (cd D F hcor x).1) (fun x => (cd_spec D F hcor x).1) j]
    refine Finset.card_le_card_of_injOn (fun t => tl F hemp (c + t)) ?_ ?_
    · intro t ht
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at ht
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      exact ht.2
    · intro t ht t' ht' h
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at ht ht'
      have h1 := tl_inj_mod F hemp h
      have h2 : (c + t) ≡ (c + t') [MOD m] := h1
      have h3 := Nat.ModEq.add_left_cancel' c h2
      exact Nat.ModEq.eq_of_lt_of_lt h3 (lt_trans ht.1 hm') (lt_trans ht'.1 hm')
  set n0 := ((Finset.range m').filter (fun t => typ t = 0)).card with hn0
  set n1 := ((Finset.range m').filter (fun t => typ t = 1)).card with hn1
  set n2 := ((Finset.range m').filter (fun t => typ t = 2)).card with hn2
  have hsum : (n0 : ℝ) * D.model.angleAt 0 + n1 * D.model.angleAt 1 + n2 * D.model.angleAt 2 = Real.pi := by
    have h1 : ∑ t ∈ Finset.range m', wd (F.p (tl F hemp (c + t))) (F.q (tl F hemp (c + t))) =
        ∑ t ∈ Finset.range m', D.model.angleAt (typ t) := Finset.sum_congr rfl (fun t _ => hwdt t)
    have h2 := sum_by_type m' typ D.model.angleAt
    rw [Fin.sum_univ_three] at h2
    rw [← hπ, h1, h2]
  have b0 := hbnd 0
  have b1 := hbnd 1
  have b2 := hbnd 2
  have := vtype_arith (α := D.model.angleAt 0) (β := D.model.angleAt 1) hβ hα n0 n1 n2 0 1 (by rw [hγ] at hsum; push_cast; linarith)
  omega

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.centre_fan
#print axioms Erdos634.Draft.LaczFormal.RG.centre_no_opp

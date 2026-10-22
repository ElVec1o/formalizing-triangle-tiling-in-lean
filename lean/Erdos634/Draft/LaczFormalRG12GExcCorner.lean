-- Draft/LaczFormalRG12GExcCorner.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2, Gamma_except, lemma L4 `gexc_start_of_corner` (FABLE_THM21_FINISH blueprint, A.2/A.4, Fig. 6): EVERY corner `V_i` of the polygon (all corners of
-- type `alpha + beta`, the case `P = N` of Subcase IIc) starts an edge of Gamma_except.
-- Route (the printed proof l. 1444-1455, with its hidden step made explicit): by Lemma 4.7 (`corner_c_status`, `walk_status_chain`) the `c`-status of the first tile is the SAME on all sides.  If it were `not c` on all sides, a side without
-- exceptional boundary point exists (at most two exceptional vertices, `caseII_exc_count`, `sideBad2_card_b`, and `M >= 3`), it has normal interior vertices (`normSide_of_good`), the first tile there has `gamma` at its head (a step between two
-- non-`gamma` corners has length `c`: `step_dist_c`), `walk_head_fwd` carries `gamma` to the last head, a corner of the polygon: but the corners have no `gamma` (Fig. 6 (B) impossible).  So every side is `c`-covered: Fig. 6 (A)
-- (`gexc_start_corner_A`).
-- NOTE (print gap, repaired): the printed text says "every vertex on XY is normal" for the chosen side XY; a side may carry an exceptional vertex (type (0,0,N/2)), where head-`gamma` propagation stops.  Here the side is chosen
-- among those without exceptional vertex, using that the statuses of all sides agree (Lemma 4.7).
-- Hypotheses: `CaseC`, `HasFansC`, `D.region = P.carrier`, gamma < pi/2, != pi/3, and `hcor` (every polygon vertex has counts `(1,1,0)`: the case `cntP0 = M` of `lemma61_core`).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2, Fig. 6, Lemma 4.7), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG12GExcCornerA
import Erdos634.Draft.LaczFormalRG12L61Count

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

set_option maxHeartbeats 12800000 in
/-- **L4: every corner of the polygon starts an edge of Gamma_except.** -/
theorem gexc_start_of_corner [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3)
    (hcor : ∀ j : Fin M, cnt D idx (P.v j) 0 = 1 ∧ cnt D idx (P.v j) 1 = 1 ∧ cnt D idx (P.v j) 2 = 0) (i : Fin M) :
    ∃ W, GExc D idx (P.v i) W := by
  classical
  have hG := hC.caseG
  set D' := relabelC D with hD'
  set idx' := relabelCIdx idx with hidx'
  haveI : HasFansC D'.toRegionDissection := (inferInstance : HasFansC D.toRegionDissection)
  have hD'0 : slen D' 0 = slen D 2 := relabelC_slen0 D
  choose L e0 el hW hh hl hs1 hs2 hT0 hT1 using edge_data D P hreg
  have hU : ∀ i, ∃ s : ℝ, 0 ≤ s ∧ toV2 (P.v i - P.v i) = (s * (toV2 (P.e i)).1, s * (toV2 (P.e i)).2) :=
    fun i => ⟨0, le_rfl, by unfold toV2; ext <;> simp⟩
  have hchain : ∀ i, ∀ e ∈ L i, (dist e.2.1 e.2.2 = slen D 2 ↔ dist (e0 i).2.1 (e0 i).2.2 = slen D 2) := by
    intro i e he
    have := walk_status_chain D' idx' hG P hreg i rfl (hW i) (hU i) (e0 i) (hh i) e he
    rwa [hD'0] at this
  have hlast : ∀ i, (dist (el i).2.1 (el i).2.2 = slen D 2 ↔ dist (e0 i).2.1 (e0 i).2.2 = slen D 2) := by
    intro i
    exact hchain i (el i) (List.mem_of_getLast? (hl i))
  have hstep : ∀ k : Fin M, (dist (e0 (k + 1)).2.1 (e0 (k + 1)).2.2 = slen D 2 ↔ dist (e0 k).2.1 (e0 k).2.2 = slen D 2) := by
    intro k
    have hSo : TriStep (D.tile (e0 (k + 1)).1) (toV2 (P.e (k + 1))) (P.v (k + 1)) (e0 (k + 1)).2.2 := by
      have := hT0 (k + 1); rwa [hs1 (k + 1)] at this
    have hSi : TriStep (D.tile (el k).1) (toV2 (P.e k)) (el k).2.1 (P.v (k + 1)) := by
      have := hT1 k; rwa [hs2 k] at this
    have := corner_c_status D idx hC P hreg k _ _ _ _ hSo hSi
    have hA : dist (e0 (k + 1)).2.1 (e0 (k + 1)).2.2 = dist (P.v (k + 1)) (e0 (k + 1)).2.2 := by rw [hs1]
    have hB : dist (el k).2.1 (el k).2.2 = dist (el k).2.1 (P.v (k + 1)) := by rw [hs2]
    rw [hA]
    exact this.trans (by rw [← hB]; exact hlast k)
  have hall : ∀ n : ℕ, (dist (e0 (n : Fin M)).2.1 (e0 (n : Fin M)).2.2 = slen D 2 ↔ dist (e0 0).2.1 (e0 0).2.2 = slen D 2) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := hstep (n : Fin M)
      rw [Nat.cast_succ]
      exact this.trans ih
  have hall' : ∀ i : Fin M, (dist (e0 i).2.1 (e0 i).2.2 = slen D 2 ↔ dist (e0 0).2.1 (e0 0).2.2 = slen D 2) := by
    intro i
    have := hall i.val
    rwa [Fin.cast_val_eq_self] at this
  -- the first tile of every side is `c`: otherwise a side without exceptional vertex gives `gamma` at a polygon corner
  have hsti : dist (e0 i).2.1 (e0 i).2.2 = slen D 2 := by
    by_contra hnot
    have hnot' : ∀ j, ¬ dist (e0 j).2.1 (e0 j).2.2 = slen D 2 := fun j hj => hnot ((hall' i).mpr ((hall' j).mp hj))
    obtain ⟨hRP, hMP, hexc, hang⟩ := caseII_exc_count D P hreg idx hC.hidxA hC.hregc h1 h3
    have hsumP : cntP0 D idx P = ∑ j : Fin M, cnt D idx (P.v j) 0 :=
      Equiv.sum_comp (Equiv.addRight (1 : Fin M)) (fun j => cnt D idx (P.v j) 0)
    have hP0 : cntP0 D idx P = M := by
      rw [hsumP]
      have : ∀ j : Fin M, cnt D idx (P.v j) 0 = 1 := fun j => (hcor j).1
      simp [this]
    have hexc2 : (excVerts2 D idx P).card ≤ 2 := by
      have : ((excVerts2 D idx P).card : ℤ) ≤ 2 := by rw [hP0] at hexc; push_cast at hexc; linarith
      exact_mod_cast this
    have hbad := sideBad2_card_b D idx P hreg
    have hfl := Finset.card_filter_le (excVerts2 D idx P) (fun v => v ∉ interior D.region)
    have hM3 := ConvPoly.three_le P
    obtain ⟨j, hj⟩ : ∃ j : Fin M, ¬ SideBad2 D idx P j := by
      by_contra hno
      push Not at hno
      have : Finset.univ.filter (SideBad2 D idx P) = Finset.univ := by
        ext j; simp [hno j]
      rw [this, Finset.card_univ, Fintype.card_fin] at hbad
      omega
    have hn := normSide_of_good D P hreg idx hC h1 h3 j hj
    obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, -⟩ := id (hT0 j)
    have hkP : (D.tile (e0 j).1).pts kk = P.v j := by rw [hk, hs1 j]
    have hp : idx (e0 j).1 kk ≠ 2 := by
      intro e
      have := cnt_one D idx 2 hkP e
      have := (hcor j).2.2
      omega
    have hq : idx (e0 j).1 f = 2 := by
      by_contra hne
      apply hnot' j
      have := step_dist_c D idx hC.hidx (Ne.symm hfk) hp hne
      rwa [hk, hf] at this
    have ty : TyAt D idx (e0 j).1 (e0 j).2.2 2 := (tyAt_iff hf 2).mpr hq
    have t3 := walk_head_fwd D P hreg idx hC j hn (hW j) (hh j) (hl j) ty
    obtain ⟨kk2, f2, g2, hk2, hf2, -⟩ := id (hT1 j)
    have e2 := (tyAt_iff hf2 2).mp t3
    have hfP : (D.tile (el j).1).pts f2 = P.v (j + 1) := by rw [hf2, hs2 j]
    have := cnt_one D idx 2 hfP e2
    have := (hcor (j + 1)).2.2
    omega
  -- the corner `i = (i - 1) + 1`
  have hk : i - 1 + 1 = i := sub_add_cancel i 1
  have hSo0 : TriStep (D.tile (e0 i).1) (toV2 (P.e (i - 1 + 1))) (P.v (i - 1 + 1)) (e0 i).2.2 := by
    rw [hk, ← hs1 i]; exact hT0 i
  have hout : ∀ (jo : Fin N) (Uo : Plane), TriStep (D.tile jo) (toV2 (P.e (i - 1 + 1))) (P.v (i - 1 + 1)) Uo → dist (P.v (i - 1 + 1)) Uo = slen D 2 := by
    intro jo Uo hjo
    obtain ⟨-, hU2⟩ := left_step_unique D.toRegionDissection hSo0 hjo
    rw [← hU2, hk, ← hs1 i]; exact hsti
  have hin : ∀ (ji : Fin N) (Ui : Plane), TriStep (D.tile ji) (toV2 (P.e (i - 1))) Ui (P.v (i - 1 + 1)) → dist Ui (P.v (i - 1 + 1)) = slen D 2 := by
    intro ji Ui hji
    exact (corner_c_status D idx hC P hreg (i - 1) _ _ _ _ hSo0 hji).mp (hout _ _ hSo0)
  have := gexc_start_corner_A D P hreg idx hC (i - 1) (by rw [hk]; exact (hcor i).1) (by rw [hk]; exact (hcor i).2.1) (by rw [hk]; exact (hcor i).2.2) hout hin
  rwa [hk] at this

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.gexc_start_of_corner

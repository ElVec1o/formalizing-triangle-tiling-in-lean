-- Draft/LaczFormalIIcSpoke4.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.3, step 3 (`spokes_angle`), item (d), ingredients:
--  (4a) `side_labels_propagate`: along a side with normal interior vertices, if the first tile has labels (a at the tail, b at the head), a,b in {0,1}, EVERY tile of the walk has them (the body of `edge_multiple_c`, whose conclusion kept only the length).
--  (4b) `corner_out_c`: at every polygon corner of type (1,1,0) the first tile of the outgoing side has its c-side on the boundary (the `hsti` step of `gexc_start_of_corner`, now exported for all corners).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2-6.3, Lemma 4.7, Fig. 6), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG12GExcCorner
import Erdos634.Draft.LaczFormalRG9SideC2
import Erdos634.Draft.LaczFormalIIcSpoke3

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

set_option maxHeartbeats 3200000 in
theorem side_labels_propagate [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseC D idx) (i : Fin M) (hnorm : ∀ V : Plane, (∃ j k, (D.tile j).pts k = V) → (∃ t : ℝ, 0 < t ∧ t < 1 ∧ V = (1 - t) • P.v i + t • P.v (i + 1)) → cnt D idx V 0 = 1 ∧ cnt D idx V 1 = 1 ∧ cnt D idx V 2 = 1) {L : List (Fin N × Plane × Plane)}
    (W : WalkT D.toRegionDissection (toV2 (P.e i)) (P.v i) (P.v (i + 1)) L) {e0 : Fin N × Plane × Plane} (hf : L.head? = some e0)
    {a b : Fin 3} (hab : (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0)) (h0 : TyAt D idx e0.1 e0.2.1 a ∧ TyAt D idx e0.1 e0.2.2 b) :
    ∀ e ∈ L, TyAt D idx e.1 e.2.1 a ∧ TyAt D idx e.1 e.2.2 b := by
  classical
  have hU : ∃ s : ℝ, 0 ≤ s ∧ toV2 (P.v i - P.v i) = (s * (toV2 (P.e i)).1, s * (toV2 (P.e i)).2) :=
    ⟨0, le_rfl, by unfold toV2; ext <;> simp⟩
  obtain ⟨L0, hL0⟩ : ∃ L0, L = e0 :: L0 := by
    cases L with
    | nil => simp at hf
    | cons x L0 => simp at hf; exact ⟨L0, by rw [hf]⟩
  have local_step : ∀ (e e2 : Fin N × Plane × Plane) (t : ℝ), 0 < t → t < 1 → e.2.2 = (1 - t) • P.v i + t • P.v (i + 1) → e2.2.1 = e.2.2 →
      TriStep (D.tile e.1) (toV2 (P.e i)) e.2.1 e.2.2 → TriStep (D.tile e2.1) (toV2 (P.e i)) e2.2.1 e2.2.2 →
      ∀ kk1 f1 kk2 f2 : Fin 3, (D.tile e.1).pts kk1 = e.2.1 → (D.tile e.1).pts f1 = e.2.2 → (D.tile e2.1).pts kk2 = e2.2.1 → (D.tile e2.1).pts f2 = e2.2.2 →
      (((idx e.1 kk1 = 0 ∧ idx e.1 f1 = 1) ∨ (idx e.1 kk1 = 1 ∧ idx e.1 f1 = 0)) → idx e2.1 kk2 = idx e.1 kk1 ∧ idx e2.1 f2 = idx e.1 f1) := by
    intro e e2 t ht0 ht1 hVt hX2 hS1 hS2 kk1 f1 kk2 f2 hk1 hf1 hk2 hf2
    exact (edge_step_pair_c D P hreg idx h i hnorm ht0 ht1 hVt (U := e.2.1) (U'' := e2.2.2) (j1 := e.1) (j2 := e2.1) hS1 (by rw [← hX2]; exact hS2)
      kk2 f2 f1 kk1 (by rw [← hX2, ← hk2]) (by rw [hf2]) hf1 hk1)
  have hall := walk_prop_forward D.toRegionDissection P hreg i (fun e => TyAt D idx e.1 e.2.1 a ∧ TyAt D idx e.1 e.2.2 b) (by
      intro e e2 t ht0 ht1 hVt hX2 hS1 hS2 hRe
      obtain ⟨kk1, f1, hk1, hf1⟩ := step_idx hS1
      obtain ⟨kk2, f2, hk2, hf2⟩ := step_idx hS2
      have ls := local_step e e2 t ht0 ht1 hVt hX2 hS1 hS2 kk1 f1 kk2 f2 hk1 hf1 hk2 hf2
      have ha : idx e.1 kk1 = a := (tyAt_iff hk1 a).mp hRe.1
      have hb : idx e.1 f1 = b := (tyAt_iff hf1 b).mp hRe.2
      have := ls (by rw [ha, hb]; exact hab)
      exact ⟨(tyAt_iff hk2 a).mpr (by rw [this.1, ha]), (tyAt_iff hf2 b).mpr (by rw [this.2, hb])⟩) rfl W hU e0 L0 hL0 h0
  exact hall

set_option maxHeartbeats 12800000 in
/-- **(4b)** At every polygon corner the first tile of the outgoing side has its `c`-side on the boundary. -/
theorem corner_out_c [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3)
    (hcor : ∀ j : Fin M, cnt D idx (P.v j) 0 = 1 ∧ cnt D idx (P.v j) 1 = 1 ∧ cnt D idx (P.v j) 2 = 0) (i : Fin M) :
    ∀ (jo : Fin N) (Uo : Plane), TriStep (D.tile jo) (toV2 (P.e i)) (P.v i) Uo → dist (P.v i) Uo = slen D 2 := by
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
  intro jo Uo hjo
  have hSo0 : TriStep (D.tile (e0 i).1) (toV2 (P.e i)) (P.v i) (e0 i).2.2 := by
    rw [← hs1 i]; exact hT0 i
  obtain ⟨-, hU2⟩ := left_step_unique D.toRegionDissection hSo0 hjo
  rw [← hU2, ← hs1 i]; exact hsti

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.side_labels_propagate
#print axioms Erdos634.Draft.LaczFormal.RG.corner_out_c

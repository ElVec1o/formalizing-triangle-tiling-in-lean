-- Draft/LaczFormalRG10Block.lean -- Laczkovich DCG 48 (2012), Lemma 4.8, the COMBINATORIAL HALF: two divisions `LA, LB` of a segment `XY` on opposite sides of a line (walks of tiles), with `Gamma_c` empty,
-- `a, b` commensurable and `c` not a rational multiple of `a`: every `c`-element of one division has a partner on the other division with the SAME endpoints.
-- (Between two consecutive common vertices both divisions consist of `c`-elements only (Lemma 4.5 + count of `c`), hence of exactly one element each.)  NOTE, UNAUDITED.
-- Credit: Laczkovich (DCG 48 (2012), Lemmas 4.5, 4.6, 4.8), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG8Final

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

theorem chain_same' {α : Type*} (S : α → Prop) : ∀ (Q : List α) (q : α),
    (∀ Q1 u1 u2 Q2, q :: Q = Q1 ++ u1 :: u2 :: Q2 → (S u1 ↔ S u2)) → ∀ u ∈ q :: Q, (S u ↔ S q) := by
  intro Q
  induction Q with
  | nil => intro q _ u hu; simp at hu; subst hu; exact Iff.rfl
  | cons r Q ih =>
    intro q hpair u hu
    have hqr : S q ↔ S r := hpair [] q r Q rfl
    rcases List.mem_cons.mp hu with rfl | hu'
    · exact Iff.rfl
    · have := ih r (fun Q1 u1 u2 Q2 hQ => hpair (q :: Q1) u1 u2 Q2 (by rw [hQ]; rfl)) u hu'
      exact this.trans hqr.symm

theorem chain_same {α : Type*} (S : α → Prop) (Q : List α)
    (hpair : ∀ Q1 u1 u2 Q2, Q = Q1 ++ u1 :: u2 :: Q2 → (S u1 ↔ S u2)) : ∀ u ∈ Q, ∀ v ∈ Q, (S u ↔ S v) := by
  cases Q with
  | nil => intro u hu; simp at hu
  | cons q Q =>
    intro u hu v hv
    exact (chain_same' S Q q hpair u hu).trans (chain_same' S Q q hpair v hv).symm

/-- The split of a walk at an element: the prefix up to and including it, and the suffix after it. -/
theorem split_end {D : RegionDissection N} {b : Bool} {d : V2} {X Y : Plane} {L P S : List (Fin N × Plane × Plane)} {fE : Fin N × Plane × Plane}
    (w : WalkU D b d X Y L) (hdec : L = P ++ fE :: S) :
    WalkU D b d X fE.2.2 (P ++ [fE]) ∧ WalkU D b d fE.2.2 Y S := by
  obtain ⟨w1, w2⟩ := walkU_split w hdec
  obtain ⟨i, A, B⟩ := fE
  cases w2 with
  | cons hS W' => exact ⟨by rw [walkU_append]; exact ⟨A, w1, WalkU.cons hS (WalkU.nil _)⟩, W'⟩

theorem dt_step_lt {X Z W : Plane} {d : V2} {T' : ℝ} (hd : d ≠ 0) (hT' : 0 < T') (h : toV2 (W - Z) = (T' * d.1, T' * d.2)) :
    dt d (toV2 (Z - X)) < dt d (toV2 (W - X)) := by
  have h3 := toV2_sub3 W Z X
  have hn := nsq_pos hd
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only at h1 h2
  rw [h3]
  unfold dt
  simp only
  rw [h1, h2]
  unfold nsq at hn
  nlinarith

theorem walkU_two {D : RegionDissection N} {b : Bool} {d : V2} {X W : Plane} {p0 r0 : Fin N × Plane × Plane} {rest : List (Fin N × Plane × Plane)}
    (w : WalkU D b d X W (p0 :: r0 :: rest)) : ∃ T' : ℝ, 0 < T' ∧ toV2 (W - p0.2.2) = (T' * d.1, T' * d.2) := by
  obtain ⟨i, A, B⟩ := p0
  cases w with
  | cons hS W' =>
    obtain ⟨T, -, hT, hTp, -⟩ := walkU_pos W'
    exact ⟨T, hTp (by simp), hT⟩

/-- **Status of consecutive elements in the prefix** (Laczkovich Lemma 4.5 + `Gamma_c` empty): up to the first common end of the two divisions, all elements of the division `L1`
have the same `c`-status. -/
theorem prefix_const (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseC D idx)
    (hGc : ∀ X H, ¬ GcEdge D X H) {d : V2} (hd : d ≠ 0) {b : Bool} {X Y : Plane} {L1 L2 : List (Fin N × Plane × Plane)}
    (w1 : WalkU D.toRegionDissection b d X Y L1) (w2 : WalkU D.toRegionDissection (!b) d X Y L2)
    {P1 S1 : List (Fin N × Plane × Plane)} {fE : Fin N × Plane × Plane} (hdec : L1 = P1 ++ fE :: S1)
    (hmin : ∀ U : Plane, (∃ g ∈ L2, g.2.2 = U) → (∃ f ∈ L1, f.2.2 = U) → dt d (toV2 (fE.2.2 - X)) ≤ dt d (toV2 (U - X))) :
    ∀ u ∈ P1 ++ [fE], ∀ v ∈ P1 ++ [fE], (dist u.2.1 u.2.2 = slen D 2 ↔ dist v.2.1 v.2.2 = slen D 2) := by
  classical
  obtain ⟨wpre, -⟩ := split_end w1 hdec
  obtain ⟨TU, -, hTU, -, hposU⟩ := walkU_pos wpre
  obtain ⟨T, -, hT, -, hposB⟩ := walkU_pos w1
  apply chain_same
  intro Q1 u1 u2 Q2 hQ
  by_contra hne
  have hord : (dist u1.2.1 u1.2.2 = slen D 2 ∧ dist u2.2.1 u2.2.2 ≠ slen D 2) ∨ (dist u1.2.1 u1.2.2 ≠ slen D 2 ∧ dist u2.2.1 u2.2.2 = slen D 2) := by
    by_cases h1 : dist u1.2.1 u1.2.2 = slen D 2
    · left; exact ⟨h1, fun h2 => hne ⟨fun _ => h2, fun _ => h1⟩⟩
    · right; exact ⟨h1, by_contra fun h2 => hne ⟨fun h => absurd h h1, fun h => absurd h h2⟩⟩
  have hL1' : L1 = Q1 ++ u1 :: u2 :: (Q2 ++ S1) := by
    rw [hdec]
    have : P1 ++ fE :: S1 = (P1 ++ [fE]) ++ S1 := by simp
    rw [this, hQ]; simp
  have hu1 : u1 ∈ L1 := by rw [hL1']; simp
  have hu2 : u2 ∈ L1 := by rw [hL1']; simp
  have hu2' : u2 ∈ P1 ++ [fE] := by rw [hQ]; simp
  have hadj : u1.2.2 = u2.2.1 := walkU_adj (hL1' ▸ w1)
  obtain ⟨t0, t1, h0, h1, h00, h01, h1T⟩ := hposU u2 hu2'
  obtain ⟨a1, b1, ha1, hb1, ha1', hlt1, hle1⟩ := hposB u1 hu1
  obtain ⟨a2, b2, ha2, hb2, ha2', hlt2, hle2⟩ := hposB u2 hu2
  have hWs : b1 = a2 := param_unique hd (by rw [← hb1, ← ha2, hadj])
  have hs0 : 0 < b1 := by linarith
  have hsT : b1 < T := by linarith
  have hWpar : toV2 (u1.2.2 - X) = (b1 * d.1, b1 * d.2) := hb1
  have hnA : ¬ ∃ g ∈ L2, g.2.2 = u1.2.2 := by
    rintro ⟨g, hg, hgW⟩
    have hmemC := hmin u1.2.2 ⟨g, hg, hgW⟩ ⟨u1, hu1, rfl⟩
    have hW : toV2 (fE.2.2 - X) = (TU * d.1, TU * d.2) := hTU
    have ht0 : toV2 (u1.2.2 - X) = (t0 * d.1, t0 * d.2) := by rw [hadj]; exact h0
    have e1 : b1 = t0 := param_unique hd (hWpar.symm.trans ht0)
    have hdn := nsq_pos hd
    unfold dt at hmemC
    rw [hW, ht0] at hmemC
    simp only at hmemC
    unfold nsq at hdn
    nlinarith
  obtain ⟨g, hg, g0, g1, hg0, hg1, hg01, hgs⟩ := walkU_cover' w2 hd hT b1 hs0 hsT.le
  have hne1 : b1 ≠ g1 := by
    intro e
    apply hnA
    refine ⟨g, hg, ?_⟩
    apply pt_eq_of_toV2 (H := X)
    rw [hg1, hWpar, e]
  have hlt : b1 < g1 := lt_of_le_of_ne hgs hne1
  have hσ0 : 0 < (b1 - g0) / (g1 - g0) := div_pos (by linarith) (by linarith)
  have hσ1 : (b1 - g0) / (g1 - g0) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hWg : u1.2.2 = g.2.1 + ((b1 - g0) / (g1 - g0)) • (g.2.2 - g.2.1) := pt_on_step hg01 hgs hg0 hg1 hWpar
  have hSA : StepU D.toRegionDissection b d u1 := walkU_mem_step w1 u1 hu1
  have hSB : StepU D.toRegionDissection b d u2 := walkU_mem_step w1 u2 hu2
  have hSg : StepU D.toRegionDissection (!b) d g := walkU_mem_step w2 g hg
  obtain ⟨H', hH'⟩ := gc_trans_walk D idx h hSA hSB hadj hSg hσ0 hσ1 hWg hord
  exact hGc _ _ hH'

/-- **Lemma 4.8, combinatorial form.**  Two divisions of the same segment on opposite sides: each `c`-element of `LA` has a partner in `LB` with the same two endpoints. -/
theorem block_pair (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseC D idx)
    (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2)) (hGc : ∀ X H, ¬ GcEdge D X H) {d : V2} (hd : d ≠ 0) {bA : Bool} :
    ∀ (n : ℕ) {X Y : Plane} {LA LB : List (Fin N × Plane × Plane)}, LA.length + LB.length = n →
      WalkU D.toRegionDissection bA d X Y LA → WalkU D.toRegionDissection (!bA) d X Y LB →
      ∀ e ∈ LA, dist e.2.1 e.2.2 = slen D 2 → ∃ f ∈ LB, f.2.1 = e.2.1 ∧ f.2.2 = e.2.2 := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X Y LA LB hn wA wB e he hec
  have hdpos : 0 < nsq d := nsq_pos hd
  have hLA : LA ≠ [] := List.ne_nil_of_mem he
  obtain ⟨T, -, hT, hTp, -⟩ := walkU_pos wA
  have hT0 : 0 < T := hTp hLA
  have hLB : LB ≠ [] := by
    rintro rfl
    have hXY := walkU_nil_eq wB
    subst hXY
    have h0 : toV2 (X - X) = (0 * d.1, 0 * d.2) := by unfold toV2; ext <;> simp
    have := param_unique hd (h0.symm.trans hT)
    linarith
  have wA2 : WalkU D.toRegionDissection (!(!bA)) d X Y LA := by simpa using wA
  -- first common end
  set AE : Finset Plane := (LA.map (fun x => x.2.2)).toFinset with hAE
  set C : Finset Plane := AE.filter (fun U => ∃ f ∈ LB, f.2.2 = U) with hCdef
  have hYC : Y ∈ C := by
    simp only [hCdef, hAE, Finset.mem_filter, List.mem_toFinset, List.mem_map]
    obtain ⟨g, hg, hgY⟩ := walkU_last wA hLA
    obtain ⟨f, hf, hfY⟩ := walkU_last wB hLB
    exact ⟨⟨g, hg, hgY⟩, f, hf, hfY⟩
  obtain ⟨Ul, hUlC, hUlmin⟩ := Finset.exists_min_image C (fun U => dt d (toV2 (U - X))) ⟨Y, hYC⟩
  have hUlC' := hUlC
  simp only [hCdef, hAE, Finset.mem_filter, List.mem_toFinset, List.mem_map] at hUlC'
  obtain ⟨⟨eS, heS, heSU⟩, fS, hfS, hfSU⟩ := hUlC'
  obtain ⟨PB, SB, hLBdec⟩ := List.append_of_mem hfS
  obtain ⟨PA, SA, hLAdec⟩ := List.append_of_mem heS
  have hmemC : ∀ U : Plane, (∃ g ∈ LA, g.2.2 = U) → (∃ f ∈ LB, f.2.2 = U) → dt d (toV2 (Ul - X)) ≤ dt d (toV2 (U - X)) := by
    intro U hA hB
    apply hUlmin
    simp only [hCdef, hAE, Finset.mem_filter, List.mem_toFinset, List.mem_map]
    obtain ⟨g, hg, hgU⟩ := hA
    exact ⟨⟨g, hg, hgU⟩, hB⟩
  have hmA : ∀ U : Plane, (∃ g ∈ LB, g.2.2 = U) → (∃ f ∈ LA, f.2.2 = U) → dt d (toV2 (eS.2.2 - X)) ≤ dt d (toV2 (U - X)) := by
    intro U hB hA; rw [heSU]; exact hmemC U hA hB
  have hmB : ∀ U : Plane, (∃ g ∈ LA, g.2.2 = U) → (∃ f ∈ LB, f.2.2 = U) → dt d (toV2 (fS.2.2 - X)) ≤ dt d (toV2 (U - X)) := by
    intro U hA hB; rw [hfSU]; exact hmemC U hA hB
  have cA := prefix_const D idx h hGc hd wA wB hLAdec hmA
  have cB := prefix_const D idx h hGc hd wB wA2 hLBdec hmB
  obtain ⟨wApre, wAsuf⟩ := split_end wA hLAdec
  obtain ⟨wBpre, wBsuf⟩ := split_end wB hLBdec
  have hendAB : eS.2.2 = fS.2.2 := heSU.trans hfSU.symm
  -- counts
  have hlenA : ∀ x ∈ (PA ++ [eS]).map (fun x => dist x.2.1 x.2.2), x = slen D 0 ∨ x = slen D 1 ∨ x = slen D 2 := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
    exact stepU_len_mem D idx h.hidx (walkU_mem_step wApre u hu)
  have hlenB : ∀ x ∈ (PB ++ [fS]).map (fun x => dist x.2.1 x.2.2), x = slen D 0 ∨ x = slen D 1 ∨ x = slen D 2 := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
    exact stepU_len_mem D idx h.hidx (walkU_mem_step wBpre u hu)
  have hsum : ((PA ++ [eS]).map (fun x => dist x.2.1 x.2.2)).sum = ((PB ++ [fS]).map (fun x => dist x.2.1 x.2.2)).sum := by
    rw [walkU_dist_sum wApre, walkU_dist_sum wBpre, hendAB]
  have hcnt := count_c_eq (slen_pos D 0) (slen_pos D 1) (slen_pos D 2) hab hac _ _ hlenA hlenB hsum
  have hLAlen : LA.length = (PA ++ [eS]).length + SA.length := by rw [hLAdec]; simp; omega
  have hLBlen : LB.length = (PB ++ [fS]).length + SB.length := by rw [hLBdec]; simp; omega
  have hpAne : 0 < (PA ++ [eS]).length := by simp
  have hpBne : 0 < (PB ++ [fS]).length := by simp
  have heLA : e ∈ PA ++ [eS] ∨ e ∈ SA := by
    have : e ∈ PA ++ eS :: SA := hLAdec ▸ he
    simp only [List.mem_append, List.mem_cons] at this ⊢
    tauto
  by_cases hcA : ∃ u ∈ PA ++ [eS], dist u.2.1 u.2.2 = slen D 2
  · -- the first block consists of single `c`-elements with the same endpoints
    obtain ⟨u0, hu0, hu0c⟩ := hcA
    have hAall : ∀ u ∈ PA ++ [eS], dist u.2.1 u.2.2 = slen D 2 := fun u hu => (cA u hu u0 hu0).mpr hu0c
    have hAcntpos : 1 ≤ ((PA ++ [eS]).map (fun x => dist x.2.1 x.2.2)).count (slen D 2) :=
      List.count_pos_iff.mpr (List.mem_map.mpr ⟨u0, hu0, hu0c⟩)
    have hBcntpos : 1 ≤ ((PB ++ [fS]).map (fun x => dist x.2.1 x.2.2)).count (slen D 2) := by rw [← hcnt]; exact hAcntpos
    obtain ⟨v0, hv0, hv0c⟩ := List.mem_map.mp (List.count_pos_iff.mp hBcntpos)
    have hBall : ∀ v ∈ PB ++ [fS], dist v.2.1 v.2.2 = slen D 2 := fun v hv => (cB v hv v0 hv0).mpr hv0c
    -- heads
    obtain ⟨a1, restA, hPA⟩ : ∃ a1 restA, PA ++ [eS] = a1 :: restA := List.exists_cons_of_ne_nil (by simp)
    obtain ⟨b1, restB, hPB⟩ : ∃ b1 restB, PB ++ [fS] = b1 :: restB := List.exists_cons_of_ne_nil (by simp)
    have ha1X : a1.2.1 = X := walkU_head (hPA ▸ wApre)
    have hb1X : b1.2.1 = X := walkU_head (hPB ▸ wBpre)
    have ha1mem : a1 ∈ PA ++ [eS] := by rw [hPA]; simp
    have hb1mem : b1 ∈ PB ++ [fS] := by rw [hPB]; simp
    have ha1c := hAall a1 ha1mem
    have hb1c := hBall b1 hb1mem
    have hSa : StepU D.toRegionDissection bA d a1 := walkU_mem_step wApre a1 ha1mem
    have hSb : StepU D.toRegionDissection (!bA) d b1 := walkU_mem_step wBpre b1 hb1mem
    obtain ⟨ca, hca, hva⟩ := stepU_vec hSa
    obtain ⟨cb, hcb, hvb⟩ := stepU_vec hSb
    have hsq : 0 < Real.sqrt (nsq d) := Real.sqrt_pos.mpr hdpos
    have hda := dist_of_toV2 hca.le hva
    have hdb := dist_of_toV2 hcb.le hvb
    have hcab : ca = cb := by
      rw [dist_comm] at hda hdb
      have : ca * Real.sqrt (nsq d) = cb * Real.sqrt (nsq d) := by rw [← hda, ← hdb, ha1c, hb1c]
      exact mul_right_cancel₀ hsq.ne' this
    have hZ : a1.2.2 = b1.2.2 := by
      apply pt_eq_of_toV2 (H := X)
      rw [ha1X] at hva; rw [hb1X] at hvb
      rw [hva, hvb, hcab]
    have ha1LA : a1 ∈ LA := by
      rw [hLAdec]; simp only [List.mem_append, List.mem_cons] at ha1mem ⊢; tauto
    have hb1LB : b1 ∈ LB := by
      rw [hLBdec]; simp only [List.mem_append, List.mem_cons] at hb1mem ⊢; tauto
    have hle := hmemC a1.2.2 ⟨a1, ha1LA, rfl⟩ ⟨b1, hb1LB, hZ.symm⟩
    have hrestA : restA = [] := by
      by_contra hne
      obtain ⟨r0, rest0, hr⟩ := List.exists_cons_of_ne_nil hne
      have w' : WalkU D.toRegionDissection bA d X eS.2.2 (a1 :: r0 :: rest0) := by rw [← hr, ← hPA]; exact wApre
      obtain ⟨T', hpos, hT'⟩ := walkU_two w'
      have := dt_step_lt (X := X) (Z := a1.2.2) hd hpos hT'
      rw [heSU] at this
      linarith
    have hrestB : restB = [] := by
      by_contra hne
      obtain ⟨r0, rest0, hr⟩ := List.exists_cons_of_ne_nil hne
      have w' : WalkU D.toRegionDissection (!bA) d X fS.2.2 (b1 :: r0 :: rest0) := by rw [← hr, ← hPB]; exact wBpre
      obtain ⟨T', hpos, hT'⟩ := walkU_two w'
      have := dt_step_lt (X := X) (Z := b1.2.2) hd hpos hT'
      rw [hfSU] at this
      have hZ' : dt d (toV2 (Ul - X)) ≤ dt d (toV2 (b1.2.2 - X)) := by rw [← hZ]; exact hle
      linarith
    rcases heLA with hpre | hsuf
    · -- `e` is the single element of the first block
      rw [hPA, hrestA] at hpre
      have hea : e = a1 := by simpa using hpre
      exact ⟨b1, hb1LB, by rw [hb1X, hea, ha1X], by rw [hea, hZ]⟩
    · have hlt : SA.length + SB.length < n := by omega
      obtain ⟨f, hf, hf1, hf2⟩ := ih _ hlt (X := Ul) (Y := Y) (LA := SA) (LB := SB) rfl (heSU ▸ wAsuf) (hfSU ▸ wBsuf) e hsuf hec
      exact ⟨f, by rw [hLBdec]; simp [hf], hf1, hf2⟩
  · -- the first block has no `c`-element on either side
    push_neg at hcA
    rcases heLA with hpre | hsuf
    · exact absurd hec (hcA e hpre)
    · have hlt : SA.length + SB.length < n := by omega
      obtain ⟨f, hf, hf1, hf2⟩ := ih _ hlt (X := Ul) (Y := Y) (LA := SA) (LB := SB) rfl (heSU ▸ wAsuf) (hfSU ▸ wBsuf) e hsuf hec
      exact ⟨f, by rw [hLBdec]; simp [hf], hf1, hf2⟩

end Erdos634.Draft.LaczFormal.RG

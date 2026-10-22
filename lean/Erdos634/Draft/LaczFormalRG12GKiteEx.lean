-- Draft/LaczFormalRG12GKiteEx.lean -- Laczkovich (DCG 48 (2012)), proof of Lemma 6.2: EXISTENCE of the outgoing edge of Gamma_kite ("there is exactly one kite having angle 2 alpha at Y", combined with
-- `gkite_succ_le_one` this is out-degree exactly one).  Route: an alpha-corner of the tile at `Y` gives the side `YZ` (length c, `Z` = its beta vertex); the midpoint of `YZ` is interior (convexity, `Y` interior);
-- `lemma48_pair` gives the partner tile; `pair_shape_tiles` gives KITE (then `GKite Y Z`) or PARALLELOGRAM, and the parallelogram case is excluded by counting the two beta corners of `Y` (they are the
-- tiles of the given kite `XY`, which forces `Z = X`) and `left_step_unique`.  Hypotheses: Case IIc (`CaseC`, `a,b` commensurable, `c` not a rational multiple of `a`, `gamma < pi/2`, `gamma != pi/3`).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Lemma 6.2, 4.8), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG12GKite
import Erdos634.Draft.LaczFormalRG12ShapeTile

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

theorem par_self_of_ne {u : V2} (hu : u ≠ 0) : Par u u := by
  refine ⟨by unfold crs; ring, ?_⟩
  have : u.1 ≠ 0 ∨ u.2 ≠ 0 := by
    by_contra hh; push Not at hh; exact hu (Prod.ext hh.1 hh.2)
  unfold dt
  rcases this with h | h
  · nlinarith [sq_pos_of_ne_zero h, sq_nonneg u.2]
  · nlinarith [sq_pos_of_ne_zero h, sq_nonneg u.1]

theorem tile_crs_ne (T : Tri) {kk f g : Fin 3} (hfk : f ≠ kk) (hgk : g ≠ kk) (hgf : g ≠ f) :
    crs (toV2 (T.pts f - T.pts kk)) (toV2 (T.pts g - T.pts kk)) ≠ 0 := by
  intro h
  rw [crs_toV2] at h
  have key : ∀ kk f g : Fin 3, f ≠ kk → g ≠ kk → g ≠ f → (f = kk + 1 ∧ g = kk + 2) ∨ (f = kk + 2 ∧ g = kk + 1) := by decide
  rcases key kk f g hfk hgk hgf with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · apply T.det_ne_zero
    rw [← T.det_cyclic kk, ← e1, ← e2]; exact h
  · apply T.det_ne_zero
    rw [← T.det_cyclic kk]
    rw [← e1, ← e2] at *
    unfold Erdos634.Geometry.cross at h ⊢
    nlinarith [h]

/-- Any side of a tile is a left step in one of its two orientations. -/
theorem tile_step_either (T : Tri) {kk f g : Fin 3} (hfk : f ≠ kk) (hgk : g ≠ kk) (hgf : g ≠ f) :
    ∃ d : V2, TriStep T d (T.pts kk) (T.pts f) ∨ TriStep T d (T.pts f) (T.pts kk) := by
  have hne := tile_crs_ne T hfk hgk hgf
  set d := toV2 (T.pts f - T.pts kk) with hd
  have hd0 : d ≠ 0 := by
    intro h0; apply hne; rw [h0]; unfold crs; simp
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · refine ⟨neg2 d, Or.inr ⟨f, kk, g, rfl, rfl, hfk.symm, hgf, hgk, ?_, ?_⟩⟩
    · have : toV2 (T.pts kk - T.pts f) = neg2 d := by
        rw [hd]; unfold toV2 neg2; ext <;> simp
      rw [this]
      have hn0 : neg2 d ≠ 0 := by
        intro h0; apply hd0
        have h1 := congrArg Prod.fst h0
        have h2 := congrArg Prod.snd h0
        simp [neg2] at h1 h2
        exact Prod.ext h1 h2
      exact par_self_of_ne hn0
    · have h1 : crs (neg2 d) (toV2 (T.pts g - T.pts f)) = - crs d (toV2 (T.pts g - T.pts kk)) := by
        rw [hd]; unfold crs neg2 toV2; simp; ring
      rw [h1]; linarith
  · exact ⟨d, Or.inl ⟨kk, f, g, rfl, rfl, hfk, hgk, hgf, par_self_of_ne hd0, hpos⟩⟩

theorem tile_sub_region (D : RegionDissection N) (i : Fin N) {x : Plane} (hx : x ∈ (D.tile i).carrier) : x ∈ D.region := by
  rw [← D.covers]; exact Set.mem_iUnion.2 ⟨i, hx⟩

theorem tile_pt_mem (T : Tri) (k : Fin 3) : T.pts k ∈ T.carrier := subset_convexHull ℝ _ ⟨k, rfl⟩

/-- Two left steps along the same oriented segment (directions positively parallel) belong to the same tile. -/
theorem same_side_tile_eq (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] {i i' : Fin N} {d d' : V2} {A B : Plane}
    (h : TriStep (D.tile i) d A B) (h' : TriStep (D.tile i') d' A B) : i = i' := by
  have hpar : Par (toV2 (B - A)) d := by obtain ⟨-, -, -, -, -, -, -, -, hp, -⟩ := h; exact hp
  have hpar' : Par (toV2 (B - A)) d' := by obtain ⟨-, -, -, -, -, -, -, -, hp, -⟩ := h'; exact hp
  exact (left_step_unique D.toRegionDissection (TriStep.of_par (hpar'.symm.trans hpar) h) h').1

/-- Partner tile of a `c`-side through an interior point, with the kite/parallelogram label data (`lemma48_pair` + `pair_shape_tiles`). -/
theorem pair_partner [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    {i : Fin N} {d : V2} {U V : Plane} (hS : TriStep (D.tile i) d U V) (hc : dist U V = slen D 2)
    {m : Plane} (hm : m ∈ openSegment ℝ U V) (hmi : m ∈ interior D.region) :
    ∃ j : Fin N, j ≠ i ∧ TriStep (D.tile j) (neg2 d) V U ∧ ∃ kk f kk' f' : Fin 3, (D.tile i).pts kk = U ∧ (D.tile i).pts f = V ∧
      (D.tile j).pts kk' = V ∧ (D.tile j).pts f' = U ∧
      ((idx j f' = idx i kk ∧ idx j kk' = idx i f) ∨ (idx j f' = idx i f ∧ idx j kk' = idx i kk)) := by
  obtain ⟨j, hji, hSj⟩ := lemma48_pair D P hreg idx hC hab hac hS hc hm hmi
  have h0 : slen D 0 ≠ slen D 2 := fun e => hac (e ▸ comm_refl' _)
  have h1 : slen D 1 ≠ slen D 2 := fun e => hac (e ▸ hab)
  obtain ⟨kk, f, g, kk', f', g', hk, hf, hk', hf', -, -, hcase⟩ := pair_shape_tiles D idx hC.hidx h0 h1 hS hSj hc
  refine ⟨j, hji, hSj, kk, f, kk', f', hk, hf, hk', hf', ?_⟩
  rcases hcase with ⟨-, e1, e2⟩ | ⟨-, e1, e2⟩
  · exact Or.inl ⟨e1, e2⟩
  · exact Or.inr ⟨e1, e2⟩

/-- **Laczkovich Lemma 6.2: out-degree of Gamma_kite is at least one** (with `gkite_succ_le_one`: exactly one): every edge `XY` of Gamma_kite is followed by an edge `YZ`. -/
theorem gkite_succ_exists [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) {X Y : Plane} (h : GKite D idx X Y) :
    ∃ Z, GKite D idx Y Z := by
  classical
  obtain ⟨⟨hYi, hc0, hc1, hc2⟩, -⟩ := gkite_vertex_type D P hreg idx hC.hidxA hC.hregc h1 h3 h
  obtain ⟨i1, j1, d1, kk1, f1, kk1', f1', hij1, hS1, hS1', hk1, hf1, hik1, hif1, hk1', hf1', hjk1, hjf1⟩ := h
  have hpos : 0 < cnt D idx Y 0 := by omega
  obtain ⟨⟨i0, a⟩, hmem⟩ := Finset.card_pos.1 (show 0 < (Finset.univ.filter (fun p : Fin N × Fin 3 => (D.tile p.1).pts p.2 = Y ∧ idx p.1 p.2 = 0)).card from hpos)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  obtain ⟨ha, hia⟩ := hmem
  obtain ⟨b, hb⟩ : ∃ b, idx i0 b = 1 := ⟨(idx i0).symm 1, by simp⟩
  obtain ⟨g, hg⟩ : ∃ g, idx i0 g = 2 := ⟨(idx i0).symm 2, by simp⟩
  have hba : b ≠ a := fun e => by rw [e, hia] at hb; exact absurd hb (by decide)
  have hga : g ≠ a := fun e => by rw [e, hia] at hg; exact absurd hg (by decide)
  have hgb : g ≠ b := fun e => by rw [e, hb] at hg; exact absurd hg (by decide)
  obtain ⟨Z, hZ⟩ : ∃ Z, (D.tile i0).pts b = Z := ⟨_, rfl⟩
  have hdist : dist Y Z = slen D 2 := by
    rw [← ha, ← hZ, hC.hidx i0 a b, hia, hb]
    exact dist_model_opp D 0 1 2 (by decide) (by decide) (by decide)
  have hconv : Convex ℝ D.region := hreg ▸ convPoly_convex P
  have hZmem : Z ∈ D.region := tile_sub_region D.toRegionDissection i0 (hZ ▸ tile_pt_mem _ b)
  have hseg : openSegment ℝ Y Z ⊆ interior D.region := hconv.openSegment_interior_self_subset_interior hYi hZmem
  have hmY : ((1 / 2 : ℝ) • Y + (1 / 2 : ℝ) • Z) ∈ openSegment ℝ Y Z := ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
  have hmZ : ((1 / 2 : ℝ) • Y + (1 / 2 : ℝ) • Z) ∈ openSegment ℝ Z Y := by rw [openSegment_symm]; exact hmY
  have hmi : ((1 / 2 : ℝ) • Y + (1 / 2 : ℝ) • Z) ∈ interior D.region := hseg hmY
  have pq1 : ((i1, f1) : Fin N × Fin 3) ≠ (j1, kk1') := fun e => hij1 (by simpa using congrArg Prod.fst e)
  -- the parallelogram case is impossible
  have par_contra : ∀ (d : V2) (j : Fin N) (cb ca : Fin 3), (D.tile j).pts cb = Y → idx j cb = 1 → (D.tile j).pts ca = Z → idx j ca = 0 →
      (TriStep (D.tile i0) d Y Z ∨ TriStep (D.tile i0) d Z Y) → False := by
    intro d j cb ca hcb hicb hca hica hS
    have hZX : Z = X := by
      rcases mem_of_cnt_two hc1 (p := (i1, f1)) (q := (j1, kk1')) (r := (j, cb)) ⟨hf1, hif1⟩ ⟨hk1', hjk1⟩ pq1 ⟨hcb, hicb⟩ with e | e
      · simp only [Prod.mk.injEq] at e
        obtain ⟨rfl, -⟩ := e
        have : ca = kk1 := (idx j).injective (hica.trans hik1.symm)
        rw [← hca, this, hk1]
      · simp only [Prod.mk.injEq] at e
        obtain ⟨rfl, -⟩ := e
        have : ca = f1' := (idx j).injective (hica.trans hjf1.symm)
        rw [← hca, this, hf1']
    subst hZX
    rcases hS with hS | hS
    · have := same_side_tile_eq D hS hS1'
      subst this
      have e : a = kk1' := (D.tile i0).indep.injective (ha.trans hk1'.symm)
      rw [e] at hia; rw [hia] at hjk1; exact absurd hjk1 (by decide)
    · have := same_side_tile_eq D hS hS1
      subst this
      have e : a = f1 := (D.tile i0).indep.injective (ha.trans hf1.symm)
      rw [e] at hia; rw [hia] at hif1; exact absurd hif1 (by decide)
  have injT : ∀ (t : Fin N) (u v : Fin 3), (D.tile t).pts u = (D.tile t).pts v → u = v := fun t u v e => (D.tile t).indep.injective e
  obtain ⟨d, hd⟩ := tile_step_either (D.tile i0) (kk := a) (f := b) (g := g) hba hga hgb
  rw [ha, hZ] at hd
  rcases hd with hS | hS
  · -- the tile `i0` is on the left of `Y -> Z`
    obtain ⟨j, hji, hSj, kk, f, kk', f', hkk, hff, hkk', hff', hcase⟩ := pair_partner D P hreg idx hC hab hac hS hdist hmY hmi
    have e1 : kk = a := injT i0 _ _ (hkk.trans ha.symm)
    have e2 : f = b := injT i0 _ _ ((hff.trans hZ.symm))
    rw [e1, hia, e2, hb] at hcase
    rcases hcase with ⟨c1, c2⟩ | ⟨c1, c2⟩
    · exact ⟨Z, i0, j, d, kk, f, kk', f', hji.symm, hS, hSj, hkk, hff, by rw [e1]; exact hia, by rw [e2]; exact hb, hkk', hff', c2, c1⟩
    · exact (par_contra d j f' kk' hff' c1 hkk' c2 (Or.inl hS)).elim
  · -- the tile `i0` is on the left of `Z -> Y`
    obtain ⟨j, hji, hSj, kk, f, kk', f', hkk, hff, hkk', hff', hcase⟩ := pair_partner D P hreg idx hC hab hac hS (by rw [dist_comm]; exact hdist) hmZ hmi
    have e1 : kk = b := injT i0 _ _ (hkk.trans hZ.symm)
    have e2 : f = a := injT i0 _ _ ((hff.trans ha.symm))
    rw [e1, hb, e2, hia] at hcase
    rcases hcase with ⟨c1, c2⟩ | ⟨c1, c2⟩
    · refine ⟨Z, j, i0, neg2 d, kk', f', kk, f, hji, hSj, ?_, hkk', hff', c2, c1, hkk, hff, by rw [e1]; exact hb, by rw [e2]; exact hia⟩
      rw [neg2_neg2']; exact hS
    · exact (par_contra d j kk' f' hkk' c2 hff' c1 (Or.inr hS)).elim

/-- **Gamma_kite has out-degree exactly one** (Laczkovich Lemma 6.2: "there is exactly one edge of Gamma_kite starting from Y"). -/
theorem gkite_succ_unique [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) {X Y : Plane} (h : GKite D idx X Y) :
    ∃! Z, GKite D idx Y Z := by
  obtain ⟨Z, hZ⟩ := gkite_succ_exists D P hreg idx hC hab hac h1 h3 h
  exact ⟨Z, hZ, fun Z' hZ' => gkite_succ_le_one D P hreg idx hC.hidxA hC.hregc h1 h3 hZ' hZ⟩

/-- Every vertex of an edge of Gamma_kite is a tile corner, so the set of tails is finite. -/
theorem gkite_tails_finite (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) :
    {X : Plane | ∃ Y, GKite D idx X Y}.Finite := by
  apply (Set.finite_range (fun p : Fin N × Fin 3 => (D.tile p.1).pts p.2)).subset
  rintro X ⟨Y, i, j, d, kk, f, kk', f', -, -, -, hk, -⟩
  exact ⟨(i, kk), hk⟩

/-- **Gamma_kite has in-degree exactly one.**  The successor map on the finite set of tails is injective (`gkite_pred_le_one`), hence surjective. -/
theorem gkite_pred_unique [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) {Y Z : Plane} (h : GKite D idx Y Z) :
    ∃! W, GKite D idx W Y := by
  classical
  set K : Set Plane := {X : Plane | ∃ Y, GKite D idx X Y} with hK
  haveI : Finite K := (gkite_tails_finite D idx).to_subtype
  have hex : ∀ X : K, ∃ Y : K, GKite D idx X.1 Y.1 := fun X => by
    obtain ⟨Y, hY⟩ := X.2
    obtain ⟨Z, hZ⟩ := gkite_succ_exists D P hreg idx hC hab hac h1 h3 hY
    exact ⟨⟨Y, Z, hZ⟩, hY⟩
  choose f hf using hex
  have hinj : Function.Injective f := fun X X' e => by
    apply Subtype.ext
    have a1 := hf X
    have a2 := hf X'
    rw [e] at a1
    exact gkite_pred_le_one D P hreg idx hC.hidxA hC.hregc h1 h3 a1 a2
  obtain ⟨W, hW⟩ := Finite.surjective_of_injective hinj ⟨Y, Z, h⟩
  refine ⟨W.1, ?_, fun W' hW' => ?_⟩
  · have := hf W; rw [hW] at this; exact this
  · have := hf W; rw [hW] at this
    exact gkite_pred_le_one D P hreg idx hC.hidxA hC.hregc h1 h3 hW' this

end Erdos634.Draft.LaczFormal.RG

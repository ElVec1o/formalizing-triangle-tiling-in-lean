-- Draft/LaczFormalIIcGenWitF.lean -- WITNESS of the GENERIC Case IIc block (alpha != beta), step F: the octagon is the union of the fan from `V0` (6 triangles), its volume, and the area identity
-- sum of the 204 tile areas = octagon area (exact, in Z[sqrt 2]).  A covering lemma for a closed convex target (copy of `ConvexCover.covers_of_volume` with `Tri` replaced by a set).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcGenWitE
import Erdos634.ConvexCover
import Erdos634.AreaDet

namespace Erdos634.Draft.LaczFormal.GenWit

open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.LaczFormal.Thm21 Z2 MeasureTheory

/-! ## A covering lemma for a closed convex target -/

theorem covers_of_volume_K {N : ℕ} (K : Set Plane) (hKc : IsClosed K) (hKconv : Convex ℝ K) (hKint : (interior K).Nonempty)
    (hKfin : volume K ≠ ⊤) (tile : Fin N → Tri) (hsub : ∀ i, (tile i).carrier ⊆ K)
    (hdisj : Pairwise fun i j => Disjoint (interior (tile i).carrier) (interior (tile j).carrier))
    (hvol : ∑ i, volume (tile i).carrier = volume K) : (⋃ i, (tile i).carrier) = K := by
  classical
  set U : Set Plane := ⋃ i, (tile i).carrier with hUdef
  have hUsub : U ⊆ K := Set.iUnion_subset hsub
  have hUvol : volume U = volume K := by
    rw [hUdef, Erdos634.ConvexCover.volume_iUnion_eq_sum tile hdisj, hvol]
  have hUclosed : IsClosed U := by
    rw [hUdef]
    exact isClosed_iUnion_of_finite fun i => (tile i).isCompact.isClosed
  refine Set.Subset.antisymm hUsub ?_
  by_contra hcon
  obtain ⟨x, hxT, hxU⟩ : ∃ x, x ∈ K ∧ x ∉ U := by
    by_contra hall
    push_neg at hall
    exact hcon fun x hx => hall x hx
  have hVopen : IsOpen (Uᶜ) := hUclosed.isOpen_compl
  have hxcl : x ∈ closure (interior K) := by
    have := hKconv.closure_interior_eq_closure_of_nonempty_interior hKint
    rw [this, hKc.closure_eq]
    exact hxT
  obtain ⟨y, hyV, hyI⟩ : ∃ y, y ∈ Uᶜ ∧ y ∈ interior K := mem_closure_iff.mp hxcl (Uᶜ) hVopen hxU
  set W : Set Plane := Uᶜ ∩ interior K with hWdef
  have hWopen : IsOpen W := hVopen.inter isOpen_interior
  have hWne : W.Nonempty := ⟨y, hyV, hyI⟩
  have hWpos : 0 < volume W := Erdos634.ConvexCover.volume_pos_of_isOpen hWopen hWne
  have hWsub : W ⊆ K := fun z hz => interior_subset hz.2
  have hWdisj : Disjoint U W := Set.disjoint_right.mpr fun z hz => hz.1
  have hsum : volume U + volume W ≤ volume K := by
    have hunion : volume (U ∪ W) = volume U + volume W :=
      measure_union₀ hWopen.measurableSet.nullMeasurableSet hWdisj.aedisjoint
    rw [← hunion]
    exact measure_mono (Set.union_subset hUsub hWsub)
  rw [hUvol] at hsum
  have : volume K + 0 < volume K + volume W := ENNReal.add_lt_add_left hKfin hWpos
  simp only [add_zero] at this
  exact absurd hsum (not_le.mpr this)

/-! ## Triangle membership by three edge signs -/

theorem cross2_det3 (u w x : Plane) : cross2 (u - w) (x - w) = det3 (w 0) (w 1) (u 0) (u 1) (x 0) (x 1) := by
  simp only [cross2, det3, PiLp.sub_apply]; ring

theorem cross2_swap (u w x : Plane) : cross2 (w - u) (x - u) = - cross2 (u - w) (x - w) := by
  simp only [cross2, PiLp.sub_apply]; ring

theorem posT_valid {t : TZ} (h : posT t = true) : validB t = true := by
  unfold posT at h
  have := (posB_iff _).mp h
  unfold validB
  simp only [Bool.not_eq_true', decide_eq_false_iff_not]
  intro e
  have := congrArg val e
  rw [val_zero] at this
  unfold detT at *
  linarith [(posB_iff _).mp h]

theorem mem_triZ_of_signs {t : TZ} (hp : posT t = true) (x : Plane)
    (h0 : 0 ≤ cross2 (ptR t.p2 - ptR t.p1) (x - ptR t.p1))
    (h1 : 0 ≤ cross2 (ptR t.p0 - ptR t.p2) (x - ptR t.p2))
    (h2 : 0 ≤ cross2 (ptR t.p1 - ptR t.p0) (x - ptR t.p0)) : x ∈ (triZ t).carrier := by
  have hv := posT_valid hp
  have hD : 0 < det3 (t.p0.1.val / 2) (t.p0.2.val / 2) (t.p1.1.val / 2) (t.p1.2.val / 2) (t.p2.1.val / 2) (t.p2.2.val / 2) := by
    rw [det3_ptR]
    have := (posB_iff _).mp hp
    unfold detT at this
    linarith
  unfold triZ
  rw [dif_pos (valid_det hv)]
  have hx : x = mkPt (x 0) (x 1) := by
    ext m; fin_cases m <;> simp
  rw [hx]
  rw [cross2_det3] at h0 h1 h2
  simp only [ptR_zero, ptR_one] at h0 h1 h2
  refine mem_carrier_of_dets (a := x 0) (b := x 1) hD ?_ ?_ ?_
  · have e : det3 (x 0) (x 1) (t.p1.1.val / 2) (t.p1.2.val / 2) (t.p2.1.val / 2) (t.p2.2.val / 2)
        = det3 (t.p1.1.val / 2) (t.p1.2.val / 2) (t.p2.1.val / 2) (t.p2.2.val / 2) (x 0) (x 1) := by simp only [det3]; ring
    rw [e]; exact h0
  · have e : det3 (t.p0.1.val / 2) (t.p0.2.val / 2) (x 0) (x 1) (t.p2.1.val / 2) (t.p2.2.val / 2)
        = det3 (t.p2.1.val / 2) (t.p2.2.val / 2) (t.p0.1.val / 2) (t.p0.2.val / 2) (x 0) (x 1) := by simp only [det3]; ring
    rw [e]; exact h1
  · exact h2

/-! ## The fan -/

def fanTZ (k : Fin 6) : TZ := ⟨polyN 0, polyN (k.val + 1), polyN (k.val + 2)⟩

theorem fanTab_eq : fanTab = List.ofFn fanTZ := by decide +kernel

theorem fanTZ_mem (k : Fin 6) : fanTZ k ∈ fanTab := by
  rw [fanTab_eq]; exact List.mem_ofFn.mpr ⟨k, rfl⟩

theorem fan_props (k : Fin 6) : posT (fanTZ k) = true ∧ inB (fanTZ k) = true := by
  have h := fan_ok
  rw [List.all_eq_true] at h
  simpa using h _ (fanTZ_mem k)

theorem pairsAll_pairwise : ∀ (l : List TZ), pairsAll l = true → l.Pairwise (fun t u => sepB t u = true)
  | [], _ => List.Pairwise.nil
  | t :: rest, h => by
    unfold pairsAll at h
    simp only [Bool.and_eq_true, List.all_eq_true] at h
    exact List.Pairwise.cons h.1 (pairsAll_pairwise rest h.2)

theorem fan_disjoint : Pairwise fun i j : Fin 6 => Disjoint (interior (triZ (fanTZ i)).carrier) (interior (triZ (fanTZ j)).carrier) := by
  have hp := pairsAll_pairwise _ fan_pairs_ok
  rw [fanTab_eq, List.pairwise_ofFn] at hp
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact sepB_sound _ _ (posT_valid (fan_props i).1) (posT_valid (fan_props j).1) (hp h)
  · exact (sepB_sound _ _ (posT_valid (fan_props j).1) (posT_valid (fan_props i).1) (hp h)).symm

theorem edge_fact {x : Plane} (hx : x ∈ octP.carrier) (j : ℕ) (hj : j + 1 < 8) :
    0 ≤ cross2 (ptR (polyN (j + 1)) - ptR (polyN j)) (x - ptR (polyN j)) := by
  have h := hx ⟨j, by omega⟩
  have e : (⟨j, by omega⟩ : Fin 8) + 1 = ⟨j + 1, hj⟩ := by
    apply Fin.ext
    simp only [Fin.val_add, Fin.val_one]
    omega
  rw [e] at h
  exact h

theorem edge_last {x : Plane} (hx : x ∈ octP.carrier) :
    0 ≤ cross2 (ptR (polyN 0) - ptR (polyN 7)) (x - ptR (polyN 7)) := by
  have h := hx 7
  have e : (7 : Fin 8) + 1 = 0 := by decide
  rw [e] at h
  exact h

theorem sector_select (s : ℕ → ℝ) (h1 : 0 ≤ s 1) (h7 : s 7 ≤ 0) : ∃ k : ℕ, k < 6 ∧ 0 ≤ s (k + 1) ∧ s (k + 2) ≤ 0 := by
  have key : ∀ n m : ℕ, 0 ≤ s m → s (m + n + 1) ≤ 0 → ∃ k : ℕ, k ≤ n ∧ 0 ≤ s (m + k) ∧ s (m + k + 1) ≤ 0 := by
    intro n
    induction n with
    | zero => intro m h0 h1; exact ⟨0, le_refl _, by simpa using h0, by simpa using h1⟩
    | succ n ih =>
      intro m h0 h1
      by_cases hc : s (m + 1) ≤ 0
      · exact ⟨0, Nat.zero_le _, by simpa using h0, by simpa using hc⟩
      · push_neg at hc
        obtain ⟨k, hk, hk1, hk2⟩ := ih (m + 1) hc.le (by
          have : m + 1 + n + 1 = m + (n + 1) + 1 := by omega
          rw [this]; exact h1)
        refine ⟨k + 1, by omega, ?_, ?_⟩
        · have : m + (k + 1) = m + 1 + k := by omega
          rw [this]; exact hk1
        · have : m + (k + 1) + 1 = m + 1 + k + 1 := by omega
          rw [this]; exact hk2
  obtain ⟨k, hk, hk1, hk2⟩ := key 5 1 h1 h7
  exact ⟨k, by omega, by simpa [add_comm] using hk1, by
    have : 1 + k + 1 = k + 2 := by omega
    rw [this] at hk2; exact hk2⟩

theorem fan_cover {x : Plane} (hx : x ∈ octP.carrier) : ∃ k : Fin 6, x ∈ (triZ (fanTZ k)).carrier := by
  set s : ℕ → ℝ := fun n => cross2 (ptR (polyN n) - ptR (polyN 0)) (x - ptR (polyN 0)) with hs
  have h1 : 0 ≤ s 1 := edge_fact hx 0 (by norm_num)
  have h7 : s 7 ≤ 0 := by
    have := edge_last hx
    rw [cross2_swap] at this
    show cross2 (ptR (polyN 7) - ptR (polyN 0)) (x - ptR (polyN 0)) ≤ 0
    linarith
  obtain ⟨k, hk, hk1, hk2⟩ := sector_select s h1 h7
  refine ⟨⟨k, hk⟩, ?_⟩
  refine mem_triZ_of_signs (fan_props ⟨k, hk⟩).1 x ?_ ?_ ?_
  · exact edge_fact hx (k + 1) (by omega)
  · show 0 ≤ cross2 (ptR (polyN 0) - ptR (polyN (k + 2))) (x - ptR (polyN (k + 2)))
    rw [cross2_swap]
    have : s (k + 2) ≤ 0 := hk2
    simp only [hs] at this
    linarith
  · exact hk1

theorem oct_eq_fans : octP.carrier = ⋃ k : Fin 6, (triZ (fanTZ k)).carrier := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨k, hk⟩ := fan_cover hx
    exact Set.mem_iUnion.mpr ⟨k, hk⟩
  · exact Set.iUnion_subset fun k => triZ_sub_oct (posT_valid (fan_props k).1) (fan_props k).2

/-! ## Areas -/

theorem abs_val (z : Z2) : |z.val| = (absZ z).val := by
  unfold absZ
  by_cases h : posB z = true
  · rw [if_pos h, abs_of_pos ((posB_iff z).mp h)]
  · rw [if_neg h]
    have : z.val ≤ 0 := by
      by_contra hh; push_neg at hh; exact h ((posB_iff z).mpr hh)
    rw [abs_of_nonpos this, val_neg]

theorem detTri_triZ {t : TZ} (hv : validB t = true) : Erdos634.AreaDet.detTri (triZ t) = (detT t).val / 4 := by
  unfold triZ
  rw [dif_pos (valid_det hv), detTri_mkTri, det3_ptR]
  rfl

theorem foldl_val (l : List Z2) (z : Z2) : (l.foldl add z).val = z.val + (l.map val).sum := by
  induction l generalizing z with
  | nil => simp
  | cons a l ih => simp only [List.foldl_cons, List.map_cons, List.sum_cons]; rw [ih, val_add]; ring

theorem sumZ_val (l : List Z2) : (sumZ l).val = (l.map val).sum := by
  unfold sumZ; rw [foldl_val, val_zero]; ring

theorem sum_ofFn_eq {α : Type} {n : ℕ} (l : List α) (f : Fin n → α) (hf : List.ofFn f = l) (g : α → ℝ) : ∑ i, g (f i) = (l.map g).sum := by
  rw [← hf, List.map_ofFn, List.sum_ofFn]; rfl

theorem ofFn_TT : List.ofFn TT = tileTab := by
  apply List.ext_getElem
  · rw [List.length_ofFn, tileTab_length]
  · intro n h1 h2
    simp only [List.getElem_ofFn]
    rw [TT_eq]

theorem area_sum_eq : ∑ i : Fin 204, |Erdos634.AreaDet.detTri (triZ (TT i))| = ∑ k : Fin 6, |Erdos634.AreaDet.detTri (triZ (fanTZ k))| := by
  have e1 : ∀ i : Fin 204, |Erdos634.AreaDet.detTri (triZ (TT i))| = (absZ (detT (TT i))).val / 4 := by
    intro i
    rw [detTri_triZ (TT_props i).1, abs_div, abs_val]; norm_num
  have e2 : ∀ k : Fin 6, |Erdos634.AreaDet.detTri (triZ (fanTZ k))| = (absZ (detT (fanTZ k))).val / 4 := by
    intro k
    rw [detTri_triZ (posT_valid (fan_props k).1), abs_div, abs_val]; norm_num
  simp only [e1, e2, ← Finset.sum_div]
  congr 1
  have a1 := sum_ofFn_eq tileTab TT ofFn_TT (fun t => (absZ (detT t)).val)
  have a2 := sum_ofFn_eq fanTab fanTZ fanTab_eq.symm (fun t => (absZ (detT t)).val)
  rw [a1, a2]
  have := congrArg val sums_ok
  rw [sumZ_val, sumZ_val] at this
  simpa [List.map_map, Function.comp_def] using this

theorem oct_convex : Convex ℝ octP.carrier := by
  have : octP.carrier = ⋂ i : Fin 8, {z : Plane | 0 ≤ cross2 (octP.v (i + 1) - octP.v i) (z - octP.v i)} := by
    ext z; simp [ConvPoly.carrier]
  rw [this]
  exact convex_iInter fun i => halfplane_convex _ _

theorem oct_closed : IsClosed octP.carrier := by
  rw [oct_eq_fans]
  exact isClosed_iUnion_of_finite fun k => (triZ (fanTZ k)).isCompact.isClosed

theorem oct_interior : (interior octP.carrier).Nonempty := by
  obtain ⟨x, hx⟩ := (triZ (fanTZ 0)).interior_nonempty
  exact ⟨x, interior_mono (triZ_sub_oct (posT_valid (fan_props 0).1) (fan_props 0).2) hx⟩

theorem oct_vol_fin : volume octP.carrier ≠ ⊤ := by
  have : IsCompact octP.carrier := by
    rw [oct_eq_fans]
    exact isCompact_iUnion fun k => (triZ (fanTZ k)).isCompact
  exact this.measure_lt_top.ne

theorem vol_oct : volume octP.carrier = ∑ k : Fin 6, volume (triZ (fanTZ k)).carrier := by
  conv_lhs => rw [oct_eq_fans]
  exact Erdos634.ConvexCover.volume_iUnion_eq_sum _ fan_disjoint

theorem vol_tiles : ∑ i : Fin 204, volume (triZ (TT i)).carrier = volume octP.carrier := by
  rw [vol_oct]
  simp only [Erdos634.AreaDet.volume_eq_det_mul]
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _),
    ← ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _), area_sum_eq]

/-- **The 204 tiles cover the octagon.** -/
theorem tiles_cover : (⋃ i : Fin 204, (triZ (TT i)).carrier) = octP.carrier :=
  covers_of_volume_K octP.carrier oct_closed oct_convex oct_interior oct_vol_fin _
    (fun i => triZ_sub_oct (TT_props i).1 (TT_props i).2.2) tile_disjoint vol_tiles

end Erdos634.Draft.LaczFormal.GenWit

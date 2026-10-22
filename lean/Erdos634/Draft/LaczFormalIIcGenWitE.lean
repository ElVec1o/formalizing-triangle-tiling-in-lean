-- Draft/LaczFormalIIcGenWitE.lean -- WITNESS of the GENERIC Case IIc block (alpha != beta), step E: from the Bool checks to the reals.
-- Real points `ptR`, triangles `triZ`, congruence to the model, the octagon `octP : ConvPoly 8`, containment, separating-line soundness, pairwise disjoint interiors of the 204 tiles.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcGenWitC
import Erdos634.Draft.LaczFormalIIcGenWitD
import Erdos634.Draft.LaczFormalIIcGenWitD2
import Erdos634.Draft.LaczFormalThm21Loc
import Erdos634.SssCongruent

namespace Erdos634.Draft.LaczFormal.GenWit

open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.LaczFormal.Thm21 Z2

noncomputable def ptR (p : Pt) : Plane := mkPt (p.1.val / 2) (p.2.val / 2)

theorem ptR_zero (p : Pt) : ptR p 0 = p.1.val / 2 := by simp [ptR]
theorem ptR_one (p : Pt) : ptR p 1 = p.2.val / 2 := by simp [ptR]

theorem det3_ptR (p q r : Pt) :
    det3 (p.1.val / 2) (p.2.val / 2) (q.1.val / 2) (q.2.val / 2) (r.1.val / 2) (r.2.val / 2) = (detZ p q r).val / 4 := by
  unfold det3 detZ; simp only [val_sub, val_mul]; ring

theorem dist_sq_ptR (p q : Pt) : dist (ptR p) (ptR q) ^ 2 = (d2 p q).val / 4 := by
  unfold ptR; rw [dist_sq_mkPt]; unfold d2; simp only [val_add, val_sub, val_mul]; ring

theorem cross2_ptR (a b c : Pt) : cross2 (ptR b - ptR a) (ptR c - ptR a) = (detZ a b c).val / 4 := by
  simp only [cross2, PiLp.sub_apply, ptR_zero, ptR_one]; unfold detZ; simp only [val_sub, val_mul]; ring

/-- the triangle of a `TZ` (a harmless fallback if degenerate). -/
noncomputable def triZ (t : TZ) : Tri :=
  if h : det3 (t.p0.1.val / 2) (t.p0.2.val / 2) (t.p1.1.val / 2) (t.p1.2.val / 2) (t.p2.1.val / 2) (t.p2.2.val / 2) ≠ 0 then
    mkTri _ _ _ _ _ _ h
  else mkTri 0 0 1 0 0 1 (by norm_num [det3])

theorem valid_det {t : TZ} (h : validB t = true) :
    det3 (t.p0.1.val / 2) (t.p0.2.val / 2) (t.p1.1.val / 2) (t.p1.2.val / 2) (t.p2.1.val / 2) (t.p2.2.val / 2) ≠ 0 := by
  have h1 : ¬ (detT t = zero) := by simpa [validB] using h
  rw [det3_ptR]
  intro e
  apply h1
  apply (val_eq_zero_iff _).mp
  unfold detT; linarith

theorem triZ_pts {t : TZ} (h : validB t = true) (k : Fin 3) : (triZ t).pts k = ptR (t.pt k) := by
  unfold triZ; rw [dif_pos (valid_det h)]
  fin_cases k <;> rfl

theorem valid_model : validB modelTZ = true := by decide

theorem congB_spec {t : TZ} (h : congB t = true) (k l : Fin 3) : d2 (t.pt k) (t.pt l) = d2 (modelTZ.pt k) (modelTZ.pt l) := by
  unfold congB at h
  simp only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] at h
  exact h k l

theorem triZ_sq {t : TZ} (hv : validB t = true) (hc : congB t = true) (i j : Fin 3) :
    dist ((triZ t).pts i) ((triZ t).pts j) ^ 2 = dist ((triZ modelTZ).pts i) ((triZ modelTZ).pts j) ^ 2 := by
  rw [triZ_pts hv i, triZ_pts hv j, triZ_pts valid_model i, triZ_pts valid_model j, dist_sq_ptR, dist_sq_ptR, congB_spec hc i j]

theorem triZ_dist {t : TZ} (hv : validB t = true) (hc : congB t = true) (i j : Fin 3) :
    dist ((triZ t).pts i) ((triZ t).pts j) = dist ((triZ modelTZ).pts i) ((triZ modelTZ).pts j) :=
  Erdos634.SssCongruent.dist_of_sq (triZ_sq hv hc i j)

theorem triZ_cong {t : TZ} (hv : validB t = true) (hc : congB t = true) : (triZ t).Congruent (triZ modelTZ) := by
  refine Erdos634.SssCongruent.congruent_of_sq_dist_perm 1 ?_
  intro i j
  simpa using triZ_sq hv hc i j

/-! ## The octagon -/

theorem conv_spec (i j : Fin 8) (h1 : j ≠ i) (h2 : j ≠ i + 1) : posB (detZ (polyV i) (polyV (i + 1)) (polyV j)) = true := by
  have h := conv_ok
  unfold convB at h
  rw [List.all_eq_true] at h
  have h := h i (List.mem_finRange i)
  rw [List.all_eq_true] at h
  have h := h j (List.mem_finRange j)
  simpa [h1, h2] using h

noncomputable def octP : ConvPoly 8 where
  v := fun i => ptR (polyV i)
  three_le := by norm_num
  left := by
    intro i j h1 h2
    show 0 < cross2 (ptR (polyV (i + 1)) - ptR (polyV i)) (ptR (polyV j) - ptR (polyV i))
    rw [cross2_ptR]
    have := (posB_iff _).mp (conv_spec i j h1 h2)
    linarith

theorem tri_sub_oct (T : Tri) (h : ∀ i k, 0 ≤ cross2 (octP.v (i + 1) - octP.v i) (T.pts k - octP.v i)) : T.carrier ⊆ octP.carrier := by
  intro x hx i
  have hS := halfplane_convex (octP.v (i + 1) - octP.v i) (octP.v i)
  have : T.carrier ⊆ {z : Plane | 0 ≤ cross2 (octP.v (i + 1) - octP.v i) (z - octP.v i)} :=
    convexHull_min (Set.range_subset_iff.mpr (fun k => h i k)) hS
  exact this hx

theorem vtxB_spec {f : Pt → Bool} {t : TZ} (h : vtxB f t = true) (k : Fin 3) : f (t.pt k) = true := by
  unfold vtxB at h
  simp only [Bool.and_eq_true] at h
  fin_cases k
  · exact h.1.1
  · exact h.1.2
  · exact h.2

theorem inB_spec {t : TZ} (h : inB t = true) (e : Fin 8) (k : Fin 3) : geB (detZ (polyV e) (polyV (e + 1)) (t.pt k)) = true := by
  unfold inB at h
  rw [List.all_eq_true] at h
  exact vtxB_spec (h e (List.mem_finRange e)) k

theorem triZ_sub_oct {t : TZ} (hv : validB t = true) (hi : inB t = true) : (triZ t).carrier ⊆ octP.carrier := by
  apply tri_sub_oct
  intro i k
  rw [triZ_pts hv]
  show 0 ≤ cross2 (ptR (polyV (i + 1)) - ptR (polyV i)) (ptR (t.pt k) - ptR (polyV i))
  rw [cross2_ptR]
  have := (geB_iff _).mp (inB_spec hi i k)
  linarith

/-! ## Separation -/

theorem sep_of_vertices {t u : Tri} (f : Plane →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0) (c : ℝ) (h1 : ∀ k, f (t.pts k) ≤ c) (h2 : ∀ k, c ≤ f (u.pts k)) :
    Disjoint (interior t.carrier) (interior u.carrier) := by
  refine Erdos634.CertGeom.interiors_disjoint_of_separating f hf c (Erdos634.CertGeom.le_of_forall_pts_le f h1) ?_
  intro x hx
  have := Erdos634.CertGeom.le_of_forall_pts_le (t := u) (-f) (c := -c) (fun k => by
    have := h2 k
    simp only [AffineMap.coe_neg, Pi.neg_apply]; linarith) x hx
  simp only [AffineMap.coe_neg, Pi.neg_apply] at this
  linarith

theorem edgeSep_sound (p q : Pt) (A B : TZ) (hA : validB A = true) (hB : validB B = true) (h : edgeSep p q A B = true) :
    Disjoint (interior (triZ A).carrier) (interior (triZ B).carrier) := by
  unfold edgeSep at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨hpq, h⟩ := h
  have hne : (p.1.val / 2 ≠ q.1.val / 2) ∨ (p.2.val / 2 ≠ q.2.val / 2) := by
    by_contra hcon
    push_neg at hcon
    apply hpq
    exact Prod.ext (val_inj (by linarith [hcon.1])) (val_inj (by linarith [hcon.2]))
  have hf := Erdos634.CertGeom.lineFun_linear_ne_zero hne
  have hval : ∀ v : Pt, Erdos634.CertGeom.lineFun (p.1.val / 2) (p.2.val / 2) (q.1.val / 2) (q.2.val / 2) (ptR v) = (detZ p q v).val / 4 := by
    intro v
    rw [Erdos634.CertGeom.lineFun_apply, ptR_one, ptR_zero]
    unfold detZ; simp only [val_sub, val_mul]; ring
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine (sep_of_vertices _ hf 0 (t := triZ B) (u := triZ A) ?_ ?_).symm
    · intro k
      rw [triZ_pts hB, hval]
      have := (leB_iff _).mp (vtxB_spec h2 k)
      linarith
    · intro k
      rw [triZ_pts hA, hval]
      have := (geB_iff _).mp (vtxB_spec h1 k)
      linarith
  · refine sep_of_vertices _ hf 0 (t := triZ A) (u := triZ B) ?_ ?_
    · intro k
      rw [triZ_pts hA, hval]
      have := (leB_iff _).mp (vtxB_spec h1 k)
      linarith
    · intro k
      rw [triZ_pts hB, hval]
      have := (geB_iff _).mp (vtxB_spec h2 k)
      linarith

theorem sepB_sound (A B : TZ) (hA : validB A = true) (hB : validB B = true) (h : sepB A B = true) :
    Disjoint (interior (triZ A).carrier) (interior (triZ B).carrier) := by
  unfold sepB at h
  simp only [Bool.or_eq_true] at h
  rcases h with ((((h | h) | h) | h) | h) | h <;> exact edgeSep_sound _ _ A B hA hB h

/-! ## The 204 tiles -/

def TT (i : Fin 204) : TZ := tileTab.getD i.val default

theorem TT_eq (i : Fin 204) : TT i = tileTab[i.val]'(by rw [tileTab_length]; exact i.2) := by
  unfold TT
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [tileTab_length]; exact i.2)]
  rfl

theorem TT_mem (i : Fin 204) : TT i ∈ tileTab := by rw [TT_eq]; exact List.getElem_mem _

theorem TT_props (i : Fin 204) : validB (TT i) = true ∧ congB (TT i) = true ∧ inB (TT i) = true := by
  have h := tiles_ok
  rw [List.all_eq_true] at h
  have := h _ (TT_mem i)
  simpa [Bool.and_eq_true, and_assoc] using this

theorem TT_sep (i j : Fin 204) (hij : i < j) : sepB (TT i) (TT j) = true := by
  have h := rowOK_all i.val i.2
  unfold rowOK at h
  rw [List.all_eq_true] at h
  have hmem : TT j ∈ tileTab.drop (i.val + 1) := by
    rw [TT_eq j]
    have hj : j.val - (i.val + 1) < (tileTab.drop (i.val + 1)).length := by
      rw [List.length_drop, tileTab_length]; have := j.2; have : i.val < j.val := hij; omega
    have := List.getElem_mem hj
    rw [List.getElem_drop] at this
    have e : i.val + 1 + (j.val - (i.val + 1)) = j.val := by have : i.val < j.val := hij; omega
    simpa [e] using this
  have := h _ hmem
  have e : tileTab.getD i.val default = TT i := rfl
  rwa [e] at this

theorem tile_disjoint : Pairwise fun i j : Fin 204 => Disjoint (interior (triZ (TT i)).carrier) (interior (triZ (TT j)).carrier) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact sepB_sound _ _ (TT_props i).1 (TT_props j).1 (TT_sep i j h)
  · exact (sepB_sound _ _ (TT_props j).1 (TT_props i).1 (TT_sep j i h)).symm

end Erdos634.Draft.LaczFormal.GenWit

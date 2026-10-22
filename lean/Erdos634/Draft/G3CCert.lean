-- Draft/G3CCert.lean — G3C (room FINISH, seat HILBERT). UNAUDITED. No sorry/native_decide/axioms.
-- GENERIC hierarchical positive certificate checker for congruent dissections of a triangle, on the
-- integer lattice (X, v) <-> real point (X, v*sqrt 3).  Certificate = list of clusters, each a BSP tree
-- (leaves = tiles); clusters are separated pairwise by explicit lines.  Check is O(N depth + k^2 N/k).
-- Soundness: `cert_cd : c.ok = true -> CongruentDissection c.leaves.length` (target/model recorded).
import Erdos634.CertCoord
import Erdos634.CertGeom
import Erdos634.SssCongruent
import Erdos634.AreaDet

open scoped Classical

namespace Erdos634.Draft.G3CCert

open Erdos634.Geometry Erdos634.CertCoord

abbrev LP := ℤ × ℤ
abbrev LT := LP × LP × LP

def cross (o a b : LP) : ℤ := (a.1 - o.1) * (b.2 - o.2) - (b.1 - o.1) * (a.2 - o.2)
def d2 (p q : LP) : ℤ := (p.1 - q.1) ^ 2 + 3 * (p.2 - q.2) ^ 2
def vtx (t : LT) (i : Fin 3) : LP := ![t.1, t.2.1, t.2.2] i

inductive Bsp
  | leaf (t : LT)
  | split (P Q : LP) (l r : Bsp)

def Bsp.leaves : Bsp → List LT
  | .leaf t => [t]
  | .split _ _ l r => l.leaves ++ r.leaves

/-- all three vertices weakly on the left (cross ≥ 0) of the line P→Q -/
def geT (P Q : LP) (t : LT) : Bool :=
  decide (0 ≤ cross P Q t.1) && decide (0 ≤ cross P Q t.2.1) && decide (0 ≤ cross P Q t.2.2)
def leT (P Q : LP) (t : LT) : Bool :=
  decide (cross P Q t.1 ≤ 0) && decide (cross P Q t.2.1 ≤ 0) && decide (cross P Q t.2.2 ≤ 0)

def Bsp.ok : Bsp → Bool
  | .leaf _ => true
  | .split P Q l r =>
    decide (P ≠ Q) && l.ok && r.ok && l.leaves.all (geT P Q) && r.leaves.all (leT P Q)

/-- A tile pair is separated by a nonconstant line (P ≠ Q) -/
def SepT (A B : LT) : Prop :=
  ∃ P Q : LP, P ≠ Q ∧
    (((0 ≤ cross P Q A.1 ∧ 0 ≤ cross P Q A.2.1 ∧ 0 ≤ cross P Q A.2.2) ∧
      (cross P Q B.1 ≤ 0 ∧ cross P Q B.2.1 ≤ 0 ∧ cross P Q B.2.2 ≤ 0)) ∨
     ((cross P Q A.1 ≤ 0 ∧ cross P Q A.2.1 ≤ 0 ∧ cross P Q A.2.2 ≤ 0) ∧
      (0 ≤ cross P Q B.1 ∧ 0 ≤ cross P Q B.2.1 ∧ 0 ≤ cross P Q B.2.2)))

theorem geT_iff {P Q : LP} {t : LT} :
    geT P Q t = true ↔ (0 ≤ cross P Q t.1 ∧ 0 ≤ cross P Q t.2.1 ∧ 0 ≤ cross P Q t.2.2) := by
  simp [geT, and_assoc]
theorem leT_iff {P Q : LP} {t : LT} :
    leT P Q t = true ↔ (cross P Q t.1 ≤ 0 ∧ cross P Q t.2.1 ≤ 0 ∧ cross P Q t.2.2 ≤ 0) := by
  simp [leT, and_assoc]

theorem Bsp.ok_pairwise : ∀ (t : Bsp), t.ok = true → t.leaves.Pairwise SepT
  | .leaf _, _ => by simp [Bsp.leaves]
  | .split P Q l r, h => by
    simp only [Bsp.ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨⟨⟨⟨hne, hl⟩, hr⟩, hgl⟩, hlr⟩ := h
    simp only [Bsp.leaves, List.pairwise_append]
    refine ⟨Bsp.ok_pairwise l hl, Bsp.ok_pairwise r hr, ?_⟩
    intro a ha b hb
    exact ⟨P, Q, hne, Or.inl ⟨geT_iff.mp (hgl a ha), leT_iff.mp (hlr b hb)⟩⟩

/-- line P→Q separates cluster A (left) from cluster B (right) -/
def clSep (P Q : LP) (A B : Bsp) : Bool :=
  decide (P ≠ Q) && A.leaves.all (geT P Q) && B.leaves.all (leT P Q)

def rowOK (c : Bsp) : List Bsp → List (LP × LP) → Option (List (LP × LP))
  | [], s => some s
  | d :: ds, (PQ :: s) => if clSep PQ.1 PQ.2 c d then rowOK c ds s else none
  | _ :: _, [] => none

def pairsOK : List Bsp → List (LP × LP) → Option (List (LP × LP))
  | [], s => some s
  | c :: cs, s => match rowOK c cs s with
    | none => none
    | some s' => pairsOK cs s'

theorem rowOK_sound (c : Bsp) : ∀ (ds : List Bsp) (s s' : List (LP × LP)),
    rowOK c ds s = some s' → ∀ d ∈ ds, ∀ a ∈ c.leaves, ∀ b ∈ d.leaves, SepT a b
  | [], s, s', _ => by simp
  | d :: ds, [], s', h => by simp [rowOK] at h
  | d :: ds, (PQ :: s), s', h => by
    simp only [rowOK] at h
    split at h
    · rename_i hc
      intro e he a ha b hb
      rcases List.mem_cons.mp he with rfl | he'
      · simp only [clSep, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
        exact ⟨PQ.1, PQ.2, hc.1.1, Or.inl ⟨geT_iff.mp (hc.1.2 a ha), leT_iff.mp (hc.2 b hb)⟩⟩
      · exact rowOK_sound c ds s s' h e he' a ha b hb
    · simp at h

theorem pairsOK_sound : ∀ (cs : List Bsp) (s s' : List (LP × LP)), pairsOK cs s = some s' →
    cs.Pairwise (fun A B => ∀ a ∈ A.leaves, ∀ b ∈ B.leaves, SepT a b)
  | [], s, s', _ => by simp
  | c :: cs, s, s', h => by
    simp only [pairsOK] at h
    split at h
    · simp at h
    · rename_i s1 hrow
      rw [List.pairwise_cons]
      refine ⟨fun d hd a ha b hb => rowOK_sound c cs s s1 hrow d hd a ha b hb, ?_⟩
      exact pairsOK_sound cs s1 s' h

structure Cert where
  target : LT
  model : LT
  clusters : List Bsp
  seps : List (LP × LP)

def Cert.leaves (c : Cert) : List LT := (c.clusters.map Bsp.leaves).flatten

def posT (t : LT) : Bool := decide (0 < cross t.1 t.2.1 t.2.2)

def insideT (T t : LT) : Bool :=
  [t.1, t.2.1, t.2.2].all (fun v =>
    decide (0 ≤ cross T.1 T.2.1 v) && decide (0 ≤ cross T.2.1 T.2.2 v) && decide (0 ≤ cross T.2.2 T.1 v))

def sig6 : List (Equiv.Perm (Fin 3)) :=
  [1, Equiv.swap 0 1, Equiv.swap 1 2, Equiv.swap 0 2, Equiv.swap 0 1 * Equiv.swap 1 2,
   Equiv.swap 1 2 * Equiv.swap 0 1]

def congT (M t : LT) : Bool :=
  sig6.any (fun σ => (List.finRange 3).all (fun i => (List.finRange 3).all (fun j =>
    decide (d2 (vtx t i) (vtx t j) = d2 (vtx M (σ i)) (vtx M (σ j))))))

def Cert.ok (c : Cert) : Bool :=
  posT c.target && posT c.model &&
  c.clusters.all Bsp.ok &&
  decide (pairsOK c.clusters c.seps = some []) &&
  c.leaves.all posT && c.leaves.all (insideT c.target) && c.leaves.all (congT c.model) &&
  decide ((c.leaves.map (fun t => cross t.1 t.2.1 t.2.2)).sum = cross c.target.1 c.target.2.1 c.target.2.2)

/-! ## Geometry -/

noncomputable def rx (p : LP) : ℝ := (p.1 : ℝ)
noncomputable def ry (p : LP) : ℝ := (p.2 : ℝ) * Real.sqrt 3
noncomputable def toPt (p : LP) : Plane := mkPt (rx p) (ry p)

theorem s3pos : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
theorem s3sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

theorem det3_lat (o a b : LP) :
    det3 (rx o) (ry o) (rx a) (ry a) (rx b) (ry b) = Real.sqrt 3 * (cross o a b : ℝ) := by
  simp only [det3, rx, ry, cross]; push_cast; ring

theorem det3_pos {t : LT} (h : 0 < cross t.1 t.2.1 t.2.2) :
    0 < det3 (rx t.1) (ry t.1) (rx t.2.1) (ry t.2.1) (rx t.2.2) (ry t.2.2) := by
  rw [det3_lat]; exact mul_pos s3pos (by exact_mod_cast h)

noncomputable def triOf (t : LT) (h : 0 < cross t.1 t.2.1 t.2.2) : Tri :=
  mkTri (rx t.1) (ry t.1) (rx t.2.1) (ry t.2.1) (rx t.2.2) (ry t.2.2) (det3_pos h).ne'

theorem triOf_pts (t : LT) (h : 0 < cross t.1 t.2.1 t.2.2) (k : Fin 3) :
    (triOf t h).pts k = toPt (vtx t k) := by
  fin_cases k <;> rfl

theorem dist_sq_toPt (p q : LP) : dist (toPt p) (toPt q) ^ 2 = (d2 p q : ℝ) := by
  unfold toPt
  rw [dist_sq_mkPt]
  simp only [rx, ry, d2]; push_cast
  have := s3sq
  nlinarith [this]

theorem cong_of_congT {M t : LT} (hM : 0 < cross M.1 M.2.1 M.2.2) (ht : 0 < cross t.1 t.2.1 t.2.2)
    (h : congT M t = true) : (triOf t ht).Congruent (triOf M hM) := by
  simp only [congT, List.any_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨σ, -, hσ⟩ := h
  refine Erdos634.SssCongruent.congruent_of_sq_dist_perm σ (fun i j => ?_)
  rw [triOf_pts, triOf_pts, triOf_pts, triOf_pts, dist_sq_toPt, dist_sq_toPt]
  exact_mod_cast hσ i (List.mem_finRange i) j (List.mem_finRange j)

/-- line functional of the line P→Q at a lattice point is √3 · cross -/
theorem line_val (P Q v : LP) :
    Erdos634.CertGeom.lineFun (rx P) (ry P) (rx Q) (ry Q) (toPt v) = Real.sqrt 3 * (cross P Q v : ℝ) := by
  rw [Erdos634.CertGeom.lineFun_apply]
  unfold toPt
  rw [mkPt_zero, mkPt_one]
  simp only [rx, ry, cross]; push_cast; ring

theorem line_ne {P Q : LP} (h : P ≠ Q) :
    (Erdos634.CertGeom.lineFun (rx P) (ry P) (rx Q) (ry Q)).linear ≠ 0 := by
  apply Erdos634.CertGeom.lineFun_linear_ne_zero
  by_contra hc
  push Not at hc
  apply h
  have h1 : (P.1 : ℝ) = Q.1 := hc.1
  have h2 : (P.2 : ℝ) * Real.sqrt 3 = Q.2 * Real.sqrt 3 := hc.2
  have h2' : (P.2 : ℝ) = Q.2 := mul_right_cancel₀ s3pos.ne' h2
  exact Prod.ext (by exact_mod_cast h1) (by exact_mod_cast h2')

theorem aff_neg (g : Plane →ᵃ[ℝ] ℝ) (p : Plane) : (-g) p = -(g p) := by
  have := congrFun (AffineMap.coe_neg g) p
  simpa using this

theorem sep_disj {A B : LT} (hA : 0 < cross A.1 A.2.1 A.2.2) (hB : 0 < cross B.1 B.2.1 B.2.2)
    (h : SepT A B) : Disjoint (interior (triOf A hA).carrier) (interior (triOf B hB).carrier) := by
  obtain ⟨P, Q, hne, h⟩ := h
  have hl := line_ne hne
  set f := Erdos634.CertGeom.lineFun (rx P) (ry P) (rx Q) (ry Q) with hf
  have hv : ∀ (t : LT) (ht : 0 < cross t.1 t.2.1 t.2.2) (k : Fin 3),
      f ((triOf t ht).pts k) = Real.sqrt 3 * (cross P Q (vtx t k) : ℝ) := by
    intro t ht k; rw [triOf_pts, hf, line_val]
  have vk : ∀ (t : LT) (k : Fin 3), cross P Q (vtx t k) = cross P Q (vtx t k) := fun _ _ => rfl
  have s := s3pos
  rcases h with ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩⟩ | ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩⟩
  · refine Erdos634.CertGeom.interiors_disjoint_of_separating (-f) (by
      intro h0
      apply hl
      have : (-f).linear = -f.linear := rfl
      rw [this] at h0
      simpa using h0) 0 ?_ ?_
    · refine Erdos634.CertGeom.le_of_forall_pts_le (-f) (fun k => ?_)
      rw [aff_neg, hv _ hA k]
      have : (0 : ℝ) ≤ (cross P Q (vtx A k) : ℝ) := by
        fin_cases k <;> simp [vtx] <;> first | exact_mod_cast a1 | exact_mod_cast a2 | exact_mod_cast a3
      nlinarith
    · intro x hx
      have hb := Erdos634.CertGeom.le_of_forall_pts_le f (t := triOf B hB) (c := 0) (fun k => by
        rw [hv _ hB k]
        have : (cross P Q (vtx B k) : ℝ) ≤ 0 := by
          fin_cases k <;> simp [vtx] <;> first | exact_mod_cast b1 | exact_mod_cast b2 | exact_mod_cast b3
        nlinarith) x hx
      rw [aff_neg]; linarith
  · refine Erdos634.CertGeom.interiors_disjoint_of_separating f hl 0 ?_ ?_
    · refine Erdos634.CertGeom.le_of_forall_pts_le f (fun k => ?_)
      rw [hv _ hA k]
      have : (cross P Q (vtx A k) : ℝ) ≤ 0 := by
        fin_cases k <;> simp [vtx] <;> first | exact_mod_cast a1 | exact_mod_cast a2 | exact_mod_cast a3
      nlinarith
    · intro x hx
      have hb := Erdos634.CertGeom.le_of_forall_pts_le (-f) (t := triOf B hB) (c := 0) (fun k => by
        rw [aff_neg, hv _ hB k]
        have : (0 : ℝ) ≤ (cross P Q (vtx B k) : ℝ) := by
          fin_cases k <;> simp [vtx] <;> first | exact_mod_cast b1 | exact_mod_cast b2 | exact_mod_cast b3
        nlinarith) x hx
      rw [aff_neg] at hb; linarith

theorem inside_mem {T t : LT} (hT : 0 < cross T.1 T.2.1 T.2.2) (ht : 0 < cross t.1 t.2.1 t.2.2)
    (h : insideT T t = true) (k : Fin 3) : (triOf t ht).pts k ∈ (triOf T hT).carrier := by
  rw [triOf_pts]
  simp only [insideT, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq] at h
  have key : 0 ≤ cross T.1 T.2.1 (vtx t k) ∧ 0 ≤ cross T.2.1 T.2.2 (vtx t k) ∧
      0 ≤ cross T.2.2 T.1 (vtx t k) := by
    obtain ⟨⟨⟨a1, a2⟩, a3⟩, ⟨⟨b1, b2⟩, b3⟩, ⟨⟨c1, c2⟩, c3⟩⟩ := h
    fin_cases k
    · exact ⟨a1, a2, a3⟩
    · exact ⟨b1, b2, b3⟩
    · exact ⟨c1, c2, c3⟩
  obtain ⟨c1, c2, c3⟩ := key
  have s := s3pos
  unfold toPt triOf
  refine mem_carrier_of_dets (det3_pos hT) ?_ ?_ ?_
  · rw [det3_lat]
    have : cross (vtx t k) T.2.1 T.2.2 = cross T.2.1 T.2.2 (vtx t k) := by simp only [cross]; ring
    rw [this]; exact mul_nonneg s.le (by exact_mod_cast c2)
  · rw [det3_lat]
    have : cross T.1 (vtx t k) T.2.2 = cross T.2.2 T.1 (vtx t k) := by simp only [cross]; ring
    rw [this]; exact mul_nonneg s.le (by exact_mod_cast c3)
  · rw [det3_lat]; exact mul_nonneg s.le (by exact_mod_cast c1)

theorem sum_get (L : List LT) (f : LT → ℝ) : ∑ i : Fin L.length, f L[i.1] = (L.map f).sum := by
  induction L with
  | nil => simp
  | cons a t ih => simp [Fin.sum_univ_succ, ih]

theorem sum_cross_cast (L : List LT) :
    (((L.map (fun t => cross t.1 t.2.1 t.2.2)).sum : ℤ) : ℝ) = (L.map (fun t => (cross t.1 t.2.1 t.2.2 : ℝ))).sum := by
  induction L with
  | nil => simp
  | cons a t ih => simp [ih]

theorem ok_parts {c : Cert} (h : c.ok = true) :
    posT c.target = true ∧ posT c.model = true ∧ c.clusters.all Bsp.ok = true ∧
    pairsOK c.clusters c.seps = some [] ∧ c.leaves.all posT = true ∧
    c.leaves.all (insideT c.target) = true ∧ c.leaves.all (congT c.model) = true ∧
    (c.leaves.map (fun t => cross t.1 t.2.1 t.2.2)).sum = cross c.target.1 c.target.2.1 c.target.2.2 := by
  simp only [Cert.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨a, b⟩, c1⟩, d⟩, e⟩, f⟩, g⟩, i⟩ := h
  exact ⟨a, b, c1, d, e, f, g, i⟩

theorem leaves_pairwise {c : Cert} (h : c.ok = true) : c.leaves.Pairwise SepT := by
  obtain ⟨-, -, hok, hp, -, -, -, -⟩ := ok_parts h
  unfold Cert.leaves
  rw [List.pairwise_flatten]
  refine ⟨?_, ?_⟩
  · intro l hl
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hl
    exact Bsp.ok_pairwise b (List.all_eq_true.mp hok b hb)
  · rw [List.pairwise_map]
    exact pairsOK_sound c.clusters c.seps [] hp

theorem pos_of_mem {c : Cert} (h : c.ok = true) {t : LT} (ht : t ∈ c.leaves) : 0 < cross t.1 t.2.1 t.2.2 := by
  obtain ⟨-, -, -, -, hp, -, -, -⟩ := ok_parts h
  have := List.all_eq_true.mp hp t ht
  simpa [posT] using this

noncomputable def cd (c : Cert) (h : c.ok = true) : CongruentDissection c.leaves.length :=
  have hT : 0 < cross c.target.1 c.target.2.1 c.target.2.2 := by
    simpa [posT] using (ok_parts h).1
  have hM : 0 < cross c.model.1 c.model.2.1 c.model.2.2 := by
    simpa [posT] using (ok_parts h).2.1
  let tile : Fin c.leaves.length → Tri := fun i =>
    triOf c.leaves[i.1] (pos_of_mem h (List.getElem_mem i.isLt))
  { toDissection := Erdos634.AreaDet.ofDetCertificate (triOf c.target hT) tile
      (fun i => Erdos634.CertGeom.carrier_subset_of_pts_mem (fun k =>
        inside_mem hT _ (List.all_eq_true.mp (ok_parts h).2.2.2.2.2.1 _ (List.getElem_mem i.isLt)) k))
      (by
        intro i j hij
        have hp := leaves_pairwise h
        rw [List.pairwise_iff_getElem] at hp
        rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hgt
        · exact sep_disj _ _ (hp i.1 j.1 i.isLt j.isLt hlt)
        · exact (sep_disj _ _ (hp j.1 i.1 j.isLt i.isLt hgt)).symm)
      (by
        have e1 : ∀ i : Fin c.leaves.length, |Erdos634.AreaDet.detTri (tile i)|
            = Real.sqrt 3 * (cross c.leaves[i.1].1 c.leaves[i.1].2.1 c.leaves[i.1].2.2 : ℝ) := by
          intro i
          have hpos := pos_of_mem h (List.getElem_mem i.isLt)
          show |Erdos634.AreaDet.detTri (triOf _ _)| = _
          unfold triOf
          rw [detTri_mkTri, det3_lat]
          exact abs_of_pos (mul_pos s3pos (by exact_mod_cast hpos))
        have e2 : Erdos634.AreaDet.detTri (triOf c.target hT)
            = Real.sqrt 3 * (cross c.target.1 c.target.2.1 c.target.2.2 : ℝ) := by
          unfold triOf; rw [detTri_mkTri, det3_lat]
        rw [Finset.sum_congr rfl (fun i _ => e1 i), e2,
          abs_of_pos (mul_pos s3pos (by exact_mod_cast hT)), ← Finset.mul_sum]
        congr 1
        have := sum_get c.leaves (fun t => (cross t.1 t.2.1 t.2.2 : ℝ))
        rw [this, ← sum_cross_cast, (ok_parts h).2.2.2.2.2.2.2]) 
    model := triOf c.model hM
    tiles_congruent := fun i => cong_of_congT hM (pos_of_mem h (List.getElem_mem i.isLt))
      (List.all_eq_true.mp (ok_parts h).2.2.2.2.2.2.1 _ (List.getElem_mem i.isLt)) }

theorem cd_target (c : Cert) (h : c.ok = true) : (cd c h).target = triOf c.target (by
    simpa [posT] using (ok_parts h).1) := by unfold cd; rfl
theorem cd_model (c : Cert) (h : c.ok = true) : (cd c h).model = triOf c.model (by
    simpa [posT] using (ok_parts h).2.1) := by unfold cd; rfl

end Erdos634.Draft.G3CCert

import Erdos634.Refl.SoundStage2

/-! Stage 3: the kill lemmas `esc`/`ovl` and positivity of placed tiles. -/

set_option linter.unusedSimpArgs false
open Erdos634.CertNode
open Erdos634.Geometry (Plane)

namespace Refl

theorem Tri.ok_w (t : _root_.Tri) (h : t.ok = true) : 0 < t.a.w ∧ 0 < t.b.w ∧ 0 < t.c.w := by
  simp only [_root_.Tri.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨ha, hb⟩, hc⟩, -⟩ := h
  exact ⟨ha, hb, hc⟩

theorem Tri.vert_w_pos (t : _root_.Tri) (h : t.ok = true) (i : Nat) : 0 < (t.vert i).w := by
  obtain ⟨a, b, c⟩ := Tri.ok_w t h
  match i with
  | 0 => exact a
  | 1 => exact b
  | k + 2 => exact c

/-- the rescaled edge form at a homogeneous point is the determinant over the weight -/
theorem evalL_linOf_det (a b q : Pt) (ha : 0 < a.w) (hb : 0 < b.w) (hq : 0 < q.w) :
    evalL (linOf a b) q.X q.Y * q.w = det3 a b q := by
  rw [evalL_linOf _ _ (Pt.w_ne _ ha) (Pt.w_ne _ hb), det3_ef _ _ _ (Pt.w_ne _ ha) (Pt.w_ne _ hb) (Pt.w_ne _ hq)]
  ring

/-- **escape**: a vertex on the wrong side of a target edge cannot lie in the target. -/
theorem esc_sound (Dn : ℝ) (hD : 0 < Dn) (tgt : _root_.Tri) (htok : tgt.ok = true) (e : Nat)
    (q : Pt) (hq : 0 < q.w)
    (hdet : det3 (tgt.vert (e % 3)) (tgt.vert ((e + 1) % 3)) q < 0)
    (hin : q.re Dn ∈ tgt.carr Dn) : False := by
  have h := Tri.edge_nonneg Dn hD tgt htok q.X q.Y hin (e % 3) (Nat.mod_lt _ (by norm_num))
  have hedge : tgt.edge (e % 3) = linOf (tgt.vert (e % 3)) (tgt.vert ((e + 1) % 3)) := by
    have h3 : (e % 3 + 1) % 3 = (e + 1) % 3 := by omega
    simp only [_root_.Tri.edge, Nat.mod_mod, h3]
  rw [hedge] at h
  have := evalL_linOf_det (tgt.vert (e % 3)) (tgt.vert ((e + 1) % 3)) q
    (Tri.vert_w_pos tgt htok _) (Tri.vert_w_pos tgt htok _) hq
  have hw : (0 : ℝ) < q.w := Pt.w_pos _ hq
  have hd : (det3 (tgt.vert (e % 3)) (tgt.vert ((e + 1) % 3)) q : ℝ) < 0 := by exact_mod_cast hdet
  nlinarith [mul_nonneg h hw.le]

/-- escape kill against a dissection -/
theorem esc_sound_D (Dn : ℝ) (hD : 0 < Dn) (I : Inst) (htok : I.tgt.ok = true) {N : ℕ}
    (D : Erdos634.Geometry.CongruentDissection N)
    (htarget : D.target.carrier = I.tgt.carr Dn) (tri : _root_.Tri) (j : Fin N)
    (hj : (D.tile j).carrier = tri.carr Dn) (e : Nat) (q : Pt) (hq : 0 < q.w)
    (hqin : q.re Dn ∈ tri.carr Dn)
    (hdet : det3 (I.tgt.vert (e % 3)) (I.tgt.vert ((e + 1) % 3)) q < 0) : False := by
  refine esc_sound Dn hD I.tgt htok e q hq hdet ?_
  rw [← htarget]
  exact Erdos634.BaseSelection.tile_subset_target D.toDissection j (by rw [hj]; exact hqin)

/-- overlap kill: an explicit point in both interiors, two distinct tiles -/
theorem ovl_sound_D (Dn : ℝ) (hD : 0 < Dn) {N : ℕ} (D : Erdos634.Geometry.CongruentDissection N)
    (tri U : _root_.Tri) (htri : tri.ok = true) (hU : U.ok = true) (i j : Fin N) (hij : i ≠ j)
    (hi : (D.tile i).carrier = U.carr Dn) (hj : (D.tile j).carrier = tri.carr Dn)
    (w : Pt) (hw : 0 < w.w) (h1 : inOpen tri w = true) (h2 : inOpen U w = true) : False :=
  by
  have hdis : Disjoint (interior (D.tile i).carrier) (interior (D.tile j).carrier) :=
    D.interiors_disjoint hij
  rw [hi, hj] at hdis
  exact Set.disjoint_left.mp hdis (inOpen_sound Dn hD U w hw hU h2) (inOpen_sound Dn hD tri w hw htri h1)

/-- a placement satisfying `placeOk` numerics gives a well-formed tile -/
theorem placeTri_ok (I : Inst) (v d : Pt) (p : Place) (hv : 0 < v.w) (hd : 0 < d.w)
    (hdu : d.x * d.x + I.Dn * d.y * d.y = d.w * d.w) (hDn : 0 < I.Dn)
    (h1 : 0 < p.l1) (hpd : 0 < p.pd) (hqd : 0 < p.qd) (hqn : 0 < p.qn) :
    (placeTri I v d p).ok = true := by
  have hdet : det3 v (placeTri I v d p).b (placeTri I v d p).c
      = p.l1 * p.pd * p.qn * v.w ^ 3 * (d.w * d.w) := by
    rw [← hdu]; simp only [placeTri, det3]; ring
  simp only [_root_.Tri.ok, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨hv, ?_⟩, ?_⟩, ?_⟩
  · show 0 < v.w * d.w; positivity
  · show 0 < v.w * d.w * p.pd * p.qd; positivity
  · show 0 < det3 v _ _
    rw [hdet]; positivity

#print axioms Refl.esc_sound_D
#print axioms Refl.ovl_sound_D
#print axioms Refl.placeTri_ok
end Refl

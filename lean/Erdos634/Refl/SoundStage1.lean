import Erdos634.Refl.Sound

/-! Stage 1: semantics of `Pt`/`Tri`/`inClosed`/`inOpen`/`Tri.edge`. -/

set_option linter.unusedSimpArgs false
open Erdos634.CertNode
open Erdos634.Geometry (Plane)

namespace Refl

/-- the plane point of a homogeneous point (same def as `SoundSkel`) -/
noncomputable def _root_.Pt.re (Dn : ℝ) (p : Pt) : Plane := rp Dn p.X p.Y

/-- the closed triangle spanned by three homogeneous points (same def as `SoundSkel`) -/
noncomputable def _root_.Tri.carr (Dn : ℝ) (t : _root_.Tri) : Set Plane :=
  convexHull ℝ {t.a.re Dn, t.b.re Dn, t.c.re Dn}

theorem Pt.w_ne (p : Pt) (h : 0 < p.w) : (p.w : ℝ) ≠ 0 := by
  have : (0 : ℝ) < p.w := by exact_mod_cast h
  exact this.ne'

theorem Pt.w_pos (p : Pt) (h : 0 < p.w) : (0 : ℝ) < p.w := by exact_mod_cast h

/-- `Tri.ok` gives a genuine coordinate triangle, and `carr` is its carrier. -/
theorem Tri.ok_sem (Dn : ℝ) (hD : 0 < Dn) (t : _root_.Tri) (h : t.ok = true) :
    ∃ hp : 0 < ef t.a.X t.a.Y t.b.X t.b.Y t.c.X t.c.Y,
      t.carr Dn = (rtri Dn hD t.a.X t.a.Y t.b.X t.b.Y t.c.X t.c.Y hp).carrier := by
  simp only [_root_.Tri.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨ha, hb⟩, hc⟩, hdet⟩ := h
  have hd : (0 : ℝ) < (det3 t.a t.b t.c : ℝ) := by exact_mod_cast hdet
  rw [det3_ef _ _ _ (Pt.w_ne _ ha) (Pt.w_ne _ hb) (Pt.w_ne _ hc)] at hd
  have hpos : 0 < ef t.a.X t.a.Y t.b.X t.b.Y t.c.X t.c.Y := by
    have := mul_pos (mul_pos (Pt.w_pos _ ha) (Pt.w_pos _ hb)) (Pt.w_pos _ hc)
    exact (mul_pos_iff_of_pos_left this).mp hd
  refine ⟨hpos, ?_⟩
  show convexHull ℝ _ = convexHull ℝ _
  congr 1
  ext p
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range, rtri, Erdos634.CertCoord.mkTri_pts]
  constructor
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  · rintro ⟨k, rfl⟩
    fin_cases k
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

theorem Tri.vert_re_mem (Dn : ℝ) (t : _root_.Tri) (i : Nat) :
    (t.vert i).re Dn ∈ t.carr Dn := by
  apply subset_convexHull
  match i with
  | 0 => simp [_root_.Tri.vert]
  | 1 => simp [_root_.Tri.vert]
  | k + 2 => simp [_root_.Tri.vert]

/-- closed membership from determinant signs -/
theorem inClosed_sound (Dn : ℝ) (hD : 0 < Dn) (t : _root_.Tri) (p : Pt) (hp : 0 < p.w)
    (ht : t.ok = true) (h : inClosed t p = true) : p.re Dn ∈ t.carr Dn := by
  have ht' := ht
  simp only [_root_.Tri.ok, Bool.and_eq_true, decide_eq_true_eq] at ht'
  obtain ⟨⟨⟨ha, hb⟩, hc⟩, -⟩ := ht'
  obtain ⟨hpos, hcar⟩ := Tri.ok_sem Dn hD t ht
  rw [hcar]
  simp only [inClosed, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  have wa := Pt.w_pos _ ha
  have wb := Pt.w_pos _ hb
  have wc := Pt.w_pos _ hc
  have wp := Pt.w_pos _ hp
  have e0 := det3_ef t.a t.b p (Pt.w_ne _ ha) (Pt.w_ne _ hb) (Pt.w_ne _ hp)
  have e1 := det3_ef t.b t.c p (Pt.w_ne _ hb) (Pt.w_ne _ hc) (Pt.w_ne _ hp)
  have e2 := det3_ef t.c t.a p (Pt.w_ne _ hc) (Pt.w_ne _ ha) (Pt.w_ne _ hp)
  have h0' : (0:ℝ) ≤ det3 t.a t.b p := by exact_mod_cast h0
  have h1' : (0:ℝ) ≤ det3 t.b t.c p := by exact_mod_cast h1
  have h2' : (0:ℝ) ≤ det3 t.c t.a p := by exact_mod_cast h2
  rw [e0] at h0'; rw [e1] at h1'; rw [e2] at h2'
  show rp Dn p.X p.Y ∈ _
  exact mem_rtri hD hpos
    ((mul_nonneg_iff_of_pos_left (mul_pos (mul_pos wa wb) wp)).mp h0')
    ((mul_nonneg_iff_of_pos_left (mul_pos (mul_pos wb wc) wp)).mp h1')
    ((mul_nonneg_iff_of_pos_left (mul_pos (mul_pos wc wa) wp)).mp h2')

/-- open membership from determinant signs -/
theorem inOpen_sound (Dn : ℝ) (hD : 0 < Dn) (t : _root_.Tri) (p : Pt) (hp : 0 < p.w)
    (ht : t.ok = true) (h : inOpen t p = true) : p.re Dn ∈ interior (t.carr Dn) := by
  have ht' := ht
  simp only [_root_.Tri.ok, Bool.and_eq_true, decide_eq_true_eq] at ht'
  obtain ⟨⟨⟨ha, hb⟩, hc⟩, -⟩ := ht'
  obtain ⟨hpos, hcar⟩ := Tri.ok_sem Dn hD t ht
  rw [hcar]
  simp only [inOpen, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  have wa := Pt.w_pos _ ha
  have wb := Pt.w_pos _ hb
  have wc := Pt.w_pos _ hc
  have wp := Pt.w_pos _ hp
  have e0 := det3_ef t.a t.b p (Pt.w_ne _ ha) (Pt.w_ne _ hb) (Pt.w_ne _ hp)
  have e1 := det3_ef t.b t.c p (Pt.w_ne _ hb) (Pt.w_ne _ hc) (Pt.w_ne _ hp)
  have e2 := det3_ef t.c t.a p (Pt.w_ne _ hc) (Pt.w_ne _ ha) (Pt.w_ne _ hp)
  have h0' : (0:ℝ) < det3 t.a t.b p := by exact_mod_cast h0
  have h1' : (0:ℝ) < det3 t.b t.c p := by exact_mod_cast h1
  have h2' : (0:ℝ) < det3 t.c t.a p := by exact_mod_cast h2
  rw [e0] at h0'; rw [e1] at h1'; rw [e2] at h2'
  show rp Dn p.X p.Y ∈ _
  exact mem_interior_rtri hD hpos
    ((mul_pos_iff_of_pos_left (mul_pos (mul_pos wa wb) wp)).mp h0')
    ((mul_pos_iff_of_pos_left (mul_pos (mul_pos wb wc) wp)).mp h1')
    ((mul_pos_iff_of_pos_left (mul_pos (mul_pos wc wa) wp)).mp h2')

/-- a point of the (closed) triangle satisfies the three edge lines nonstrictly. -/
theorem Tri.edge_nonneg (Dn : ℝ) (hD : 0 < Dn) (t : _root_.Tri) (ht : t.ok = true) (X Y : ℝ)
    (hm : rp Dn X Y ∈ t.carr Dn) (i : Nat) (hi : i < 3) : 0 ≤ evalL (t.edge i) X Y := by
  have ht' := ht
  simp only [_root_.Tri.ok, Bool.and_eq_true, decide_eq_true_eq] at ht'
  obtain ⟨⟨⟨ha, hb⟩, hc⟩, -⟩ := ht'
  obtain ⟨hpos, hcar⟩ := Tri.ok_sem Dn hD t ht
  rw [hcar] at hm
  obtain ⟨n0, n1, n2⟩ := rtri_ef_nonneg hD hpos hm
  have wa := Pt.w_pos _ ha
  have wb := Pt.w_pos _ hb
  have wc := Pt.w_pos _ hc
  interval_cases i
  · simp only [_root_.Tri.edge, _root_.Tri.vert, Nat.zero_mod, Nat.reduceMod, Nat.reduceAdd]
    rw [evalL_linOf _ _ (Pt.w_ne _ ha) (Pt.w_ne _ hb)]
    exact mul_nonneg (mul_pos wa wb).le n0
  · simp only [_root_.Tri.edge, _root_.Tri.vert, Nat.reduceMod, Nat.reduceAdd]
    rw [evalL_linOf _ _ (Pt.w_ne _ hb) (Pt.w_ne _ hc)]
    exact mul_nonneg (mul_pos wb wc).le n1
  · simp only [_root_.Tri.edge, _root_.Tri.vert, Nat.reduceMod, Nat.reduceAdd]
    rw [evalL_linOf _ _ (Pt.w_ne _ hc) (Pt.w_ne _ ha)]
    exact mul_nonneg (mul_pos wc wa).le n2

end Refl

#print axioms Refl.Tri.ok_sem
#print axioms Refl.inClosed_sound
#print axioms Refl.inOpen_sound
#print axioms Refl.Tri.edge_nonneg
#print axioms Refl.Tri.vert_re_mem

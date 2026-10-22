-- Draft/LaczFormalIVcRatB7i.lean -- Laczkovich DCG 48 (2012), Sect. 8.3 (Subcase IVc, rational branch), BLUEPRINT Part B, item B7, stage i: THE TWO STEPS.
--   `VWTiling.step_base` (the corner): T a VWTiling of a convex A inside the quadrant {fa >= 0, fb >= 0} of a frame F = (U; p, q) with U in A, and a point y of A with fa y > 0:
--       some rhombus piece of T is exactly Par U p q.
--   `VWTiling.step_next` (along the side): T a VWTiling of a convex A inside {fb >= 0}, a rhombus piece equal to Par (U - p) p q (the previous rhombus of the row), U in A, and F.pt t 0 in A for some t > 0 (the side
--       continues past U): some rhombus piece of T is exactly Par U p q.
--   Hypotheses of the form `hrow` are what the induction B7h' (the row) maintains; no hypothesis beyond B1-B6 data (Frame, VWTiling, convexity).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 8.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIVcRatB7h
import Erdos634.Draft.LaczFormalIVcRatB6w

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

theorem Frame.continuous_fa {b : ℝ} (F : Frame b) : Continuous F.fa := by
  have h0 : Continuous fun y : Plane => y 0 := (EuclideanSpace.proj (0 : Fin 2)).continuous
  have h1 : Continuous fun y : Plane => y 1 := (EuclideanSpace.proj (1 : Fin 2)).continuous
  unfold Frame.fa
  exact ((h0.sub continuous_const).mul continuous_const |>.sub ((h1.sub continuous_const).mul continuous_const)).div_const _

theorem Frame.continuous_fb {b : ℝ} (F : Frame b) : Continuous F.fb := by
  have h0 : Continuous fun y : Plane => y 0 := (EuclideanSpace.proj (0 : Fin 2)).continuous
  have h1 : Continuous fun y : Plane => y 1 := (EuclideanSpace.proj (1 : Fin 2)).continuous
  unfold Frame.fb
  exact ((continuous_const.mul (h1.sub continuous_const)).sub (continuous_const.mul (h0.sub continuous_const))).div_const _

theorem Box.isOpen {b : ℝ} (F : Frame b) : IsOpen {z | Box F z} := by
  have ha := F.continuous_fa
  have hb := F.continuous_fb
  have : {z | Box F z} = {z | -1 < F.fa z} ∩ ({z | F.fa z < 0} ∩ ({z | 0 < F.fb z} ∩ {z | F.fb z < 1})) := by
    ext z; simp [Box]
  rw [this]
  exact (isOpen_lt continuous_const ha).inter ((isOpen_lt ha continuous_const).inter
    ((isOpen_lt continuous_const hb).inter (isOpen_lt hb continuous_const)))

/-- The previous rhombus of the row: `Par (U - p) p q`. -/
noncomputable def prevPar {b : ℝ} (F : Frame b) : Set Plane := Par (F.U0 - F.p0) (F.U1 - F.p1) F.p0 F.p1 F.q0 F.q1

theorem box_subset_interior_prevPar {b : ℝ} (F : Frame b) (hb : 0 < b) : {z | Box F z} ⊆ interior (prevPar F) := by
  refine interior_maximal ?_ (Box.isOpen F)
  intro z hz
  obtain ⟨h1, h2, h3, h4⟩ := hz
  have := F.recon hb z
  refine ⟨1 + F.fa z, F.fb z, by linarith, by linarith, by linarith, by linarith, ?_, ?_⟩
  · have h := congrArg (fun y : Plane => y 0) this
    simp only [F.pt_zero] at h
    rw [h]; ring
  · have h := congrArg (fun y : Plane => y 1) this
    simp only [F.pt_one] at h
    rw [h]; ring

theorem prevPar_fa_nonpos {b : ℝ} (F : Frame b) (hb : 0 < b) : ∀ z ∈ prevPar F, F.fa z ≤ 0 := by
  rintro z ⟨l, m, hl, hl1, hm, hm1, e0, e1⟩
  have := (F.fa_fb_of hb (y := z) (a := l - 1) (β := m) (by rw [e0]; ring) (by rw [e1]; ring)).1
  rw [this]; linarith

theorem miss_box_of_disjoint {b : ℝ} (F : Frame b) (hb : 0 < b) {S : Set Plane} (hS : S ⊆ closure (interior S))
    (hd : Disjoint (interior S) (interior (prevPar F))) : ∀ z ∈ S, ¬ Box F z := by
  intro z hzS hbox
  obtain ⟨w, hwb, hwS⟩ := mem_closure_iff.mp (hS hzS) _ (Box.isOpen F) hbox
  exact Set.disjoint_left.mp hd hwS (box_subset_interior_prevPar F hb hwb)

theorem closure_interior_superset {S : Set Plane} (hconv : Convex ℝ S) (hcl : IsClosed S) (hint : (interior S).Nonempty) :
    S ⊆ closure (interior S) := by
  rw [hconv.closure_interior_eq_closure_of_nonempty_interior hint, hcl.closure_eq]

theorem KiteData.closure_interior {b : ℝ} (K : KiteData b) : K.set ⊆ closure (interior K.set) := by
  have hc : K.set = (ct K.v0 K.v1 (2 * K.s0) (2 * K.s1) (2 * K.w0) (2 * K.w1) (hD4 K.hD)).carrier := rfl
  apply closure_interior_superset
  · rw [hc]; exact Tri.convex _
  · rw [hc]; exact (Tri.isCompact _).isClosed
  · rw [hc]; exact Tri.interior_nonempty _

theorem RhombData.closure_interior {b : ℝ} (R : RhombData b) : R.set ⊆ closure (interior R.set) := by
  apply closure_interior_superset
  · exact Par_convex _ _ _ _ _ _
  · rw [← R.set_eq_iUnion]; exact isClosed_iUnion_of_finite fun i => (R.cell i).isCompact.isClosed
  · obtain ⟨x, hx⟩ := (R.cell 0).interior_nonempty
    exact ⟨x, interior_mono (R.cell_subset 0) hx⟩

namespace VWTiling
variable {b : ℝ} {A : Set Plane} {ιK ιR : Type} [Fintype ιK] [Fintype ιR] (T : VWTiling b A ιK ιR)

/-- **B7i (base: the corner).** -/
theorem step_base (hb : 0 < b) (hconv : Convex ℝ A) (F : Frame b) (hquad : ∀ y ∈ A, 0 ≤ F.fa y ∧ 0 ≤ F.fb y)
    (hUA : F.pt 0 0 ∈ A) {y : Plane} (hyA : y ∈ A) (hya : 0 < F.fa y) :
    ∃ r, (T.R r).set = Par F.U0 F.U1 F.p0 F.p1 F.q0 F.q1 := by
  have hnob : ∀ z ∈ A, ¬ Box F z := fun z hz hbox => absurd hbox.2.1 (not_lt.mpr (hquad z hz).1)
  refine T.step_core hb hconv F (fun y hy => (hquad y hy).2) hUA hyA hya
    (fun k z hz => hnob z (T.K_subset k hz)) (fun r => Or.inl (fun z hz => hnob z (T.R_subset r hz))) ?_
  intro c hUc _
  have hsub : (T.cellT c).carrier ⊆ A := (Set.subset_iUnion (fun c => (T.cellT c).carrier) c).trans T.cells_cover.subset
  exact vertex_of_corner F hb (T.cellT c) (fun y hy => hquad y (hsub hy)) hUc

/-- **B7i (next, with a witness point).** -/
theorem step_next_y (hb : 0 < b) (hconv : Convex ℝ A) (F : Frame b) (hbel : ∀ y ∈ A, 0 ≤ F.fb y) (hUA : F.pt 0 0 ∈ A)
    {y : Plane} (hyA : y ∈ A) (hpos : 0 < F.fa y) {r0 : ιR} (hrow : (T.R r0).set = prevPar F) :
    ∃ r, (T.R r).set = Par F.U0 F.U1 F.p0 F.p1 F.q0 F.q1 := by
  have hfr : F.pt 0 0 ∈ frontier A := frontier_of_fb_zero F hb T.region_closed hbel hUA (F.fb_pt hb 0 0)
  have hdis := prevPar_fa_nonpos F hb
  refine T.step_core hb hconv F hbel hUA hyA hpos ?_ ?_ ?_
  · intro k z hz
    refine miss_box_of_disjoint F hb ((T.K k).closure_interior) ?_ z hz
    have := T.disjKR k r0
    rwa [hrow] at this
  · intro r
    by_cases hr : r = r0
    · right; subst hr; rw [hrow]; exact hdis
    · left
      refine miss_box_of_disjoint F hb ((T.R r).closure_interior) ?_
      have := T.disjRR r r0 hr
      rwa [hrow] at this
  · intro c hUc ⟨z, hz, hzpos⟩
    have hU0 : F.pt 0 0 ∈ (T.R r0).set := by
      rw [hrow]; exact ⟨1, 0, by norm_num, by norm_num, by norm_num, by norm_num, by rw [F.pt_zero]; ring, by rw [F.pt_one]; ring⟩
    rw [← (T.R r0).set_eq_iUnion] at hU0
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hU0
    have hne : c ≠ Sum.inr (r0, i) := by
      intro hc
      subst hc
      have hz' : z ∈ (T.R r0).set := (T.R r0).cell_subset i hz
      rw [hrow] at hz'
      exact absurd (hdis z hz') (not_le.mpr hzpos)
    exact T.vertex_of_second_cell hb hconv hne hfr hUc hi

/-- **B7i (next: along the side).** -/
theorem step_next (hb : 0 < b) (hconv : Convex ℝ A) (F : Frame b) (hbel : ∀ y ∈ A, 0 ≤ F.fb y) (hUA : F.pt 0 0 ∈ A)
    {t : ℝ} (ht : 0 < t) (htA : F.pt t 0 ∈ A) {r0 : ιR} (hrow : (T.R r0).set = prevPar F) :
    ∃ r, (T.R r).set = Par F.U0 F.U1 F.p0 F.p1 F.q0 F.q1 := by
  have hq1 : F.pt 0 1 ∈ A := by
    apply T.R_subset r0; rw [hrow]
    exact ⟨1, 1, by norm_num, by norm_num, by norm_num, by norm_num, by rw [F.pt_zero]; ring, by rw [F.pt_one]; ring⟩
  have hmid : F.pt (t / 2) (1 / 2) ∈ A := by
    have := hconv htA hq1 (a := 1 / 2) (b := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
    have e : (1 / 2 : ℝ) • F.pt t 0 + (1 / 2 : ℝ) • F.pt 0 1 = F.pt (t / 2) (1 / 2) := by
      apply plane_ext'
      · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, F.pt_zero]; ring
      · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, F.pt_one]; ring
    rwa [e] at this
  have hfa : F.fa (F.pt (t / 2) (1 / 2)) = t / 2 := F.fa_pt hb _ _
  have hpos : 0 < F.fa (F.pt (t / 2) (1 / 2)) := by rw [hfa]; positivity
  exact T.step_next_y hb hconv F hbel hUA hmid hpos hrow

end VWTiling

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.VWTiling.step_base
#print axioms Erdos634.Draft.LaczFormal.RG.VWTiling.step_next

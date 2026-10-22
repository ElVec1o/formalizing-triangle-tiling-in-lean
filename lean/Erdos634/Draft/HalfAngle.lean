import Mathlib.Tactic
import Erdos634.AngleSumDissection
import Erdos634.VertexSector
import Erdos634.TP_erdos

/-!
# T30L stage 1(c) — `HalfAngle`: the one-sided angle sum π at a point of a wall

Erdős #634, composite-N debt (G* case 2 step "claim at Z"; `E_partition_lean_scope.md` F11(i)).
UNAUDITED.  Not progress on /goal outcomes 1-2.

`PinPlumbing.pin_angle_sum` gives `π` only at a point of the TARGET boundary and
`Dissection.sum_localAngle_eq` gives `2π` at an interior point.  The hand proof needs the half
plane version at a point `p` of the target interior lying on a line `{f = c}` that no tile
straddles near `p`: the tiles on the side `{f ≤ c}` have local angles at `p` summing to exactly `π`.

`half_angle_sum`: for a `Dissection D`, `f ≠ 0`, `p ∈ interior target` with `f p = c`, such that
every tile containing `p` lies wholly in `{f ≤ c}` or wholly in `{c ≤ f}` (`hside`):

    `∑ i with carrier_i ⊆ {f ≤ c}, localAngle_i p = π`.

Proof: the measure route of `AngleSumDissection`: for small `r` the near tiles' traces on `B(p,r)`
cover `B(p,r) ∩ {f < c}` and lie in `B(p,r) ∩ {f ≤ c}`, whose measure is `π r²/2`
(`volume_halfplane_inter_ball_at`); the line is null.
-/

namespace Erdos634.HalfAngle

open Erdos634.Geometry MeasureTheory Set Metric
open scoped ENNReal

/-- The level line of a nonzero functional is Lebesgue-null. -/
theorem volume_level_line (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) {p : Plane} (c : ℝ) (hp : f p = c) :
    volume {y : Plane | f y = c} = 0 := by
  have hker : LinearMap.ker f ≠ ⊤ := fun h => hf (LinearMap.ker_eq_top.mp h)
  have hpre : (fun v : Plane => p + v) ⁻¹' {y : Plane | f y = c} = (LinearMap.ker f : Set Plane) := by
    ext v; simp [hp]
  have := Measure.addHaar_submodule (volume : Measure Plane) _ hker
  rw [← measure_preimage_add (volume : Measure Plane) p {y : Plane | f y = c}, hpre]
  exact this

/-- The half-plane measure in the form needed: `2·|B ∩ {f ≤ c}| = |B|` for `f p = c`. -/
theorem two_mul_volume_half (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) {p : Plane} (c : ℝ) (hp : f p = c)
    (r : ℝ) :
    2 * volume ({y : Plane | f y ≤ c} ∩ ball p r) = volume (ball p r) := by
  let g : Plane →ᵃ[ℝ] ℝ :=
    { toFun := fun y => c - f y
      linear := -f
      map_vadd' := by intro q v; simp [sub_eq_add_neg]; ring }
  have hg : g.linear ≠ 0 := by
    intro h; apply hf; have : -f = 0 := h; simpa using this
  have hgp : g p = 0 := by show c - f p = 0; rw [hp]; ring
  have := volume_halfplane_inter_ball_at g hg hgp r
  have hset : {y : Plane | 0 ≤ g y} = {y : Plane | f y ≤ c} := by
    ext y; simp only [Set.mem_setOf_eq]; show 0 ≤ c - f y ↔ f y ≤ c; constructor <;> intro h <;> linarith
  rwa [hset] at this

open Classical in
/-- **The one-sided angle sum.** -/
theorem half_angle_sum {N : ℕ} (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    {p : Plane} (hp : f p = c) (hpint : p ∈ interior D.target.carrier)
    (hside : ∀ i, p ∈ (D.tile i).carrier →
      (D.tile i).carrier ⊆ {y | f y ≤ c} ∨ (D.tile i).carrier ⊆ {y | c ≤ f y}) :
    ∑ i ∈ Finset.univ.filter (fun i => (D.tile i).carrier ⊆ {y | f y ≤ c}),
        (D.tile i).localAngle p = Real.pi := by
  classical
  -- radii
  obtain ⟨rI, hrI, hballI⟩ := Metric.isOpen_iff.mp isOpen_interior p hpint
  have hrad : ∀ i, ∃ r > 0, (∀ r', 0 < r' → r' ≤ r →
        volume ((D.tile i).carrier ∩ ball p r')
          = ENNReal.ofReal ((D.tile i).localAngle p / 2 * r' ^ 2)) ∧
      (p ∉ (D.tile i).carrier → ∀ y ∈ ball p r, y ∉ (D.tile i).carrier) := by
    intro i
    obtain ⟨r1, hr1, h1⟩ := (D.tile i).volume_inter_ball_localAngle p
    by_cases hmem : p ∈ (D.tile i).carrier
    · exact ⟨r1, hr1, h1, fun h => absurd hmem h⟩
    · obtain ⟨r2, hr2, h2⟩ := Metric.isOpen_iff.mp (D.tile i).isCompact.isClosed.isOpen_compl p hmem
      exact ⟨min r1 r2, lt_min hr1 hr2,
        fun r' h' hle => h1 r' h' (hle.trans (min_le_left _ _)),
        fun _ y hy => h2 (Metric.ball_subset_ball (min_le_right _ _) hy)⟩
  choose ri hri hcontrib hfar using hrad
  obtain ⟨r0, hr0, hr0le⟩ := exists_common_radius D.pos ri hri
  set r : ℝ := min rI r0 with hrdef
  have hrpos : 0 < r := lt_min hrI hr0
  have hrI' : r ≤ rI := min_le_left _ _
  have hrle : ∀ i, r ≤ ri i := fun i => (min_le_right _ _).trans (hr0le i)
  have hball_target : ball p r ⊆ D.target.carrier :=
    fun y hy => interior_subset (hballI (Metric.ball_subset_ball hrI' hy))
  set near : Finset (Fin N) := Finset.univ.filter (fun i => (D.tile i).carrier ⊆ {y | f y ≤ c})
    with hnear
  set U : Set Plane := ⋃ i ∈ near, ((D.tile i).carrier ∩ ball p r) with hU
  have hUsub : U ⊆ {y | f y ≤ c} ∩ ball p r := by
    intro y hy
    obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.mp hy
    have hi' : (D.tile i).carrier ⊆ {y | f y ≤ c} := (Finset.mem_filter.mp hi).2
    exact ⟨hi' hyi.1, hyi.2⟩
  have hcover : {y | f y ≤ c} ∩ ball p r ⊆ U ∪ {y | f y = c} := by
    intro y ⟨hy1, hy2⟩
    have hy1' : f y ≤ c := hy1
    rcases hy1'.lt_or_eq with hlt | heq
    · left
      have hyT : y ∈ D.target.carrier := hball_target hy2
      rw [← D.covers] at hyT
      obtain ⟨i, hyi⟩ := Set.mem_iUnion.mp hyT
      have hpi : p ∈ (D.tile i).carrier := by
        by_contra hnp; exact hfar i hnp y (Metric.ball_subset_ball (hrle i) hy2) hyi
      refine Set.mem_iUnion₂.mpr ⟨i, ?_, hyi, hy2⟩
      rcases hside i hpi with h | h
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
      · exact absurd (h hyi) (not_le.mpr hlt)
    · right; exact heq
  have hvolU_le : volume ({y | f y ≤ c} ∩ ball p r) ≤ volume U := by
    calc volume ({y | f y ≤ c} ∩ ball p r) ≤ volume (U ∪ {y | f y = c}) := measure_mono hcover
      _ ≤ volume U + volume {y | f y = c} := measure_union_le _ _
      _ = volume U := by rw [volume_level_line f hf c hp, add_zero]
  have hvolU : volume U = volume ({y | f y ≤ c} ∩ ball p r) :=
    le_antisymm (measure_mono hUsub) hvolU_le
  -- U is a.e.-disjoint union of the near traces
  have hdisj := measure_biUnion_finset₀ (μ := volume) (s := near)
    (f := fun i => (D.tile i).carrier ∩ ball p r)
    (fun i _ j _ hij => measure_mono_null
      (Set.inter_subset_inter Set.inter_subset_left Set.inter_subset_left) (D.aedisjoint hij))
    (fun i _ => ((D.tile i).nullMeasurableSet).inter
      Metric.isOpen_ball.measurableSet.nullMeasurableSet)
  have htiles : ∀ i ∈ near, volume ((D.tile i).carrier ∩ ball p r)
      = ENNReal.ofReal ((D.tile i).localAngle p / 2 * r ^ 2) := fun i _ =>
    hcontrib i r hrpos (hrle i)
  have hsumU : volume U = ENNReal.ofReal (∑ i ∈ near, (D.tile i).localAngle p / 2 * r ^ 2) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by
      have := (D.tile i).localAngle_nonneg p; positivity)]
    rw [hU, hdisj]
    exact Finset.sum_congr rfl htiles
  have h2 := two_mul_volume_half f hf c hp r
  rw [← hvolU, hsumU, volume_ball_plane p hrpos.le] at h2
  have hnn : 0 ≤ ∑ i ∈ near, (D.tile i).localAngle p / 2 * r ^ 2 :=
    Finset.sum_nonneg fun i _ => by have := (D.tile i).localAngle_nonneg p; positivity
  rw [two_mul, ← ENNReal.ofReal_add hnn hnn,
    ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)] at h2
  have hfact : ∑ i ∈ near, (D.tile i).localAngle p / 2 * r ^ 2
      = (∑ i ∈ near, (D.tile i).localAngle p) * (r ^ 2 / 2) := by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [hfact] at h2
  have hr2 : (0 : ℝ) < r ^ 2 := by positivity
  have : (∑ i ∈ near, (D.tile i).localAngle p) * r ^ 2 = Real.pi * r ^ 2 := by linarith
  exact mul_right_cancel₀ hr2.ne' this

/-! ## Witness: `wallDissection` at the midpoint of its median

`p = (½,½)` is interior to the target, on the median `{x₀ − x₁ = 0}`; tile `A` lies in
`{0 ≤ wallF}`, tile `B` in `{wallF ≤ 0}`.  So `hside` holds, and the one-sided sum is the local
angle of `B` at `p` (an edge-interior point), namely `π`. -/

open Classical Erdos634.TPErdos Erdos634.CertCoord in
theorem half_angle_witness :
    ∑ i ∈ Finset.univ.filter (fun i => (wallDissection.tile i).carrier ⊆ {y | wallF y ≤ 0}),
        (wallDissection.tile i).localAngle (mkPt (1/2) (1/2)) = Real.pi := by
  classical
  have hmid : mkPt (1/2) (1/2) ∈ openSegment ℝ wallU wallV := by
    refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
    ext i; fin_cases i <;> simp [wallU, wallV] <;> norm_num
  refine half_angle_sum wallDissection wallF wallF_ne 0 (by rw [wallF_pt]; norm_num)
    (wall_hint hmid) ?_
  intro i _
  fin_cases i
  · right
    have h := Tri.carrier_subset_halfplane wallTileA (-wallF) 0 (by
      intro j; fin_cases j <;> simp [wallTileA, mkTri, wallF_pt] <;> norm_num)
    intro x hx; have := h x hx; simp at this ⊢; linarith
  · left
    exact Tri.carrier_subset_halfplane wallTileB wallF 0 (by
      intro j; fin_cases j <;> simp [wallTileB, mkTri, wallF_pt] <;> norm_num)

/-! ## `hside` from a wall

If a segment `[u,v]` of the line `{f = c}` is a wall (no tile interior meets its open segment),
then every tile through a point `p` of the OPEN segment lies on one side of the line.  Proof: a
straddling tile has an interior point `q` on the line (intermediate value along a segment from an
interior point), and the open segment `q p` lies in the tile interior and, near `p`, inside the
open wall segment. -/

theorem side_of_wall {N : ℕ} (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    {u v : Plane} (huv : u ≠ v) (hu : f u = c) (hv : f v = c)
    (hwall : ∀ y ∈ openSegment ℝ u v, ∀ i, y ∉ interior (D.tile i).carrier)
    {p : Plane} (hp : p ∈ openSegment ℝ u v) {i : Fin N} (hpi : p ∈ (D.tile i).carrier) :
    (D.tile i).carrier ⊆ {y | f y ≤ c} ∨ (D.tile i).carrier ⊆ {y | c ≤ f y} := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  rw [Set.not_subset] at h1 h2
  obtain ⟨y2, hy2, hy2'⟩ := h1
  obtain ⟨y1, hy1, hy1'⟩ := h2
  simp only [Set.mem_setOf_eq, not_le] at hy1' hy2'
  obtain ⟨w, hw⟩ := (D.tile i).interior_nonempty
  have hconv := (D.tile i).convex
  -- an interior point on the line
  have key : ∀ a b : Plane, a ∈ interior (D.tile i).carrier → b ∈ (D.tile i).carrier →
      f a ≠ f b → (f a - c) * (f b - c) < 0 → ∃ q ∈ interior (D.tile i).carrier, f q = c := by
    intro a b ha hb hne hneg
    have hfab : f b - f a ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    set t : ℝ := (c - f a) / (f b - f a) with ht
    have hft : f (a + t • (b - a)) = c := by
      simp only [map_add, map_smul, map_sub, smul_eq_mul, ht]; field_simp; ring
    have ht01 : 0 < t ∧ t < 1 := by
      rw [ht]
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hc1 : f a < c := by nlinarith
        have hc2 : c < f b := by nlinarith
        constructor
        · exact div_pos (by linarith) (by linarith)
        · rw [div_lt_one (by linarith)]; linarith
      · have hc1 : c < f a := by nlinarith
        have hc2 : f b < c := by nlinarith
        constructor
        · exact div_pos_of_neg_of_neg (by linarith) (by linarith)
        · rw [div_lt_one_of_neg (by linarith)]; linarith
    have hmem : a + t • (b - a) ∈ openSegment ℝ a b := by
      rw [openSegment_eq_image' ℝ a b]; exact ⟨t, ht01, rfl⟩
    exact ⟨_, hconv.openSegment_interior_closure_subset_interior ha (subset_closure hb) hmem, hft⟩
  obtain ⟨q, hq, hfq⟩ : ∃ q ∈ interior (D.tile i).carrier, f q = c := by
    rcases lt_trichotomy (f w) c with hlt | heq | hgt
    · exact key w y2 hw hy2 (by linarith) (by nlinarith)
    · exact ⟨w, hw, heq⟩
    · exact key w y1 hw hy1 (by linarith) (by nlinarith)
  have hqp : q ≠ p := by
    rintro rfl; exact hwall q hp i hq
  -- parametrise
  obtain ⟨tq, htq⟩ := Erdos634.TPErdos.line_eq_lineMap f hf c hu hv huv hfq
  have hp' := hp
  rw [openSegment_eq_image' ℝ u v] at hp'
  obtain ⟨s, ⟨hs0, hs1⟩, hps⟩ := hp'
  have hqd : q = u + tq • (v - u) := by
    rw [htq, AffineMap.lineMap_apply]; simp [add_comm]
  -- the point near p
  set A : ℝ := |tq - s| with hA
  set M : ℝ := min s (1 - s) with hM
  have hMpos : 0 < M := lt_min hs0 (by linarith)
  have hMs : M ≤ s := min_le_left _ _
  have hM1 : M ≤ 1 - s := min_le_right _ _
  have hA0 : 0 ≤ A := abs_nonneg _
  set δ : ℝ := M / (2 * (A + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  have hδA : δ * A < M / 2 := by
    rw [hδ, div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hδle : δ ≤ M / 2 := by
    rw [hδ, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hδ1 : δ < 1 := by linarith
  have habs := abs_le.mp (le_refl A)
  have hlow : -(δ * A) ≤ δ * (tq - s) := by
    have := neg_abs_le (tq - s); nlinarith
  have hhigh : δ * (tq - s) ≤ δ * A := by
    have := le_abs_self (tq - s); nlinarith
  set m : ℝ := s + δ * (tq - s) with hm
  have hm01 : 0 < m ∧ m < 1 := ⟨by rw [hm]; linarith, by rw [hm]; linarith⟩
  set r : Plane := u + m • (v - u) with hr
  have hr_wall : r ∈ openSegment ℝ u v := by
    rw [openSegment_eq_image' ℝ u v]; exact ⟨m, hm01, rfl⟩
  have hr_int : r ∈ interior (D.tile i).carrier := by
    have hmem : r ∈ openSegment ℝ q p := by
      rw [openSegment_eq_image' ℝ q p]
      refine ⟨1 - δ, ⟨by linarith, by linarith⟩, ?_⟩
      rw [hr, hqd, ← hps, hm]; module
    exact hconv.openSegment_interior_closure_subset_interior hq (subset_closure hpi) hmem
  exact hwall r hr_wall i hr_int

open Classical in
/-- **The one-sided angle sum at a point of a wall** (the fact G* case 2 needs): `p` in the open
wall segment `(u,v)` inside the target, then the tiles on the near side of the line have local
angles at `p` summing to `π`. -/
theorem half_angle_of_wall {N : ℕ} (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    {u v : Plane} (huv : u ≠ v) (hu : f u = c) (hv : f v = c)
    (hwall : ∀ y ∈ openSegment ℝ u v, ∀ i, y ∉ interior (D.tile i).carrier)
    {p : Plane} (hp : p ∈ openSegment ℝ u v) (hpint : p ∈ interior D.target.carrier) :
    ∑ i ∈ Finset.univ.filter (fun i => (D.tile i).carrier ⊆ {y | f y ≤ c}),
        (D.tile i).localAngle p = Real.pi := by
  have hpf : f p = c := by
    obtain ⟨a, b, _, _, hab, rfl⟩ := hp
    simp only [map_add, map_smul, smul_eq_mul, hu, hv]; rw [← add_mul, hab, one_mul]
  exact half_angle_sum D f hf c hpf hpint
    (fun i hi => side_of_wall D f hf c huv hu hv hwall hp hi)

open Classical Erdos634.TPErdos Erdos634.CertCoord in
/-- Witness for `half_angle_of_wall`: the wall of `wallDissection`, same point as above. -/
theorem half_angle_of_wall_witness :
    ∑ i ∈ Finset.univ.filter (fun i => (wallDissection.tile i).carrier ⊆ {y | wallF y ≤ 0}),
        (wallDissection.tile i).localAngle (mkPt (1/2) (1/2)) = Real.pi := by
  have hmid : mkPt (1/2) (1/2) ∈ openSegment ℝ wallU wallV := by
    refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
    ext i; fin_cases i <;> simp [wallU, wallV] <;> norm_num
  exact half_angle_of_wall wallDissection wallF wallF_ne 0 wallU_ne_wallV wallF_u wallF_v
    wall_hwall hmid (wall_hint hmid)

end Erdos634.HalfAngle

#print axioms Erdos634.HalfAngle.volume_level_line
#print axioms Erdos634.HalfAngle.two_mul_volume_half
#print axioms Erdos634.HalfAngle.half_angle_sum
#print axioms Erdos634.HalfAngle.half_angle_witness
#print axioms Erdos634.HalfAngle.side_of_wall
#print axioms Erdos634.HalfAngle.half_angle_of_wall
#print axioms Erdos634.HalfAngle.half_angle_of_wall_witness

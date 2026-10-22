-- Draft/LaczFormalRGLoc.lean -- S2/S3 of PLAN_THM21, part 1: the vertex fan for a dissection of an arbitrary REGION (not only a triangle).
-- Port of LaczFormalGraphLocal/Gen from `Dissection N` (target a triangle) to `RegionDissection N` (target a set).  The only place the target entered
-- was (a) its local cone `Tgt` near the vertex and (b) the angle sum `sum tile localAngle = target.localAngle`; (b) is replaced by the hypothesis
-- `sum tile localAngle + sum virtual widths = 2 pi` of `vertex_fan_ext`, proved for regions from volumes (`sum_localAngle_of_vol`).
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 4), Beeson, Beeson-Zhang; port of the project's own LaczFormalGraph* modules.
import Erdos634.Draft.LaczFormalGraphGen
import Erdos634.RegionDissection

open MeasureTheory Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

theorem not_interior_of_mem_other (D : RegionDissection N) {i j : Fin N} (hij : i ≠ j) {V : Plane}
    (hi : V ∈ (D.tile i).carrier) : V ∉ interior (D.tile j).carrier := by
  intro hj
  have hcl : V ∈ closure (interior (D.tile i).carrier) := by
    rw [(D.tile i).convex.closure_interior_eq_closure_of_nonempty_interior (D.tile i).interior_nonempty,
      (D.tile i).isCompact.isClosed.closure_eq]
    exact hi
  obtain ⟨y, hy1, hy2⟩ := mem_closure_iff.mp hcl _ isOpen_interior hj
  exact Set.disjoint_left.mp (D.interiors_disjoint hij) hy2 hy1

theorem not_interior_of_vertex (D : RegionDissection N) {V : Plane} (hv : ∃ i k, (D.tile i).pts k = V)
    (j : Fin N) : V ∉ interior (D.tile j).carrier := by
  obtain ⟨i, k, hk⟩ := hv
  have hmem : V ∈ (D.tile i).carrier := hk ▸ subset_convexHull ℝ _ ⟨k, rfl⟩
  by_cases hij : i = j
  · subst hij
    intro hint
    have h1 := (D.tile i).mem_interior_iff_coord_pos V |>.mp hint
    have h2 : (D.tile i).basis.coord (k + 1) V = 0 := by
      rw [← hk]; exact (D.tile i).basis.coord_apply_ne (fin3_ne_one k)
    exact absurd h2 (h1 _).ne'
  · exact not_interior_of_mem_other D hij hmem

/-- The tiles through `V`. -/
def AtV (D : RegionDissection N) (V : Plane) : Type := {i : Fin N // V ∈ (D.tile i).carrier}

noncomputable instance (D : RegionDissection N) (V : Plane) : Fintype (AtV D V) := by
  classical unfold AtV; exact Subtype.fintype _

theorem common_radius (D : RegionDissection N) (V : Plane) (p q : AtV D V → V2)
    (hloc : ∀ s : AtV D V, LocalCone (D.tile s.1) V (p s) (q s)) :
    ∃ r > 0, (∀ s : AtV D V, ∀ y : Plane, dist y V < r →
        (y ∈ (D.tile s.1).carrier ↔ inCone (p s) (q s) (toV2 (y - V)))) ∧
      (∀ i : Fin N, V ∉ (D.tile i).carrier → ∀ y : Plane, dist y V < r → y ∉ (D.tile i).carrier) := by
  classical
  choose rs hrs hiff using hloc
  have hρ : ∀ i : Fin N, ∃ ρ > 0, V ∉ (D.tile i).carrier →
      ∀ y : Plane, dist y V < ρ → y ∉ (D.tile i).carrier := by
    intro i
    by_cases h : V ∈ (D.tile i).carrier
    · exact ⟨1, one_pos, fun h' => absurd h h'⟩
    · have hopen : IsOpen ((D.tile i).carrier)ᶜ := (D.tile i).isCompact.isClosed.isOpen_compl
      obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hopen V h
      exact ⟨ρ, hρ, fun _ y hy => hball (by simpa [Metric.mem_ball] using hy)⟩
  choose ρ hρpos hρ' using hρ
  obtain ⟨r1, hr1, hle1⟩ := exists_min_pos rs hrs
  obtain ⟨r2, hr2, hle2⟩ := exists_min_pos ρ hρpos
  exact ⟨min r1 r2, lt_min hr1 hr2,
    fun s y hy => hiff s y (lt_of_lt_of_le hy ((min_le_left _ _).trans (hle1 s))),
    fun i hi y hy => hρ' i hi y (lt_of_lt_of_le hy ((min_le_right _ _).trans (hle2 i)))⟩

theorem tiles_disjoint (D : RegionDissection N) (V : Plane) (p q : AtV D V → V2)
    (hloc : ∀ s : AtV D V, LocalCone (D.tile s.1) V (p s) (q s)) :
    Disjoint' p q := by
  intro s t hst z ⟨hzs, hzt⟩
  obtain ⟨rs, hrs, hs⟩ := hloc s
  obtain ⟨rt, hrt, ht⟩ := hloc t
  obtain ⟨ε, hε, hd⟩ := exists_ptOf_small V z (lt_min hrs hrt)
  have hds : dist (ptOf V z ε) V < rs := lt_of_lt_of_le hd (min_le_left _ _)
  have hdt : dist (ptOf V z ε) V < rt := lt_of_lt_of_le hd (min_le_right _ _)
  rw [← inInt_smul_iff hε, ← toV2_ptOf V z ε] at hzs hzt
  have h1 := mem_interior_of_inInt hs hds hzs
  have h2 := mem_interior_of_inInt ht hdt hzt
  have hne : s.1 ≠ t.1 := fun h => hst (Subtype.ext h)
  exact Set.disjoint_left.mp (D.interiors_disjoint hne) h1 h2

/-- The closed cones of the tiles through `V` cover the region cone `Tgt` (a cone, locally equal to the region at `V`). -/
theorem tiles_cover (D : RegionDissection N) (V : Plane) (p q : AtV D V → V2)
    (hloc : ∀ s : AtV D V, LocalCone (D.tile s.1) V (p s) (q s))
    (Tgt : Set V2) (R : ℝ) (hR : 0 < R)
    (hT : ∀ y : Plane, dist y V < R → (y ∈ D.region ↔ toV2 (y - V) ∈ Tgt))
    (hTs : ∀ z ∈ Tgt, ∀ t : ℝ, 0 < t → ((t * z.1, t * z.2) : V2) ∈ Tgt) :
    ∀ z ∈ Tgt, ∃ s : AtV D V, inCone (p s) (q s) z := by
  intro z hz
  obtain ⟨r, hr, hiff, hout⟩ := common_radius D V p q hloc
  obtain ⟨ε, hε, hd⟩ := exists_ptOf_small V z (lt_min hr hR)
  have hd1 : dist (ptOf V z ε) V < r := lt_of_lt_of_le hd (min_le_left _ _)
  have hd2 : dist (ptOf V z ε) V < R := lt_of_lt_of_le hd (min_le_right _ _)
  have hy : ptOf V z ε ∈ D.region := by
    rw [hT _ hd2, toV2_ptOf]; exact hTs z hz ε hε
  rw [← D.covers] at hy
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
  have hVi : V ∈ (D.tile i).carrier := by
    by_contra hnot
    exact hout i hnot _ hd1 hi
  refine ⟨⟨i, hVi⟩, ?_⟩
  have := (hiff ⟨i, hVi⟩ _ hd1).mp hi
  rw [toV2_ptOf] at this
  exact (inCone_smul_iff hε).mp this

theorem tiles_angle_sum (D : RegionDissection N) (V : Plane) (p q : AtV D V → V2)
    (hwd : ∀ s : AtV D V, wd (p s) (q s) = (D.tile s.1).localAngle V) :
    ∑ s : AtV D V, wd (p s) (q s) = ∑ i, (D.tile i).localAngle V := by
  classical
  simp only [hwd]
  have h1 := Finset.sum_subtype (Finset.univ.filter fun i : Fin N => V ∈ (D.tile i).carrier)
    (p := fun i => V ∈ (D.tile i).carrier) (F := (inferInstance : Fintype (AtV D V))) (by simp) (fun i => (D.tile i).localAngle V)
  have h2 : ∑ s : AtV D V, (D.tile s.1).localAngle V
      = ∑ i ∈ Finset.univ.filter (fun i : Fin N => V ∈ (D.tile i).carrier), (D.tile i).localAngle V := h1.symm
  rw [h2]
  apply Finset.sum_filter_of_ne
  intro i _ hne
  by_contra hmem
  exact hne (Tri.localAngle_eq_zero_of_not_mem _ hmem)

/-! ## The angle sum for a region dissection -/

theorem aedisjoint (D : RegionDissection N) {i j : Fin N} (hij : i ≠ j) :
    AEDisjoint volume (D.tile i).carrier (D.tile j).carrier := by
  have hsub : (D.tile i).carrier ∩ (D.tile j).carrier ⊆
      frontier (D.tile i).carrier ∪ frontier (D.tile j).carrier := by
    rintro x ⟨hxi, hxj⟩
    by_cases h1 : x ∈ interior (D.tile i).carrier
    · by_cases h2 : x ∈ interior (D.tile j).carrier
      · exact absurd h2 (Set.disjoint_left.mp (D.interiors_disjoint hij) h1)
      · exact Or.inr ⟨subset_closure hxj, h2⟩
    · exact Or.inl ⟨subset_closure hxi, h1⟩
  exact measure_mono_null hsub (measure_union_null (D.tile i).volume_frontier (D.tile j).volume_frontier)

theorem volume_inter_ball_eq_sum (D : RegionDissection N) (x : Plane) (r : ℝ) :
    volume (D.region ∩ Metric.ball x r) = ∑ i, volume ((D.tile i).carrier ∩ Metric.ball x r) := by
  have h := measure_biUnion_finset₀ (μ := volume)
    (s := (Finset.univ : Finset (Fin N)))
    (f := fun i => (D.tile i).carrier ∩ Metric.ball x r)
    (fun i _ j _ hij => measure_mono_null
      (Set.inter_subset_inter Set.inter_subset_left Set.inter_subset_left) (aedisjoint D hij))
    (fun i _ => ((D.tile i).nullMeasurableSet).inter
      Metric.isOpen_ball.measurableSet.nullMeasurableSet)
  have hU : (⋃ i ∈ (Finset.univ : Finset (Fin N)), ((D.tile i).carrier ∩ Metric.ball x r))
          = D.region ∩ Metric.ball x r := by
    simp only [Finset.mem_univ, Set.iUnion_true]
    rw [← Set.iUnion_inter, D.covers]
  rw [hU] at h
  exact h

/-- **Angle sum from a volume.**  If the region meets every small ball at `V` in area `θ/2 · r²`, the tiles' local angles at `V` add up to `θ`. -/
theorem sum_localAngle_of_vol (D : RegionDissection N) (hN : 0 < N) (V : Plane) (θ : ℝ) (hθ : 0 ≤ θ) (ρ : ℝ) (hρ : 0 < ρ)
    (hvol : ∀ r, 0 < r → r ≤ ρ → volume (D.region ∩ Metric.ball V r) = ENNReal.ofReal (θ / 2 * r ^ 2)) :
    ∑ i, (D.tile i).localAngle V = θ := by
  classical
  choose ri hri hcontrib using fun i => (D.tile i).volume_inter_ball_localAngle V
  obtain ⟨r0, hr0, hr0le⟩ := exists_common_radius hN ri hri
  set r : ℝ := min ρ r0 with hrdef
  have hrpos : 0 < r := lt_min hρ hr0
  have hsum := volume_inter_ball_eq_sum D V r
  rw [hvol r hrpos (min_le_left _ _)] at hsum
  have htiles : ∀ i ∈ (Finset.univ : Finset (Fin N)),
      volume ((D.tile i).carrier ∩ Metric.ball V r)
        = ENNReal.ofReal ((D.tile i).localAngle V / 2 * r ^ 2) := fun i _ =>
    hcontrib i r hrpos ((min_le_right _ _).trans (hr0le i))
  rw [Finset.sum_congr rfl htiles,
    ← ENNReal.ofReal_sum_of_nonneg (fun i _ => by
      have := (D.tile i).localAngle_nonneg V
      positivity)] at hsum
  have hreal := (ENNReal.ofReal_eq_ofReal_iff
    (by positivity)
    (Finset.sum_nonneg fun i _ => by
      have := (D.tile i).localAngle_nonneg V
      positivity)).mp hsum
  have hfact : ∑ i, (D.tile i).localAngle V / 2 * r ^ 2
      = (∑ i, (D.tile i).localAngle V) * (r ^ 2 / 2) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hfact] at hreal
  have hr2 : (0:ℝ) < r ^ 2 / 2 := by positivity
  have hkey : (∑ i, (D.tile i).localAngle V) * (r ^ 2 / 2) = θ * (r ^ 2 / 2) := by
    rw [← hreal]; ring
  exact mul_right_cancel₀ hr2.ne' hkey

/-- Interior point of the region: the tiles' local angles add up to `2π`. -/
theorem sum_localAngle_interior (D : RegionDissection N) (hN : 0 < N) {V : Plane} (hV : V ∈ interior D.region) :
    ∑ i, (D.tile i).localAngle V = 2 * Real.pi := by
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp isOpen_interior V hV
  refine sum_localAngle_of_vol D hN V (2 * Real.pi) (by positivity) ρ hρ (fun r hr hrρ => ?_)
  have : D.region ∩ Metric.ball V r = Metric.ball V r := by
    apply Set.inter_eq_right.mpr
    intro y hy
    exact interior_subset (hball (Metric.ball_subset_ball hrρ hy))
  rw [this, volume_ball_plane V hr.le]
  congr 1; ring

/-- Point of the region where the region agrees near `V` with a triangle `T`: the tiles' local angles add up to `T`'s local angle. -/
theorem sum_localAngle_tri (D : RegionDissection N) (hN : 0 < N) {V : Plane} (T : Tri) {ρ : ℝ} (hρ : 0 < ρ)
    (hiff : ∀ y, dist y V < ρ → (y ∈ D.region ↔ y ∈ T.carrier)) :
    ∑ i, (D.tile i).localAngle V = T.localAngle V := by
  obtain ⟨rT, hrT, hT⟩ := T.volume_inter_ball_localAngle V
  refine sum_localAngle_of_vol D hN V (T.localAngle V) (T.localAngle_nonneg V) (min ρ rT) (lt_min hρ hrT) (fun r hr hrle => ?_)
  have : D.region ∩ Metric.ball V r = T.carrier ∩ Metric.ball V r := by
    ext y
    simp only [Set.mem_inter_iff, Metric.mem_ball]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨(hiff y (lt_of_lt_of_le h2 (hrle.trans (min_le_left _ _)))).mp h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨(hiff y (lt_of_lt_of_le h2 (hrle.trans (min_le_left _ _)))).mpr h1, h2⟩
  rw [this]
  exact hT r hr (hrle.trans (min_le_right _ _))

end Erdos634.Draft.LaczFormal.RG

-- Draft/LaczFormalFluxPolyInt.lean -- FLUX-CANCELLATION for polygon targets, part 1: the interior double covering (G4 chain) for a
-- `RegionDissection` (any region, no triangle target).  Mechanical port of Dissection.lean (aedisjoint, volume_ball_eq_sum, local_balance,
-- local_contribution, two_tiles_at_edge_point, cross_disjoint_of_onEdge, leftDir_antiparallel, second_tile_at_edge_point, dirSet, leftUnit_neg,
-- dirSet_sub): each of those used the target only through `D.target.carrier`, `covers`, `interiors_disjoint`; here `D.region` replaces it.
-- NOTE / UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 7.3/8.3: the functional Phi), Beeson, Beeson-Zhang.
import Erdos634.Dissection
import Erdos634.EdgeChain
import Erdos634.RegionDissection

open scoped Classical
open MeasureTheory Set Erdos634.Geometry
open scoped ENNReal
set_option linter.dupNamespace false

namespace Erdos634.RegionDissection

variable {N : ℕ}

/-- **Disjoint interiors ⟹ a.e. disjoint.**  Two tiles meet only in their frontiers, which are null
because the tiles are convex (`Tri.volume_frontier`).  This is the step at which a non-edge-to-edge
incidence stops mattering. -/
theorem RegionDissection.aedisjoint (D : RegionDissection N) {i j : Fin N} (hij : i ≠ j) :
    AEDisjoint volume (D.tile i).carrier (D.tile j).carrier := by
  -- a point in both tiles lies in the frontier of at least one of them
  have hsub : (D.tile i).carrier ∩ (D.tile j).carrier ⊆
      frontier (D.tile i).carrier ∪ frontier (D.tile j).carrier := by
    rintro x ⟨hxi, hxj⟩
    by_cases h1 : x ∈ interior (D.tile i).carrier
    · by_cases h2 : x ∈ interior (D.tile j).carrier
      · exfalso
        have hd : Disjoint (interior (D.tile i).carrier) (interior (D.tile j).carrier) :=
          D.interiors_disjoint hij
        exact Set.disjoint_left.mp hd h1 h2
      · exact Or.inr ⟨subset_closure hxj, h2⟩
    · exact Or.inl ⟨subset_closure hxi, h1⟩
  refine measure_mono_null hsub ?_
  exact measure_union_null (D.tile i).volume_frontier (D.tile j).volume_frontier

/-- **G4 step 3 — a ball inside the target is partitioned by the tiles.**  The same argument as
`Dissection.volume_target`, localised to a ball: the tiles cover the target and are a.e. disjoint, so
their traces on any ball contained in the target are a.e. disjoint and cover it. -/
theorem RegionDissection.volume_ball_eq_sum {N : ℕ} (D : RegionDissection N) {x : Plane} {r : ℝ}
    (hball : Metric.ball x r ⊆ D.region) :
    volume (Metric.ball x r) = ∑ i, volume ((D.tile i).carrier ∩ Metric.ball x r) := by
  have h := measure_biUnion_finset₀ (μ := volume)
    (s := (Finset.univ : Finset (Fin N)))
    (f := fun i => (D.tile i).carrier ∩ Metric.ball x r)
    (fun i _ j _ hij => measure_mono_null
      (Set.inter_subset_inter Set.inter_subset_left Set.inter_subset_left) (D.aedisjoint hij))
    (fun i _ => ((D.tile i).nullMeasurableSet).inter
      Metric.isOpen_ball.measurableSet.nullMeasurableSet)
  have hU : (⋃ i ∈ (Finset.univ : Finset (Fin N)), ((D.tile i).carrier ∩ Metric.ball x r))
          = Metric.ball x r := by
    simp only [Finset.mem_univ, Set.iUnion_true]
    rw [← Set.iUnion_inter, D.covers]
    exact Set.inter_eq_self_of_subset_right hball
  rw [hU] at h
  exact h

theorem RegionDissection.local_balance {N : ℕ} (D : RegionDissection N) {x : Plane} {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball x r ⊆ D.region)
    (E I : Finset (Fin N)) (hdisj : Disjoint E I)
    (hE : ∀ i ∈ E, 2 * volume ((D.tile i).carrier ∩ Metric.ball x r) = volume (Metric.ball x r))
    (hI : ∀ i ∈ I, volume ((D.tile i).carrier ∩ Metric.ball x r) = volume (Metric.ball x r))
    (hrest : ∀ i ∈ (Finset.univ : Finset (Fin N)), i ∉ E ∪ I →
      volume ((D.tile i).carrier ∩ Metric.ball x r) = 0)
    (hEne : E.Nonempty) :
    E.card = 2 ∧ I.card = 0 := by
  classical
  set V : ℝ≥0∞ := volume (Metric.ball x r) with hV
  have hV0 : V ≠ 0 := (Metric.measure_ball_pos volume x hr).ne'
  have hVt : V ≠ ⊤ := measure_ball_lt_top.ne
  -- the tiles that contribute are exactly those in `E ∪ I`
  have hsum : ∑ i ∈ E ∪ I, volume ((D.tile i).carrier ∩ Metric.ball x r) = V := by
    rw [Finset.sum_subset (Finset.subset_univ (E ∪ I)) hrest]
    exact (D.volume_ball_eq_sum hball).symm
  -- split that sum and weigh each part
  have hsplit : ∑ i ∈ E ∪ I, volume ((D.tile i).carrier ∩ Metric.ball x r)
      = (∑ i ∈ E, volume ((D.tile i).carrier ∩ Metric.ball x r))
        + ∑ i ∈ I, volume ((D.tile i).carrier ∩ Metric.ball x r) :=
    Finset.sum_union hdisj
  have hEsum : 2 * ∑ i ∈ E, volume ((D.tile i).carrier ∩ Metric.ball x r) = (E.card : ℝ≥0∞) * V := by
    rw [Finset.mul_sum, Finset.sum_congr rfl hE, Finset.sum_const, nsmul_eq_mul]
  have hIsum : ∑ i ∈ I, volume ((D.tile i).carrier ∩ Metric.ball x r) = (I.card : ℝ≥0∞) * V := by
    rw [Finset.sum_congr rfl hI, Finset.sum_const, nsmul_eq_mul]
  -- `2·V = card E · V + card I · 2V`, so `card E + 2·card I = 2`
  rw [hsplit] at hsum
  have hkey : (E.card : ℝ≥0∞) * V + (I.card : ℝ≥0∞) * (2 * V) = 2 * V := by
    have h1 : (I.card : ℝ≥0∞) * (2 * V) = 2 * ((I.card : ℝ≥0∞) * V) := by ring
    rw [h1, ← hEsum, ← hIsum, ← mul_add, hsum]
  have hcount : E.card + 2 * I.card = 2 := local_degree_eq hV0 hVt hkey
  exact local_degree_two (Finset.card_pos.mpr hEne) hcount

/-- `x` lies in the relative interior of one of tile `i`'s edges. -/
def OnEdgeR {N : ℕ} (D : RegionDissection N) (x : Plane) (i : Fin N) : Prop :=
  ∃ k, (D.tile i).basis.coord k x = 0 ∧ ∀ j, j ≠ k → 0 < (D.tile i).basis.coord j x

/-- `x` is interior to tile `i`. -/
def InsideR {N : ℕ} (D : RegionDissection N) (x : Plane) (i : Fin N) : Prop :=
  ∀ j, 0 < (D.tile i).basis.coord j x

/-- **Every tile has a radius below which its local contribution is pinned.**  Which of the three
values it takes is decided by `Tri.classify`, so this is where the classification becomes a single
uniform statement that can be quantified over the tiles. -/
theorem RegionDissection.local_contribution {N : ℕ} (D : RegionDissection N) {x : Plane} (i : Fin N)
    (hxv : ∀ k, x ≠ (D.tile i).pts k) :
    ∃ ri > 0, ∀ r', 0 < r' → r' ≤ ri →
      (OnEdgeR D x i →
        2 * volume ((D.tile i).carrier ∩ Metric.ball x r') = volume (Metric.ball x r'))
    ∧ (InsideR D x i →
        volume ((D.tile i).carrier ∩ Metric.ball x r') = volume (Metric.ball x r'))
    ∧ (¬ OnEdgeR D x i → ¬ InsideR D x i →
        volume ((D.tile i).carrier ∩ Metric.ball x r') = 0) := by
  classical
  rcases (D.tile i).classify hxv with hpos | ⟨k, hk0, hkpos⟩ | ⟨k, hkneg⟩
  · -- interior: `OnEdge` is impossible, since no coordinate vanishes
    obtain ⟨r, hr, h⟩ := (D.tile i).volume_inter_ball_interior hpos
    refine ⟨r, hr, fun r' h1 h2 => ⟨fun hE => ?_, fun _ => h r' h1 h2, fun _ hI => absurd hpos hI⟩⟩
    obtain ⟨m, hm, -⟩ := hE
    exact absurd hm (ne_of_gt (hpos m))
  · -- edge: `Inside` is impossible, since the `k`-th coordinate vanishes
    have hne : ∀ j : Fin 3, j + 1 ≠ j ∧ j + 2 ≠ j := by decide
    obtain ⟨r, hr, h⟩ := (D.tile i).volume_inter_ball_edge k hk0
      (hkpos _ (hne k).1) (hkpos _ (hne k).2)
    refine ⟨r, hr, fun r' h1 h2 => ⟨fun _ => h r' h1 h2, fun hI => ?_, fun hE _ => ?_⟩⟩
    · exact absurd hk0 (ne_of_gt (hI k))
    · exact absurd ⟨k, hk0, hkpos⟩ hE
  · -- exterior
    obtain ⟨r, hr, h⟩ := (D.tile i).volume_inter_ball_exterior hkneg
    refine ⟨r, hr, fun r' h1 h2 => ⟨fun hE => ?_, fun hI => ?_, fun _ _ => h r' h1 h2⟩⟩
    · obtain ⟨m, hm, hrest⟩ := hE
      by_cases hmk : k = m
      · rw [hmk] at hkneg; exact absurd hm (ne_of_lt hkneg)
      · exact absurd (hrest k hmk) (not_lt.mpr hkneg.le)
    · exact absurd (hI k) (not_lt.mpr hkneg.le)

theorem RegionDissection.two_tiles_at_edge_point {N : ℕ} (D : RegionDissection N) (hN : 0 < N) {x : Plane}
    (hxv : ∀ i k, x ≠ (D.tile i).pts k)
    {R : ℝ} (hR : 0 < R) (hRt : Metric.ball x R ⊆ D.region)
    (hEne : (Finset.univ.filter (fun i => OnEdgeR D x i)).Nonempty) :
    (Finset.univ.filter (fun i => OnEdgeR D x i)).card = 2
      ∧ (Finset.univ.filter (fun i => InsideR D x i)).card = 0 := by
  classical
  choose ri hri hcontrib using fun i => D.local_contribution i (hxv i)
  -- one radius for every tile at once, and inside the target
  obtain ⟨r0, hr0, hr0le⟩ := exists_common_radius hN ri hri
  refine D.local_balance (x := x) (r := min R r0) (lt_min hR hr0) ?_ _ _ ?_ ?_ ?_ ?_ hEne
  · exact (Metric.ball_subset_ball (min_le_left _ _)).trans hRt
  · -- a tile cannot both contain `x` inside and meet it on an edge
    rw [Finset.disjoint_left]
    intro i hiE hiI
    obtain ⟨m, hm, -⟩ := (Finset.mem_filter.mp hiE).2
    exact absurd hm (ne_of_gt ((Finset.mem_filter.mp hiI).2 m))
  · exact fun i hi => (hcontrib i _ (lt_min hR hr0)
      ((min_le_right R r0).trans (hr0le i))).1 (Finset.mem_filter.mp hi).2
  · exact fun i hi => (hcontrib i _ (lt_min hR hr0)
      ((min_le_right R r0).trans (hr0le i))).2.1 (Finset.mem_filter.mp hi).2
  · intro i _ hi
    rw [Finset.mem_union, not_or] at hi
    exact (hcontrib i _ (lt_min hR hr0) ((min_le_right R r0).trans (hr0le i))).2.2
      (fun h => hi.1 (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩))
      (fun h => hi.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩))

theorem RegionDissection.cross_disjoint_of_onEdge {N : ℕ} (D : RegionDissection N)
    {i₁ i₂ : Fin N} (hne : i₁ ≠ i₂) {x : Plane} {m₁ m₂ : Fin 3}
    (hm₁ : (D.tile i₁).basis.coord m₁ x = 0)
    (ho₁ : ∀ j, j ≠ m₁ → 0 < (D.tile i₁).basis.coord j x)
    (hm₂ : (D.tile i₂).basis.coord m₂ x = 0)
    (ho₂ : ∀ j, j ≠ m₂ → 0 < (D.tile i₂).basis.coord j x)
    (v : Plane) :
    ¬(0 < cross ((D.tile i₁).leftDir (m₁ + 1)) v
      ∧ 0 < cross ((D.tile i₂).leftDir (m₂ + 1)) v) := by
  rintro ⟨hv₁, hv₂⟩
  obtain ⟨ε₁, hε₁, h₁⟩ := (D.tile i₁).mem_interior_of_cross_pos hm₁ ho₁ hv₁
  obtain ⟨ε₂, hε₂, h₂⟩ := (D.tile i₂).mem_interior_of_cross_pos hm₂ ho₂ hv₂
  set ε := min ε₁ ε₂ / 2 with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]; exact half_pos (lt_min hε₁ hε₂)
  have hlt₁ : ε < ε₁ := by
    rw [hεdef]; have := min_le_left ε₁ ε₂; linarith
  have hlt₂ : ε < ε₂ := by
    rw [hεdef]; have := min_le_right ε₁ ε₂; linarith
  exact Set.disjoint_left.mp (D.interiors_disjoint hne)
    (h₁ ε hεpos hlt₁) (h₂ ε hεpos hlt₂)

theorem RegionDissection.leftDir_antiparallel {N : ℕ} (D : RegionDissection N)
    {i₁ i₂ : Fin N} (hne : i₁ ≠ i₂) {x : Plane} {m₁ m₂ : Fin 3}
    (hm₁ : (D.tile i₁).basis.coord m₁ x = 0)
    (ho₁ : ∀ j, j ≠ m₁ → 0 < (D.tile i₁).basis.coord j x)
    (hm₂ : (D.tile i₂).basis.coord m₂ x = 0)
    (ho₂ : ∀ j, j ≠ m₂ → 0 < (D.tile i₂).basis.coord j x) :
    ∃ c : ℝ, c < 0 ∧ (D.tile i₂).leftDir (m₂ + 1) = c • (D.tile i₁).leftDir (m₁ + 1) := by
  obtain ⟨c, hcneg, hc⟩ := proportional_of_disjoint_pos
    (crossL ((D.tile i₁).leftDir (m₁ + 1))) (crossL ((D.tile i₂).leftDir (m₂ + 1)))
    (crossL_ne_zero ((D.tile i₁).leftDir_ne_zero _))
    (crossL_ne_zero ((D.tile i₂).leftDir_ne_zero _))
    (fun v => by
      simpa using D.cross_disjoint_of_onEdge hne hm₁ ho₁ hm₂ ho₂ v)
  refine ⟨c, hcneg, ?_⟩
  have hzero : ∀ v, cross ((D.tile i₂).leftDir (m₂ + 1) - c • (D.tile i₁).leftDir (m₁ + 1)) v = 0 := by
    intro v
    have h1 : cross ((D.tile i₂).leftDir (m₂ + 1)) v = c * cross ((D.tile i₁).leftDir (m₁ + 1)) v := by
      simpa using hc v
    simp only [cross, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    simp only [cross] at h1
    linarith [h1]
  exact sub_eq_zero.mp (eq_zero_of_cross_eq_zero hzero)

theorem RegionDissection.second_tile_at_edge_point {N : ℕ} (D : RegionDissection N) (hN : 0 < N) {x : Plane}
    (hxv : ∀ i k, x ≠ (D.tile i).pts k)
    {R : ℝ} (hR : 0 < R) (hRt : Metric.ball x R ⊆ D.region)
    {i₀ : Fin N} (hi₀ : OnEdgeR D x i₀) :
    ∃ i₁, i₁ ≠ i₀ ∧ OnEdgeR D x i₁ := by
  classical
  have hmem : i₀ ∈ Finset.univ.filter (fun i => OnEdgeR D x i) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi₀⟩
  have hcard := (D.two_tiles_at_edge_point hN hxv hR hRt ⟨i₀, hmem⟩).1
  obtain ⟨i₁, hi₁mem, hne⟩ := exists_second_of_card_two hcard i₀
  exact ⟨i₁, hne, (Finset.mem_filter.mp hi₁mem).2⟩

noncomputable def RegionDissection.dirSet {N : ℕ} (D : RegionDissection N) (d : Dir) : Set Plane :=
  (⋃ i : Fin N, ⋃ k : Fin 3, ⋃ (_ : (D.tile i).leftUnit k = d), (D.tile i).edge k)
    ∩ interior D.region

theorem RegionDissection.dirSet_subset_interior {N : ℕ} (D : RegionDissection N) (d : Dir) :
    D.dirSet d ⊆ interior D.region := Set.inter_subset_right

/-- Every point of `dirSet d` lies on some tile edge whose left-hand direction is `d`.  This is the
form the orientation argument consumes: given such a tile, `two_tiles_at_edge_point` produces the
second one and `leftDir_opposite_of_opposite_sides` gives it the reversed direction. -/
theorem RegionDissection.mem_dirSet {N : ℕ} (D : RegionDissection N) (d : Dir) {x : Plane}
    (hx : x ∈ D.dirSet d) :
    ∃ i k, (D.tile i).leftUnit k = d ∧ x ∈ (D.tile i).edge k := by
  obtain ⟨hu, -⟩ := hx
  simp only [Set.mem_iUnion] at hu
  obtain ⟨i, k, hik, hmem⟩ := hu
  exact ⟨i, k, hik, hmem⟩

/-- **`leftUnit` reverses across a shared edge point** — `horient` for two tiles, normalised. -/
theorem RegionDissection.leftUnit_neg {N : ℕ} (D : RegionDissection N)
    {i₁ i₂ : Fin N} (hne : i₁ ≠ i₂) {x : Plane} {m₁ m₂ : Fin 3}
    (hm₁ : (D.tile i₁).basis.coord m₁ x = 0)
    (ho₁ : ∀ j, j ≠ m₁ → 0 < (D.tile i₁).basis.coord j x)
    (hm₂ : (D.tile i₂).basis.coord m₂ x = 0)
    (ho₂ : ∀ j, j ≠ m₂ → 0 < (D.tile i₂).basis.coord j x) :
    (D.tile i₂).leftUnit (m₂ + 1) = Dir.neg ((D.tile i₁).leftUnit (m₁ + 1)) := by
  obtain ⟨c, hcneg, hc⟩ := D.leftDir_antiparallel hne hm₁ ho₁ hm₂ ho₂
  apply Subtype.ext
  simpa [Tri.leftUnit, Dir.neg] using
    unit_smul_of_neg hcneg ((D.tile i₁).leftDir_ne_zero (m₁ + 1)) hc

/-- The (finite) set of tile vertices — the exceptional set `g4` quotients by. -/
def RegionDissection.vertexSet {N : ℕ} (D : RegionDissection N) : Set Plane :=
  ⋃ i : Fin N, ⋃ k : Fin 3, {(D.tile i).pts k}

theorem RegionDissection.vertexSet_finite {N : ℕ} (D : RegionDissection N) : D.vertexSet.Finite :=
  Set.finite_iUnion fun _ => Set.finite_iUnion fun _ => Set.finite_singleton _

theorem RegionDissection.notMem_vertexSet {N : ℕ} (D : RegionDissection N) {x : Plane}
    (hx : x ∉ D.vertexSet) : ∀ i k, x ≠ (D.tile i).pts k := by
  intro i k h
  exact hx (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨k, by simp [h]⟩⟩)

/-- **One inclusion of `horient` for `dirSet`.**  At a non-vertex point of an interior edge carrying
direction `d`, `Dissection.second_tile_at_edge_point` produces a *different* tile also meeting `x` on
an edge, and `Dissection.leftUnit_neg` says that edge carries `Dir.neg d`. -/
theorem RegionDissection.dirSet_sub {N : ℕ} (D : RegionDissection N) (hN : 0 < N) (d : Dir) :
    D.dirSet d \ D.vertexSet ⊆ D.dirSet (Dir.neg d) \ D.vertexSet := by
  rintro x ⟨hxd, hxv⟩
  refine ⟨?_, hxv⟩
  have hxint : x ∈ interior D.region := hxd.2
  obtain ⟨i₀, k₀, hk₀, hmem⟩ := D.mem_dirSet d hxd
  have hnv := D.notMem_vertexSet hxv
  obtain ⟨hz₀, hp₀⟩ := (D.tile i₀).onEdge_data hmem (hnv i₀)
  -- a ball around `x` inside the target
  obtain ⟨R, hR, hRt⟩ := Metric.isOpen_iff.mp isOpen_interior x hxint
  have hRt' : Metric.ball x R ⊆ D.region := hRt.trans interior_subset
  -- the second tile
  obtain ⟨i₁, hne, hi₁⟩ := D.second_tile_at_edge_point hN hnv hR hRt' ⟨k₀ + 2, hz₀, hp₀⟩
  obtain ⟨m₁, hz₁, hp₁⟩ := hi₁
  have hkey := D.leftUnit_neg (Ne.symm hne) hz₀ hp₀ hz₁ hp₁
  have hshift : (k₀ + 2 + 1 : Fin 3) = k₀ := by fin_cases k₀ <;> rfl
  rw [hshift, hk₀] at hkey
  refine ⟨?_, hxint⟩
  exact Set.mem_iUnion.mpr ⟨i₁, Set.mem_iUnion.mpr ⟨m₁ + 1, Set.mem_iUnion.mpr
    ⟨hkey, (D.tile i₁).mem_edge_of_coord_zero hz₁ hp₁⟩⟩⟩

/-- **`horient` for `dirSet`** — the hypothesis `g4` consumes, now a theorem. -/
theorem RegionDissection.dirSet_horient {N : ℕ} (D : RegionDissection N) (hN : 0 < N) (d : Dir) :
    D.dirSet d \ D.vertexSet = D.dirSet (Dir.neg d) \ D.vertexSet := by
  refine Set.Subset.antisymm (D.dirSet_sub hN d) ?_
  have h := D.dirSet_sub hN (Dir.neg d)
  rwa [Dir.neg_involutive d] at h

end Erdos634.RegionDissection

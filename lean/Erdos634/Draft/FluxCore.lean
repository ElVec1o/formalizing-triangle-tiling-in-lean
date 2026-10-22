-- Draft/FluxCore.lean — `lem:cancel`, layer 1, part 1: the flux, the edge index, the
-- classification of tile edges, and same-direction exclusion.  Imported into All.lean (All.lean:459).
-- Design: (private working notes, not included) §3.1.
--
-- Formalization debt on the prime-case VERIFIED path; not progress on the three /goal outcomes.
--
-- Reuse (cited, not re-derived): `Tri.coord_eq_zero_of_mem_edge`, `Tri.onEdge_param`,
-- `mem_ne_ends_of_avg`, `Dissection.leftUnit_neg`, `Tri.eq_vertex_of_two_coords_zero`,
-- `Tri.interior_coord_pos`, `Tri.ball_subset_of_pos`, `tile_subset_target`,
-- `Tri.carrier_eq_nonneg_coord`, `Tri.edge_subset_carrier`.
-- Local re-proof (import weight, sanctioned by DESIGN.md §3): `Tri.coord_zero_mem_segment'` is a
-- verbatim copy of `BaseSelection.coord_zero_mem_segment` (that module pulls 24 project modules).
import Erdos634.Dissection
import Erdos634.EdgeChain

open scoped Classical

namespace Erdos634.Geometry

open MeasureTheory Set

variable {N : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- **`C_f(T)` of the paper**: the flux of a direction weight `f` through the ccw boundary of `T`,
each edge directed with `T` on its left (`Tri.leftUnit`) and weighted by its length. -/
noncomputable def Tri.flux (T : Tri) (f : Dir → E) : E :=
  ∑ k : Fin 3, dist (T.pts k) (T.pts (k + 1)) • f (T.leftUnit k)

/-- A direction is never its own reversal (a unit vector is nonzero). -/
theorem Dir.neg_ne_self (d : Dir) : Dir.neg d ≠ d := by
  intro h
  have h1 : -d.1 = d.1 := congrArg Subtype.val h
  have h2 : (2:ℝ) • d.1 = 0 := by
    rw [two_smul]
    nth_rewrite 1 [← h1]
    exact neg_add_cancel _
  have h3 : d.1 = 0 := by
    rcases smul_eq_zero.mp h2 with h | h
    · norm_num at h
    · exact h
  have h4 := d.2
  rw [h3, norm_zero] at h4
  norm_num at h4

namespace Dissection

/-- Length of tile edge `e = (i, k)`. -/
noncomputable def eLen (D : Dissection N) (e : Fin N × Fin 3) : ℝ :=
  dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))

/-- Left-hand unit direction of tile edge `e`. -/
noncomputable def eDir (D : Dissection N) (e : Fin N × Fin 3) : Dir := (D.tile e.1).leftUnit e.2

/-- Point set of tile edge `e`. -/
def eSet (D : Dissection N) (e : Fin N × Fin 3) : Set Plane := (D.tile e.1).edge e.2

/-- The tile edges lying on target side `j`. -/
noncomputable def sideEdges (D : Dissection N) (j : Fin 3) : Finset (Fin N × Fin 3) :=
  Finset.univ.filter fun e => D.eSet e ⊆ D.target.edge j

/-- The tile edges lying on no target side (the interior edges). -/
noncomputable def intEdges (D : Dissection N) : Finset (Fin N × Fin 3) :=
  Finset.univ.filter fun e => ∀ j, ¬ D.eSet e ⊆ D.target.edge j

/-- The sum of the tiles' fluxes is a sum over all `3N` tile edges. -/
theorem flux_sum_eq (D : Dissection N) (f : Dir → E) :
    ∑ i, (D.tile i).flux f = ∑ e : Fin N × Fin 3, D.eLen e • f (D.eDir e) := by
  rw [Fintype.sum_prod_type]
  rfl

theorem eLen_nonneg (D : Dissection N) (e : Fin N × Fin 3) : 0 ≤ D.eLen e := dist_nonneg

end Dissection

/-- A point of a side of a triangle is not interior to it. -/
theorem Tri.notMem_interior_of_mem_edge (T : Tri) {j : Fin 3} {x : Plane}
    (hx : x ∈ T.edge j) : x ∉ interior T.carrier := by
  intro hint
  have h0 := T.coord_eq_zero_of_mem_edge j hx
  have hpos := T.interior_coord_pos hint (j + 2)
  rw [h0] at hpos
  exact lt_irrefl _ hpos

/-- Verbatim local copy of `BaseSelection.coord_zero_mem_segment` (import weight). -/
theorem Tri.coord_zero_mem_segment' (T : Tri) (k : Fin 3) (x : Plane)
    (h0 : T.basis.coord k x = 0) (hnn : ∀ j, 0 ≤ T.basis.coord j x) :
    x ∈ segment ℝ (T.pts (k+1)) (T.pts (k+2)) := by
  have hx : x = (T.basis.coord 0 x) • T.pts 0 + (T.basis.coord 1 x) • T.pts 1
        + (T.basis.coord 2 x) • T.pts 2 := by
    have h := T.basis.affineCombination_coord_eq_self (k := ℝ) x
    rw [Finset.affineCombination_eq_linear_combination] at h
    · rw [Fin.sum_univ_three] at h; simpa [Tri.basis] using h.symm
    · exact T.basis.sum_coord_apply_eq_one x
  have hsum : T.basis.coord 0 x + T.basis.coord 1 x + T.basis.coord 2 x = 1 := by
    have := T.basis.sum_coord_apply_eq_one (k := ℝ) x
    rwa [Fin.sum_univ_three] at this
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
  rcases hk with rfl | rfl | rfl
  · refine ⟨T.basis.coord 1 x, T.basis.coord 2 x, hnn 1, hnn 2, by linarith [h0, hsum], ?_⟩
    simp only [show ((0:Fin 3)+1) = 1 from rfl, show ((0:Fin 3)+2) = 2 from rfl]
    conv_rhs => rw [hx]
    rw [h0]; module
  · refine ⟨T.basis.coord 2 x, T.basis.coord 0 x, hnn 2, hnn 0, by linarith [h0, hsum], ?_⟩
    simp only [show ((1:Fin 3)+1) = 2 from rfl, show ((1:Fin 3)+2) = 0 from rfl]
    conv_rhs => rw [hx]
    rw [h0]; module
  · refine ⟨T.basis.coord 0 x, T.basis.coord 1 x, hnn 0, hnn 1, by linarith [h0, hsum], ?_⟩
    simp only [show ((2:Fin 3)+1) = 0 from rfl, show ((2:Fin 3)+2) = 1 from rfl]
    conv_rhs => rw [hx]
    rw [h0]; module

/-- A point of the carrier with a vanishing coordinate lies on the opposite side. -/
theorem Tri.mem_edge_of_coord_zero_nonneg (T : Tri) {m : Fin 3} {x : Plane}
    (h0 : T.basis.coord m x = 0) (hnn : ∀ j, 0 ≤ T.basis.coord j x) :
    x ∈ T.edge (m + 1) := by
  have h := T.coord_zero_mem_segment' m x h0 hnn
  have hidx : m + 1 + 1 = m + 2 := by fin_cases m <;> rfl
  rw [Tri.edge, hidx]
  exact h

/-- **The classification (M2).**  A non-endpoint point of a tile edge is either interior to the
target, or the whole tile edge lies on a target side.  (The vanishing target coordinate at `x` is
`≥ 0` on the tile and `0` at a strict convex combination of the edge's endpoints, so it vanishes at
both endpoints.) -/
theorem Dissection.edge_interior_or_side (D : Dissection N) (e : Fin N × Fin 3) {x : Plane}
    (hx : x ∈ D.eSet e) (hx1 : x ≠ (D.tile e.1).pts e.2) (hx2 : x ≠ (D.tile e.1).pts (e.2 + 1)) :
    x ∈ interior D.target.carrier ∨ ∃ j, D.eSet e ⊆ D.target.edge j := by
  by_cases hint : x ∈ interior D.target.carrier
  · exact Or.inl hint
  right
  have hnnT : ∀ y ∈ (D.tile e.1).carrier, ∀ i, 0 ≤ D.target.basis.coord i y := by
    intro y hy i
    have := tile_subset_target D e.1 hy
    rw [D.target.carrier_eq_nonneg_coord] at this
    exact this i
  have haT : (D.tile e.1).pts e.2 ∈ (D.tile e.1).carrier := subset_convexHull ℝ _ ⟨e.2, rfl⟩
  have hbT : (D.tile e.1).pts (e.2 + 1) ∈ (D.tile e.1).carrier :=
    subset_convexHull ℝ _ ⟨e.2 + 1, rfl⟩
  have hxT : x ∈ (D.tile e.1).carrier := (D.tile e.1).edge_subset_carrier e.2 hx
  obtain ⟨m, hm⟩ : ∃ m, D.target.basis.coord m x = 0 := by
    by_contra hcon
    push Not at hcon
    apply hint
    have hpos : ∀ i, 0 < D.target.basis.coord i x := fun i =>
      lt_of_le_of_ne (hnnT x hxT i) (Ne.symm (hcon i))
    obtain ⟨r, hr, hsub⟩ := D.target.ball_subset_of_pos hpos
    exact mem_interior.mpr ⟨Metric.ball x r, hsub, Metric.isOpen_ball, Metric.mem_ball_self hr⟩
  have hx' : x ∈ segment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) := hx
  obtain ⟨s, t, hs, ht, hst, hxst⟩ := hx'
  have hspos : 0 < s := by
    rcases hs.lt_or_eq with h | h
    · exact h
    · exfalso; apply hx2
      have ht1 : t = 1 := by linarith
      rw [← hxst, ← h, ht1, zero_smul, one_smul, zero_add]
  have htpos : 0 < t := by
    rcases ht.lt_or_eq with h | h
    · exact h
    · exfalso; apply hx1
      have hs1 : s = 1 := by linarith
      rw [← hxst, ← h, hs1, zero_smul, one_smul, add_zero]
  have hcomb : D.target.basis.coord m x
      = s * D.target.basis.coord m ((D.tile e.1).pts e.2)
        + t * D.target.basis.coord m ((D.tile e.1).pts (e.2 + 1)) := by
    rw [← hxst, Convex.combo_affine_apply hst, smul_eq_mul, smul_eq_mul]
  have hga := hnnT _ haT m
  have hgb := hnnT _ hbT m
  have h1 : 0 ≤ s * D.target.basis.coord m ((D.tile e.1).pts e.2) := mul_nonneg hs hga
  have h2 : 0 ≤ t * D.target.basis.coord m ((D.tile e.1).pts (e.2 + 1)) := mul_nonneg ht hgb
  have h3 : s * D.target.basis.coord m ((D.tile e.1).pts e.2) = 0 := by linarith
  have h4 : t * D.target.basis.coord m ((D.tile e.1).pts (e.2 + 1)) = 0 := by linarith
  have hza := (mul_eq_zero.mp h3).resolve_left hspos.ne'
  have hzb := (mul_eq_zero.mp h4).resolve_left htpos.ne'
  have haE := D.target.mem_edge_of_coord_zero_nonneg hza (hnnT _ haT)
  have hbE := D.target.mem_edge_of_coord_zero_nonneg hzb (hnnT _ hbT)
  exact ⟨m + 1, (convex_segment _ _).segment_subset haE hbE⟩

/-- Non-endpoint points of an interior edge are interior to the target. -/
theorem Dissection.mem_interior_of_mem_intEdges (D : Dissection N) {e : Fin N × Fin 3}
    (he : e ∈ D.intEdges) {x : Plane} (hx : x ∈ D.eSet e)
    (hx1 : x ≠ (D.tile e.1).pts e.2) (hx2 : x ≠ (D.tile e.1).pts (e.2 + 1)) :
    x ∈ interior D.target.carrier := by
  rcases D.edge_interior_or_side e hx hx1 hx2 with h | ⟨j, hj⟩
  · exact h
  · unfold Dissection.intEdges at he
    exact absurd hj ((Finset.mem_filter.mp he).2 j)

/-- An edge through a point interior to the target is an interior edge. -/
theorem Dissection.mem_intEdges_of_interior (D : Dissection N) {e : Fin N × Fin 3} {x : Plane}
    (hx : x ∈ D.eSet e) (hxi : x ∈ interior D.target.carrier) : e ∈ D.intEdges := by
  unfold Dissection.intEdges
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, fun j hj => D.target.notMem_interior_of_mem_edge (hj hx) hxi⟩

/-- Two distinct sides of a triangle meet in at most one point. -/
theorem Tri.edge_inter_edge_subsingleton (T : Tri) {j j' : Fin 3} (h : j ≠ j') :
    (T.edge j ∩ T.edge j').Subsingleton := by
  have h2 : j + 2 ≠ j' + 2 := fun h' => h (add_right_cancel h')
  have key : ∀ y ∈ T.edge j ∩ T.edge j', ∃ m, y = T.pts m ∧ m ≠ j + 2 ∧ m ≠ j' + 2 := by
    rintro y ⟨hy, hy'⟩
    have hz := T.coord_eq_zero_of_mem_edge j hy
    have hz' := T.coord_eq_zero_of_mem_edge j' hy'
    obtain ⟨m, rfl⟩ := T.eq_vertex_of_two_coords_zero h2 hz hz'
    have e1 : T.basis.coord m (T.pts m) = 1 := T.basis.coord_apply_eq m
    refine ⟨m, rfl, ?_, ?_⟩
    · intro hm; rw [← hm, e1] at hz; exact one_ne_zero hz
    · intro hm; rw [← hm, e1] at hz'; exact one_ne_zero hz'
  intro y hy z hz
  obtain ⟨m, rfl, hm1, hm2⟩ := key y hy
  obtain ⟨m', rfl, hm1', hm2'⟩ := key z hz
  have hall : ∀ a b c d : Fin 3, a ≠ b → c ≠ a → c ≠ b → d ≠ a → d ≠ b → c = d := by decide
  rw [hall _ _ _ _ h2 hm1 hm2 hm1' hm2']

/-- A tile edge lies on at most one target side. -/
theorem Dissection.sideEdges_disjoint (D : Dissection N) {j j' : Fin 3} (h : j ≠ j') :
    Disjoint (D.sideEdges j) (D.sideEdges j') := by
  rw [Finset.disjoint_left]
  intro e he he'
  unfold Dissection.sideEdges at he he'
  have hj := (Finset.mem_filter.mp he).2
  have hj' := (Finset.mem_filter.mp he').2
  have ha : (D.tile e.1).pts e.2 ∈ D.eSet e := left_mem_segment ℝ _ _
  have hb : (D.tile e.1).pts (e.2 + 1) ∈ D.eSet e := right_mem_segment ℝ _ _
  have hsucc : ∀ i : Fin 3, i ≠ i + 1 := by decide
  have hne : (D.tile e.1).pts e.2 ≠ (D.tile e.1).pts (e.2 + 1) := fun hh =>
    hsucc e.2 ((D.tile e.1).indep.injective hh)
  exact hne (D.target.edge_inter_edge_subsingleton h ⟨hj ha, hj' ha⟩ ⟨hj hb, hj' hb⟩)

omit [Module ℝ E] in
/-- **The edge sum splits** into interior edges and the edges on each of the three sides. -/
theorem Dissection.sum_split (D : Dissection N) (g : Fin N × Fin 3 → E) :
    ∑ e, g e = ∑ e ∈ D.intEdges, g e + ∑ j : Fin 3, ∑ e ∈ D.sideEdges j, g e := by
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin 3))) D.sideEdges :=
    fun j _ j' _ hjj' => D.sideEdges_disjoint hjj'
  rw [← Finset.sum_biUnion hdisj]
  have hunion : D.intEdges ∪ (Finset.univ : Finset (Fin 3)).biUnion D.sideEdges
      = Finset.univ := by
    ext e
    simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and, iff_true,
      Dissection.intEdges, Dissection.sideEdges, Finset.mem_filter]
    by_cases h : ∀ j, ¬ D.eSet e ⊆ D.target.edge j
    · exact Or.inl h
    · push Not at h; exact Or.inr h
  have hdis2 : Disjoint D.intEdges ((Finset.univ : Finset (Fin 3)).biUnion D.sideEdges) := by
    rw [Finset.disjoint_left]
    intro e he he'
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Dissection.sideEdges,
      Finset.mem_filter] at he'
    simp only [Dissection.intEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he
    obtain ⟨j, hj⟩ := he'
    exact he j hj
  rw [← Finset.sum_union hdis2, hunion]

/-- **Same-direction exclusion (M3).**  Two distinct tile edges with the same left-hand direction
meet in at most one point.  (At the midpoint of two common points both edges carry `OnEdge` data;
the same tile gives a coordinate clash, two tiles give opposite directions by
`Dissection.leftUnit_neg`.) -/
theorem Dissection.sameDir_subsingleton (D : Dissection N) {e₁ e₂ : Fin N × Fin 3}
    (hne : e₁ ≠ e₂) (hdir : D.eDir e₁ = D.eDir e₂) :
    (D.eSet e₁ ∩ D.eSet e₂).Subsingleton := by
  intro p hp q hq
  by_contra hpq
  obtain ⟨hm1, hn1A, hn1B⟩ := mem_ne_ends_of_avg hpq hp.1 hq.1
  obtain ⟨hm2, hn2A, hn2B⟩ := mem_ne_ends_of_avg hpq hp.2 hq.2
  obtain ⟨hz₁, hp₁⟩ := (D.tile e₁.1).onEdge_param (k := e₁.2) hm1 hn1A hn1B
  obtain ⟨hz₂, hp₂⟩ := (D.tile e₂.1).onEdge_param (k := e₂.2) hm2 hn2A hn2B
  have hshift : ∀ k : Fin 3, k + 2 + 1 = k := by decide
  by_cases hsame : e₁.1 = e₂.1
  · have hk : e₁.2 ≠ e₂.2 := fun h => hne (Prod.ext hsame h)
    have hk2 : e₁.2 + 2 ≠ e₂.2 + 2 := fun h => hk (add_right_cancel h)
    rw [hsame] at hz₁
    exact absurd hz₁ (ne_of_gt (hp₂ _ hk2))
  · have hkey := D.leftUnit_neg hsame hz₁ hp₁ hz₂ hp₂
    simp only [hshift] at hkey
    exact Dir.neg_ne_self _ (hkey.symm.trans hdir.symm)

end Erdos634.Geometry

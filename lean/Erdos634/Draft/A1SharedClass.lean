-- Draft/A1SharedClass.lean — row0c Lemma 1 (b′), the local step at a shared point (node A1).
--
-- Formalization debt on a paper-level PROVED result (PROOF_row0c.md, P1 A1 (b′) steps 2–4);
-- NOT /goal progress.  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).  H59: no (e, f) evaluated.
--
-- Statement (`shared_cls`): let `L` be any additive subgroup of the plane containing every tile
-- edge vector.  If two distinct tiles share a point that is a vertex of no tile, their corners are
-- congruent mod `L`.
--
-- This is exactly what the U/W connectivity argument of `A1EdgeDirections` needs at the points it
-- does not discard, so the paper's maximal segments σ are NEVER constructed: the only global
-- object is the line through the shared point, and on it
--   * the two side chains are `Dissection.lineChain f c` and `lineChain (−f) (−c)` (WallChain);
--   * pairwise at-most-a-point intersection is `Dissection.sameside_edges_subsingleton` (EdgeChain);
--   * "each side covers what the other covers" is `Dissection.wall_cover` (WallChain), applied to
--     the segment from the component's left end to the shared point, plus a density/closure step;
--   * the chain order / T-junction bookkeeping is the 1D `A1ChainClass1D.class_eq`.
-- The paper's step 3 (a corner at a T-junction is a chain point of the other side) is not needed:
-- such corners are tile vertices, which the U/W argument removes (finite set).
--
-- Also `shared_interior`: a non-vertex point common to two distinct tiles is interior to the target.
import Erdos634.Draft.A1ChainClass1D
import Erdos634.Draft.A1EdgeDirections
import Erdos634.WallChain

open scoped Classical

namespace Erdos634.Geometry.A1Pos

open Erdos634.Geometry Set

variable {N : ℕ}

/-! ## Classes mod L -/

/-- The class of a tile: its vertex 0 modulo `L`. -/
noncomputable def tileCls (D : Dissection N) (L : AddSubgroup Plane) (k : Fin N) : Plane ⧸ L :=
  ((D.tile k).pts 0 : Plane ⧸ L)

theorem vertex_cls (D : Dissection N) (L : AddSubgroup Plane)
    (hL : ∀ k (m : Fin 3), (D.tile k).pts (m + 1) - (D.tile k).pts m ∈ L) (k : Fin N) (m : Fin 3) :
    ((D.tile k).pts m : Plane ⧸ L) = tileCls D L k := by
  unfold tileCls
  rw [QuotientAddGroup.eq]
  have h0 := hL k 0
  have h1 := hL k 1
  have h2 := hL k 2
  simp only [show (0 : Fin 3) + 1 = 1 from rfl, show (1 : Fin 3) + 1 = 2 from rfl,
    show (2 : Fin 3) + 1 = 0 from rfl] at h0 h1 h2
  fin_cases m
  · simp
  · have := neg_mem h0
    simpa [neg_sub, sub_eq_neg_add] using this
  · have := h2
    simpa [sub_eq_neg_add] using this

/-! ## A non-vertex shared point is interior to the target -/

theorem cross_perp_pos {d : Plane} (hd : d ≠ 0) :
    0 < cross d (EuclideanSpace.single 0 (-(d 1)) + EuclideanSpace.single 1 (d 0)) := by
  have hval : cross d (EuclideanSpace.single 0 (-(d 1)) + EuclideanSpace.single 1 (d 0))
      = d 0 * d 0 + d 1 * d 1 := by
    simp [cross]
  rw [hval]
  by_contra hle
  push Not at hle
  have h0 : d 0 = 0 := by nlinarith [mul_self_nonneg (d 0), mul_self_nonneg (d 1)]
  have h1 : d 1 = 0 := by nlinarith [mul_self_nonneg (d 0), mul_self_nonneg (d 1)]
  apply hd
  ext i
  fin_cases i
  · simpa using h0
  · simpa using h1

/-- Coordinate data at a non-vertex point shared by two distinct tiles. -/
theorem shared_coords (D : Dissection N) {i j : Fin N} (hij : i ≠ j) {x : Plane}
    (hxi : x ∈ (D.tile i).carrier) (hxj : x ∈ (D.tile j).carrier) (hxv : x ∉ D.vertexSet) :
    ∃ m m', (D.tile i).basis.coord m x = 0 ∧ (∀ l, l ≠ m → 0 < (D.tile i).basis.coord l x) ∧
      (D.tile j).basis.coord m' x = 0 ∧ (∀ l, l ≠ m' → 0 < (D.tile j).basis.coord l x) := by
  have hnv := D.notMem_vertexSet hxv
  rcases A1Dir.pt_cases _ hxi (hnv i) with hp | ⟨m, hm, ho⟩
  · exact (A1Dir.interior_meets D hij (A1Dir.mem_interior_of_pos _ hp) hxj).elim
  rcases A1Dir.pt_cases _ hxj (hnv j) with hp' | ⟨m', hm', ho'⟩
  · exact (A1Dir.interior_meets D hij.symm (A1Dir.mem_interior_of_pos _ hp') hxi).elim
  exact ⟨m, m', hm, ho, hm', ho'⟩

theorem shared_interior (D : Dissection N) {i j : Fin N} (hij : i ≠ j) {x : Plane}
    (hxi : x ∈ (D.tile i).carrier) (hxj : x ∈ (D.tile j).carrier) (hxv : x ∉ D.vertexSet) :
    x ∈ interior D.target.carrier := by
  by_contra hx
  have hnv := D.notMem_vertexSet hxv
  obtain ⟨m, m', hm, ho, hm', ho'⟩ := shared_coords D hij hxi hxj hxv
  have hxe : x ∈ D.eSet (i, m + 1) := (D.tile i).mem_edge_of_coord_zero hm ho
  rcases D.edge_interior_or_side (i, m + 1) hxe (hnv i _) (hnv i _) with h | ⟨j', hj'⟩
  · exact hx h
  set g := D.target.basis.coord (j' + 2) with hgdef
  have hg0 : g x = 0 := D.target.coord_eq_zero_of_mem_edge j' (hj' hxe)
  set w := (D.tile i).leftDir (m + 1) with hw
  have hw0 : w ≠ 0 := (D.tile i).leftDir_ne_zero _
  set v : Plane := EuclideanSpace.single 0 (-(w 1)) + EuclideanSpace.single 1 (w 0) with hv
  have hv1 : 0 < cross w v := cross_perp_pos hw0
  obtain ⟨c, hc, hcw⟩ := D.leftDir_antiparallel hij hm ho hm' ho'
  have hv2 : 0 < cross ((D.tile j).leftDir (m' + 1)) (-v) := by
    rw [hcw, ← hw]
    have : cross (c • w) (-v) = -c * cross w v := by
      simp only [cross, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
      ring
    rw [this]
    exact mul_pos (neg_pos.mpr hc) hv1
  obtain ⟨ε₁, hε₁, h₁⟩ := (D.tile i).mem_interior_of_cross_pos hm ho hv1
  obtain ⟨ε₂, hε₂, h₂⟩ := (D.tile j).mem_interior_of_cross_pos hm' ho' hv2
  set ε := min ε₁ ε₂ / 2 with hε
  have hεpos : 0 < ε := by positivity
  have hε1 : ε < ε₁ := by have := min_le_left ε₁ ε₂; linarith
  have hε2 : ε < ε₂ := by have := min_le_right ε₁ ε₂; linarith
  have hy1 := interior_mono (tile_subset_target D i) (h₁ ε hεpos hε1)
  have hy2 := interior_mono (tile_subset_target D j) (h₂ ε hεpos hε2)
  have hp1 := D.target.interior_coord_pos hy1 (j' + 2)
  have hp2 := D.target.interior_coord_pos hy2 (j' + 2)
  have hg : ∀ u : Plane, g (x + u) = g.linear u + g x := fun u => by
    rw [add_comm x u, ← vadd_eq_add, AffineMap.map_vadd, vadd_eq_add]
  rw [← hgdef, hg] at hp1 hp2
  have hsum : g.linear (ε • v) + g.linear (ε • -v) = 0 := by
    rw [smul_neg, map_neg, add_neg_cancel]
  linarith

/-! ## The line through the shared point -/

section Line

variable (x w : Plane)

/-- The line `t ↦ x + t • w`. -/
noncomputable def ell : ℝ →ᵃ[ℝ] Plane := AffineMap.lineMap x (x + w)

theorem ell_apply (t : ℝ) : ell x w t = x + t • w := by
  simp [ell, AffineMap.lineMap_apply, add_comm]

variable {x w}

theorem ell_injective (hw : w ≠ 0) : Function.Injective (ell x w) := by
  intro s t h
  rw [ell_apply, ell_apply] at h
  have h2 : (s - t) • w = 0 := by
    rw [sub_smul]
    exact sub_eq_zero.mpr (add_left_cancel h)
  rcases smul_eq_zero.mp h2 with h3 | h3
  · linarith [sub_eq_zero.mp h3]
  · exact absurd h3 hw

theorem f_ell (t : ℝ) : crossL w (ell x w t) = crossL w x := by
  rw [ell_apply, map_add, map_smul, crossL_apply w w, cross_self, smul_zero, add_zero]

theorem exists_param (hw : w ≠ 0) {y : Plane} (hy : crossL w y = crossL w x) :
    ∃ t, ell x w t = y := by
  have h0 : cross w (y - x) = 0 := by
    rw [cross_sub_right]
    simpa [crossL_apply] using sub_eq_zero.mpr hy
  obtain ⟨τ, hτ⟩ := parallel_of_cross_eq_zero hw h0
  exact ⟨τ, by rw [ell_apply, ← hτ]; abel⟩

variable (x w)

/-- The parameter of a point of the line (junk `0` off the line). -/
noncomputable def par (y : Plane) : ℝ :=
  if h : ∃ t, ell x w t = y then h.choose else 0

variable {x w}

theorem ell_par (hw : w ≠ 0) {y : Plane} (hy : crossL w y = crossL w x) :
    ell x w (par x w y) = y := by
  have h := exists_param hw hy
  unfold par
  rw [dif_pos h]
  exact h.choose_spec

variable (x w)

/-- Sorted parameters of a tile edge. -/
noncomputable def aP (D : Dissection N) (e : Fin N × Fin 3) : ℝ :=
  min (par x w ((D.tile e.1).pts e.2)) (par x w ((D.tile e.1).pts (e.2 + 1)))

noncomputable def bP (D : Dissection N) (e : Fin N × Fin 3) : ℝ :=
  max (par x w ((D.tile e.1).pts e.2)) (par x w ((D.tile e.1).pts (e.2 + 1)))

variable {x w}

/-- An edge whose endpoints lie on the line is the image of its parameter interval. -/
theorem edge_param (hw : w ≠ 0) (D : Dissection N) {e : Fin N × Fin 3}
    (h1 : crossL w ((D.tile e.1).pts e.2) = crossL w x)
    (h2 : crossL w ((D.tile e.1).pts (e.2 + 1)) = crossL w x) (t : ℝ) :
    ell x w t ∈ (D.tile e.1).edge e.2 ↔ t ∈ Icc (aP x w D e) (bP x w D e) := by
  have hseg : (D.tile e.1).edge e.2 = ell x w '' segment ℝ (par x w ((D.tile e.1).pts e.2))
      (par x w ((D.tile e.1).pts (e.2 + 1))) := by
    rw [image_segment, ell_par hw h1, ell_par hw h2]
    rfl
  rw [hseg, (ell_injective hw).mem_set_image, segment_eq_uIcc, aP, bP]
  rcases le_total (par x w ((D.tile e.1).pts e.2)) (par x w ((D.tile e.1).pts (e.2 + 1))) with h | h
  · rw [uIcc_of_le h, min_eq_left h, max_eq_right h]
  · rw [uIcc_of_ge h, min_eq_right h, max_eq_left h]

theorem aP_lt_bP (hw : w ≠ 0) (D : Dissection N) {e : Fin N × Fin 3}
    (h1 : crossL w ((D.tile e.1).pts e.2) = crossL w x)
    (h2 : crossL w ((D.tile e.1).pts (e.2 + 1)) = crossL w x) :
    aP x w D e < bP x w D e := by
  have hsucc : ∀ l : Fin 3, l ≠ l + 1 := by decide
  have hne : par x w ((D.tile e.1).pts e.2) ≠ par x w ((D.tile e.1).pts (e.2 + 1)) := by
    intro h
    have := congrArg (ell x w) h
    rw [ell_par hw h1, ell_par hw h2] at this
    exact hsucc e.2 ((D.tile e.1).indep.injective this)
  exact min_lt_max.mpr hne

theorem cls_aP (hw : w ≠ 0) (D : Dissection N) (L : AddSubgroup Plane)
    (hL : ∀ k (m : Fin 3), (D.tile k).pts (m + 1) - (D.tile k).pts m ∈ L) {e : Fin N × Fin 3}
    (h1 : crossL w ((D.tile e.1).pts e.2) = crossL w x)
    (h2 : crossL w ((D.tile e.1).pts (e.2 + 1)) = crossL w x) :
    ((ell x w (aP x w D e) : Plane) : Plane ⧸ L) = tileCls D L e.1 := by
  unfold aP
  rcases min_choice (par x w ((D.tile e.1).pts e.2)) (par x w ((D.tile e.1).pts (e.2 + 1)))
    with h | h <;> rw [h]
  · rw [ell_par hw h1, vertex_cls D L hL]
  · rw [ell_par hw h2, vertex_cls D L hL]

theorem cls_bP (hw : w ≠ 0) (D : Dissection N) (L : AddSubgroup Plane)
    (hL : ∀ k (m : Fin 3), (D.tile k).pts (m + 1) - (D.tile k).pts m ∈ L) {e : Fin N × Fin 3}
    (h1 : crossL w ((D.tile e.1).pts e.2) = crossL w x)
    (h2 : crossL w ((D.tile e.1).pts (e.2 + 1)) = crossL w x) :
    ((ell x w (bP x w D e) : Plane) : Plane ⧸ L) = tileCls D L e.1 := by
  unfold bP
  rcases max_choice (par x w ((D.tile e.1).pts e.2)) (par x w ((D.tile e.1).pts (e.2 + 1)))
    with h | h <;> rw [h]
  · rw [ell_par hw h1, vertex_cls D L hL]
  · rw [ell_par hw h2, vertex_cls D L hL]

/-- A line chain whose edges lie on the line is a chain in the sense of `A1ChainClass1D`. -/
theorem isChain_lineChain (hw : w ≠ 0) (D : Dissection N) (L : AddSubgroup Plane)
    (hL : ∀ k (m : Fin 3), (D.tile k).pts (m + 1) - (D.tile k).pts m ∈ L)
    (g : Plane →ₗ[ℝ] ℝ) (d : ℝ) (hg : g ≠ 0)
    (hon : ∀ e ∈ D.lineChain g d, crossL w ((D.tile e.1).pts e.2) = crossL w x ∧
      crossL w ((D.tile e.1).pts (e.2 + 1)) = crossL w x) :
    IsChain (D.lineChain g d) (aP x w D) (bP x w D)
      (fun t => ((ell x w t : Plane) : Plane ⧸ L)) where
  lt e he := aP_lt_bP hw D (hon e he).1 (hon e he).2
  disj e he e' he' hne := by
    have hle : ∀ {e}, e ∈ D.lineChain g d → ∀ y ∈ (D.tile e.1).carrier, g y ≤ d := fun he =>
      Tri.carrier_subset_halfplane _ g d (Dissection.mem_lineChain.mp he).2.2
    have hsub := D.sameside_edges_subsingleton g d hg hne (hle he) (hle he')
      (D.lineChain_edge_subset he) (D.lineChain_edge_subset he')
    intro s hs t ht
    have hs1 := (edge_param hw D (hon e he).1 (hon e he).2 s).mpr hs.1
    have hs2 := (edge_param hw D (hon e' he').1 (hon e' he').2 s).mpr hs.2
    have ht1 := (edge_param hw D (hon e he).1 (hon e he).2 t).mpr ht.1
    have ht2 := (edge_param hw D (hon e' he').1 (hon e' he').2 t).mpr ht.2
    exact ell_injective hw (hsub ⟨hs1, hs2⟩ ⟨ht1, ht2⟩)
  cls e he := by
    rw [cls_aP hw D L hL (hon e he).1 (hon e he).2, cls_bP hw D L hL (hon e he).1 (hon e he).2]

/-- **Transfer.**  If the chain of `(g, d)` covers `[p, 0]` then so does the chain of `(g', d')`,
the other side of the same line, provided the base point is interior to the target. -/
theorem transfer (hw : w ≠ 0) (D : Dissection N) (hx : x ∈ interior D.target.carrier)
    (g : Plane →ₗ[ℝ] ℝ) (d : ℝ)
    (hon : ∀ e ∈ D.lineChain g d, crossL w ((D.tile e.1).pts e.2) = crossL w x ∧
      crossL w ((D.tile e.1).pts (e.2 + 1)) = crossL w x)
    (g' : Plane →ₗ[ℝ] ℝ) (d' : ℝ) (hg' : g' ≠ 0)
    (hon' : ∀ e ∈ D.lineChain g' d', crossL w ((D.tile e.1).pts e.2) = crossL w x ∧
      crossL w ((D.tile e.1).pts (e.2 + 1)) = crossL w x)
    (hline : ∀ t, g' (ell x w t) = d') {p : ℝ} (hp : p < 0)
    (hcov : Icc p 0 ⊆ chainUnion (D.lineChain g d) (aP x w D) (bP x w D)) :
    Icc p 0 ⊆ chainUnion (D.lineChain g' d') (aP x w D) (bP x w D) := by
  have hmem : ∀ t ∈ Icc p 0, ∃ e ∈ D.lineChain g d, ell x w t ∈ (D.tile e.1).edge e.2 := by
    intro t ht
    obtain ⟨e, he, hte⟩ := mem_iUnion₂.mp (hcov ht)
    exact ⟨e, he, (edge_param hw D (hon e he).1 (hon e he).2 t).mpr hte⟩
  have hx0 : ell x w 0 = x := by rw [ell_apply, zero_smul, add_zero]
  have hne : ell x w p ≠ ell x w 0 := fun h => hp.ne (ell_injective hw h)
  have hseg : segment ℝ (ell x w p) (ell x w 0) = ell x w '' Icc p 0 := by
    rw [← image_segment, segment_eq_Icc hp.le]
  have hoseg : openSegment ℝ (ell x w p) (ell x w 0) = ell x w '' Ioo p 0 := by
    rw [← image_openSegment, openSegment_eq_Ioo hp]
  have hS : segment ℝ (ell x w p) (ell x w 0) ⊆ {y | g' y = d'} := by
    rw [hseg]
    rintro _ ⟨t, -, rfl⟩
    exact hline t
  have hpT : ell x w p ∈ D.target.carrier := by
    obtain ⟨e, -, he⟩ := hmem p ⟨le_rfl, hp.le⟩
    exact tile_subset_target D e.1 ((D.tile e.1).edge_subset_carrier e.2 he)
  have hint : openSegment ℝ (ell x w p) (ell x w 0) ⊆ interior D.target.carrier := by
    rw [hx0]
    exact D.target.convex.openSegment_closure_interior_subset_interior (subset_closure hpT) hx
  have hwall : ∀ y ∈ openSegment ℝ (ell x w p) (ell x w 0), ∀ i,
      y ∉ interior (D.tile i).carrier := by
    rw [hoseg]
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨e, -, he⟩ := hmem t (Ioo_subset_Icc_self ht)
    exact D.edge_point_not_interior he
  set Z : Set ℝ := ell x w ⁻¹' D.vertexSet with hZ
  have hZfin : Z.Finite := D.vertexSet_finite.preimage (ell_injective hw).injOn
  have hgood : Ioo p 0 ∩ Zᶜ ⊆ chainUnion (D.lineChain g' d') (aP x w D) (bP x w D) := by
    rintro t ⟨ht, htZ⟩
    have hy : ell x w t ∈ openSegment ℝ (ell x w p) (ell x w 0) := by
      rw [hoseg]; exact ⟨t, ht, rfl⟩
    obtain ⟨e, he, hte⟩ := D.wall_cover g' d' hg' hne hS hint hwall hy htZ
    exact mem_biUnion he ((edge_param hw D (hon' e he).1 (hon' e he).2 t).mp hte)
  have hdense : Dense Zᶜ := hZfin.countable.dense_compl ℝ
  calc Icc p 0 = closure (Ioo p 0) := (closure_Ioo hp.ne).symm
    _ ⊆ closure (closure (Ioo p 0 ∩ Zᶜ)) :=
        closure_mono (hdense.open_subset_closure_inter isOpen_Ioo)
    _ = closure (Ioo p 0 ∩ Zᶜ) := closure_closure
    _ ⊆ _ := closure_minimal hgood (isClosed_chainUnion _ _ _)

end Line

/-- A tile edge through the line, with third vertex off it, is in one of the two side chains. -/
theorem mem_side_chains (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (k : Fin N) (m : Fin 3)
    (h1 : f ((D.tile k).pts (m + 1)) = c) (h2 : f ((D.tile k).pts (m + 2)) = c)
    (h3 : f ((D.tile k).pts m) ≠ c) :
    (k, m + 1) ∈ D.lineChain f c ∨ (k, m + 1) ∈ D.lineChain (-f) (-c) := by
  have hidx : m + 1 + 1 = m + 2 := by fin_cases m <;> rfl
  have hall : ∀ l : Fin 3, l = m ∨ l = m + 1 ∨ l = m + 2 := by
    have : ∀ u v : Fin 3, v = u ∨ v = u + 1 ∨ v = u + 2 := by decide
    exact fun l => this m l
  rcases lt_or_gt_of_ne h3 with hlt | hgt
  · left
    refine Dissection.mem_lineChain.mpr ⟨h1, by simpa [hidx] using h2, fun l => ?_⟩
    rcases hall l with rfl | rfl | rfl
    · exact hlt.le
    · exact h1.le
    · exact h2.le
  · right
    refine Dissection.mem_lineChain.mpr ⟨by simp [h1], by simp [hidx, h2], fun l => ?_⟩
    simp only [LinearMap.neg_apply, neg_le_neg_iff]
    rcases hall l with rfl | rfl | rfl
    · exact hgt.le
    · exact h1.ge
    · exact h2.ge

/-- **Shared point ⇒ same class.**  Two distinct tiles through a common point that is a vertex of
no tile have their corners in one coset of `L`, for any `L` containing every tile edge vector. -/
theorem shared_cls (D : Dissection N) (L : AddSubgroup Plane)
    (hL : ∀ k (m : Fin 3), (D.tile k).pts (m + 1) - (D.tile k).pts m ∈ L)
    {i j : Fin N} (hij : i ≠ j) {x : Plane}
    (hxi : x ∈ (D.tile i).carrier) (hxj : x ∈ (D.tile j).carrier) (hxv : x ∉ D.vertexSet) :
    tileCls D L i = tileCls D L j := by
  obtain ⟨m, m', hm, ho, hm', ho'⟩ := shared_coords D hij hxi hxj hxv
  have hx := shared_interior D hij hxi hxj hxv
  set w := (D.tile i).leftDir (m + 1) with hwdef
  have hw : w ≠ 0 := (D.tile i).leftDir_ne_zero _
  set f := crossL w with hfdef
  have hf : f ≠ 0 := crossL_ne_zero hw
  have hfw : f w = 0 := by rw [hfdef, crossL_apply, cross_self]
  -- both tiles have their edge through `x` on the line `{f = f x}`
  obtain ⟨hi1, hi2, hi3⟩ := (D.tile i).edge_on_line f (f x) hf hm ho rfl hw hfw
    (by rw [← hwdef, cross_self])
  obtain ⟨c, -, hcw⟩ := D.leftDir_antiparallel hij hm ho hm' ho'
  obtain ⟨hj1, hj2, hj3⟩ := (D.tile j).edge_on_line f (f x) hf hm' ho' rfl hw hfw
    (by rw [hcw, ← hwdef, cross_smul_left, cross_self, mul_zero])
  set S := D.lineChain f (f x)
  set T := D.lineChain (-f) (-(f x))
  have honS : ∀ e ∈ S, f ((D.tile e.1).pts e.2) = f x ∧ f ((D.tile e.1).pts (e.2 + 1)) = f x :=
    fun e he => ⟨(Dissection.mem_lineChain.mp he).1, (Dissection.mem_lineChain.mp he).2.1⟩
  have honT : ∀ e ∈ T, f ((D.tile e.1).pts e.2) = f x ∧ f ((D.tile e.1).pts (e.2 + 1)) = f x := by
    intro e he
    obtain ⟨h1, h2, -⟩ := Dissection.mem_lineChain.mp he
    simp only [LinearMap.neg_apply, neg_inj] at h1 h2
    exact ⟨h1, h2⟩
  have hSc := isChain_lineChain hw D L hL f (f x) hf honS
  have hTc := isChain_lineChain hw D L hL (-f) (-(f x)) (neg_ne_zero.mpr hf) honT
  have hlineS : ∀ t, f (ell x w t) = f x := f_ell
  have hlineT : ∀ t, (-f) (ell x w t) = -(f x) := fun t => by
    rw [LinearMap.neg_apply, f_ell]
  have htr₁ := fun p (hp : p < 0) =>
    transfer hw D hx f (f x) honS (-f) (-(f x)) (neg_ne_zero.mpr hf) honT hlineT hp
  have htr₂ := fun p (hp : p < 0) =>
    transfer hw D hx (-f) (-(f x)) honT f (f x) hf honS hlineS hp
  have hidx : ∀ m : Fin 3, m + 1 + 1 = m + 2 := by decide
  have hx0 : ell x w 0 = x := by rw [ell_apply, zero_smul, add_zero]
  have hmemi : (0 : ℝ) ∈ Icc (aP x w D (i, m + 1)) (bP x w D (i, m + 1)) := by
    refine (edge_param hw D hi1 (by simpa [hidx] using hi2) 0).mp ?_
    rw [hx0]
    exact (D.tile i).mem_edge_of_coord_zero hm ho
  have hmemj : (0 : ℝ) ∈ Icc (aP x w D (j, m' + 1)) (bP x w D (j, m' + 1)) := by
    refine (edge_param hw D hj1 (by simpa [hidx] using hj2) 0).mp ?_
    rw [hx0]
    exact (D.tile j).mem_edge_of_coord_zero hm' ho'
  have hkey := class_eq hSc hTc htr₁ htr₂ (mem_side_chains D f (f x) i m hi1 hi2 hi3)
    (mem_side_chains D f (f x) j m' hj1 hj2 hj3) hmemi hmemj
  rw [cls_aP hw D L hL hi1 (by simpa [hidx] using hi2),
    cls_aP hw D L hL hj1 (by simpa [hidx] using hj2)] at hkey
  exact hkey

end Erdos634.Geometry.A1Pos

#print axioms Erdos634.Geometry.A1Pos.shared_interior
#print axioms Erdos634.Geometry.A1Pos.shared_cls

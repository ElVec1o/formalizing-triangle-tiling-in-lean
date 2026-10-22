-- Draft/FluxERow2C.lean — ROW 2, the CORNER CONDITIONS (A), (B) of Lemma D ((private working notes, not included)
-- row2/PROOF.md §5 "Lemma D", *Corners*) for the REAL side matrix `CongruentDissection.sideCount` of a
-- tile-similar tiling.  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
--
-- Statement (file): at the corner `A` of angle `α` (smallest) exactly one tile has a corner, an
-- `α`-corner; at `B` (angle `β`, `β ∉ ℕα`) exactly one tile, a `β`-corner; the edges at a tile's
-- `α`-vertex are its `b`- and `c`-edges and they lie along `AB` and `AC`, and at a `β`-vertex its
-- `a`- and `c`-edges along `BA`, `BC`.  So
--   (A) `(D_cb ≥ 1 ∧ D_bc ≥ 1) ∨ (D_cc ≥ 1 ∧ D_bb ≥ 1)`, (B) `(D_ca ≥ 1 ∧ D_ac ≥ 1) ∨ (D_cc ≥ 1 ∧ D_aa ≥ 1)`.
--
-- ROUTE (named; no cone/angle-additivity argument is needed): the tiles' local angles at a target
-- vertex sum to the corner angle (`Dissection.sum_localAngle_eq`, G2) and each is a model angle, `π`
-- or `0` (`Dissection.congruentDissection_localAngle_mem`), so one tile `i0` carries the corner and the
-- others have local angle `0` (`Row2.fill_min`, `Row2.fill_mid`).  Each target side through the corner
-- is covered by its side edges (`hasEdgeChains_edge`, G3), so some side edge contains the corner; its
-- tile contains the corner, hence has nonzero local angle (`MarchFlank.localAngle_ne_zero_of_mem`),
-- hence IS `i0`; the corner is a vertex `jv` of `i0` (`PinPlumbing.localAngle_cases`), and a vertex
-- on an edge is an endpoint (`Tri.vertex_mem_edge`), so the edge is one of the two edges of `i0` at
-- `jv`, of model type `σ(e.2 + 2) ≠ σ(jv)` (`Tri.Congruent.exists_perm`).  The two sides give the
-- two distinct edges (`Dissection.sideEdges_disjoint`).  `Row2.corner_edges` is this, for any corner.
--
-- * `Row2.cornerA`, `Row2.cornerB`: (A), (B) exactly in the form `Row2.lemmaD_tiling` takes them,
--   for a model with `angleAt 0 < angleAt 1 < angleAt 2` and a target with the same angles
--   (`cornerB` also needs `angleAt 1 ∉ ℕ·angleAt 0`, Lemma E's output).
--
-- Witness (Draft/FluxERow2CWitness.lean): the real `FluxRow2Witness.D2` (`N = 4`, model `(24,32,16)`)
-- after sorting its angles.
--
-- Formalization debt; not progress on the three /goal outcomes.
import Erdos634.Draft.FluxERow2E
import Erdos634.TileAt

open scoped Classical

namespace Erdos634.Geometry

open Real

variable {N : ℕ}

theorem Row2.fin3_ne_add_two : ∀ m k : Fin 3, m ≠ k + 2 → m = k ∨ m = k + 1 := by decide

/-- A vertex of a triangle lying on its edge `k` (`= [pts k, pts (k+1)]`) is one of its endpoints. -/
theorem Tri.vertex_mem_edge (T : Tri) {m k : Fin 3} (h : T.pts m ∈ T.edge k) :
    m = k ∨ m = k + 1 := by
  have h0 := T.coord_eq_zero_of_mem_edge k h
  have hb : T.pts m = (T.basis : Fin 3 → Plane) m := rfl
  rw [hb, AffineBasis.coord_apply] at h0
  refine Row2.fin3_ne_add_two m k fun hmk => ?_
  rw [if_pos hmk.symm] at h0
  exact one_ne_zero h0

/-- The length of tile edge `e` is the tile's side opposite vertex `e.2 + 2`. -/
theorem Dissection.eLen_eq_oppLen (D : Dissection N) (e : Fin N × Fin 3) :
    D.eLen e = (D.tile e.1).oppLen (e.2 + 2) := by
  have h : ∀ k : Fin 3, k + 2 + 1 = k ∧ k + 2 + 2 = k + 1 := by decide
  unfold Dissection.eLen Tri.oppLen
  rw [(h e.2).1, (h e.2).2]

/-- **Every point of target side `j` lies on one of its side edges** (G3). -/
theorem Dissection.exists_sideEdge_mem (D : Dissection N) (j : Fin 3) {y : Plane}
    (hy : y ∈ D.target.edge j) : ∃ e ∈ D.sideEdges j, y ∈ D.eSet e := by
  obtain ⟨part, hpart⟩ := hasEdgeChains_edge D j
  have hy' := (Set.ext_iff.mp hpart y).mpr hy
  obtain ⟨e, he, hye⟩ := Set.mem_iUnion₂.mp hy'
  refine ⟨e, ?_, hye⟩
  unfold Dissection.sideEdges
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, fun z hz => ?_⟩
  exact (Set.ext_iff.mp hpart z).mp (Set.mem_iUnion₂.mpr ⟨e, he, hz⟩)

/-- A side edge of type `k` on target side `i + 1` makes `D_ik ≥ 1`. -/
theorem Row2.sideCount_pos (D : CongruentDissection N) {i k : Fin 3} {e : Fin N × Fin 3}
    (he : e ∈ D.sideEdges (i + 1)) (hl : D.eLen e = D.model.oppLen k) : 0 < D.sideCount i k :=
  Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hl⟩⟩

/-- **The corner tile's two edges**, at any target vertex `t`: if tile `i0` has local angle
`model.angleAt m0` at `pts t` and every other tile has local angle `0` there, then side `t` and side
`t + 2` each carry an edge of `i0`, of the two model types other than `m0`, and different ones. -/
theorem Row2.corner_edges (D : CongruentDissection N) (t m0 : Fin 3)
    (hdist : ∀ i j : Fin 3, i ≠ j → D.model.angleAt i ≠ D.model.angleAt j)
    (i0 : Fin N) (hi0 : (D.tile i0).localAngle (D.target.pts t) = D.model.angleAt m0)
    (hother : ∀ i, i ≠ i0 → (D.tile i).localAngle (D.target.pts t) = 0) :
    ∃ k1 k2 : Fin 3, k1 ≠ m0 ∧ k2 ≠ m0 ∧ k1 ≠ k2 ∧
      (∃ e ∈ D.sideEdges t, D.eLen e = D.model.oppLen k1) ∧
      (∃ e ∈ D.sideEdges (t + 2), D.eLen e = D.model.oppLen k2) := by
  have hθ0 : 0 < D.model.angleAt m0 := D.model.angleAt_pos' m0
  have hθπ : D.model.angleAt m0 < π := by
    have hne : m0 ≠ m0 + 1 := by
      have : ∀ a : Fin 3, a ≠ a + 1 := by decide
      exact this m0
    have := D.model.angleAt_add_lt hne
    linarith [D.model.angleAt_pos' (m0 + 1)]
  -- the corner is a vertex `jv` of tile `i0`, with the model angle `m0` there
  obtain ⟨jv, hjv, hang⟩ : ∃ jv : Fin 3, D.target.pts t = (D.tile i0).pts jv ∧
      (D.tile i0).angleAt jv = D.model.angleAt m0 := by
    rcases Erdos634.PinPlumbing.localAngle_cases (D.tile i0) (D.target.pts t) with
      ⟨j, hj, hjl⟩ | h | h | h
    · exact ⟨j, hj, by rw [← hi0, hjl]; rfl⟩
    · rw [hi0] at h; linarith [Real.pi_pos]
    · rw [hi0] at h; linarith
    · rw [hi0] at h; linarith
  obtain ⟨σ, hσ⟩ := (D.tiles_congruent i0).exists_perm
  have hσjv : σ jv = m0 := by
    by_contra hne
    exact hdist _ _ hne (by rw [← (hσ jv).1, hang])
  -- a side through the corner carries an edge of `i0` at `jv`
  have side : ∀ j : Fin 3, D.target.pts t ∈ D.target.edge j → ∃ e ∈ D.sideEdges j,
      D.eLen e = D.model.oppLen (σ (e.2 + 2)) ∧ e.1 = i0 ∧ e.2 + 2 ≠ jv := by
    intro j hPj
    obtain ⟨e, he, hPe⟩ := D.toDissection.exists_sideEdge_mem j hPj
    have hcar : D.target.pts t ∈ (D.tile e.1).carrier :=
      (D.tile e.1).edge_subset_carrier e.2 hPe
    have he1 : e.1 = i0 := by
      by_contra hne
      exact Erdos634.MarchFlank.localAngle_ne_zero_of_mem _ hcar (hother e.1 hne)
    refine ⟨e, he, ?_, he1, ?_⟩
    · rw [D.toDissection.eLen_eq_oppLen e, he1, (hσ _).2]
    · have hmem : (D.tile i0).pts jv ∈ (D.tile i0).edge e.2 := by
        rw [← hjv, ← he1]; exact hPe
      intro h2
      rcases (D.tile i0).vertex_mem_edge hmem with h | h
      · have : ∀ a : Fin 3, a + 2 ≠ a := by decide
        exact this e.2 (h2.trans h)
      · have : ∀ a : Fin 3, a + 2 ≠ a + 1 := by decide
        exact this e.2 (h2.trans h)
  have hPt : D.target.pts t ∈ D.target.edge t := left_mem_segment ℝ _ _
  have hPt2 : D.target.pts t ∈ D.target.edge (t + 2) := by
    have h : ∀ a : Fin 3, a + 2 + 1 = a := by decide
    show D.target.pts t ∈ segment ℝ (D.target.pts (t + 2)) (D.target.pts (t + 2 + 1))
    rw [h t]; exact right_mem_segment ℝ _ _
  obtain ⟨e, he, hel, he1, he2⟩ := side t hPt
  obtain ⟨e', he', hel', he1', he2'⟩ := side (t + 2) hPt2
  have hee : e ≠ e' := by
    intro h
    have htt : t ≠ t + 2 := by
      have : ∀ a : Fin 3, a ≠ a + 2 := by decide
      exact this t
    exact Finset.disjoint_left.mp (D.toDissection.sideEdges_disjoint htt) he (by rw [h]; exact he')
  have h22 : e.2 ≠ e'.2 := fun h => hee (Prod.ext (he1.trans he1'.symm) h)
  refine ⟨σ (e.2 + 2), σ (e'.2 + 2), ?_, ?_, ?_, ⟨e, he, hel⟩, ⟨e', he', hel'⟩⟩
  · intro h; exact he2 (σ.injective (h.trans hσjv.symm))
  · intro h; exact he2' (σ.injective (h.trans hσjv.symm))
  · intro h; exact h22 (add_right_cancel (σ.injective h))

/-! ## Filling a corner -/

/-- In a sum of nonnegative terms, a term equal to the whole sum leaves the others zero. -/
theorem Row2.others_zero (f : Fin N → ℝ) (hnn : ∀ i, 0 ≤ f i) {i0 : Fin N}
    (h : f i0 = ∑ i, f i) : ∀ i, i ≠ i0 → f i = 0 := by
  intro i hi
  have h2 : f i0 + f i ≤ ∑ j, f j := by
    rw [← Finset.sum_pair hi.symm]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => hnn j)
  linarith [hnn i]

/-- **The smallest angle fills a corner alone.** -/
theorem Row2.fill_min (f : Fin N → ℝ) (φ : ℝ) (hnn : ∀ i, 0 ≤ f i) (hsum : ∑ i, f i = φ)
    (hφ : 0 < φ) (hge : ∀ i, f i ≠ 0 → φ ≤ f i) :
    ∃ i0, f i0 = φ ∧ ∀ i, i ≠ i0 → f i = 0 := by
  obtain ⟨i0, -, hi0⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) (f := f)
    (by rw [hsum]; exact hφ.ne')
  have hle : f i0 ≤ φ := by
    rw [← hsum]; exact Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i0)
  have heq : f i0 = φ := le_antisymm hle (hge i0 hi0)
  exact ⟨i0, heq, Row2.others_zero f hnn (heq.trans hsum.symm)⟩

/-- **The middle angle fills a corner alone** when it is no natural multiple of the smallest. -/
theorem Row2.fill_mid (f : Fin N → ℝ) {α β γ : ℝ}
    (hvals : ∀ i, f i ∈ ({α, β, γ, π, 0} : Finset ℝ))
    (hα : 0 < α) (hαβ : α < β) (hβγ : β < γ) (hγπ : γ < π) (hsum : ∑ i, f i = β)
    (hmult : ∀ k : ℕ, β ≠ k * α) : ∃ i0, f i0 = β ∧ ∀ i, i ≠ i0 → f i = 0 := by
  have hnn : ∀ i, 0 ≤ f i := by
    intro i
    have hv := hvals i
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with h | h | h | h | h <;> rw [h] <;> linarith [Real.pi_pos]
  by_cases hex : ∃ i0, f i0 = β
  · obtain ⟨i0, hi0⟩ := hex
    exact ⟨i0, hi0, Row2.others_zero f hnn (hi0.trans hsum.symm)⟩
  · exfalso
    push Not at hex
    have hle : ∀ i, f i ≤ β := fun i => by
      rw [← hsum]; exact Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)
    have hsplit : ∀ i, f i = if f i = α then α else 0 := by
      intro i
      have hv := hvals i
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      have hi := hle i
      rcases hv with h | h | h | h | h
      · rw [if_pos h, h]
      · exact absurd h (hex i)
      · rw [h] at hi; linarith
      · rw [h] at hi; linarith
      · rw [if_neg (by rw [h]; exact hα.ne), h]
    have hcount : ∑ i, f i = ((Finset.univ.filter (fun i => f i = α)).card : ℝ) * α := by
      rw [Finset.sum_congr rfl (fun i _ => hsplit i), ← Finset.sum_filter, Finset.sum_const,
        nsmul_eq_mul]
    exact hmult _ (hsum.symm.trans hcount)

/-! ## The corners of a tile-similar target -/

/-- The tiles' local angles at a target vertex sum to its corner angle (G2). -/
theorem Row2.corner_sum (D : CongruentDissection N) (t : Fin 3) :
    ∑ i, (D.tile i).localAngle (D.target.pts t) = D.target.angleAt t :=
  (D.toDissection.sum_localAngle_eq _).trans (D.target.localAngle_vertex t)

/-- Each local angle at a target vertex is a model angle, `π` or `0`. -/
theorem Row2.corner_vals (D : CongruentDissection N) (t : Fin 3) (i : Fin N) :
    (D.tile i).localAngle (D.target.pts t) ∈
      ({D.model.angleAt 0, D.model.angleAt 1, D.model.angleAt 2, π, 0} : Finset ℝ) :=
  Dissection.congruentDissection_localAngle_mem D _ _ _ rfl rfl rfl t i

/-- Sorted angles are distinct. -/
theorem Row2.dist_of_lt (T : Tri) (h01 : T.angleAt 0 < T.angleAt 1)
    (h12 : T.angleAt 1 < T.angleAt 2) : ∀ i j : Fin 3, i ≠ j → T.angleAt i ≠ T.angleAt j := by
  intro i j hij h
  rcases Row2.fin3_pairs i j hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> linarith

theorem Row2.angle2_lt_pi (T : Tri) : T.angleAt 2 < π := by
  have := T.angleAt_add_lt (show (2 : Fin 3) ≠ 0 by decide)
  linarith [T.angleAt_pos' 0]

theorem Row2.fin3_others0 : ∀ k1 k2 : Fin 3, k1 ≠ 0 → k2 ≠ 0 → k1 ≠ k2 →
    (k1 = 1 ∧ k2 = 2) ∨ (k1 = 2 ∧ k2 = 1) := by decide

theorem Row2.fin3_others1 : ∀ k1 k2 : Fin 3, k1 ≠ 1 → k2 ≠ 1 → k1 ≠ k2 →
    (k1 = 0 ∧ k2 = 2) ∨ (k1 = 2 ∧ k2 = 0) := by decide

/-- **Corner (A)** for the real side matrix: the corner `A = pts 0` of angle `α = angleAt 0`
(smallest) holds one tile, whose `b`- and `c`-edges lie on `AB` and `AC`. -/
theorem Row2.cornerA (D : CongruentDissection N)
    (hang : ∀ k, D.target.angleAt k = D.model.angleAt k)
    (h01 : D.model.angleAt 0 < D.model.angleAt 1) (h12 : D.model.angleAt 1 < D.model.angleAt 2) :
    (0 < D.sideCount 2 1 ∧ 0 < D.sideCount 1 2) ∨ (0 < D.sideCount 2 2 ∧ 0 < D.sideCount 1 1) := by
  have hdist := Row2.dist_of_lt D.model h01 h12
  have h2π := Row2.angle2_lt_pi D.model
  have hge : ∀ i, (D.tile i).localAngle (D.target.pts 0) ≠ 0 →
      D.model.angleAt 0 ≤ (D.tile i).localAngle (D.target.pts 0) := by
    intro i hi
    have hv := Row2.corner_vals D 0 i
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with h | h | h | h | h
    · rw [h]
    · rw [h]; linarith
    · rw [h]; linarith
    · rw [h]; linarith
    · exact absurd h hi
  obtain ⟨i0, hi0, hoth⟩ := Row2.fill_min (fun i => (D.tile i).localAngle (D.target.pts 0))
    (D.model.angleAt 0) (fun i => (D.tile i).localAngle_nonneg _)
    (by rw [← hang 0]; exact Row2.corner_sum D 0) (D.model.angleAt_pos' 0) hge
  obtain ⟨k1, k2, hk1, hk2, hk12, ⟨e, he, hel⟩, ⟨e', he', hel'⟩⟩ :=
    Row2.corner_edges D 0 0 hdist i0 hi0 hoth
  have c1 : 0 < D.sideCount 2 k1 := Row2.sideCount_pos D (i := 2) he hel
  have c2 : 0 < D.sideCount 1 k2 := Row2.sideCount_pos D (i := 1) he' hel'
  rcases Row2.fin3_others0 k1 k2 hk1 hk2 hk12 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨c1, c2⟩
  · exact Or.inr ⟨c1, c2⟩

/-- **Corner (B)** for the real side matrix: the corner `B = pts 1` of angle `β = angleAt 1`,
`β ∉ ℕα`, holds one tile, whose `a`- and `c`-edges lie on `BC` and `BA`. -/
theorem Row2.cornerB (D : CongruentDissection N)
    (hang : ∀ k, D.target.angleAt k = D.model.angleAt k)
    (h01 : D.model.angleAt 0 < D.model.angleAt 1) (h12 : D.model.angleAt 1 < D.model.angleAt 2)
    (hmult : ∀ k : ℕ, D.model.angleAt 1 ≠ k * D.model.angleAt 0) :
    (0 < D.sideCount 2 0 ∧ 0 < D.sideCount 0 2) ∨ (0 < D.sideCount 2 2 ∧ 0 < D.sideCount 0 0) := by
  have hdist := Row2.dist_of_lt D.model h01 h12
  obtain ⟨i0, hi0, hoth⟩ := Row2.fill_mid (fun i => (D.tile i).localAngle (D.target.pts 1))
    (Row2.corner_vals D 1) (D.model.angleAt_pos' 0) h01 h12 (Row2.angle2_lt_pi D.model)
    (by rw [← hang 1]; exact Row2.corner_sum D 1) hmult
  obtain ⟨k1, k2, hk1, hk2, hk12, ⟨e, he, hel⟩, ⟨e', he', hel'⟩⟩ :=
    Row2.corner_edges D 1 1 hdist i0 hi0 hoth
  have c1 : 0 < D.sideCount 0 k1 := Row2.sideCount_pos D (i := 0) he hel
  have c2 : 0 < D.sideCount 2 k2 := Row2.sideCount_pos D (i := 2) he' hel'
  rcases Row2.fin3_others1 k1 k2 hk1 hk2 hk12 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inr ⟨c2, c1⟩
  · exact Or.inl ⟨c2, c1⟩

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Tri.vertex_mem_edge
#print axioms Erdos634.Geometry.Dissection.exists_sideEdge_mem
#print axioms Erdos634.Geometry.Row2.corner_edges
#print axioms Erdos634.Geometry.Row2.fill_min
#print axioms Erdos634.Geometry.Row2.fill_mid
#print axioms Erdos634.Geometry.Row2.cornerA
#print axioms Erdos634.Geometry.Row2.cornerB

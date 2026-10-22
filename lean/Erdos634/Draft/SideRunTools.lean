/-
Draft/SideRunTools.lean -- general tools for the formalization of the side theorem of room GAP3 (no fact about a
particular target or lattice).

* `lin a b`: the linear functional `p ↦ a p₀ + b p₁`;
* `HasV D t A B C`: tile `t` has the three vertices `A`, `B`, `C`; its angles from the opposite sides
  (`HasV.angles`), distinctness of tiles from their vertices or from a side functional;
* `seg_wall`: a segment between two vertices of a tile meets no tile's interior;
* `edge_interior_push`: a point in the relative interior of an edge of a tile lying on one side of the edge's line;
* `abc_interior`: a convex combination of the three vertices with positive weights is an interior point;
* `first_edge_local` / `next_tile`: at an end `P` of a wall that is not straddled on one side, a tile of that side
  has an edge that starts at `P` and runs along the wall (the far end of the wall need not be clamped);
* `clamp_b`: an end of a wall where a same-side tile has an edge ending is not straddled on that side;
* `third_unique_F`: the third vertex from its two distances and its side, the side given by a functional;
* `exists_nat_between`, angle sums of five and six tiles.

Composite-N work; not prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.W2E1Tools

namespace Erdos634.Draft.SideRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.RunPartition Erdos634.Draft.W2E1 Set

/-! ## 1. The functional `a p₀ + b p₁` -/

/-- the linear functional `p ↦ a p₀ + b p₁` -/
noncomputable def lin (a b : ℝ) : Plane →ₗ[ℝ] ℝ := crossL (mkPt b (-a))

theorem lin_apply (a b : ℝ) (p : Plane) : lin a b p = a * p 0 + b * p 1 := by
  show cross (mkPt b (-a)) p = _
  simp only [cross, mkPt_zero, mkPt_one]; ring

theorem lin_mk (a b x y : ℝ) : lin a b (mkPt x y) = a * x + b * y := by
  rw [lin_apply, mkPt_zero, mkPt_one]

theorem lin_ne_zero {a b : ℝ} (h : a ≠ 0 ∨ b ≠ 0) : lin a b ≠ 0 := by
  apply crossL_ne_zero
  intro h0
  have h1 : (mkPt b (-a)) 0 = (0 : Plane) 0 := by rw [h0]
  have h2 : (mkPt b (-a)) 1 = (0 : Plane) 1 := by rw [h0]
  rw [mkPt_zero, PiLp.zero_apply] at h1
  rw [mkPt_one, PiLp.zero_apply] at h2
  rcases h with h | h
  · exact h (by linarith)
  · exact h h1

/-! ## 2. Tiles given by their vertices -/

/-- tile `t` has the three vertices `A`, `B`, `C` -/
def HasV {N : ℕ} (D : CongruentDissection N) (t : Fin N) (A B C : Plane) : Prop :=
  ∃ k m j : Fin 3, k ≠ m ∧ k ≠ j ∧ m ≠ j ∧ (D.tile t).pts k = A ∧ (D.tile t).pts m = B ∧
    (D.tile t).pts j = C

namespace HasV

variable {N : ℕ} {D : CongruentDissection N} {t : Fin N} {A B C : Plane}

theorem rot (h : HasV D t A B C) : HasV D t B C A := by
  obtain ⟨k, m, j, hkm, hkj, hmj, hk, hm, hj⟩ := h
  exact ⟨m, j, k, hmj, Ne.symm hkm, Ne.symm hkj, hm, hj, hk⟩

theorem swap (h : HasV D t A B C) : HasV D t B A C := by
  obtain ⟨k, m, j, hkm, hkj, hmj, hk, hm, hj⟩ := h
  exact ⟨m, k, j, Ne.symm hkm, hmj, hkj, hm, hk, hj⟩

theorem cases (h : HasV D t A B C) (i : Fin 3) :
    (D.tile t).pts i = A ∨ (D.tile t).pts i = B ∨ (D.tile t).pts i = C := by
  obtain ⟨k, m, j, hkm, hkj, hmj, hk, hm, hj⟩ := h
  rcases fin3_cover k m j hkm hkj hmj i with h | h | h
  · left; rw [h]; exact hk
  · right; left; rw [h]; exact hm
  · right; right; rw [h]; exact hj

theorem all (h : HasV D t A B C) {P : Plane → Prop} (hA : P A) (hB : P B) (hC : P C) :
    ∀ i, P ((D.tile t).pts i) := by
  intro i
  rcases h.cases i with h' | h' | h'
  · rw [h']; exact hA
  · rw [h']; exact hB
  · rw [h']; exact hC

theorem mem₁ (h : HasV D t A B C) : A ∈ D.target.carrier := by
  obtain ⟨k, m, j, -, -, -, hk, -, -⟩ := h
  rw [← hk]; exact pts_mem_target D.toDissection t k

theorem mem₂ (h : HasV D t A B C) : B ∈ D.target.carrier := h.swap.mem₁

theorem mem₃ (h : HasV D t A B C) : C ∈ D.target.carrier := h.rot.rot.mem₁

/-- the angles of the tile, read off the opposite sides -/
theorem angles {f α β γ : ℝ} (hf : 2 ≤ f) (hM : ModelData D f α β γ) (h : HasV D t A B C) :
    (dist B C = f → (D.tile t).localAngle A = α) ∧
    (dist B C = f ^ 2 - 1 → (D.tile t).localAngle A = β) ∧
    (dist B C = f ^ 2 → (D.tile t).localAngle A = γ) := by
  obtain ⟨k, m, j, hkm, hkj, hmj, hk, hm, hj⟩ := h
  have hA := angle_at_vertex D hf hM t hkm hkj hmj
  rw [hk, hm, hj] at hA
  exact hA

/-- a tile with a vertex that is none of `A`, `B`, `C` is another tile -/
theorem ne_of_vertex (h : HasV D t A B C) {t' : Fin N} {i : Fin 3} {X : Plane}
    (hX : (D.tile t').pts i = X) (hA : X ≠ A) (hB : X ≠ B) (hC : X ≠ C) : t' ≠ t := by
  rintro rfl
  rcases h.cases i with h' | h' | h'
  · exact hA (hX.symm.trans h')
  · exact hB (hX.symm.trans h')
  · exact hC (hX.symm.trans h')

end HasV

/-- tiles on the two sides of a level are different -/
theorem ne_of_F {N : ℕ} {D : CongruentDissection N} (F : Plane → ℝ) {c : ℝ} {t t' : Fin N}
    (hle : ∀ i, F ((D.tile t).pts i) ≤ c) {i : Fin 3} (hlt : c < F ((D.tile t').pts i)) : t ≠ t' := by
  rintro rfl
  exact absurd (hle i) (not_le.mpr hlt)

theorem ne_of_angle {N : ℕ} {D : CongruentDissection N} {p : Plane} {i j : Fin N}
    (h : (D.tile i).localAngle p ≠ (D.tile j).localAngle p) : i ≠ j := by
  rintro rfl
  exact h rfl

/-- **A segment between two vertices of a tile meets no tile's interior.** -/
theorem seg_wall {N : ℕ} (D : Dissection N) {t : Fin N} {k m : Fin 3} (hkm : k ≠ m) {y : Plane}
    (hy : y ∈ segment ℝ ((D.tile t).pts k) ((D.tile t).pts m)) :
    ∀ i, y ∉ interior (D.tile i).carrier := by
  obtain ⟨k₀, hk₀⟩ := (D.tile t).pair_eq_edge hkm
  intro i
  exact D.edge_point_not_interior (j := t) (k := k₀) (by rw [← hk₀]; exact hy) i

theorem pair_index : ∀ k m : Fin 3, k ≠ m → m = k + 1 ∨ k = m + 1 := by decide

/-! ## 3. A point in the relative interior of an edge -/

theorem edge_interior_push_aux (T : Tri) (k : Fin 3) (F : Plane →ₗ[ℝ] ℝ) (hF : F ≠ 0) (c : ℝ)
    (hk : F (T.pts k) = c) (hq : F (T.pts (k + 1)) = c) (hle : ∀ i, F (T.pts i) ≤ c) {x : Plane}
    (hx : x ∈ openSegment ℝ (T.pts k) (T.pts (k + 1))) :
    x ∈ T.carrier ∧ T.localAngle x = Real.pi ∧
    ∀ v : Plane, F v < 0 → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      x + ε • v ∈ interior T.carrier := by
  classical
  have hxE : x ∈ T.edge k := openSegment_subset_segment ℝ _ _ hx
  have hFx : F x = c := Erdos634.RunPartition.CSlot.segment_subset_level F c hk hq hxE
  have hcov : ∀ i k : Fin 3, i = k ∨ i = k + 1 ∨ i = k + 2 := by decide
  have h3 : F (T.pts (k + 2)) < c := by
    rcases lt_or_eq_of_le (hle (k + 2)) with h | h
    · exact h
    · exfalso
      refine two_vertices_on_line T F c hF (fun i => ?_)
      rcases hcov i k with h' | h' | h'
      · rw [h']; exact hk
      · rw [h']; exact hq
      · rw [h']; exact h
  have hne : T.pts k ≠ T.pts (k + 1) := fun h =>
    (fin3_succ_ne k).2.1 (T.indep.injective h).symm
  have hxv : ∀ i, x ≠ T.pts i := by
    intro i hxi
    rcases hcov i k with h' | h' | h'
    · rw [h'] at hxi
      rw [hxi] at hx
      exact hne (left_mem_openSegment_iff.mp hx)
    · rw [h'] at hxi
      rw [hxi] at hx
      exact hne (right_mem_openSegment_iff.mp hx)
    · rw [h'] at hxi
      rw [hxi] at hFx
      linarith
  obtain ⟨hk0, hkpos⟩ := T.onEdge_data hxE hxv
  refine ⟨T.edge_subset_carrier k hxE, ?_, ?_⟩
  · have hIn : ¬ ∀ j, 0 < T.basis.coord j x := fun hI => absurd hk0 (ne_of_gt (hI _))
    rw [Tri.localAngle, dif_neg (not_exists.mpr hxv), if_neg hIn, if_pos ⟨_, hk0, hkpos⟩]
  · intro w hw
    exact push_into T F c hk0 hkpos hk hq h3 hw

/-- **A point in the relative interior of an edge `[pts k, pts m]` of a tile lying in `{F ≤ c}`**, the edge on the
line `{F = c}`: the tile shows a straight angle there and contains every short push to its side. -/
theorem edge_interior_push (T : Tri) {k m : Fin 3} (hkm : k ≠ m) (F : Plane →ₗ[ℝ] ℝ) (hF : F ≠ 0)
    (c : ℝ) (hk : F (T.pts k) = c) (hm : F (T.pts m) = c) (hle : ∀ i, F (T.pts i) ≤ c) {x : Plane}
    (hx : x ∈ openSegment ℝ (T.pts k) (T.pts m)) :
    x ∈ T.carrier ∧ T.localAngle x = Real.pi ∧
    ∀ v : Plane, F v < 0 → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      x + ε • v ∈ interior T.carrier := by
  rcases pair_index k m hkm with h | h
  · subst h
    exact edge_interior_push_aux T k F hF c hk hm hle hx
  · subst h
    rw [openSegment_symm] at hx
    exact edge_interior_push_aux T m F hF c hm hk hle hx

/-! ## 4. Convex combinations with positive weights -/

/-- **A convex combination of the three vertices with positive weights is an interior point.** -/
theorem abc_interior (T : Tri) {k m j : Fin 3} (hkm : k ≠ m) (hkj : k ≠ j) (hmj : m ≠ j)
    {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) :
    a • T.pts k + b • T.pts m + c • T.pts j ∈ interior T.carrier := by
  rw [T.mem_interior_iff_coord_pos]
  intro i
  have hb' : ∀ l : Fin 3, (T.basis : Fin 3 → Plane) l = T.pts l := fun _ => rfl
  have hcoord : ∀ l : Fin 3, T.basis.coord i (T.pts l) = if i = l then 1 else 0 := by
    intro l
    rw [← hb' l]
    exact T.basis.coord_apply i l
  have h1 : (1 - a) ≠ 0 := by
    have : 0 < 1 - a := by linarith
    exact this.ne'
  have e : a • T.pts k + b • T.pts m + c • T.pts j
      = a • T.pts k + (1 - a) • ((b / (1 - a)) • T.pts m + (c / (1 - a)) • T.pts j) := by
    apply plane_ext <;>
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] <;> field_simp <;> ring
  have e2 : b / (1 - a) + c / (1 - a) = 1 := by
    field_simp
    linarith
  rw [e, Convex.combo_affine_apply (by ring : a + (1 - a) = 1), Convex.combo_affine_apply e2,
    hcoord k, hcoord m, hcoord j]
  have hbm : (1 - a) * (b / (1 - a)) = b := by field_simp
  have hcm : (1 - a) * (c / (1 - a)) = c := by field_simp
  rcases fin3_cover k m j hkm hkj hmj i with h | h | h
  · subst h
    rw [if_pos rfl, if_neg hkm, if_neg hkj]
    simp only [smul_eq_mul, mul_zero, mul_one, add_zero]
    exact ha
  · subst h
    rw [if_neg (Ne.symm hkm), if_pos rfl, if_neg hmj]
    simp only [smul_eq_mul, mul_zero, mul_one, add_zero, zero_add]
    rw [hbm]; exact hb
  · subst h
    rw [if_neg (Ne.symm hkj), if_neg (Ne.symm hmj), if_pos rfl]
    simp only [smul_eq_mul, mul_zero, mul_one, add_zero, zero_add]
    rw [hcm]; exact hc

/-! ## 5. The first edge at one clamped end -/

theorem finset_min_pos {ι : Type*} (s : Finset ι) (P : ι → ℝ → Prop)
    (hmono : ∀ e, ∀ δ δ' : ℝ, δ' ≤ δ → P e δ → P e δ')
    (h : ∀ e ∈ s, ∃ δ : ℝ, 0 < δ ∧ P e δ) : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ e ∈ s, P e δ := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, le_refl _, fun e he => by simp at he⟩
  | insert a s ha ih =>
    obtain ⟨δ₁, h1, h1', hP1⟩ := ih (fun e he => h e (Finset.mem_insert_of_mem he))
    obtain ⟨δ₂, h2, hP2⟩ := h a (Finset.mem_insert_self a s)
    refine ⟨min δ₁ δ₂, lt_min h1 h2, le_trans (min_le_left _ _) h1', fun e he => ?_⟩
    rcases Finset.mem_insert.mp he with rfl | he'
    · exact hmono _ δ₂ _ (min_le_right _ _) hP2
    · exact hmono e δ₁ _ (min_le_left _ _) (hP1 e he')

/-- **The first edge at a clamped end.**  `[P, Q]` is a wall on the line `{F = c}` with its open part inside the
target, and no chain edge of the side `{F ≤ c}` straddles `P`.  Then a chain edge of that side has an end at `P` and
its other end on the open ray from `P` through `Q`. -/
theorem first_edge_local {N : ℕ} (D : Dissection N) (F : Plane →ₗ[ℝ] ℝ) (hF : F ≠ 0) (c : ℝ)
    {P Q P' : Plane} (hPQ : P ≠ Q) (hfP : F P = c) (hfQ : F Q = c) (hfP' : F P' = c)
    (hP' : P ∈ openSegment ℝ P' Q)
    (hint : openSegment ℝ P Q ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ P Q, ∀ i, y ∉ interior (D.tile i).carrier)
    (hP : ∀ e ∈ D.lineChain F c, ¬ Straddles ((D.tile e.1).edge e.2) P' P Q) :
    ∃ e ∈ D.lineChain F c, ∃ t : ℝ, 0 < t ∧
      (((D.tile e.1).pts e.2 = P ∧ (D.tile e.1).pts (e.2 + 1) = AffineMap.lineMap P Q t) ∨
       ((D.tile e.1).pts (e.2 + 1) = P ∧ (D.tile e.1).pts e.2 = AffineMap.lineMap P Q t)) := by
  classical
  by_contra hno
  obtain ⟨t', ht', rfl⟩ := param_of_left F hF c hPQ hfP hfQ hfP' hP'
  have hclaim : ∀ e ∈ D.lineChain F c, ∃ δ : ℝ, 0 < δ ∧
      ∀ s : ℝ, 0 < s → s < δ → AffineMap.lineMap P Q s ∉ (D.tile e.1).edge e.2 := by
    intro e he
    obtain ⟨hp, hq, -⟩ := Dissection.mem_lineChain.mp he
    obtain ⟨t₁, ht₁⟩ := Erdos634.TPErdos.line_eq_lineMap F hF c hfP hfQ hPQ hp
    obtain ⟨t₂, ht₂⟩ := Erdos634.TPErdos.line_eq_lineMap F hF c hfP hfQ hPQ hq
    have hmem : ∀ s : ℝ, AffineMap.lineMap P Q s ∈ (D.tile e.1).edge e.2 ↔ s ∈ segment ℝ t₁ t₂ := by
      intro s
      show AffineMap.lineMap P Q s ∈ segment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) ↔ _
      rw [ht₁, ht₂]
      exact mem_segment_lineMap_iff hPQ t₁ t₂ s
    have hmm : min t₁ t₂ ≤ max t₁ t₂ := min_le_max
    by_cases hpos : 0 < min t₁ t₂
    · refine ⟨min t₁ t₂, hpos, fun s _ hs hmem' => ?_⟩
      have := (mem_segment_real ((hmem s).mp hmem')).1
      linarith
    · have hpos' : min t₁ t₂ ≤ 0 := not_lt.mp hpos
      by_cases hmax : max t₁ t₂ ≤ 0
      · refine ⟨1, one_pos, fun s hs0 _ hmem' => ?_⟩
        have := (mem_segment_real ((hmem s).mp hmem')).2
        linarith
      · have hmax' : 0 < max t₁ t₂ := not_le.mp hmax
        exfalso
        rcases lt_or_eq_of_le hpos' with hneg | hzero
        · -- the edge straddles `P`
          have hM1 : max (min t₁ t₂) t' < 0 := max_lt hneg ht'
          have hM2 : min t₁ t₂ ≤ max (min t₁ t₂) t' := le_max_left _ _
          have hM3 : t' ≤ max (min t₁ t₂) t' := le_max_right _ _
          have hm1 : 0 < min (max t₁ t₂) 1 := lt_min hmax' one_pos
          have hm2 : min (max t₁ t₂) 1 ≤ max t₁ t₂ := min_le_left _ _
          have hm3 : min (max t₁ t₂) 1 ≤ 1 := min_le_right _ _
          refine hP e he ⟨⟨AffineMap.lineMap P Q (max (min t₁ t₂) t' / 2), ?_, ?_⟩,
            ⟨AffineMap.lineMap P Q (min (max t₁ t₂) 1 / 2), ?_, ?_⟩⟩
          · exact (hmem _).mpr (mem_segment_real_of (by linarith) (by linarith))
          · have h := (mem_openSegment_lineMap_iff hPQ t' 0 (max (min t₁ t₂) t' / 2)).mpr
              (mem_openSegment_real_of (by rw [min_eq_left ht'.le]; linarith)
                (by rw [max_eq_right ht'.le]; linarith))
            rwa [lineMap_zero'] at h
          · exact (hmem _).mpr (mem_segment_real_of (by linarith) (by linarith))
          · have h := (mem_openSegment_lineMap_iff hPQ 0 1 (min (max t₁ t₂) 1 / 2)).mpr
              (mem_openSegment_real_of (by rw [min_eq_left zero_le_one]; linarith)
                (by rw [max_eq_right zero_le_one]; linarith))
            rwa [lineMap_zero', lineMap_one'] at h
        · -- the edge starts at `P`
          rcases le_total t₁ t₂ with h12 | h12
          · rw [min_eq_left h12] at hzero
            rw [max_eq_right h12] at hmax'
            exact hno ⟨e, he, t₂, hmax', Or.inl ⟨by rw [ht₁, hzero, lineMap_zero'], ht₂⟩⟩
          · rw [min_eq_right h12] at hzero
            rw [max_eq_left h12] at hmax'
            exact hno ⟨e, he, t₁, hmax', Or.inr ⟨by rw [ht₂, hzero, lineMap_zero'], ht₁⟩⟩
  obtain ⟨δ, hδ0, hδ1, hall⟩ := finset_min_pos (D.lineChain F c)
    (fun e δ => ∀ s : ℝ, 0 < s → s < δ → AffineMap.lineMap P Q s ∉ (D.tile e.1).edge e.2)
    (fun e δ δ' hle h s hs0 hs => h s hs0 (lt_of_lt_of_le hs hle)) hclaim
  have ht0 : (0:ℝ) < δ / 2 := by linarith
  have ht1 : δ / 2 ≤ 1 := by linarith
  have hPP₁ : P ≠ AffineMap.lineMap P Q (δ / 2) := by
    intro h
    have h' : AffineMap.lineMap P Q (0:ℝ) = AffineMap.lineMap P Q (δ / 2) := by
      rw [lineMap_zero']; exact h
    have := Erdos634.LineParam.lineMap_injective_of_ne hPQ h'
    linarith
  have hsub₁ : segment ℝ P (AffineMap.lineMap P Q (δ / 2)) ⊆ segment ℝ P Q := by
    refine (convex_segment _ _).segment_subset (left_mem_segment ℝ P Q) ?_
    have := (mem_segment_lineMap_iff hPQ (0:ℝ) (1:ℝ) (δ / 2)).mpr
      (mem_segment_real_of (by rw [min_eq_left zero_le_one]; exact ht0.le)
        (by rw [max_eq_right zero_le_one]; exact ht1))
    rwa [lineMap_zero', lineMap_one'] at this
  have hopen₁ : openSegment ℝ P (AffineMap.lineMap P Q (δ / 2)) ⊆ openSegment ℝ P Q := by
    intro y hy
    have hy' : y ∈ openSegment ℝ (AffineMap.lineMap P Q (0:ℝ)) (AffineMap.lineMap P Q (δ / 2)) := by
      rw [lineMap_zero']; exact hy
    obtain ⟨s, hs, rfl⟩ := exists_param_of_mem_openSegment P Q hy'
    obtain ⟨hs1, hs2⟩ := mem_openSegment_real ht0.ne hs
    rw [min_eq_left ht0.le] at hs1; rw [max_eq_right ht0.le] at hs2
    have := (mem_openSegment_lineMap_iff hPQ (0:ℝ) (1:ℝ) s).mpr
      (mem_openSegment_real_of (by rw [min_eq_left zero_le_one]; exact hs1)
        (by rw [max_eq_right zero_le_one]; linarith))
    rwa [lineMap_zero', lineMap_one'] at this
  have hS₁ : segment ℝ P (AffineMap.lineMap P Q (δ / 2)) ⊆ {y | F y = c} := fun y hy =>
    Erdos634.RunPartition.CSlot.segment_subset_level F c hfP hfQ (hsub₁ hy)
  have hpart := D.wall_partition F c hF hPP₁ hS₁ (hopen₁.trans hint)
    (fun y hy => hwall y (hopen₁ hy))
  have honly : ∀ e ∈ D.lineChain F c, ∀ y : Plane, y ∈ (D.tile e.1).edge e.2 →
      y ∈ segment ℝ P (AffineMap.lineMap P Q (δ / 2)) → y = P := by
    intro e he y hyE hyS
    have hy' : y ∈ segment ℝ (AffineMap.lineMap P Q (0:ℝ)) (AffineMap.lineMap P Q (δ / 2)) := by
      rw [lineMap_zero']; exact hyS
    obtain ⟨s, hs, rfl⟩ := exists_param_of_mem_segment P Q hy'
    obtain ⟨hs1, hs2⟩ := mem_segment_real hs
    rw [min_eq_left ht0.le] at hs1; rw [max_eq_right ht0.le] at hs2
    rcases lt_or_eq_of_le hs1 with h | h
    · exact absurd hyE (hall e he s h (by linarith))
    · rw [← h, lineMap_zero']
  have hzero : ∀ e ∈ D.lineChain F c,
      (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
        ((D.tile e.1).edge e.2 ∩ segment ℝ P (AffineMap.lineMap P Q (δ / 2))) = 0 := by
    intro e he
    apply Erdos634.ChordTraceReal.hausdorffMeasure_one_subsingleton_eq_zero
    intro y hy z hz
    rw [honly e he y hy.1 hy.2, honly e he z hz.1 hz.2]
  rw [Finset.sum_eq_zero hzero, MeasureTheory.hausdorffMeasure_segment, edist_dist] at hpart
  have h0 : dist P (AffineMap.lineMap P Q (δ / 2)) ≤ 0 := ENNReal.ofReal_eq_zero.mp hpart.symm
  exact hPP₁ (dist_le_zero.mp h0)

/-- **The tile next to a wall at a clamped end**: a tile of the side `{F ≤ c}` has a vertex at `P` and another one
at `P + t (Q − P)`, `t > 0`.  The chain edge is returned too. -/
theorem next_tile {N : ℕ} (D : Dissection N) (F : Plane →ₗ[ℝ] ℝ) (hF : F ≠ 0) (c : ℝ)
    {P Q P' : Plane} (hPQ : P ≠ Q) (hfP : F P = c) (hfQ : F Q = c) (hfP' : F P' = c)
    (hP' : P ∈ openSegment ℝ P' Q)
    (hint : openSegment ℝ P Q ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ P Q, ∀ i, y ∉ interior (D.tile i).carrier)
    (hP : ∀ e ∈ D.lineChain F c, ¬ Straddles ((D.tile e.1).edge e.2) P' P Q) :
    ∃ e ∈ D.lineChain F c, ∃ (k m : Fin 3) (t : ℝ), k ≠ m ∧ (D.tile e.1).pts k = P ∧ 0 < t ∧
      (D.tile e.1).pts m = AffineMap.lineMap P Q t ∧ (∀ j, F ((D.tile e.1).pts j) ≤ c) ∧
      (D.tile e.1).edge e.2 = segment ℝ P (AffineMap.lineMap P Q t) ∧
      dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
        = dist P (AffineMap.lineMap P Q t) := by
  obtain ⟨e, he, t, ht, hcase⟩ := first_edge_local D F hF c hPQ hfP hfQ hfP' hP' hint hwall hP
  obtain ⟨-, -, hle⟩ := Dissection.mem_lineChain.mp he
  have hne := fin3_succ_ne e.2
  rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨e, he, e.2, e.2 + 1, t, hne.2.1.symm, h1, ht, h2, hle, ?_, ?_⟩
    · show segment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = _
      rw [h1, h2]
    · rw [h1, h2]
  · refine ⟨e, he, e.2 + 1, e.2, t, hne.2.1, h1, ht, h2, hle, ?_, ?_⟩
    · show segment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = _
      rw [h1, h2]; exact segment_symm ℝ _ _
    · rw [h1, h2]; exact dist_comm _ _

/-! ## 6. Clamp (b) -/

/-- **Clamp (b)**: if a tile of the side `{F ≤ c}` has the edge `[P', P]` on the line, no chain edge of that side
straddles `P`. -/
theorem clamp_b {N : ℕ} (D : Dissection N) (F : Plane →ₗ[ℝ] ℝ) (hF : F ≠ 0) (c : ℝ)
    {P Q P' : Plane} (hPQ : P ≠ Q) (hfP : F P = c) (hfQ : F Q = c) (hfP' : F P' = c)
    (hP' : P ∈ openSegment ℝ P' Q) {t : Fin N} {k m : Fin 3} (hkm : k ≠ m)
    (hk : (D.tile t).pts k = P') (hm : (D.tile t).pts m = P)
    (hle : ∀ i, F ((D.tile t).pts i) ≤ c) :
    ∀ e ∈ D.lineChain F c, ¬ Straddles ((D.tile e.1).edge e.2) P' P Q := by
  obtain ⟨k₁, hk₁⟩ := (D.tile t).pair_eq_edge hkm
  rw [hk, hm] at hk₁
  intro e he
  by_cases hne : e = (t, k₁)
  · subst hne
    exact not_straddles_extension F hF c hPQ hfP hfQ hfP' hP' hk₁.symm.subset
  · refine not_straddles_of_sameside_edge D F hF c hPQ hfP hfQ hfP' hP'
      ((D.tile t).carrier_subset_halfplane F c hle) (fun y hy => ?_) hk₁.subset he hne
    rw [← hk₁] at hy
    exact Erdos634.RunPartition.CSlot.segment_subset_level F c hfP' hfP hy

/-! ## 7. The third vertex -/

/-- **The third vertex of a triangle from its two distances and its side**, the side given by a functional that is
a multiple of the cross product with the base. -/
theorem third_unique_F (F : Plane →ₗ[ℝ] ℝ) {P Q R R' : Plane} {c κ : ℝ} (hκ : κ ≠ 0)
    (hcr : ∀ y : Plane, cross (Q - P) y = κ * F y) (hP : F P = c)
    (h1 : dist R P = dist R' P) (h2 : dist R Q = dist R' Q) (hR : F R < c) (hR' : F R' < c) :
    R = R' := by
  refine third_vertex_unique h1 h2 ?_
  rw [hcr, hcr, map_sub, map_sub, hP]
  have h3 : 0 < (c - F R) * (c - F R') := mul_pos (by linarith) (by linarith)
  have h4 : 0 < κ ^ 2 := by positivity
  have e : κ * (F R - c) * (κ * (F R' - c)) = κ ^ 2 * ((c - F R) * (c - F R')) := by ring
  rw [e]
  exact mul_pos h4 h3

/-- the third vertex of a tile is strictly on its side of the line of the other two -/
theorem third_strict (T : Tri) {k m j : Fin 3} (hkm : k ≠ m) (hkj : k ≠ j) (hmj : m ≠ j)
    (F : Plane →ₗ[ℝ] ℝ) (hF : F ≠ 0) (c : ℝ) (hk : F (T.pts k) = c) (hm : F (T.pts m) = c)
    (hle : ∀ i, F (T.pts i) ≤ c) : F (T.pts j) < c := by
  rcases lt_or_eq_of_le (hle j) with h | h
  · exact h
  · exfalso
    refine two_vertices_on_line T F c hF (fun i => ?_)
    rcases fin3_cover k m j hkm hkj hmj i with h' | h' | h'
    · rw [h']; exact hk
    · rw [h']; exact hm
    · rw [h']; exact h

/-! ## 8. Small tools -/

theorem exists_nat_between {q : ℕ} (hq : 1 ≤ q) {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ q) :
    ∃ i : ℕ, i < q ∧ (i:ℝ) ≤ s ∧ s ≤ (i:ℝ) + 1 := by
  by_cases hs : s < q
  · exact ⟨⌊s⌋₊, (Nat.floor_lt h0).mpr hs, Nat.floor_le h0, (Nat.lt_floor_add_one s).le⟩
  · have hs' : s = q := le_antisymm h1 (not_lt.mp hs)
    have hc : ((q - 1 : ℕ) : ℝ) = (q:ℝ) - 1 := by
      rw [Nat.cast_sub hq, Nat.cast_one]
    refine ⟨q - 1, by omega, ?_, ?_⟩
    · rw [hc, hs']; linarith
    · rw [hc, hs']; linarith

theorem five_angles_le {N : ℕ} (D : Dissection N) (p : Plane) {i j k l m : Fin N} (hij : i ≠ j)
    (hik : i ≠ k) (hil : i ≠ l) (him : i ≠ m) (hjk : j ≠ k) (hjl : j ≠ l) (hjm : j ≠ m)
    (hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m) :
    (D.tile i).localAngle p + (D.tile j).localAngle p + (D.tile k).localAngle p
      + (D.tile l).localAngle p + (D.tile m).localAngle p ≤ D.target.localAngle p := by
  have := sum_angles_le D p {i, j, k, l, m}
  rw [Finset.sum_insert (by simp [hij, hik, hil, him]), Finset.sum_insert (by simp [hjk, hjl, hjm]),
    Finset.sum_insert (by simp [hkl, hkm]), Finset.sum_pair hlm] at this
  linarith

theorem six_angles_le {N : ℕ} (D : Dissection N) (p : Plane) {i j k l m o : Fin N} (hij : i ≠ j)
    (hik : i ≠ k) (hil : i ≠ l) (him : i ≠ m) (hio : i ≠ o) (hjk : j ≠ k) (hjl : j ≠ l)
    (hjm : j ≠ m) (hjo : j ≠ o) (hkl : k ≠ l) (hkm : k ≠ m) (hko : k ≠ o) (hlm : l ≠ m)
    (hlo : l ≠ o) (hmo : m ≠ o) :
    (D.tile i).localAngle p + (D.tile j).localAngle p + (D.tile k).localAngle p
      + (D.tile l).localAngle p + (D.tile m).localAngle p + (D.tile o).localAngle p
      ≤ D.target.localAngle p := by
  have := sum_angles_le D p {i, j, k, l, m, o}
  rw [Finset.sum_insert (by simp [hij, hik, hil, him, hio]),
    Finset.sum_insert (by simp [hjk, hjl, hjm, hjo]), Finset.sum_insert (by simp [hkl, hkm, hko]),
    Finset.sum_insert (by simp [hlm, hlo]), Finset.sum_pair hmo] at this
  linarith

end Erdos634.Draft.SideRun

#print axioms Erdos634.Draft.SideRun.edge_interior_push
#print axioms Erdos634.Draft.SideRun.abc_interior
#print axioms Erdos634.Draft.SideRun.first_edge_local
#print axioms Erdos634.Draft.SideRun.next_tile
#print axioms Erdos634.Draft.SideRun.clamp_b
#print axioms Erdos634.Draft.SideRun.third_unique_F

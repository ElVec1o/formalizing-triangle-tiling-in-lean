/-
Draft/W2E1Tools.lean -- general tools for the formalization of `prop:w2e1` (no fact about a particular target).

* angle sums: distinct tiles' local angles at a point add up to at most the target's local angle
  (`AngleSumDissection.Dissection.sum_localAngle_eq`);
* `straddle_data`: a chain edge that straddles `P` has `P` in its relative interior: its tile shows a straight
  angle at `P` and contains every short push from `P` to its side of the line (`push_into`);
* `first_edge`: in the situation of `RunPartition.run_partition` some chain edge inside the run starts at `P`;
  `wall_first`, `wall_whole`: its length against the partition sum (`rep_a`, `rep_b`, `rep_c`, `rep_2b`);
* `partner` (the partner of a `b`-edge clamped at both ends: the common core of the half-turn lemma and of the
  corner lemma), `apex_dichotomy`, `half_turn` (the half-turn lemma H of the proof, free of coordinates).

Composite-N work; not prime-case work.  No sorry, no native_decide.
-/
import Erdos634.E1BaseWord
import Erdos634.Draft.W2E1Words

namespace Erdos634.Draft.W2E1

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.RunPartition Set

/-! ## 1. Angle sums -/

theorem sum_angles_le {N : ℕ} (D : Dissection N) (p : Plane) (s : Finset (Fin N)) :
    ∑ i ∈ s, (D.tile i).localAngle p ≤ D.target.localAngle p := by
  rw [← D.sum_localAngle_eq p]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
    (fun i _ _ => (D.tile i).localAngle_nonneg p)

theorem one_angle_le {N : ℕ} (D : Dissection N) (p : Plane) (i : Fin N) :
    (D.tile i).localAngle p ≤ D.target.localAngle p := by
  have := sum_angles_le D p {i}
  rwa [Finset.sum_singleton] at this

theorem two_angles_le {N : ℕ} (D : Dissection N) (p : Plane) {i j : Fin N} (hij : i ≠ j) :
    (D.tile i).localAngle p + (D.tile j).localAngle p ≤ D.target.localAngle p := by
  have := sum_angles_le D p {i, j}
  rwa [Finset.sum_pair hij] at this

theorem three_angles_le {N : ℕ} (D : Dissection N) (p : Plane) {i j k : Fin N} (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) :
    (D.tile i).localAngle p + (D.tile j).localAngle p + (D.tile k).localAngle p
      ≤ D.target.localAngle p := by
  have := sum_angles_le D p {i, j, k}
  rw [Finset.sum_insert (by simp [hij, hik]), Finset.sum_pair hjk] at this
  linarith

theorem four_angles_le {N : ℕ} (D : Dissection N) (p : Plane) {i j k l : Fin N} (hij : i ≠ j)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    (D.tile i).localAngle p + (D.tile j).localAngle p + (D.tile k).localAngle p
      + (D.tile l).localAngle p ≤ D.target.localAngle p := by
  have := sum_angles_le D p {i, j, k, l}
  rw [Finset.sum_insert (by simp [hij, hik, hil]), Finset.sum_insert (by simp [hjk, hjl]),
    Finset.sum_pair hkl] at this
  linarith

theorem localAngle_le_two_pi (T : Tri) (p : Plane) : T.localAngle p ≤ 2 * Real.pi := by
  have hπ := Real.pi_pos
  rcases Erdos634.PinPlumbing.localAngle_cases T p with ⟨j, -, h⟩ | h | h | h
  · have h1 : cornerAngle (T.pts (j + 1)) (T.pts j) (T.pts (j + 2)) ≤ Real.pi :=
      EuclideanGeometry.angle_le_pi _ _ _
    rw [h]; linarith
  · rw [h]
  · rw [h]; linarith
  · rw [h]; linarith

/-- consequences of the angle bundle -/
theorem angle_facts {α β γ : ℝ} (hA : AngleData α β γ) :
    0 < α ∧ 0 < β ∧ Real.pi < 2 * γ ∧ α + β + γ = Real.pi ∧ γ < Real.pi := by
  have h1 := hA.hα; have h2 := hA.hβ; have h3 := hA.hγdef; have h4 := hA.hrel
  refine ⟨h1, h2, by linarith, by linarith, by linarith⟩

/-! ## 2. Sides and angles of a tile -/

theorem vertex_dist_cases {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ}
    (hM : ModelData D f α β γ) (i : Fin N) {k m : Fin 3} (hkm : k ≠ m) :
    dist ((D.tile i).pts k) ((D.tile i).pts m) = f ∨
    dist ((D.tile i).pts k) ((D.tile i).pts m) = f ^ 2 - 1 ∨
    dist ((D.tile i).pts k) ((D.tile i).pts m) = f ^ 2 := by
  have hcov : ∀ a b : Fin 3, a ≠ b → b = a + 1 ∨ a = b + 1 := by decide
  rcases hcov k m hkm with h | h
  · rw [h]; exact edge_length_cases D hM i k
  · rw [h, dist_comm]; exact edge_length_cases D hM i m

/-- **The local angle at a vertex, read off the opposite side.** -/
theorem angle_at_vertex {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (hM : ModelData D f α β γ) (i : Fin N) {k m j : Fin 3} (hkm : k ≠ m) (hkj : k ≠ j)
    (hmj : m ≠ j) :
    (dist ((D.tile i).pts m) ((D.tile i).pts j) = f →
      (D.tile i).localAngle ((D.tile i).pts k) = α) ∧
    (dist ((D.tile i).pts m) ((D.tile i).pts j) = f ^ 2 - 1 →
      (D.tile i).localAngle ((D.tile i).pts k) = β) ∧
    (dist ((D.tile i).pts m) ((D.tile i).pts j) = f ^ 2 →
      (D.tile i).localAngle ((D.tile i).pts k) = γ) := by
  have h := localAngle_of_oppSide D hf hM.hs0 hM.hs1 hM.hs2 hM.hα' hM.hβ' hM.hγ' i k
  rcases fin3_succ k m j hkm hkj hmj with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2] at h; exact h
  · rw [h1, h2, dist_comm ((D.tile i).pts j) ((D.tile i).pts m)] at h; exact h

/-! ## 3. A point in the relative interior of an edge -/

theorem fin3_sum (k : Fin 3) (g : Fin 3 → ℝ) : ∑ i, g i = g k + g (k + 1) + g (k + 2) := by
  fin_cases k <;> simp [Fin.sum_univ_three] <;> ring

/-- the barycentric coordinate opposite an edge on the line `F = c`, as a multiple of `c − F` -/
theorem coord_eq_of_line (T : Tri) (F : Plane →ₗ[ℝ] ℝ) (c : ℝ) {k : Fin 3}
    (h1 : F (T.pts k) = c) (h2 : F (T.pts (k + 1)) = c) (y : Plane) :
    (c - F (T.pts (k + 2))) * T.basis.coord (k + 2) y = c - F y := by
  have hsum := T.basis.sum_coord_apply_eq_one y
  have hcomb := T.basis.linear_combination_coord_eq_self y
  have hF := congrArg F hcomb
  rw [map_sum] at hF
  have hb : ∀ i : Fin 3, (T.basis : Fin 3 → Plane) i = T.pts i := fun _ => rfl
  simp only [map_smul, smul_eq_mul, hb] at hF
  rw [fin3_sum k] at hF hsum
  rw [h1, h2] at hF
  linear_combination (-1 : ℝ) * hF + c * hsum

/-- **A push from a relatively interior point of an edge to the tile's side stays in the tile.** -/
theorem push_into (T : Tri) (F : Plane →ₗ[ℝ] ℝ) (c : ℝ) {k : Fin 3} {x : Plane}
    (hk : T.basis.coord (k + 2) x = 0) (ho : ∀ j, j ≠ k + 2 → 0 < T.basis.coord j x)
    (h1 : F (T.pts k) = c) (h2 : F (T.pts (k + 1)) = c) (h3 : F (T.pts (k + 2)) < c)
    {v : Plane} (hv : F v < 0) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → x + ε • v ∈ interior T.carrier := by
  have hd : 0 < c - F (T.pts (k + 2)) := by linarith
  have hFx : F x = c := by
    have := coord_eq_of_line T F c h1 h2 x
    rw [hk, mul_zero] at this; linarith
  have hmpos : ∀ ε : ℝ, 0 < ε → 0 < T.basis.coord (k + 2) (x + ε • v) := by
    intro ε hε
    have h := coord_eq_of_line T F c h1 h2 (x + ε • v)
    have hFv : F (x + ε • v) = c + ε * F v := by
      rw [map_add, map_smul, smul_eq_mul, hFx]
    rw [hFv] at h
    have hpos : 0 < ε * (-(F v)) := mul_pos hε (neg_pos.mpr hv)
    by_contra hneg
    push Not at hneg
    nlinarith [mul_nonneg hd.le (neg_nonneg.mpr hneg)]
  have hvne : v ≠ 0 := by
    rintro rfl
    simp at hv
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hvne
  have hopen : IsOpen {y : Plane | ∀ j, j ≠ k + 2 → 0 < T.basis.coord j y} := by
    have heq : {y : Plane | ∀ j, j ≠ k + 2 → 0 < T.basis.coord j y}
        = ⋂ j : Fin 3, {y : Plane | j ≠ k + 2 → 0 < T.basis.coord j y} := by
      ext y; simp [Set.mem_iInter]
    rw [heq]
    refine isOpen_iInter_of_finite fun j => ?_
    by_cases hj : j = k + 2
    · have : {y : Plane | j ≠ k + 2 → 0 < T.basis.coord j y} = Set.univ := by ext y; simp [hj]
      rw [this]; exact isOpen_univ
    · have : {y : Plane | j ≠ k + 2 → 0 < T.basis.coord j y} = {y | 0 < T.basis.coord j y} := by
        ext y; simp [hj]
      rw [this]
      exact isOpen_lt continuous_const (AffineMap.continuous_of_finiteDimensional _)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen x ho
  refine ⟨r / ‖v‖, div_pos hr hvpos, fun ε hε hlt => ?_⟩
  have hin : x + ε • v ∈ Metric.ball x r := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hsub : x + ε • v - x = ε • v := by abel
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
    calc ε * ‖v‖ < (r / ‖v‖) * ‖v‖ := mul_lt_mul_of_pos_right hlt hvpos
      _ = r := div_mul_cancel₀ r (ne_of_gt hvpos)
  have hallpos : ∀ j, 0 < T.basis.coord j (x + ε • v) := by
    intro j
    by_cases hj : j = k + 2
    · rw [hj]; exact hmpos ε hε
    · exact hball hin j hj
  exact (T.mem_interior_iff_coord_pos _).mpr hallpos

/-- **A chain edge that straddles `P` has `P` in its relative interior**: its tile contains `P`, shows a straight
angle there, and contains every short push from `P` to its side of the line. -/
theorem straddle_data {N : ℕ} (D : Dissection N) (F : Plane →ₗ[ℝ] ℝ) (hF : F ≠ 0) (c : ℝ)
    {P Q P' : Plane} (hPQ : P ≠ Q) (hfP : F P = c) (hfQ : F Q = c) (hfP' : F P' = c)
    (hP' : P ∈ openSegment ℝ P' Q) {e : Fin N × Fin 3} (he : e ∈ D.lineChain F c)
    (hs : Straddles ((D.tile e.1).edge e.2) P' P Q) :
    P ∈ (D.tile e.1).carrier ∧ (D.tile e.1).localAngle P = Real.pi ∧
    ∀ v : Plane, F v < 0 → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      P + ε • v ∈ interior (D.tile e.1).carrier := by
  classical
  obtain ⟨⟨y, hyE, hyP⟩, ⟨z, hzE, hzQ⟩⟩ := hs
  obtain ⟨t', ht', rfl⟩ := param_of_left F hF c hPQ hfP hfQ hfP' hP'
  have hP0 : P = AffineMap.lineMap P Q (0:ℝ) := (lineMap_zero' P Q).symm
  have hQ1 : Q = AffineMap.lineMap P Q (1:ℝ) := (lineMap_one' P Q).symm
  have hy' : y ∈ openSegment ℝ (AffineMap.lineMap P Q t') (AffineMap.lineMap P Q (0:ℝ)) := by
    rw [← hP0]; exact hyP
  have hz' : z ∈ openSegment ℝ (AffineMap.lineMap P Q (0:ℝ)) (AffineMap.lineMap P Q (1:ℝ)) := by
    rw [← hP0, ← hQ1]; exact hzQ
  obtain ⟨u, hu, rfl⟩ := exists_param_of_mem_openSegment P Q hy'
  obtain ⟨v, hv, rfl⟩ := exists_param_of_mem_openSegment P Q hz'
  obtain ⟨hu1, hu2⟩ := mem_openSegment_real ht'.ne hu
  obtain ⟨hv1, hv2⟩ := mem_openSegment_real zero_ne_one hv
  rw [max_eq_right ht'.le] at hu2
  rw [min_eq_left zero_le_one] at hv1
  obtain ⟨hp, hq, hle⟩ := Dissection.mem_lineChain.mp he
  obtain ⟨t₁, ht₁⟩ := Erdos634.TPErdos.line_eq_lineMap F hF c hfP hfQ hPQ hp
  obtain ⟨t₂, ht₂⟩ := Erdos634.TPErdos.line_eq_lineMap F hF c hfP hfQ hPQ hq
  have hyE' : AffineMap.lineMap P Q u
      ∈ segment ℝ (AffineMap.lineMap P Q t₁) (AffineMap.lineMap P Q t₂) := by
    rw [← ht₁, ← ht₂]; exact hyE
  have hzE' : AffineMap.lineMap P Q v
      ∈ segment ℝ (AffineMap.lineMap P Q t₁) (AffineMap.lineMap P Q t₂) := by
    rw [← ht₁, ← ht₂]; exact hzE
  rw [mem_segment_lineMap_iff hPQ] at hyE' hzE'
  obtain ⟨hy1, -⟩ := mem_segment_real hyE'
  obtain ⟨-, hz2⟩ := mem_segment_real hzE'
  -- `P` is on the edge
  have hPE : P ∈ (D.tile e.1).edge e.2 := by
    have h0 : (0:ℝ) ∈ segment ℝ u v :=
      mem_segment_real_of (by rw [min_eq_left (by linarith)]; linarith)
        (by rw [max_eq_right (by linarith)]; linarith)
    have h1 := (mem_segment_lineMap_iff hPQ u v (0:ℝ)).mpr h0
    rw [lineMap_zero'] at h1
    exact (convex_segment _ _).segment_subset hyE hzE h1
  -- `P` is not an end of the edge
  have ht1ne : t₁ ≠ 0 := by
    intro h0
    rw [h0] at hy1 hz2
    rcases le_total t₂ 0 with h | h
    · rw [max_eq_left h] at hz2; linarith
    · rw [min_eq_left h] at hy1; linarith
  have ht2ne : t₂ ≠ 0 := by
    intro h0
    rw [h0] at hy1 hz2
    rcases le_total t₁ 0 with h | h
    · rw [max_eq_right h] at hz2; linarith
    · rw [min_eq_right h] at hy1; linarith
  have hPne1 : P ≠ (D.tile e.1).pts e.2 := by
    intro h
    apply ht1ne
    have h' : AffineMap.lineMap P Q t₁ = AffineMap.lineMap P Q (0:ℝ) := by
      rw [← ht₁, lineMap_zero']; exact h.symm
    exact Erdos634.LineParam.lineMap_injective_of_ne hPQ h'
  have hPne2 : P ≠ (D.tile e.1).pts (e.2 + 1) := by
    intro h
    apply ht2ne
    have h' : AffineMap.lineMap P Q t₂ = AffineMap.lineMap P Q (0:ℝ) := by
      rw [← ht₂, lineMap_zero']; exact h.symm
    exact Erdos634.LineParam.lineMap_injective_of_ne hPQ h'
  have hcov : ∀ i k : Fin 3, i = k ∨ i = k + 1 ∨ i = k + 2 := by decide
  have h3 : F ((D.tile e.1).pts (e.2 + 2)) < c := by
    rcases lt_or_eq_of_le (hle (e.2 + 2)) with h | h
    · exact h
    · exfalso
      refine two_vertices_on_line (D.tile e.1) F c hF (fun i => ?_)
      rcases hcov i e.2 with h' | h' | h'
      · rw [h']; exact hp
      · rw [h']; exact hq
      · rw [h']; exact h
  have hPne3 : P ≠ (D.tile e.1).pts (e.2 + 2) := by
    intro h
    rw [← h] at h3
    linarith
  have hxv : ∀ m, P ≠ (D.tile e.1).pts m := by
    intro m
    rcases hcov m e.2 with h' | h' | h'
    · rw [h']; exact hPne1
    · rw [h']; exact hPne2
    · rw [h']; exact hPne3
  obtain ⟨hk0, hkpos⟩ := (D.tile e.1).onEdge_data hPE hxv
  refine ⟨(D.tile e.1).edge_subset_carrier e.2 hPE, ?_, ?_⟩
  · have hIn : ¬ ∀ j, 0 < (D.tile e.1).basis.coord j P := fun hI => absurd hk0 (ne_of_gt (hI _))
    rw [Tri.localAngle, dif_neg (not_exists.mpr hxv), if_neg hIn, if_pos ⟨_, hk0, hkpos⟩]
  · intro w hw
    exact push_into (D.tile e.1) F c hk0 hkpos hp hq h3 hw

/-! ## 4. The first edge of a clamped run -/

theorem endpoint_of_mem {P Q p q : Plane} (hPQ : P ≠ Q) (hsub : segment ℝ p q ⊆ segment ℝ P Q)
    (hP : P ∈ segment ℝ p q) : P = p ∨ P = q := by
  have hp : p ∈ segment ℝ (AffineMap.lineMap P Q (0:ℝ)) (AffineMap.lineMap P Q (1:ℝ)) := by
    rw [lineMap_zero', lineMap_one']; exact hsub (left_mem_segment ℝ p q)
  have hq : q ∈ segment ℝ (AffineMap.lineMap P Q (0:ℝ)) (AffineMap.lineMap P Q (1:ℝ)) := by
    rw [lineMap_zero', lineMap_one']; exact hsub (right_mem_segment ℝ p q)
  obtain ⟨s, hs, hps⟩ := exists_param_of_mem_segment P Q hp
  obtain ⟨t, ht, hqt⟩ := exists_param_of_mem_segment P Q hq
  obtain ⟨hs0, -⟩ := mem_segment_real hs
  obtain ⟨ht0, -⟩ := mem_segment_real ht
  rw [min_eq_left zero_le_one] at hs0 ht0
  have hP' : AffineMap.lineMap P Q (0:ℝ)
      ∈ segment ℝ (AffineMap.lineMap P Q s) (AffineMap.lineMap P Q t) := by
    rw [lineMap_zero', ← hps, ← hqt]; exact hP
  rw [mem_segment_lineMap_iff hPQ] at hP'
  obtain ⟨h1, -⟩ := mem_segment_real hP'
  rcases le_total s t with hst | hst
  · rw [min_eq_left hst] at h1
    left
    have h0 : s = 0 := le_antisymm h1 hs0
    rw [hps, h0, lineMap_zero']
  · rw [min_eq_right hst] at h1
    right
    have h0 : t = 0 := le_antisymm h1 ht0
    rw [hqt, h0, lineMap_zero']

/-- **The first edge of a clamped run**: in the situation of `RunPartition.run_partition`, some chain edge
contained in the run `[P, Q]` contains `P`. -/
theorem first_edge {N : ℕ} (D : Dissection N) (F : Plane →ₗ[ℝ] ℝ) (hF : F ≠ 0) (c : ℝ)
    {P Q P' Q' : Plane} (hPQ : P ≠ Q) (hfP : F P = c) (hfQ : F Q = c) (hfP' : F P' = c)
    (hfQ' : F Q' = c) (hP' : P ∈ openSegment ℝ P' Q) (hQ' : Q ∈ openSegment ℝ P Q')
    (hint : openSegment ℝ P Q ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ P Q, ∀ i, y ∉ interior (D.tile i).carrier)
    (hP : ∀ e ∈ D.lineChain F c, ¬ Straddles ((D.tile e.1).edge e.2) P' P Q)
    (hQ : ∀ e ∈ D.lineChain F c, ¬ Straddles ((D.tile e.1).edge e.2) Q' Q P) :
    ∃ e ∈ D.lineChain F c, (D.tile e.1).edge e.2 ⊆ segment ℝ P Q ∧ P ∈ (D.tile e.1).edge e.2 := by
  classical
  by_contra hno
  push Not at hno
  have hKclosed : IsClosed (⋃ e ∈ (D.lineChain F c).filter
      (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ P Q), (D.tile e.1).edge e.2) :=
    isClosed_biUnion_finset (fun e _ => (D.tile e.1).isClosed_edge e.2)
  have hPK : P ∉ (⋃ e ∈ (D.lineChain F c).filter
      (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ P Q), (D.tile e.1).edge e.2) := by
    intro h
    obtain ⟨e, heS, hPe⟩ := Set.mem_iUnion₂.mp h
    obtain ⟨he, hsub⟩ := Finset.mem_filter.mp heS
    exact hno e he hsub hPe
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hKclosed.isOpen_compl P hPK
  have hd : 0 < dist P Q := dist_pos.mpr hPQ
  obtain ⟨t, ht0, ht1, htr⟩ : ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ t * dist P Q < r := by
    have h2d : 0 < 2 * dist P Q := mul_pos two_pos hd
    have hq : 0 < r / (2 * dist P Q) := div_pos hr h2d
    refine ⟨min 1 (r / (2 * dist P Q)), lt_min one_pos hq, min_le_left _ _, ?_⟩
    have h1 : min 1 (r / (2 * dist P Q)) ≤ r / (2 * dist P Q) := min_le_right _ _
    rw [le_div_iff₀ h2d] at h1
    have h2 : 0 < min 1 (r / (2 * dist P Q)) * dist P Q := mul_pos (lt_min one_pos hq) hd
    nlinarith
  have hPP₁ : P ≠ AffineMap.lineMap P Q t := by
    intro h
    have h' : AffineMap.lineMap P Q (0:ℝ) = AffineMap.lineMap P Q t := by
      rw [lineMap_zero']; exact h
    have := Erdos634.LineParam.lineMap_injective_of_ne hPQ h'
    linarith
  have hsub₁ : segment ℝ P (AffineMap.lineMap P Q t) ⊆ segment ℝ P Q := by
    refine (convex_segment _ _).segment_subset (left_mem_segment ℝ P Q) ?_
    have := (mem_segment_lineMap_iff hPQ (0:ℝ) (1:ℝ) t).mpr
      (mem_segment_real_of (by rw [min_eq_left zero_le_one]; exact ht0.le)
        (by rw [max_eq_right zero_le_one]; exact ht1))
    rwa [lineMap_zero', lineMap_one'] at this
  have hopen₁ : openSegment ℝ P (AffineMap.lineMap P Q t) ⊆ openSegment ℝ P Q := by
    intro y hy
    have hy' : y ∈ openSegment ℝ (AffineMap.lineMap P Q (0:ℝ)) (AffineMap.lineMap P Q t) := by
      rw [lineMap_zero']; exact hy
    obtain ⟨s, hs, rfl⟩ := exists_param_of_mem_openSegment P Q hy'
    obtain ⟨hs1, hs2⟩ := mem_openSegment_real ht0.ne hs
    rw [min_eq_left ht0.le] at hs1; rw [max_eq_right ht0.le] at hs2
    have := (mem_openSegment_lineMap_iff hPQ (0:ℝ) (1:ℝ) s).mpr
      (mem_openSegment_real_of (by rw [min_eq_left zero_le_one]; exact hs1)
        (by rw [max_eq_right zero_le_one]; linarith))
    rwa [lineMap_zero', lineMap_one'] at this
  have hball₁ : segment ℝ P (AffineMap.lineMap P Q t) ⊆ Metric.ball P r := by
    intro y hy
    have hy' : y ∈ segment ℝ (AffineMap.lineMap P Q (0:ℝ)) (AffineMap.lineMap P Q t) := by
      rw [lineMap_zero']; exact hy
    obtain ⟨s, hs, rfl⟩ := exists_param_of_mem_segment P Q hy'
    obtain ⟨hs1, hs2⟩ := mem_segment_real hs
    rw [min_eq_left ht0.le] at hs1; rw [max_eq_right ht0.le] at hs2
    rw [Metric.mem_ball, dist_lineMap_left, Real.norm_eq_abs, abs_of_nonneg hs1]
    calc s * dist P Q ≤ t * dist P Q := mul_le_mul_of_nonneg_right hs2 hd.le
      _ < r := htr
  have hS₁ : segment ℝ P (AffineMap.lineMap P Q t) ⊆ {y | F y = c} := fun y hy =>
    Erdos634.RunPartition.CSlot.segment_subset_level F c hfP hfQ (hsub₁ hy)
  have hpart := D.wall_partition F c hF hPP₁ hS₁ (hopen₁.trans hint)
    (fun y hy => hwall y (hopen₁ hy))
  have hzero : ∀ e ∈ D.lineChain F c,
      (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
        ((D.tile e.1).edge e.2 ∩ segment ℝ P (AffineMap.lineMap P Q t)) = 0 := by
    intro e he
    apply Erdos634.ChordTraceReal.hausdorffMeasure_one_subsingleton_eq_zero
    obtain ⟨hp, hq, -⟩ := Dissection.mem_lineChain.mp he
    rcases edge_clamped F hF c hPQ hfP hfQ hfP' hfQ' hP' hQ' hp hq (hP e he) (hQ e he) with
      hss | hsubE
    · exact hss.anti (Set.inter_subset_inter_right _ hsub₁)
    · have heS : e ∈ (D.lineChain F c).filter
          (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ P Q) := Finset.mem_filter.mpr ⟨he, hsubE⟩
      intro y hy z _
      exfalso
      exact hball (hball₁ hy.2) (Set.mem_iUnion₂.mpr ⟨e, heS, hy.1⟩)
  rw [Finset.sum_eq_zero hzero, MeasureTheory.hausdorffMeasure_segment, edist_dist] at hpart
  have h0 : dist P (AffineMap.lineMap P Q t) ≤ 0 := ENNReal.ofReal_eq_zero.mp hpart.symm
  exact hPP₁ (dist_le_zero.mp h0)

theorem sum_split_semigroup {ι : Type*} [DecidableEq ι] (s : Finset ι) (g : ι → ℝ) (a b c T : ℝ)
    (h : ∀ i ∈ s, g i = a ∨ g i = b ∨ g i = c) {e : ι} (he : e ∈ s) (hT : ∑ i ∈ s, g i = T) :
    ∃ x y z : ℕ, g e + ((x:ℝ) * a + y * b + z * c) = T := by
  obtain ⟨x, y, z, hxyz⟩ := sum_mem_semigroup (s.erase e) g a b c
    (fun i hi => h i (Finset.mem_of_mem_erase hi))
  exact ⟨x, y, z, by rw [hxyz, ← hT]; exact Finset.add_sum_erase s g he⟩

/-- **The first edge of a clamped run, with the partition sum**: a tile on the chain's side has a vertex at `P`
and another one on `[P, Q]`, and the length of that edge plus a combination of the three sides is `|PQ|`. -/
theorem wall_first {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hM : ModelData D f α β γ)
    (F : Plane →ₗ[ℝ] ℝ) (hF : F ≠ 0) (c : ℝ) {P Q P' Q' : Plane} (hPQ : P ≠ Q)
    (hfP : F P = c) (hfQ : F Q = c) (hfP' : F P' = c) (hfQ' : F Q' = c)
    (hP' : P ∈ openSegment ℝ P' Q) (hQ' : Q ∈ openSegment ℝ P Q')
    (hint : openSegment ℝ P Q ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ P Q, ∀ i, y ∉ interior (D.tile i).carrier)
    (hP : ∀ e ∈ D.lineChain F c, ¬ Straddles ((D.tile e.1).edge e.2) P' P Q)
    (hQ : ∀ e ∈ D.lineChain F c, ¬ Straddles ((D.tile e.1).edge e.2) Q' Q P) :
    ∃ (i : Fin N) (k m : Fin 3) (x y z : ℕ), k ≠ m ∧ (D.tile i).pts k = P ∧
      (D.tile i).pts m ∈ segment ℝ P Q ∧ (∀ j, F ((D.tile i).pts j) ≤ c) ∧
      dist P ((D.tile i).pts m) + ((x:ℝ) * f + y * (f ^ 2 - 1) + z * f ^ 2) = dist P Q := by
  classical
  have hS := Erdos634.RunPartition.CSlot.segment_subset_level F c hfP hfQ
  obtain ⟨e, he, hsub, hPe⟩ :=
    first_edge D.toDissection F hF c hPQ hfP hfQ hfP' hfQ' hP' hQ' hint hwall hP hQ
  have hrun := run_partition D.toDissection F hF c hPQ hfP' hfQ' hP' hQ' hS hint hwall hP hQ
  obtain ⟨hp, hq, hle⟩ := Dissection.mem_lineChain.mp he
  obtain ⟨x, y, z, hxyz⟩ := sum_split_semigroup _ _ f (f ^ 2 - 1) (f ^ 2) (dist P Q)
    (fun e' _ => edge_length_cases D hM e'.1 e'.2) (Finset.mem_filter.mpr ⟨he, hsub⟩) hrun
  have hends : P = (D.tile e.1).pts e.2 ∨ P = (D.tile e.1).pts (e.2 + 1) :=
    endpoint_of_mem hPQ hsub hPe
  have hne := fin3_succ_ne e.2
  rcases hends with h | h
  · refine ⟨e.1, e.2, e.2 + 1, x, y, z, hne.2.1.symm, h.symm, ?_, hle, ?_⟩
    · exact hsub (right_mem_segment ℝ _ _)
    · rw [← h] at hxyz; exact hxyz
  · refine ⟨e.1, e.2 + 1, e.2, x, y, z, hne.2.1, h.symm, ?_, hle, ?_⟩
    · exact hsub (left_mem_segment ℝ _ _)
    · rw [← h, dist_comm ((D.tile e.1).pts e.2) P] at hxyz; exact hxyz

theorem cast_rep {n x y z : ℕ} {T : ℤ}
    (h : (x:ℝ) * n + y * ((n:ℝ) ^ 2 - 1) + z * (n:ℝ) ^ 2 = (T:ℝ)) :
    (x:ℤ) * n + y * ((n:ℤ) ^ 2 - 1) + z * (n:ℤ) ^ 2 = T := by
  exact_mod_cast h

/-- **The length of the first edge against the partition sum.** -/
theorem first_len {n : ℕ} (hn3 : 3 ≤ n) {ℓ T : ℝ} {x y z : ℕ}
    (hℓ : ℓ = (n:ℝ) ∨ ℓ = (n:ℝ) ^ 2 - 1 ∨ ℓ = (n:ℝ) ^ 2)
    (h : ℓ + ((x:ℝ) * n + y * ((n:ℝ) ^ 2 - 1) + z * (n:ℝ) ^ 2) = T) :
    (T = n → ℓ = n) ∧ (T = (n:ℝ) ^ 2 - 1 → ℓ = (n:ℝ) ^ 2 - 1) ∧
    (T = (n:ℝ) ^ 2 → ℓ ≠ (n:ℝ) ^ 2 - 1) ∧ (T = 2 * ((n:ℝ) ^ 2 - 1) → ℓ = (n:ℝ) ^ 2 - 1) := by
  refine ⟨fun hT => ?_, fun hT => ?_, fun hT hb => ?_, fun hT => ?_⟩
  · rcases hℓ with h1 | h1 | h1
    · exact h1
    · exfalso
      have := (rep_a hn3 (cast_rep (x := x) (y := y + 1) (z := z) (T := (n:ℤ))
        (by push_cast; linarith))).2.1
      omega
    · exfalso
      have := (rep_a hn3 (cast_rep (x := x) (y := y) (z := z + 1) (T := (n:ℤ))
        (by push_cast; linarith))).2.2
      omega
  · rcases hℓ with h1 | h1 | h1
    · exfalso
      have := (rep_b hn3 (cast_rep (x := x + 1) (y := y) (z := z) (T := (n:ℤ) ^ 2 - 1)
        (by push_cast; linarith))).1
      omega
    · exact h1
    · exfalso
      have := (rep_b hn3 (cast_rep (x := x) (y := y) (z := z + 1) (T := (n:ℤ) ^ 2 - 1)
        (by push_cast; linarith))).2.2
      omega
  · have := rep_c hn3 (cast_rep (x := x) (y := y + 1) (z := z) (T := (n:ℤ) ^ 2)
      (by push_cast; linarith))
    omega
  · rcases hℓ with h1 | h1 | h1
    · exfalso
      have := (rep_2b hn3 (cast_rep (x := x + 1) (y := y) (z := z) (T := 2 * ((n:ℤ) ^ 2 - 1))
        (by push_cast; linarith))).1
      omega
    · exact h1
    · exfalso
      have := (rep_2b hn3 (cast_rep (x := x) (y := y) (z := z + 1) (T := 2 * ((n:ℤ) ^ 2 - 1))
        (by push_cast; linarith))).2.2
      omega

theorem eq_of_mem_segment_of_dist {P Q X Y : Plane} (hPQ : P ≠ Q) (hX : X ∈ segment ℝ P Q)
    (hY : Y ∈ segment ℝ P Q) (h : dist P X = dist P Y) : X = Y := by
  rw [segment_eq_image_lineMap] at hX hY
  obtain ⟨s, ⟨hs0, -⟩, rfl⟩ := hX
  obtain ⟨t, ⟨ht0, -⟩, rfl⟩ := hY
  rw [dist_left_lineMap, dist_left_lineMap, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hs0,
    abs_of_nonneg ht0] at h
  have hd : dist P Q ≠ 0 := (dist_pos.mpr hPQ).ne'
  have hst : s = t := mul_right_cancel₀ hd h
  rw [hst]

/-- **A clamped run of length `a` or `b` is one whole edge.** -/
theorem wall_whole {N : ℕ} (D : CongruentDissection N) {n : ℕ} (hn3 : 3 ≤ n) {α β γ : ℝ}
    (hM : ModelData D (n:ℝ) α β γ)
    (F : Plane →ₗ[ℝ] ℝ) (hF : F ≠ 0) (c : ℝ) {P Q P' Q' : Plane} (hPQ : P ≠ Q)
    (hfP : F P = c) (hfQ : F Q = c) (hfP' : F P' = c) (hfQ' : F Q' = c)
    (hP' : P ∈ openSegment ℝ P' Q) (hQ' : Q ∈ openSegment ℝ P Q')
    (hint : openSegment ℝ P Q ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ P Q, ∀ i, y ∉ interior (D.tile i).carrier)
    (hP : ∀ e ∈ D.lineChain F c, ¬ Straddles ((D.tile e.1).edge e.2) P' P Q)
    (hQ : ∀ e ∈ D.lineChain F c, ¬ Straddles ((D.tile e.1).edge e.2) Q' Q P)
    (hlen : dist P Q = n ∨ dist P Q = (n:ℝ) ^ 2 - 1) :
    ∃ (i : Fin N) (k m : Fin 3), k ≠ m ∧ (D.tile i).pts k = P ∧ (D.tile i).pts m = Q ∧
      ∀ j, F ((D.tile i).pts j) ≤ c := by
  obtain ⟨i, k, m, x, y, z, hkm, hk, hm, hle, hsum⟩ :=
    wall_first D hM F hF c hPQ hfP hfQ hfP' hfQ' hP' hQ' hint hwall hP hQ
  have hℓ := vertex_dist_cases D hM i hkm
  rw [hk] at hℓ
  obtain ⟨ha, hb, -, -⟩ := first_len hn3 hℓ hsum
  have hd : dist P ((D.tile i).pts m) = dist P Q := by
    rcases hlen with h | h
    · rw [h]; exact ha h
    · rw [h]; exact hb h
  exact ⟨i, k, m, hkm, hk, eq_of_mem_segment_of_dist hPQ hm (right_mem_segment ℝ P Q) hd, hle⟩

/-! ## 5. Extension points -/

theorem mem_openSegment_ext (P Q : Plane) {s : ℝ} (hs : 0 < s) :
    P ∈ openSegment ℝ (P + s • (P - Q)) Q := by
  have h1 : (1 + s) ≠ 0 := by positivity
  refine ⟨1 / (1 + s), s / (1 + s), by positivity, by positivity, by field_simp, ?_⟩
  apply plane_ext <;>
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] <;>
    field_simp <;> ring

theorem openSegment_ext_param {P Q y : Plane} {s : ℝ} (hs : 0 < s)
    (hy : y ∈ openSegment ℝ (P + s • (P - Q)) P) : ∃ r : ℝ, 0 < r ∧ y = P + r • (P - Q) := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hy
  refine ⟨a * s, by positivity, ?_⟩
  have hb' : b = 1 - a := by linarith
  subst hb'
  apply plane_ext <;>
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] <;> ring

theorem ext_level (F : Plane →ₗ[ℝ] ℝ) {c : ℝ} {P Q : Plane} (hP : F P = c) (hQ : F Q = c) (s : ℝ) :
    F (P + s • (P - Q)) = c := by
  rw [map_add, map_smul, map_sub, hP, hQ, sub_self, smul_zero, add_zero]

/-- the clamp of a run by the target's boundary -/
theorem clamp_out {N : ℕ} (D : Dissection N) (F : Plane →ₗ[ℝ] ℝ) (c : ℝ) {P Q : Plane}
    (hout : ∀ s : ℝ, 0 < s → P + s • (P - Q) ∉ D.target.carrier) :
    ∀ e ∈ D.lineChain F c,
      ¬ Straddles ((D.tile e.1).edge e.2) (P + (1:ℝ) • (P - Q)) P Q := by
  intro e _
  refine not_straddles_of_outside D (fun y hy => ?_) e.1 e.2
  obtain ⟨r, hr, rfl⟩ := openSegment_ext_param one_pos hy
  exact hout r hr

theorem ext_point_of_push {T : Tri} (F : Plane →ₗ[ℝ] ℝ) {c : ℝ} {P Q : Plane} (hfP : F P = c)
    (hfQ : F Q = c) (hPT : P ∈ T.carrier)
    (hpush : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → P + ε • (P - Q) ∈ interior T.carrier) :
    ∃ P' : Plane, F P' = c ∧ P ∈ openSegment ℝ P' Q ∧ openSegment ℝ P' P ⊆ interior T.carrier := by
  obtain ⟨ε₀, hε₀, hpush⟩ := hpush
  have hε : 0 < ε₀ / 2 := by positivity
  refine ⟨P + (ε₀ / 2) • (P - Q), ext_level F hfP hfQ _, mem_openSegment_ext P Q hε, ?_⟩
  exact T.convex.openSegment_interior_closure_subset_interior (hpush _ hε (by linarith))
    (subset_closure hPT)

theorem cross_sub_right (u v w : Plane) : cross u (v - w) = cross u v - cross u w := by
  simp only [cross, PiLp.sub_apply]; ring

theorem unique_aux {d0 d1 a0 a1 b0 b1 : ℝ} (E1 : a0 ^ 2 + a1 ^ 2 = b0 ^ 2 + b1 ^ 2)
    (E2 : (a0 - d0) ^ 2 + (a1 - d1) ^ 2 = (b0 - d0) ^ 2 + (b1 - d1) ^ 2)
    (hs : 0 < (d0 * a1 - d1 * a0) * (d0 * b1 - d1 * b0)) : a0 = b0 ∧ a1 = b1 := by
  have E3 : a0 * d0 + a1 * d1 = b0 * d0 + b1 * d1 := by linear_combination (E1 - E2) / 2
  have hc2 : (d0 * a1 - d1 * a0) ^ 2 = (d0 * b1 - d1 * b0) ^ 2 := by
    linear_combination (d0 ^ 2 + d1 ^ 2) * E1 - (a0 * d0 + a1 * d1 + b0 * d0 + b1 * d1) * E3
  have hc : d0 * a1 - d1 * a0 = d0 * b1 - d1 * b0 := by
    rcases eq_or_eq_neg_of_sq_eq_sq _ _ hc2 with h | h
    · exact h
    · exfalso
      rw [h] at hs
      nlinarith [sq_nonneg (d0 * b1 - d1 * b0)]
  have hdd : 0 < d0 ^ 2 + d1 ^ 2 := by
    by_contra h
    push Not at h
    have h0 : d0 = 0 := by
      have h' : d0 ^ 2 = 0 := by nlinarith [sq_nonneg d0, sq_nonneg d1]
      exact (pow_eq_zero_iff two_ne_zero).mp h'
    have h1 : d1 = 0 := by
      have h' : d1 ^ 2 = 0 := by nlinarith [sq_nonneg d0, sq_nonneg d1]
      exact (pow_eq_zero_iff two_ne_zero).mp h'
    rw [h0, h1] at hs
    simp at hs
  have e0 : (d0 ^ 2 + d1 ^ 2) * (a0 - b0) = 0 := by linear_combination d0 * E3 - d1 * hc
  have e1 : (d0 ^ 2 + d1 ^ 2) * (a1 - b1) = 0 := by linear_combination d1 * E3 + d0 * hc
  constructor
  · rcases mul_eq_zero.mp e0 with h | h
    · exact absurd h hdd.ne'
    · linarith
  · rcases mul_eq_zero.mp e1 with h | h
    · exact absurd h hdd.ne'
    · linarith

/-- **The third vertex of a triangle is determined by its two distances and its side of the base.** -/
theorem third_vertex_unique {P Q R R' : Plane} (h1 : dist R P = dist R' P) (h2 : dist R Q = dist R' Q)
    (hs : 0 < cross (Q - P) (R - P) * cross (Q - P) (R' - P)) : R = R' := by
  have E1 : dist R P ^ 2 = dist R' P ^ 2 := by rw [h1]
  have E2 : dist R Q ^ 2 = dist R' Q ^ 2 := by rw [h2]
  rw [dist_sq_pts, dist_sq_pts] at E1 E2
  simp only [cross, PiLp.sub_apply] at hs
  obtain ⟨e0, e1⟩ := unique_aux (d0 := Q 0 - P 0) (d1 := Q 1 - P 1) (a0 := R 0 - P 0) (a1 := R 1 - P 1)
    (b0 := R' 0 - P 0) (b1 := R' 1 - P 1) E1 (by linear_combination E2) hs
  exact plane_ext (by linarith) (by linarith)

/-- a segment through its midpoint -/
theorem segment_split_mid {P G E y : Plane} (hG : G = (1 / 2 : ℝ) • P + (1 / 2 : ℝ) • E)
    (hy : y ∈ segment ℝ P E) : y ∈ segment ℝ P G ∨ y ∈ segment ℝ G E := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hy
  have ha' : a = 1 - b := by linarith
  subst ha'
  by_cases h : b ≤ 1 / 2
  · left
    refine ⟨1 - 2 * b, 2 * b, by linarith, by linarith, by ring, ?_⟩
    rw [hG]
    apply plane_ext <;>
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] <;> ring
  · right
    push Not at h
    refine ⟨2 - 2 * b, 2 * b - 1, by linarith, by linarith, by ring, ?_⟩
    rw [hG]
    apply plane_ext <;>
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] <;> ring

/-! ## 6. The partner of a `b`-edge, the apex dichotomy and the half-turn lemma -/

/-- a functional of the line `V G` that is larger at the third vertex `O` of the tile -/
theorem exists_side_functional {T : Tri} {kv kg ko : Fin 3} (hvg : kv ≠ kg) (hvo : kv ≠ ko)
    (hgo : kg ≠ ko) :
    ∃ w : Plane, w ≠ 0 ∧ cross w (T.pts kg) = cross w (T.pts kv) ∧
      cross w (T.pts kv) < cross w (T.pts ko) ∧
      (w = T.pts kg - T.pts kv ∨ w = -(T.pts kg - T.pts kv)) := by
  have hne : T.pts kg ≠ T.pts kv := fun h => hvg (T.indep.injective h).symm
  have hu : T.pts kg - T.pts kv ≠ 0 := sub_ne_zero.mpr hne
  have h1 : cross (T.pts kg - T.pts kv) (T.pts kg) = cross (T.pts kg - T.pts kv) (T.pts kv) := by
    simp only [cross, PiLp.sub_apply]; ring
  have h2 : cross (T.pts kg - T.pts kv) (T.pts ko) ≠ cross (T.pts kg - T.pts kv) (T.pts kv) := by
    intro h
    refine two_vertices_on_line T (crossL (T.pts kg - T.pts kv))
      (cross (T.pts kg - T.pts kv) (T.pts kv)) (crossL_ne_zero hu) (fun i => ?_)
    rcases fin3_cover kv kg ko hvg hvo hgo i with h' | h' | h'
    · rw [h']; rfl
    · rw [h']; exact h1
    · rw [h']; exact h
  rcases lt_or_gt_of_ne h2 with h | h
  · refine ⟨-(T.pts kg - T.pts kv), neg_ne_zero.mpr hu, ?_, ?_, Or.inr rfl⟩
    · rw [cross_neg_left, cross_neg_left, h1]
    · rw [cross_neg_left, cross_neg_left]; linarith
  · exact ⟨T.pts kg - T.pts kv, hu, h1, h, Or.inl rfl⟩

/-- **The partner of a `b`-edge.**  Tile `t` has the `b`-edge `[Va, G]`; the open edge is interior to the target;
its line leaves the target beyond `Va`; beyond `G` it leaves the target or enters the interior of a tile; and no
tile other than `t` shows `γ` at `G`.  Then a tile `t' ≠ t` has the vertices `Va` and `G` and shows `γ` at `Va`. -/
theorem partner {N : ℕ} (D : CongruentDissection N) {n : ℕ} (hn3 : 3 ≤ n) {α β γ : ℝ}
    (hM : ModelData D (n:ℝ) α β γ)
    {t : Fin N} {ka kg kb : Fin 3} (hag : ka ≠ kg) (hab : ka ≠ kb) (hgb : kg ≠ kb)
    {Va G : Plane} (hVa : (D.tile t).pts ka = Va) (hG : (D.tile t).pts kg = G)
    (hlen : dist Va G = (n:ℝ) ^ 2 - 1)
    (hint : openSegment ℝ Va G ⊆ interior D.target.carrier)
    (hVa_out : ∀ s : ℝ, 0 < s → Va + s • (Va - G) ∉ D.target.carrier)
    (hG_clamp : (∀ s : ℝ, 0 < s → G + s • (G - Va) ∉ D.target.carrier) ∨
      (∃ j : Fin N, G ∈ (D.tile j).carrier ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        G + ε • (G - Va) ∈ interior (D.tile j).carrier))
    (hG_ang : ∀ i' : Fin N, i' ≠ t → (D.tile i').localAngle G = γ → False) :
    ∃ t' : Fin N, t' ≠ t ∧ ∃ k m j : Fin 3, k ≠ m ∧ k ≠ j ∧ m ≠ j ∧
      (D.tile t').pts k = Va ∧ (D.tile t').pts m = G ∧
      dist ((D.tile t').pts j) Va = n ∧ dist ((D.tile t').pts j) G = (n:ℝ) ^ 2 ∧
      (D.tile t').localAngle Va = γ ∧
      0 ≤ cross (G - Va) ((D.tile t').pts j - Va) * cross (G - Va) (Va - (D.tile t).pts kb) := by
  have hf : (2:ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
  have hb : (0:ℝ) < (n:ℝ) ^ 2 - 1 := by nlinarith
  have hVG : Va ≠ G := by
    intro h; rw [h, dist_self] at hlen; linarith
  obtain ⟨w, hw0, hwG, hwb, hw⟩ := exists_side_functional (T := D.tile t) hag hab hgb
  rw [hVa, hG] at hwG hw
  rw [hVa] at hwb
  have hF : crossL w ≠ 0 := crossL_ne_zero hw0
  have hfVa : crossL w Va = cross w Va := rfl
  have hfG : crossL w G = cross w Va := hwG
  -- the wall
  obtain ⟨k₀, hk₀⟩ := (D.tile t).pair_eq_edge hag
  rw [hVa, hG] at hk₀
  have hwall : ∀ y ∈ openSegment ℝ Va G, ∀ i, y ∉ interior (D.tile i).carrier := by
    intro y hy i
    refine D.edge_point_not_interior (j := t) (k := k₀) ?_ i
    rw [← hk₀]; exact openSegment_subset_segment ℝ _ _ hy
  -- the clamp at `G`
  obtain ⟨Q', hfQ', hGQ', hQc⟩ : ∃ Q' : Plane, crossL w Q' = cross w Va ∧
      G ∈ openSegment ℝ Va Q' ∧
      ∀ e ∈ D.lineChain (crossL w) (cross w Va), ¬ Straddles ((D.tile e.1).edge e.2) Q' G Va := by
    rcases hG_clamp with hout | ⟨j, hGj, hpush⟩
    · refine ⟨G + (1:ℝ) • (G - Va), ext_level _ hfG hfVa _, ?_, ?_⟩
      · rw [openSegment_symm]; exact mem_openSegment_ext G Va one_pos
      · exact clamp_out D.toDissection _ _ hout
    · obtain ⟨Q', h1, h2, h3⟩ := ext_point_of_push (crossL w) hfG hfVa hGj hpush
      refine ⟨Q', h1, ?_, fun e _ => not_straddles_of_interior D.toDissection h3 e.1 e.2⟩
      rw [openSegment_symm]; exact h2
  obtain ⟨t', k, m, hkm, hk, hm, hle⟩ := wall_whole D hn3 hM (crossL w) hF (cross w Va) hVG hfVa hfG
    (ext_level _ hfVa hfG 1) hfQ' (mem_openSegment_ext Va G one_pos) hGQ' hint hwall
    (clamp_out D.toDissection _ _ hVa_out) hQc (Or.inr hlen)
  have ht' : t' ≠ t := by
    intro h
    have := hle kb
    rw [h] at this
    exact absurd this (not_le.mpr hwb)
  obtain ⟨j₃, hj₃k, hj₃m⟩ := fin3_third k m hkm
  have hd : dist ((D.tile t').pts k) ((D.tile t').pts m) = (n:ℝ) ^ 2 - 1 := by rw [hk, hm]; exact hlen
  rcases sides_of_b_edge D hf hM t' hkm (Ne.symm hj₃k) (Ne.symm hj₃m) hd with ⟨h1, h2⟩ | ⟨h1, -⟩
  · refine ⟨t', ht', k, m, j₃, hkm, Ne.symm hj₃k, Ne.symm hj₃m, hk, hm, ?_, ?_, ?_, ?_⟩
    · rw [← hk]; exact h1
    · rw [← hm]; exact h2
    · have := (angle_at_vertex D hf hM t' hkm (Ne.symm hj₃k) (Ne.symm hj₃m)).2.2
        (by rw [dist_comm]; exact h2)
      rw [hk] at this; exact this
    · have hl' : cross w ((D.tile t').pts j₃) ≤ cross w Va := hle j₃
      rcases hw with hw | hw
      · rw [hw] at hl' hwb
        rw [cross_sub_right, cross_sub_right]
        exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
      · rw [hw, cross_neg_left, cross_neg_left] at hl' hwb
        rw [cross_sub_right, cross_sub_right]
        exact mul_nonneg (by linarith) (by linarith)
  · exfalso
    have := (angle_at_vertex D hf hM t' (Ne.symm hkm) (Ne.symm hj₃m) (Ne.symm hj₃k)).2.2
      (by rw [dist_comm]; exact h1)
    rw [hm] at this
    exact hG_ang t' ht' this

/-- **The apex dichotomy.**  Tile `t` has the `a`-edge `[V, G]` and the third vertex `O`; the open edge is
interior to the target and its line leaves the target beyond `V`.  Then either some tile contains `G`, shows a
straight angle there and contains every short push from `G` across the line away from `O`, or a tile other than
`t` has both `G` and `V` as vertices. -/
theorem apex_dichotomy {N : ℕ} (D : CongruentDissection N) {n : ℕ} (hn3 : 3 ≤ n) {α β γ : ℝ}
    (hM : ModelData D (n:ℝ) α β γ)
    {t : Fin N} {kv kg ko : Fin 3} (hvg : kv ≠ kg) (hvo : kv ≠ ko) (hgo : kg ≠ ko)
    {V G O : Plane} (hV : (D.tile t).pts kv = V) (hG : (D.tile t).pts kg = G)
    (hO : (D.tile t).pts ko = O) (hlen : dist G V = n ∨ dist G V = (n:ℝ) ^ 2 - 1)
    (hint : openSegment ℝ G V ⊆ interior D.target.carrier)
    (hV_out : ∀ s : ℝ, 0 < s → V + s • (V - G) ∉ D.target.carrier) :
    (∃ j : Fin N, G ∈ (D.tile j).carrier ∧ (D.tile j).localAngle G = Real.pi ∧
      ∀ a μ : ℝ, 0 < μ → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        G + ε • (a • (G - V) + μ • (G - O)) ∈ interior (D.tile j).carrier) ∨
    (∃ t' : Fin N, t' ≠ t ∧ ∃ k m : Fin 3, k ≠ m ∧ (D.tile t').pts k = G ∧
      (D.tile t').pts m = V) := by
  have hn3' : (3:ℝ) ≤ n := by exact_mod_cast hn3
  have hGV : G ≠ V := by
    intro h; rw [h, dist_self] at hlen
    rcases hlen with h' | h' <;> nlinarith
  obtain ⟨w, hw0, hwG, hwb, -⟩ := exists_side_functional (T := D.tile t) hvg hvo hgo
  rw [hV, hG] at hwG
  rw [hV, hO] at hwb
  have hF : crossL w ≠ 0 := crossL_ne_zero hw0
  have hfV : crossL w V = cross w V := rfl
  have hfG : crossL w G = cross w V := hwG
  obtain ⟨k₀, hk₀⟩ := (D.tile t).pair_eq_edge (Ne.symm hvg)
  rw [hV, hG] at hk₀
  have hwall : ∀ y ∈ openSegment ℝ G V, ∀ i, y ∉ interior (D.tile i).carrier := by
    intro y hy i
    refine D.edge_point_not_interior (j := t) (k := k₀) ?_ i
    rw [← hk₀]; exact openSegment_subset_segment ℝ _ _ hy
  have hQc := clamp_out D.toDissection (crossL w) (cross w V) hV_out
  by_cases hPc : ∀ e ∈ D.lineChain (crossL w) (cross w V),
      ¬ Straddles ((D.tile e.1).edge e.2) (G + (1:ℝ) • (G - V)) G V
  · right
    obtain ⟨t', k, m, hkm, hk, hm, hle⟩ := wall_whole D hn3 hM (crossL w) hF (cross w V) hGV hfG hfV
      (ext_level _ hfG hfV 1) (ext_level _ hfV hfG 1) (mem_openSegment_ext G V one_pos)
      (by rw [openSegment_symm]; exact mem_openSegment_ext V G one_pos) hint hwall hPc hQc
      hlen
    refine ⟨t', ?_, k, m, hkm, hk, hm⟩
    intro h
    have := hle ko
    rw [h, hO] at this
    exact absurd this (not_le.mpr hwb)
  · left
    push Not at hPc
    obtain ⟨e, he, hs⟩ := hPc
    obtain ⟨hGc, hπ, hpush⟩ := straddle_data D.toDissection (crossL w) hF (cross w V) hGV hfG hfV
      (ext_level _ hfG hfV 1) (mem_openSegment_ext G V one_pos) he hs
    refine ⟨e.1, hGc, hπ, fun a μ hμ => hpush _ ?_⟩
    have hfO : crossL w O = cross w O := rfl
    have hexp : crossL w (a • (G - V) + μ • (G - O))
        = a * (crossL w G - crossL w V) + μ * (crossL w G - crossL w O) := by
      simp only [map_add, map_smul, map_sub, smul_eq_mul]
    rw [hexp, hfG, hfV, hfO, sub_self, mul_zero, zero_add]
    nlinarith

/-- **THE HALF-TURN LEMMA** (lemma H of the proof, free of coordinates).  Tile `t` has the vertices `Vb`, `Va`,
`G` with `|G Vb| = a`, `|Va G| = b`, and shows `γ` at `G`; the two open edges at `G` are interior to the target and
their lines leave the target beyond `Vb` and `Va`; no other tile has both `G` and `Vb` as vertices.  Then a tile
`t' ≠ t` has the vertices `Va` and `G` and shows `γ` at `Va`. -/
theorem half_turn {N : ℕ} (D : CongruentDissection N) {n : ℕ} (hn3 : 3 ≤ n) {α β γ : ℝ}
    (hM : ModelData D (n:ℝ) α β γ) (hA : AngleData α β γ)
    {t : Fin N} {kb ka kg : Fin 3} (hba : kb ≠ ka) (hbg : kb ≠ kg) (hag : ka ≠ kg)
    {Vb Va G : Plane} (hVb : (D.tile t).pts kb = Vb) (hVa : (D.tile t).pts ka = Va)
    (hG : (D.tile t).pts kg = G)
    (hlen_a : dist G Vb = n) (hlen_b : dist Va G = (n:ℝ) ^ 2 - 1)
    (htG : (D.tile t).localAngle G = γ)
    (hint1 : openSegment ℝ G Vb ⊆ interior D.target.carrier)
    (hint2 : openSegment ℝ Va G ⊆ interior D.target.carrier)
    (hVb_out : ∀ s : ℝ, 0 < s → Vb + s • (Vb - G) ∉ D.target.carrier)
    (hVa_out : ∀ s : ℝ, 0 < s → Va + s • (Va - G) ∉ D.target.carrier)
    (hno : ∀ t' : Fin N, t' ≠ t →
      (∃ k m : Fin 3, k ≠ m ∧ (D.tile t').pts k = G ∧ (D.tile t').pts m = Vb) → False) :
    ∃ t' : Fin N, t' ≠ t ∧ ∃ k m j : Fin 3, k ≠ m ∧ k ≠ j ∧ m ≠ j ∧
      (D.tile t').pts k = Va ∧ (D.tile t').pts m = G ∧
      dist ((D.tile t').pts j) Va = n ∧ dist ((D.tile t').pts j) G = (n:ℝ) ^ 2 ∧
      (D.tile t').localAngle Va = γ ∧
      0 ≤ cross (G - Va) ((D.tile t').pts j - Va) * cross (G - Va) (Va - (D.tile t).pts kb) := by
  obtain ⟨-, -, hγ2, -, hγπ⟩ := angle_facts hA
  have hπ := Real.pi_pos
  rcases apex_dichotomy D hn3 hM hbg hba (Ne.symm hag) hVb hG hVa (Or.inl hlen_a) hint1 hVb_out with
    ⟨j, hGj, hjπ, hpush⟩ | ⟨t', ht', hex⟩
  · refine partner D hn3 hM hag (Ne.symm hba) (Ne.symm hbg) hVa hG hlen_b hint2 hVa_out
      (Or.inr ⟨j, hGj, ?_⟩) ?_
    · obtain ⟨ε₀, hε₀, h⟩ := hpush 0 1 one_pos
      refine ⟨ε₀, hε₀, fun ε h1 h2 => ?_⟩
      have := h ε h1 h2
      rwa [zero_smul, zero_add, one_smul] at this
    · intro i' hi' hi'γ
      have hjt : j ≠ t := by
        intro h; rw [h, htG] at hjπ; linarith
      have hji : j ≠ i' := by
        intro h; rw [h, hi'γ] at hjπ; linarith
      have h3 := three_angles_le D.toDissection G hjt hji (Ne.symm hi')
      have h4 := localAngle_le_two_pi D.target G
      rw [hjπ, htG, hi'γ] at h3
      linarith
  · exact absurd hex (fun h => hno t' ht' h)

end Erdos634.Draft.W2E1

#print axioms Erdos634.Draft.W2E1.first_edge
#print axioms Erdos634.Draft.W2E1.wall_whole
#print axioms Erdos634.Draft.W2E1.third_vertex_unique
#print axioms Erdos634.Draft.W2E1.partner
#print axioms Erdos634.Draft.W2E1.half_turn

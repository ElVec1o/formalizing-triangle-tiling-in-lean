import Erdos634.PlacementCompleteness

/-!
# Placement completeness at an arbitrary convex corner

`placement_completeness` is stated at the lexicographically least point of the unfilled region.
Its proof uses that hypothesis in exactly one place: *an unplaced tile through `v` has a vertex at
`v`*.  That holds at **any** point `v` near which the unfilled region lies in a pointed cone
`{v + s·d + t·g : s, t ≥ 0}` with `0 < cross d g` (a convex corner of the unfilled region), and the
"clockwise wedge is blocked" hypothesis is then automatic.

Consequence for certificates: the branch point of a search-tree node may be ANY convex corner of the
unfilled region (most-constrained-corner branching), and the per-node obligation is LOCAL (a
neighbourhood of `v`), not a global sweep statement.

Formalization infrastructure; no /goal outcome moves by this file alone.  Axiom-clean; no `sorry`.
-/

namespace Erdos634.PlacementCompleteness

open Erdos634.Geometry Erdos634.Geometry.Dissection Set MeasureTheory

/-- `placement_completeness` with the lexicographic hypothesis replaced by the only consequence of it
that the proof uses: every unplaced tile through `v` has a vertex at `v`. -/
theorem placement_completeness_of_corner {N : ℕ} (D : Dissection N) (S : Finset (Fin N)) (v d : Plane)
    (hunit : d 0 ^ 2 + d 1 ^ 2 = 1)
    (hcorner : ∀ j, j ∉ S → v ∈ (D.tile j).carrier → ∃ k, (D.tile j).pts k = v)
    (hfree : ∀ ε : ℝ, 0 < ε → ∃ t s : ℝ, 0 < t ∧ t < ε ∧ 0 < s ∧ s < ε ∧
      v + t • (d + s • perp d) ∈ unfilled D S)
    (hblocked : ∃ δ : ℝ, 0 < δ ∧ ∀ t s : ℝ, 0 < t → t < δ → 0 < s → s < δ →
      v + t • (d - s • perp d) ∉ unfilled D S) :
    ∃ j, j ∉ S ∧ ∃ k₀ k₁ k₂ : Fin 3, k₀ ≠ k₁ ∧ k₀ ≠ k₂ ∧ k₁ ≠ k₂ ∧
      (D.tile j).pts k₀ = v ∧
      (∃ c : ℝ, 0 < c ∧ (D.tile j).pts k₁ = v + c • d) ∧
      0 < cross d ((D.tile j).pts k₂ - v) := by
  classical
  by_contra hcon
  -- every unplaced tile is avoided by the counter-clockwise near-`d` points
  have hexcl : ∀ j ∈ (Finset.univ.filter fun j => j ∉ S), ∃ δ : ℝ, 0 < δ ∧
      ∀ t s : ℝ, 0 < t → t < δ → 0 < s → s < δ →
        v + t • (d + s • perp d) ∉ (D.tile j).carrier := by
    intro j hj
    have hj : j ∉ S := by simpa using hj
    by_cases hvj : v ∈ (D.tile j).carrier
    · obtain ⟨k, hk⟩ := hcorner j hj hvj
      set T := (D.tile j).relabel (Equiv.addRight k) with hT
      have hT0 : T.pts 0 = v := by rw [hT, Tri.relabel_pts]; simpa using hk
      have hTc : T.carrier = (D.tile j).carrier := relabel_carrier _ _
      have hCW := not_cw_wedge_interior D S hunit hblocked hj
      rw [← hT0, ← hTc] at hCW
      rcases corner_edge_dichotomy T d hunit hCW with ⟨δ, hδ, hex⟩ |
        ⟨k₁, k₂, h1, h2, h12, ⟨c, hc, hk₁⟩, hk₂⟩
      · refine ⟨δ, hδ, fun t s ht htδ hs hsδ => ?_⟩
        have := hex t s ht htδ hs hsδ
        rwa [hT0, hTc] at this
      · exfalso
        apply hcon
        refine ⟨j, hj, (Equiv.addRight k) 0, (Equiv.addRight k) k₁, (Equiv.addRight k) k₂,
          (Equiv.addRight k).injective.ne (Ne.symm h1),
          (Equiv.addRight k).injective.ne (Ne.symm h2),
          (Equiv.addRight k).injective.ne h12, ?_, ⟨c, hc, ?_⟩, ?_⟩
        · exact hT0
        · rw [← hT0]; exact hk₁
        · rw [← hT0]; exact hk₂
    · obtain ⟨ρ, hρ, hball⟩ :=
        Metric.isOpen_iff.mp (D.tile j).isCompact.isClosed.isOpen_compl v hvj
      refine ⟨min 1 (ρ / 2), by positivity, fun t s ht htδ hs hsδ => ?_⟩
      have ht1 : t < ρ / 2 := lt_of_lt_of_le htδ (min_le_right _ _)
      have hs1 : s < 1 := lt_of_lt_of_le hsδ (min_le_left _ _)
      have hdist : dist (v + t • (d + s • perp d)) v < ρ := by
        have hsq : dist (v + t • (d + s • perp d)) v ^ 2 = t ^ 2 * (1 + s ^ 2) := by
          rw [dist_sq_coord]
          simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, perp_zero, perp_one]
          linear_combination (t ^ 2 * (1 + s ^ 2)) * hunit
        have hlt : dist (v + t • (d + s • perp d)) v ^ 2 < ρ ^ 2 := by
          rw [hsq]
          have h1 : t ^ 2 < (ρ / 2) ^ 2 := by nlinarith
          have h2 : s ^ 2 < 1 := by nlinarith
          have h3 : t ^ 2 * (1 + s ^ 2) < t ^ 2 * 2 :=
            mul_lt_mul_of_pos_left (by linarith) (by positivity)
          nlinarith
        nlinarith [dist_nonneg (x := v + t • (d + s • perp d)) (y := v)]
      exact hball (Metric.mem_ball.mpr hdist)
  obtain ⟨δ, hδ, hall⟩ := exists_uniform_delta (Finset.univ.filter fun j => j ∉ S)
    (fun j δ => ∀ t s : ℝ, 0 < t → t < δ → 0 < s → s < δ →
      v + t • (d + s • perp d) ∉ (D.tile j).carrier)
    (fun j δ δ' hle h t s ht htδ hs hsδ => h t s ht (lt_of_lt_of_le htδ hle) hs
      (lt_of_lt_of_le hsδ hle))
    hexcl
  obtain ⟨t, s, ht, htδ, hs, hsδ, hq⟩ := hfree δ hδ
  obtain ⟨j, hj, hqj⟩ := exists_unplaced_of_mem_unfilled D S hq
  exact hall j (by simp [hj]) t s ht htδ hs hsδ hqj

/-- In a cone with `0 < cross d g`, a vector with both cross products zero is zero. -/
theorem eq_zero_of_cross_zero {d g u : Plane} (hdg : 0 < cross d g)
    (h1 : cross d u = 0) (h2 : cross g u = 0) : u = 0 := by
  simp only [cross] at hdg h1 h2
  have hne : d 0 * g 1 - d 1 * g 0 ≠ 0 := ne_of_gt hdg
  have e0 : u 0 * (d 0 * g 1 - d 1 * g 0) = 0 := by linear_combination g 0 * h1 - d 0 * h2
  have e1 : u 1 * (d 0 * g 1 - d 1 * g 0) = 0 := by linear_combination g 1 * h1 - d 1 * h2
  have u0 : u 0 = 0 := (mul_eq_zero.mp e0).resolve_right hne
  have u1 : u 1 = 0 := (mul_eq_zero.mp e1).resolve_right hne
  exact plane_ext (by simpa using u0) (by simpa using u1)

/-- **Cone ⇒ corner.**  If near `v` the unfilled region lies in the cone spanned by `d` and `g`
(`0 < cross d g`), every unplaced tile through `v` has a vertex at `v`. -/
theorem corner_of_cone {N : ℕ} (D : Dissection N) (S : Finset (Fin N)) (v d g : Plane)
    (hdg : 0 < cross d g)
    (hcone : ∃ ε : ℝ, 0 < ε ∧ ∀ p ∈ unfilled D S, dist p v < ε →
      0 ≤ cross d (p - v) ∧ 0 ≤ cross (p - v) g)
    {j : Fin N} (hj : j ∉ S) (hv : v ∈ (D.tile j).carrier) : ∃ k, (D.tile j).pts k = v := by
  classical
  obtain ⟨ε, hε, hU⟩ := hcone
  set T := D.tile j with hT
  -- the closed cone
  set C : Set Plane := {p | 0 ≤ cross d (p - v) ∧ 0 ≤ cross (p - v) g} with hC
  have h0 : Continuous fun q : Plane => q 0 :=
    (EuclideanSpace.proj (0 : Fin 2) : Plane →L[ℝ] ℝ).continuous
  have h1 : Continuous fun q : Plane => q 1 :=
    (EuclideanSpace.proj (1 : Fin 2) : Plane →L[ℝ] ℝ).continuous
  have hCclosed : IsClosed C := by
    have c1 : Continuous fun p : Plane => cross d (p - v) := by
      simp only [cross, PiLp.sub_apply]; fun_prop
    have c2 : Continuous fun p : Plane => cross (p - v) g := by
      simp only [cross, PiLp.sub_apply]; fun_prop
    exact (isClosed_le continuous_const c1).inter (isClosed_le continuous_const c2)
  -- closure of the unfilled region, near `v`, is in the cone
  have hcl : ∀ p ∈ closure (unfilled D S), dist p v < ε → p ∈ C := by
    intro p hp hd
    have hmem : p ∈ Metric.ball v ε ∩ closure (unfilled D S) := ⟨Metric.mem_ball.mpr hd, hp⟩
    have h2 := Metric.isOpen_ball.inter_closure hmem
    refine closure_minimal ?_ hCclosed h2
    rintro q ⟨hq1, hq2⟩
    exact hU q hq2 (Metric.mem_ball.mp hq1)
  -- the whole tile is in the cone
  have hconv : Convex ℝ T.carrier := by
    rw [Tri.carrier]; exact convex_convexHull ℝ _
  have htile : ∀ q ∈ T.carrier, 0 ≤ cross d (q - v) ∧ 0 ≤ cross (q - v) g := by
    intro q hq
    set lam : ℝ := min 1 (ε / (2 * (‖q - v‖ + 1))) with hlam
    have hden : 0 < 2 * (‖q - v‖ + 1) := by positivity
    have hlpos : 0 < lam := lt_min one_pos (div_pos hε hden)
    have hl1 : lam ≤ 1 := min_le_left _ _
    have hl2 : lam ≤ ε / (2 * (‖q - v‖ + 1)) := min_le_right _ _
    have hmem : v + lam • (q - v) ∈ T.carrier :=
      hconv.add_smul_sub_mem hv hq ⟨hlpos.le, hl1⟩
    have hdist : dist (v + lam • (q - v)) v < ε := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hlpos.le]
      have hb : lam * ‖q - v‖ ≤ ε / (2 * (‖q - v‖ + 1)) * ‖q - v‖ :=
        mul_le_mul_of_nonneg_right hl2 (norm_nonneg _)
      have hc : ε / (2 * (‖q - v‖ + 1)) * ‖q - v‖ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
        nlinarith [norm_nonneg (q - v)]
      linarith
    have hin := hcl _ (carrier_subset_closure_unfilled D S hj hmem) hdist
    simp only [hC, Set.mem_setOf_eq, add_sub_cancel_left] at hin
    obtain ⟨a, b⟩ := hin
    have ea : cross d (lam • (q - v)) = lam * cross d (q - v) := by
      simp only [cross, PiLp.smul_apply, smul_eq_mul]; ring
    have eb : cross (lam • (q - v)) g = lam * cross (q - v) g := by
      simp only [cross, PiLp.smul_apply, smul_eq_mul]; ring
    rw [ea] at a; rw [eb] at b
    exact ⟨nonneg_of_mul_nonneg_right a hlpos, nonneg_of_mul_nonneg_right b hlpos⟩
  -- vertex extraction: two support faces
  set s : Finset Plane := Finset.univ.image T.pts with hs
  have hcar : T.carrier = convexHull ℝ (s : Set Plane) := by
    rw [Tri.carrier, hs, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  have hmem : ∀ w ∈ s, w ∈ T.carrier := fun w hw => by
    rw [hcar]; exact subset_convexHull ℝ _ hw
  have sub1 : ∀ w : Plane, cross d (w - v) = cross d w - cross d v := fun w => by
    simp only [cross, PiLp.sub_apply]; ring
  have sub2 : ∀ w : Plane, cross (w - v) g = -(cross g w - cross g v) := fun w => by
    simp only [cross, PiLp.sub_apply]; ring
  set f₁ : Plane →ₗ[ℝ] ℝ := -(crossL d) with hf₁
  have hf₁v : ∀ w : Plane, f₁ w = -(cross d w) := fun w => by simp [hf₁]
  have hle₁ : ∀ w ∈ s, f₁ w ≤ f₁ v := by
    intro w hw
    rw [hf₁v, hf₁v]
    have := (htile w (hmem w hw)).1
    rw [sub1] at this; linarith
  have hv₁ : v ∈ convexHull ℝ (s : Set Plane) := by rw [← hcar]; exact hv
  have hstep₁ := Erdos634.SupportFace.mem_convexHull_max f₁ (f₁ v) s hle₁ hv₁ rfl
  set s₁ := s.filter (fun w => f₁ w = f₁ v) with hs₁
  have hs₁mem : ∀ w ∈ s₁, w ∈ s ∧ cross d (w - v) = 0 := fun w hw => by
    rw [hs₁, Finset.mem_filter] at hw
    refine ⟨hw.1, ?_⟩
    have := hw.2; rw [hf₁v, hf₁v] at this
    rw [sub1]; linarith
  set f₂ : Plane →ₗ[ℝ] ℝ := crossL g with hf₂
  have hf₂v : ∀ w : Plane, f₂ w = cross g w := fun w => by simp [hf₂]
  have hle₂ : ∀ w ∈ s₁, f₂ w ≤ f₂ v := by
    intro w hw
    rw [hf₂v, hf₂v]
    have := (htile w (hmem w (hs₁mem w hw).1)).2
    rw [sub2] at this; linarith
  have hstep₂ := Erdos634.SupportFace.mem_convexHull_max f₂ (f₂ v) s₁ hle₂ hstep₁ rfl
  set s₂ := s₁.filter (fun w => f₂ w = f₂ v) with hs₂
  have hs₂mem : ∀ w ∈ s₂, w ∈ s ∧ w = v := fun w hw => by
    rw [hs₂, Finset.mem_filter] at hw
    obtain ⟨hws, hw1⟩ := hs₁mem w hw.1
    have hw2 : cross g (w - v) = 0 := by
      have := hw.2; rw [hf₂v, hf₂v] at this
      have e : cross g (w - v) = cross g w - cross g v := by
        simp only [cross, PiLp.sub_apply]; ring
      rw [e]; linarith
    have := eq_zero_of_cross_zero hdg hw1 hw2
    exact ⟨hws, sub_eq_zero.mp this⟩
  have hne : s₂.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    rw [hemp] at hstep₂
    simp at hstep₂
  obtain ⟨w, hw⟩ := hne
  obtain ⟨hws, hwv⟩ := hs₂mem w hw
  rw [hs, Finset.mem_image] at hws
  obtain ⟨k, _, hk⟩ := hws
  exact ⟨k, hk.trans hwv⟩

/-- **PLACEMENT COMPLETENESS AT A CONVEX CORNER.**  If near `v` the unfilled region lies in the
cone spanned by the unit vector `d` and a vector `g` with `0 < cross d g`, and points just
counter-clockwise of `d` are unfilled arbitrarily close to `v`, then some unplaced tile has a vertex
at `v`, a second vertex on the ray `v + ℝ₊·d`, and its third vertex strictly counter-clockwise of `d`. -/
theorem placement_completeness_cone {N : ℕ} (D : Dissection N) (S : Finset (Fin N)) (v d g : Plane)
    (hunit : d 0 ^ 2 + d 1 ^ 2 = 1) (hdg : 0 < cross d g)
    (hcone : ∃ ε : ℝ, 0 < ε ∧ ∀ p ∈ unfilled D S, dist p v < ε →
      0 ≤ cross d (p - v) ∧ 0 ≤ cross (p - v) g)
    (hfree : ∀ ε : ℝ, 0 < ε → ∃ t s : ℝ, 0 < t ∧ t < ε ∧ 0 < s ∧ s < ε ∧
      v + t • (d + s • perp d) ∈ unfilled D S) :
    ∃ j, j ∉ S ∧ ∃ k₀ k₁ k₂ : Fin 3, k₀ ≠ k₁ ∧ k₀ ≠ k₂ ∧ k₁ ≠ k₂ ∧
      (D.tile j).pts k₀ = v ∧
      (∃ c : ℝ, 0 < c ∧ (D.tile j).pts k₁ = v + c • d) ∧
      0 < cross d ((D.tile j).pts k₂ - v) := by
  refine placement_completeness_of_corner D S v d hunit
    (fun j hj hv => corner_of_cone D S v d g hdg hcone hj hv) hfree ?_
  obtain ⟨ε, hε, hU⟩ := hcone
  refine ⟨min 1 (ε / 2), by positivity, fun t s ht htδ hs hsδ hmem => ?_⟩
  have ht1 : t < ε / 2 := lt_of_lt_of_le htδ (min_le_right _ _)
  have hs1 : s < 1 := lt_of_lt_of_le hsδ (min_le_left _ _)
  have hdist : dist (v + t • (d - s • perp d)) v < ε := by
    have hsq : dist (v + t • (d - s • perp d)) v ^ 2 = t ^ 2 * (1 + s ^ 2) := by
      rw [dist_sq_coord]
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, perp_zero, perp_one]
      linear_combination (t ^ 2 * (1 + s ^ 2)) * hunit
    have hlt : dist (v + t • (d - s • perp d)) v ^ 2 < ε ^ 2 := by
      rw [hsq]
      have h1 : t ^ 2 < (ε / 2) ^ 2 := by nlinarith
      have h2 : s ^ 2 < 1 := by nlinarith
      have h3 : t ^ 2 * (1 + s ^ 2) < t ^ 2 * 2 :=
        mul_lt_mul_of_pos_left (by linarith) (by positivity)
      nlinarith
    nlinarith [dist_nonneg (x := v + t • (d - s • perp d)) (y := v)]
  have h := (hU _ hmem hdist).1
  have e : cross d (v + t • (d - s • perp d) - v) = -(t * s) := by
    simp only [cross, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, perp_zero,
      perp_one]
    linear_combination (-(t * s)) * hunit
  rw [e] at h
  nlinarith [mul_pos ht hs]

end Erdos634.PlacementCompleteness

#print axioms Erdos634.PlacementCompleteness.placement_completeness_cone

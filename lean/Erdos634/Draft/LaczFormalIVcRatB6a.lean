-- Draft/LaczFormalIVcRatB6a.lean -- Laczkovich DCG 48 (2012), Sect. 8.3 (Subcase IVc, rational branch), BLUEPRINT Part B, item B6, step (a): a tile that fills a corner of a convex set has its edges on the frontier.
--   `tri_edge_frontier` : A convex, T a triangle with T subset A, j a vertex index, and (hvol) for the radius r0 the area of A in the ball B(pts j, r0) is at most the area of T there
--   (the corner of A at pts j is exactly the corner of T, in measure).  Then the other endpoint `pts n` of an edge at `pts j` lies in `frontier A`.
--   Proof: if some y in A had g y < 0 for the barycentric coordinate g = coord m vanishing on that edge, the convex hull of (an interior point of T near pts j) and y would give an open set of positive area
--   inside A, on the far side of the edge, within B(pts j, r0): contradicting the area bound; then pts n is on the zero line of g with A inside {g >= 0}.
--   This is the printed step of P3 ("the sector is exactly filled; the base lies along XY, so W lies on bd A") made precise.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 8.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIVcRatB5

open scoped Classical Fin.NatCast
open MeasureTheory
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

theorem aff_eq (g : Plane →ᵃ[ℝ] ℝ) (p q : Plane) : g p = g q + g.linear (p - q) := by
  have := g.linearMap_vsub p q
  rw [vsub_eq_sub, vsub_eq_sub] at this
  linarith

theorem tri_edge_frontier {A : Set Plane} (hA : Convex ℝ A) (T : Tri) (hT : T.carrier ⊆ A) {j m n : Fin 3}
    (hmj : m ≠ j) (hnm : n ≠ m) {r0 : ℝ} (hr0 : 0 < r0)
    (hvol : ∀ r, 0 < r → r ≤ r0 → volume (A ∩ Metric.ball (T.pts j) r) ≤ volume (T.carrier ∩ Metric.ball (T.pts j) r)) :
    T.pts n ∈ frontier A := by
  set g := T.basis.coord m with hgdef
  have hgj : g (T.pts j) = 0 := T.basis.coord_apply_ne hmj
  have hgn : g (T.pts n) = 0 := T.basis.coord_apply_ne hnm.symm
  have hgT : ∀ x ∈ T.carrier, 0 ≤ g x := by
    intro x hx; rw [T.carrier_eq_nonneg_coord] at hx; exact hx m
  have hgc : Continuous g := g.continuous_of_finiteDimensional
  set a := T.pts j with hadef
  have haT : a ∈ T.carrier := subset_convexHull ℝ _ ⟨j, rfl⟩
  have hg : ∀ p, g p = g.linear (p - a) := fun p => by rw [aff_eq g p a, hgj]; ring
  have claim : ∀ y ∈ A, 0 ≤ g y := by
    intro y hy
    by_contra hneg
    push Not at hneg
    obtain ⟨c, hc⟩ := T.interior_nonempty
    have hGc : 0 < g c := (T.mem_interior_iff_coord_pos c).mp hc m
    set G := g c with hG
    set H := -(g y) with hH
    have hHpos : 0 < H := by rw [hH]; linarith
    set Nc := ‖c - a‖ with hNc
    set Ny := ‖y - a‖ with hNy
    have hNc0 : 0 ≤ Nc := norm_nonneg _
    have hNy0 : 0 ≤ Ny := norm_nonneg _
    set r := r0 with hrdef
    set t : ℝ := min (1 / 2) (r / (4 * (Ny + 1))) with htdef
    have ht0 : 0 < t := lt_min (by norm_num) (by positivity)
    have ht2 : t ≤ 1 / 2 := min_le_left _ _
    have ht3 : t * (Ny + 1) ≤ r / 4 := by
      have : t ≤ r / (4 * (Ny + 1)) := min_le_right _ _
      calc t * (Ny + 1) ≤ r / (4 * (Ny + 1)) * (Ny + 1) := by gcongr
        _ = r / 4 := by field_simp
    set δ : ℝ := min (min (1 / 2) (t * H / (2 * (G + 1)))) (r / (4 * (Nc + 1))) with hδdef
    have hδ0 : 0 < δ := lt_min (lt_min (by norm_num) (by positivity)) (by positivity)
    have hδ2 : δ ≤ 1 / 2 := (min_le_left _ _).trans (min_le_left _ _)
    have hδ3 : δ * (G + 1) ≤ t * H / 2 := by
      have : δ ≤ t * H / (2 * (G + 1)) := (min_le_left _ _).trans (min_le_right _ _)
      calc δ * (G + 1) ≤ t * H / (2 * (G + 1)) * (G + 1) := by gcongr
        _ = t * H / 2 := by field_simp
    have hδ4 : δ * (Nc + 1) ≤ r / 4 := by
      have : δ ≤ r / (4 * (Nc + 1)) := min_le_right _ _
      calc δ * (Nc + 1) ≤ r / (4 * (Nc + 1)) * (Nc + 1) := by gcongr
        _ = r / 4 := by field_simp
    set u : Plane := δ • c + (1 - δ) • a with hudef
    have hu : u ∈ interior T.carrier :=
      T.convex.openSegment_interior_self_subset_interior hc haT ⟨δ, 1 - δ, hδ0, by linarith, by ring, hudef.symm⟩
    set z : Plane := (1 - t) • u + t • y with hzdef
    have hz : z ∈ interior A :=
      hA.openSegment_interior_self_subset_interior (interior_mono hT hu) hy ⟨1 - t, t, by linarith, ht0, by ring, hzdef.symm⟩
    have hzsub : z - a = ((1 - t) * δ) • (c - a) + t • (y - a) := by
      rw [hzdef, hudef]; module
    have hgz : g z = (1 - t) * δ * G + t * g y := by
      rw [hg z, hzsub, map_add, map_smul, map_smul, ← hg c, ← hg y, smul_eq_mul, smul_eq_mul]
    have hgzneg : g z < 0 := by
      rw [hgz]
      have h0 : 0 ≤ t * (δ * G) := by positivity
      have h1 : (1 - t) * δ * G ≤ δ * G := by linarith [h0]
      have h2 : δ * G ≤ δ * (G + 1) := by linarith
      have h3 : t * g y = -(t * H) := by rw [hH]; ring
      have h4 : 0 < t * H := by positivity
      linarith [hδ3, hδ0]
    have hzball : z ∈ Metric.ball a r := by
      rw [Metric.mem_ball, dist_eq_norm, hzsub]
      refine lt_of_le_of_lt (norm_add_le _ _) ?_
      rw [norm_smul, norm_smul, Real.norm_of_nonneg (by have := mul_nonneg ht0.le hδ0.le; nlinarith), Real.norm_of_nonneg ht0.le]
      have h0 : 0 ≤ t * (δ * Nc) := by positivity
      have h1 : (1 - t) * δ * Nc ≤ δ * Nc := by linarith [h0]
      linarith [h1, hδ4, ht3, hδ0, ht0, hr0]
    set U : Set Plane := (interior A ∩ {x | g x < 0}) ∩ Metric.ball a r with hUdef
    have hUo : IsOpen U := (isOpen_interior.inter (isOpen_lt hgc continuous_const)).inter Metric.isOpen_ball
    have hUpos : 0 < volume U := hUo.measure_pos volume ⟨z, ⟨hz, hgzneg⟩, hzball⟩
    have hdisj : Disjoint (T.carrier ∩ Metric.ball a r) U := by
      refine Set.disjoint_left.mpr fun x hx hxU => ?_
      have h1 := hgT x hx.1
      have h2 : g x < 0 := hxU.1.2
      linarith
    have hsub : (T.carrier ∩ Metric.ball a r) ∪ U ⊆ A ∩ Metric.ball a r := by
      rintro x (⟨hx1, hx2⟩ | ⟨⟨hx1, _⟩, hx2⟩)
      · exact ⟨hT hx1, hx2⟩
      · exact ⟨interior_subset hx1, hx2⟩
    have h1 : volume (T.carrier ∩ Metric.ball a r) + volume U ≤ volume (A ∩ Metric.ball a r) := by
      rw [← measure_union hdisj hUo.measurableSet]; exact measure_mono hsub
    have h2 := hvol r hr0 le_rfl
    have hfin : volume (T.carrier ∩ Metric.ball a r) ≠ ⊤ :=
      ((measure_mono Set.inter_subset_right).trans_lt measure_ball_lt_top).ne
    have h3 : volume (T.carrier ∩ Metric.ball a r) < volume (T.carrier ∩ Metric.ball a r) + volume U :=
      ENNReal.lt_add_right hfin hUpos.ne'
    exact absurd (lt_of_lt_of_le h3 (h1.trans h2)) (lt_irrefl _)
  -- the edge endpoint lies on the zero line of g, with A inside {g >= 0}
  have hnT : T.pts n ∈ T.carrier := subset_convexHull ℝ _ ⟨n, rfl⟩
  refine ⟨subset_closure (hT hnT), fun hint => ?_⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior _ hint
  have hne : g.linear ≠ 0 := T.coord_linear_ne_zero m
  obtain ⟨v, hv⟩ : ∃ v, g.linear v ≠ 0 := by
    by_contra hall; push Not at hall; exact hne (LinearMap.ext hall)
  set v' : Plane := (-(g.linear v)) • v with hv'
  have hgv' : g.linear v' = -(g.linear v) ^ 2 := by rw [hv', map_smul, smul_eq_mul]; ring
  set τ : ℝ := ε / (2 * (‖v'‖ + 1)) with hτ
  have hτ0 : 0 < τ := by positivity
  have hy : T.pts n + τ • v' ∈ interior A := by
    refine hball ?_
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hτ0.le, hτ]
    have : ε / (2 * (‖v'‖ + 1)) * ‖v'‖ ≤ ε / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [norm_nonneg v']
    linarith
  have hneg : g (T.pts n + τ • v') < 0 := by
    rw [aff_eq g _ (T.pts n), add_sub_cancel_left, hgn, map_smul, hgv', smul_eq_mul]
    have : 0 < (g.linear v) ^ 2 := by positivity
    nlinarith
  have := claim _ (interior_subset hy)
  linarith

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.tri_edge_frontier

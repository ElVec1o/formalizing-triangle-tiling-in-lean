-- Draft/H1gPosCover.lean — ATOM H1.g (position half), sub-atom P2/P3 geometry: on a line through an
-- interior point of the target, the union of the near-side chain edges equals the union of the
-- far-side chain edges (as a set of line parameters).  Uses `Dissection.wall_cover`.
-- Formalization debt; NOT /goal progress.  Standard axioms, no sorry.
import Erdos634.Draft.H1gPosLine

open Set

namespace Erdos634.H1gPos

open Erdos634.Geometry

/-- A segment on a line through an interior point of a convex set lies, in its relative interior,
in the interior. -/
theorem collinear_open_int {A : Set Plane} (hA : Convex ℝ A) {r u v x : Plane}
    (hr : r ∈ interior A) (hu : u ∈ A) (hv : v ∈ A) (ρ : ℝ) (hρ : r = u + ρ • (v - u))
    (hx : x ∈ openSegment ℝ u v) : x ∈ interior A := by
  rw [openSegment_eq_image'] at hx
  obtain ⟨θ, ⟨h0, h1⟩, rfl⟩ := hx
  rcases lt_trichotomy θ ρ with h | h | h
  · have hρ0 : 0 < ρ := by linarith
    have hmem : (u + θ • (v - u)) ∈ openSegment ℝ u r := by
      rw [openSegment_eq_image']
      refine ⟨θ / ρ, ⟨by positivity, by rw [div_lt_one hρ0]; exact h⟩, ?_⟩
      show u + (θ / ρ) • (r - u) = _
      rw [hρ, add_sub_cancel_left, smul_smul, div_mul_cancel₀ _ hρ0.ne']
    have := hA.openSegment_interior_closure_subset_interior hr (subset_closure hu)
    rw [openSegment_symm] at hmem
    exact this hmem
  · subst h; show u + θ • (v - u) ∈ interior A; rw [← hρ]; exact hr
  · have hρ1 : 0 < 1 - ρ := by linarith
    have hmem : (u + θ • (v - u)) ∈ openSegment ℝ r v := by
      rw [openSegment_eq_image']
      refine ⟨(θ - ρ) / (1 - ρ), ⟨by apply div_pos <;> linarith, ?_⟩, ?_⟩
      · rw [div_lt_one hρ1]; linarith
      · show r + ((θ - ρ) / (1 - ρ)) • (v - r) = _
        have e1 : v - r = (1 - ρ) • (v - u) := by rw [hρ]; module
        have e2 : (θ - ρ) / (1 - ρ) * (1 - ρ) = θ - ρ := div_mul_cancel₀ _ hρ1.ne'
        rw [e1, smul_smul, e2, hρ]; module
    exact hA.openSegment_interior_closure_subset_interior hr (subset_closure hv) hmem

theorem pts_mem_carrier (T : Tri) (k : Fin 3) : T.pts k ∈ T.carrier :=
  subset_convexHull ℝ _ (Set.mem_range_self k)

/-- Every edge on a line through an interior point `r` of the target has its relative interior in
the interior of the target. -/
theorem openEdge_interior {N : ℕ} (D : Dissection N) {d O r : Plane} (hd : d ≠ 0)
    (hr : r ∈ interior D.target.carrier) (hrl : cross d (r - O) = 0)
    {e : Fin N × Fin 3} (he : OnLine D O d e) :
    openSegment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) ⊆
      interior D.target.carrier := by
  intro x hx
  obtain ⟨h1, h2⟩ := pts_eq_pt hd he
  obtain ⟨τ, hτ⟩ := parallel_of_cross_eq_zero hd hrl
  have hne := eA_ne_eB hd he
  have hsub : eB D O d e - eA D O d e ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  refine collinear_open_int D.target.convex hr
    (tile_subset_target D e.1 (pts_mem_carrier _ _))
    (tile_subset_target D e.1 (pts_mem_carrier _ _))
    ((τ - eA D O d e) / (eB D O d e - eA D O d e)) ?_ hx
  have hr' : r = O + τ • d := by rw [← hτ]; abel
  rw [hr', h1, h2]
  simp only [pt]
  have : (τ - eA D O d e) / (eB D O d e - eA D O d e) * (eB D O d e - eA D O d e) =
      τ - eA D O d e := div_mul_cancel₀ _ hsub
  have e3 : (O + eB D O d e • d) - (O + eA D O d e • d) = (eB D O d e - eA D O d e) • d := by
    module
  rw [e3, smul_smul, this]; module

/-- **The other side covers.**  Every point of a near-side chain edge lies on a far-side chain edge,
provided the relative interiors of near-side edges lie in the interior of the target. -/
theorem cover_other {N : ℕ} (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf : f ≠ 0)
    (hch : ∀ e ∈ D.lineChain f c, openSegment ℝ ((D.tile e.1).pts e.2)
      ((D.tile e.1).pts (e.2 + 1)) ⊆ interior D.target.carrier)
    {e : Fin N × Fin 3} (he : e ∈ D.lineChain f c) {x : Plane} (hx : x ∈ (D.tile e.1).edge e.2) :
    ∃ e' ∈ D.lineChain (-f) (-c), x ∈ (D.tile e'.1).edge e'.2 := by
  classical
  by_contra hcon
  push Not at hcon
  set U : Set Plane := ⋃ e' ∈ D.lineChain (-f) (-c), (D.tile e'.1).edge e'.2 with hU
  have hUc : IsClosed U := isClosed_biUnion_finset (fun e' _ => (D.tile e'.1).isClosed_edge e'.2)
  have hxU : x ∉ U := by
    simp only [hU, mem_iUnion, not_exists]
    intro e' he' h; exact hcon e' he' h
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hUc.isOpen_compl x hxU
  set u₁ := (D.tile e.1).pts e.2 with hu₁
  set u₂ := (D.tile e.1).pts (e.2 + 1) with hu₂
  have hu : u₁ ≠ u₂ := by
    intro h
    have h3 := (D.tile e.1).indep.injective h
    have h4 : ∀ m : Fin 3, m ≠ m + 1 := by decide
    exact h4 _ h3
  have hw : u₂ - u₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  obtain ⟨a, b, ha, hb, hab, hxe⟩ : x ∈ segment ℝ u₁ u₂ := hx
  set γ : ℝ → Plane := fun τ => u₁ + τ • (u₂ - u₁) with hγ
  have hγx : γ b = x := by
    have : a = 1 - b := by linarith
    subst this
    rw [← hxe]; simp only [hγ]; module
  have hγc : Continuous γ := by simp only [hγ]; fun_prop
  obtain ⟨η, hη, hηsub⟩ := Metric.isOpen_iff.mp (Metric.isOpen_ball.preimage hγc) b
    (by show γ b ∈ Metric.ball x δ; rw [hγx]; exact Metric.mem_ball_self hδ)
  have hb0 : 0 ≤ b := hb
  have hb1 : b ≤ 1 := by linarith
  have hlt : max 0 (b - η) < min 1 (b + η) := by
    refine max_lt (lt_min one_pos (by linarith)) (lt_min (by linarith) (by linarith))
  have hinj : Set.InjOn γ (Ioo (max 0 (b - η)) (min 1 (b + η))) := by
    intro s _ t _ hst
    have : s • (u₂ - u₁) = t • (u₂ - u₁) := add_left_cancel hst
    exact smul_left_injective ℝ hw this
  have hinf := (Set.Ioo_infinite hlt).image hinj
  obtain ⟨y, hy, hyV⟩ := (hinf.diff D.vertexSet_finite).nonempty
  obtain ⟨τ, hτ, rfl⟩ := hy
  have hτ0 : 0 < τ := lt_of_le_of_lt (le_max_left _ _) hτ.1
  have hτ1 : τ < 1 := lt_of_lt_of_le hτ.2 (min_le_left _ _)
  have hτb : τ ∈ Metric.ball b η := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor
    · have := lt_of_le_of_lt (le_max_right 0 (b - η)) hτ.1; linarith
    · have := lt_of_lt_of_le hτ.2 (min_le_right 1 (b + η)); linarith
  have hyball : γ τ ∈ Metric.ball x δ := hηsub hτb
  have hyopen : γ τ ∈ openSegment ℝ u₁ u₂ := by
    rw [openSegment_eq_image']; exact ⟨τ, ⟨hτ0, hτ1⟩, rfl⟩
  have hf' : (-f : Plane →ₗ[ℝ] ℝ) ≠ 0 := fun h => hf (neg_eq_zero.mp h)
  have hS : segment ℝ u₁ u₂ ⊆ {y | (-f) y = -c} := by
    intro y hy
    have := D.lineChain_edge_subset he y hy
    simp only [mem_setOf_eq, LinearMap.neg_apply, this]
  have hwall : ∀ y ∈ openSegment ℝ u₁ u₂, ∀ i, y ∉ interior (D.tile i).carrier :=
    fun y hy i => D.edge_point_not_interior (openSegment_subset_segment ℝ _ _ hy : y ∈ (D.tile e.1).edge e.2) i
  obtain ⟨e', he', hye'⟩ := D.wall_cover (-f) (-c) hf' hu hS (hch e he) hwall hyopen hyV
  have hyU : γ τ ∈ U := by
    simp only [hU, mem_iUnion]; exact ⟨e', he', hye'⟩
  exact hball hyball hyU

variable {N : ℕ}

/-- **`Σ⁺ = Σ⁻`** (as sets of line parameters): on a line through an interior point of the target,
the near-side and far-side chains cover the same parameters. -/
theorem sig_iff {D : Dissection N} {d O r : Plane} (hd : d ≠ 0)
    (hr : r ∈ interior D.target.carrier) (hrl : cross d (r - O) = 0) (t : ℝ) :
    InSig (D.lineChain (crossL d) (cross d O)) (eLo D O d) (eHi D O d) t ↔
      InSig (D.lineChain (-(crossL d)) (-(cross d O))) (eLo D O d) (eHi D O d) t := by
  have hf : crossL d ≠ 0 := crossL_ne_zero hd
  have hf' : (-(crossL d) : Plane →ₗ[ℝ] ℝ) ≠ 0 := fun h => hf (neg_eq_zero.mp h)
  constructor
  · rintro ⟨e, he, hl, hh⟩
    have hon := onLine_of_mem_lineChain he
    have hmem := (pt_mem_edge_iff hd hon t).mpr ⟨hl, hh⟩
    obtain ⟨e', he', hx⟩ := cover_other D (crossL d) (cross d O) hf
      (fun e he => openEdge_interior D hd hr hrl (onLine_of_mem_lineChain he)) he hmem
    have hon' := onLine_of_mem_lineChain_neg he'
    exact ⟨e', he', (pt_mem_edge_iff hd hon' t).mp hx⟩
  · rintro ⟨e, he, hl, hh⟩
    have hon := onLine_of_mem_lineChain_neg he
    have hmem := (pt_mem_edge_iff hd hon t).mpr ⟨hl, hh⟩
    obtain ⟨e', he', hx⟩ := cover_other D (-(crossL d)) (-(cross d O)) hf'
      (fun e he => openEdge_interior D hd hr hrl (onLine_of_mem_lineChain_neg he)) he hmem
    rw [neg_neg, neg_neg] at he'
    have hon' := onLine_of_mem_lineChain he'
    exact ⟨e', he', (pt_mem_edge_iff hd hon' t).mp hx⟩

end Erdos634.H1gPos

#print axioms Erdos634.H1gPos.cover_other
#print axioms Erdos634.H1gPos.sig_iff

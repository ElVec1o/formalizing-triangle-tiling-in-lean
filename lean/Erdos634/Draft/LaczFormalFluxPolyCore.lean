-- Draft/LaczFormalFluxPolyCore.lean -- FLUX-CANCELLATION for polygon targets, part 2: edge-level objects of a `RegionDissection` and the interior
-- cancellation `sum over interior edges of len(e) * f(dir e) = 0` for an odd direction weight f, under the single geometric hypothesis `EdgeDich`
-- (a tile edge with one non-endpoint point off the interior of the region has NO point in the interior: true for a convex polygon, proved in
-- LaczFormalFluxPolyBdy).  Port of Draft/FluxCore.lean, Draft/FluxInterior.lean (target-free versions); uses LaczFormalFluxPolyInt.
-- NOTE / UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 7.3/8.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalFluxPolyInt
import Erdos634.Draft.FluxCore

open scoped Classical
open MeasureTheory Set Erdos634.Geometry
open scoped ENNReal
set_option linter.dupNamespace false

namespace Erdos634.RegionDissection

variable {N : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Length of tile edge `e = (i, k)`. -/
noncomputable def RegionDissection.eLen (D : RegionDissection N) (e : Fin N × Fin 3) : ℝ :=
  dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))

/-- Left-hand unit direction of tile edge `e`. -/
noncomputable def RegionDissection.eDir (D : RegionDissection N) (e : Fin N × Fin 3) : Dir := (D.tile e.1).leftUnit e.2

/-- Point set of tile edge `e`. -/
def RegionDissection.eSet (D : RegionDissection N) (e : Fin N × Fin 3) : Set Plane := (D.tile e.1).edge e.2

/-- The tile edges that contain a point interior to the region (the "interior edges"). -/
noncomputable def RegionDissection.intEdges (D : RegionDissection N) : Finset (Fin N × Fin 3) :=
  Finset.univ.filter fun e => ∃ x ∈ D.eSet e, x ∈ interior D.region

/-- **Edge dichotomy** (hypothesis, true for convex polygons): if one non-endpoint point of a tile edge is off the interior of the region, then no
point of the edge is interior to the region. -/
def RegionDissection.EdgeDich (D : RegionDissection N) : Prop :=
  ∀ e : Fin N × Fin 3, ∀ x ∈ D.eSet e, x ≠ (D.tile e.1).pts e.2 → x ≠ (D.tile e.1).pts (e.2 + 1) →
    x ∉ interior D.region → ∀ y ∈ D.eSet e, y ∉ interior D.region

theorem RegionDissection.mem_interior_of_mem_intEdges (D : RegionDissection N) (hd : D.EdgeDich) {e : Fin N × Fin 3}
    (he : e ∈ D.intEdges) {x : Plane} (hx : x ∈ D.eSet e)
    (hx1 : x ≠ (D.tile e.1).pts e.2) (hx2 : x ≠ (D.tile e.1).pts (e.2 + 1)) : x ∈ interior D.region := by
  by_contra hxn
  obtain ⟨y, hy, hyi⟩ := (Finset.mem_filter.mp he).2
  exact hd e x hx hx1 hx2 hxn y hy hyi

theorem RegionDissection.mem_intEdges_of_interior (D : RegionDissection N) {e : Fin N × Fin 3} {x : Plane}
    (hx : x ∈ D.eSet e) (hxi : x ∈ interior D.region) : e ∈ D.intEdges :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hx, hxi⟩

/-- The sum of the tiles' fluxes is a sum over all `3N` tile edges. -/
theorem RegionDissection.flux_sum_eq (D : RegionDissection N) (f : Dir → E) :
    ∑ i, (D.tile i).flux f = ∑ e : Fin N × Fin 3, D.eLen e • f (D.eDir e) := by
  rw [Fintype.sum_prod_type]
  rfl

theorem RegionDissection.eLen_nonneg (D : RegionDissection N) (e : Fin N × Fin 3) : 0 ≤ D.eLen e := dist_nonneg

/-- **Same-direction exclusion (M3).**  Two distinct tile edges with the same left-hand direction
meet in at most one point.  (At the midpoint of two common points both edges carry `OnEdge` data;
the same tile gives a coordinate clash, two tiles give opposite directions by
`Dissection.leftUnit_neg`.) -/
theorem RegionDissection.sameDir_subsingleton (D : RegionDissection N) {e₁ e₂ : Fin N × Fin 3}
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
/-- `W(e,e')`: the length of the overlap of two tile edges. -/
noncomputable def RegionDissection.overlap (D : RegionDissection N) (e e' : Fin N × Fin 3) : ℝ :=
  ((Measure.hausdorffMeasure 1 : Measure Plane) (D.eSet e ∩ D.eSet e')).toReal

theorem RegionDissection.overlap_comm (D : RegionDissection N) (e e' : Fin N × Fin 3) :
    D.overlap e e' = D.overlap e' e := by
  unfold RegionDissection.overlap
  rw [Set.inter_comm]

/-- **(M4) Opposite covering, in `μH¹`.**  An interior edge `e` is covered exactly once, up to
the finite vertex set, by the interior edges carrying the reversed direction. -/
theorem RegionDissection.opposite_cover (D : RegionDissection N) (hN : 0 < N) (hd : D.EdgeDich) {e : Fin N × Fin 3} (he : e ∈ D.intEdges) :
    ∑ e' ∈ D.intEdges.filter (fun e' => D.eDir e' = Dir.neg (D.eDir e)),
        (Measure.hausdorffMeasure 1 : Measure Plane) (D.eSet e' ∩ D.eSet e)
      = (Measure.hausdorffMeasure 1 : Measure Plane) (D.eSet e) := by
  refine sum_hausdorff_of_partition _ (fun e' => D.eSet e' ∩ D.eSet e) (D.eSet e) D.vertexSet
    D.vertexSet_finite ?_ ?_ ?_ ?_
  · intro e' _
    exact (((D.tile e'.1).isClosed_edge e'.2).inter
      ((D.tile e.1).isClosed_edge e.2)).measurableSet
  · intro e₁ h₁ e₂ h₂ hne
    have hd₁ := (Finset.mem_filter.mp h₁).2
    have hd₂ := (Finset.mem_filter.mp h₂).2
    exact (D.sameDir_subsingleton hne (hd₁.trans hd₂.symm)).anti
      (fun y hy => ⟨hy.1.1, hy.2.1⟩)
  · intro e' _
    exact Set.inter_subset_right
  · rintro x ⟨hx, hxv⟩
    have hnv := D.notMem_vertexSet hxv
    have hxint : x ∈ interior D.region :=
      D.mem_interior_of_mem_intEdges hd he hx (hnv _ _) (hnv _ _)
    have hxd : x ∈ D.dirSet (D.eDir e) := by
      unfold RegionDissection.dirSet
      exact ⟨Set.mem_iUnion.mpr ⟨e.1, Set.mem_iUnion.mpr ⟨e.2, Set.mem_iUnion.mpr ⟨rfl, hx⟩⟩⟩,
        hxint⟩
    have hxd' := (D.dirSet_sub hN (D.eDir e) ⟨hxd, hxv⟩).1
    obtain ⟨i, k, hik, hxik⟩ := D.mem_dirSet _ hxd'
    refine Set.mem_iUnion₂.mpr ⟨(i, k), ?_, hxik, hx⟩
    rw [Finset.mem_filter]
    exact ⟨D.mem_intEdges_of_interior (e := (i, k)) hxik hxint, hik⟩

/-- The opposite covering in real lengths, over all interior edges. -/
theorem RegionDissection.opposite_cover_real (D : RegionDissection N) (hN : 0 < N) (hd : D.EdgeDich) {e : Fin N × Fin 3}
    (he : e ∈ D.intEdges) :
    ∑ e' ∈ D.intEdges, (if D.eDir e' = Dir.neg (D.eDir e) then D.overlap e' e else 0)
      = D.eLen e := by
  rw [← Finset.sum_filter]
  have hfin : ∀ e' ∈ D.intEdges.filter (fun e' => D.eDir e' = Dir.neg (D.eDir e)),
      (Measure.hausdorffMeasure 1 : Measure Plane) (D.eSet e' ∩ D.eSet e) ≠ ⊤ := by
    intro e' _
    refine ne_top_of_le_ne_top ?_ (measure_mono Set.inter_subset_right)
    rw [show D.eSet e = (D.tile e.1).edge e.2 from rfl, Tri.hausdorff_edge]
    exact edist_ne_top _ _
  unfold RegionDissection.overlap
  rw [← ENNReal.toReal_sum hfin, D.opposite_cover hN hd he,
    show D.eSet e = (D.tile e.1).edge e.2 from rfl, Tri.hausdorff_edge, edist_dist,
    ENNReal.toReal_ofReal dist_nonneg]
  rfl

/-- **Interior cancellation.**  For an odd weight the interior edges contribute nothing:
double counting over the overlap matrix gives `X = −X`. -/
theorem RegionDissection.interior_flux_zero (D : RegionDissection N) (hN : 0 < N) (hd : D.EdgeDich) (f : Dir → E)
    (hodd : ∀ d, f (Dir.neg d) = - f d) :
    ∑ e ∈ D.intEdges, D.eLen e • f (D.eDir e) = 0 := by
  set I := D.intEdges with hI
  let A : Fin N × Fin 3 → Fin N × Fin 3 → ℝ := fun e e' =>
    if D.eDir e' = Dir.neg (D.eDir e) then D.overlap e' e else 0
  set X := ∑ e ∈ I, D.eLen e • f (D.eDir e) with hX
  have h1 : X = ∑ e ∈ I, ∑ e' ∈ I, A e e' • f (D.eDir e) := by
    refine Finset.sum_congr rfl fun e he => ?_
    rw [← Finset.sum_smul]
    congr 1
    exact (D.opposite_cover_real hN hd he).symm
  have hterm : ∀ e e', A e e' • f (D.eDir e) = -(A e' e • f (D.eDir e')) := by
    intro e e'
    by_cases h : D.eDir e' = Dir.neg (D.eDir e)
    · have h' : D.eDir e = Dir.neg (D.eDir e') := by rw [h, Dir.neg_involutive (D.eDir e)]
      have hA : A e e' = D.overlap e' e := if_pos h
      have hA' : A e' e = D.overlap e e' := if_pos h'
      rw [hA, hA', h', hodd, D.overlap_comm e' e, smul_neg]
    · have h' : ¬ D.eDir e = Dir.neg (D.eDir e') := fun h'' =>
        h (by rw [h'', Dir.neg_involutive (D.eDir e')])
      have hA : A e e' = 0 := if_neg h
      have hA' : A e' e = 0 := if_neg h'
      rw [hA, hA', zero_smul, zero_smul, neg_zero]
  have h2 : X = -X := by
    calc X = ∑ e ∈ I, ∑ e' ∈ I, A e e' • f (D.eDir e) := h1
      _ = ∑ e' ∈ I, ∑ e ∈ I, A e e' • f (D.eDir e) := Finset.sum_comm
      _ = ∑ e' ∈ I, ∑ e ∈ I, -(A e' e • f (D.eDir e')) :=
          Finset.sum_congr rfl fun e' _ => Finset.sum_congr rfl fun e _ => hterm e e'
      _ = -∑ e' ∈ I, ∑ e ∈ I, A e' e • f (D.eDir e') := by
          simp only [Finset.sum_neg_distrib]
      _ = -X := by rw [h1]
  have h3 : (2:ℝ) • X = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h2]
    exact neg_add_cancel X
  calc X = (2:ℝ)⁻¹ • ((2:ℝ) • X) := by
        rw [smul_smul, inv_mul_cancel₀ (two_ne_zero), one_smul]
    _ = 0 := by rw [h3, smul_zero]

end Erdos634.RegionDissection

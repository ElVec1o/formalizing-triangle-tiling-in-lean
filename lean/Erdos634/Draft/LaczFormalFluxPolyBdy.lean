-- Draft/LaczFormalFluxPolyBdy.lean -- FLUX-CANCELLATION for polygon targets, part 3: polygon-specific facts (sides carry c_j = 0, interior points have all c_j > 0,
-- the edge dichotomy `EdgeDich`, edge-on-side classification, distinct sides share no tile edge).
-- NOTE / UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 7.3/8.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalFluxPolyCore
import Erdos634.Draft.LaczFormalThm21Loc

open scoped Classical
open MeasureTheory Set Erdos634.Geometry Erdos634.RegionDissection
set_option linter.dupNamespace false

namespace Erdos634.Draft.LaczFormal.Thm21

variable {N M : ℕ} [NeZero M]

namespace ConvPoly
variable (P : ConvPoly M)

/-- The `j`-th side as a closed segment. -/
def sideSet (j : Fin M) : Set Plane := segment ℝ (P.v j) (P.v (j + 1))

theorem c_bilin_sub (j : Fin M) (x u : Plane) (t : ℝ) : P.c j (x - t • u) = P.c j x - t * cross2 (P.e j) u := by
  unfold c cross2; simp; ring

theorem c_sideSet {j : Fin M} {x : Plane} (hx : x ∈ P.sideSet j) : P.c j x = 0 := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hx
  have : a = 1 - b := by linarith
  subst this
  rw [P.c_comb, P.c_self, P.c_next]; ring

theorem v_mem_carrier (k : Fin M) : P.v k ∈ P.carrier := by
  intro j
  by_cases h1 : k = j
  · subst h1; have := P.c_self k; show 0 ≤ P.c k (P.v k); linarith
  by_cases h2 : k = j + 1
  · subst h2; have := P.c_next j; show 0 ≤ P.c j _; linarith
  · exact (P.c_vertex_pos h1 h2).le

theorem sideSet_sub_carrier (j : Fin M) : P.sideSet j ⊆ P.carrier := by
  have hc : Convex ℝ P.carrier := by
    have : P.carrier = ⋂ i : Fin M, {z : Plane | 0 ≤ cross2 (P.e i) (z - P.v i)} := by
      ext z; simp [carrier, e]
    rw [this]
    exact convex_iInter fun i => halfplane_convex (P.e i) (P.v i)
  exact hc.segment_subset (P.v_mem_carrier j) (P.v_mem_carrier (j + 1))

/-- **Interior points of the polygon satisfy every edge constraint strictly.** -/
theorem c_pos_of_interior {x : Plane} (hx : x ∈ interior P.carrier) (j : Fin M) : 0 < P.c j x := by
  have hnn : 0 ≤ P.c j x := interior_subset hx j
  by_contra hneg
  have h0 : P.c j x = 0 := le_antisymm (not_lt.mp hneg) hnn
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
  have hM := P.three_le
  obtain ⟨-, h2, h3, -⟩ := fin_facts hM j
  set u : Plane := P.v (j + 2) - P.v j with hu
  have hpos : 0 < cross2 (P.e j) u := by
    have := P.c_vertex_pos (j := j) (m := j + 2) h2 h3
    simpa [c] using this
  set t : ℝ := ε / (2 * (‖u‖ + 1)) with ht
  have htpos : 0 < t := by positivity
  have hy : x - t • u ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    have : x - (x - t • u) = t • u := by abel
    rw [show x - t • u - x = -(t • u) by abel, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
    have h1 : t * ‖u‖ ≤ t * (‖u‖ + 1) := by nlinarith [norm_nonneg u]
    have h2 : t * (‖u‖ + 1) = ε / 2 := by rw [ht]; field_simp
    linarith
  have hmem : x - t • u ∈ P.carrier := interior_subset (hball hy)
  have : 0 ≤ P.c j (x - t • u) := hmem j
  rw [P.c_bilin_sub, h0] at this
  nlinarith

theorem not_interior_of_sideSet {j : Fin M} {x : Plane} (hx : x ∈ P.sideSet j) : x ∉ interior P.carrier := by
  intro h
  have := P.c_pos_of_interior h j
  rw [P.c_sideSet hx] at this
  exact lt_irrefl _ this

end ConvPoly

theorem _root_.Erdos634.RegionDissection.RegionDissection.tile_sub_region (R : RegionDissection N) (i : Fin N) : (R.tile i).carrier ⊆ R.region := by
  rw [← R.covers]; exact Set.subset_iUnion (fun k => (R.tile k).carrier) i

theorem _root_.Erdos634.RegionDissection.RegionDissection.pts_mem_region (R : RegionDissection N) (i : Fin N) (k : Fin 3) : (R.tile i).pts k ∈ R.region :=
  R.tile_sub_region i (subset_convexHull ℝ _ ⟨k, rfl⟩)

namespace ConvPoly
variable (P : ConvPoly M)

/-- **A tile edge with a non-endpoint point off the polygon interior lies on one side.** -/
theorem edge_on_side (R : RegionDissection N) (hR : R.region = P.carrier) (e : Fin N × Fin 3) {x : Plane}
    (hx : x ∈ R.eSet e) (h1 : x ≠ (R.tile e.1).pts e.2) (h2 : x ≠ (R.tile e.1).pts (e.2 + 1))
    (hxn : x ∉ interior P.carrier) : ∃ j, R.eSet e ⊆ P.sideSet j := by
  have hM := P.three_le
  set a := (R.tile e.1).pts e.2 with ha
  set b := (R.tile e.1).pts (e.2 + 1) with hb
  have haC : a ∈ P.carrier := hR ▸ R.pts_mem_region e.1 e.2
  have hbC : b ∈ P.carrier := hR ▸ R.pts_mem_region e.1 (e.2 + 1)
  have hxC : x ∈ P.carrier := hR ▸ R.tile_sub_region e.1 (by
    have : R.eSet e ⊆ (R.tile e.1).carrier := (R.tile e.1).edge_subset_carrier e.2
    exact this hx)
  have hj : ∃ j, P.c j x = 0 := by
    by_contra hcon
    push Not at hcon
    exact hxn (P.interior_of_pos fun j => lt_of_le_of_ne (hxC j) (Ne.symm (hcon j)))
  obtain ⟨j, hj⟩ := hj
  obtain ⟨s, t, hs, ht, hst, hxe⟩ := hx
  have ht1 : s = 1 - t := by linarith
  subst ht1
  have hs0 : 0 < 1 - t := by
    rcases hs.lt_or_eq with h | h
    · exact h
    · exfalso; apply h2; have h' : t = 1 := by linarith
      rw [← hxe, h']; simp [hb]
  have ht0 : 0 < t := by
    rcases ht.lt_or_eq with h | h
    · exact h
    · exfalso; apply h1; rw [← hxe, ← h]; simp [ha]
  rw [← hxe, P.c_comb] at hj
  have hca : 0 ≤ P.c j a := haC j
  have hcb : 0 ≤ P.c j b := hbC j
  have hza : P.c j a = 0 := by nlinarith [mul_nonneg hs hca, mul_nonneg ht hcb, mul_pos hs0 ht0]
  have hzb : P.c j b = 0 := by nlinarith [mul_nonneg hs hca, mul_nonneg ht hcb, mul_pos hs0 ht0]
  refine ⟨j, ?_⟩
  have hseg : ∀ V, V ∈ P.carrier → P.c j V = 0 → V ∈ P.sideSet j := by
    intro V hV h0
    obtain ⟨t, ht, hW⟩ := P.edge_param hM hV h0
    exact ⟨1 - t, t, by linarith [ht.2], ht.1, by ring, hW.symm⟩
  exact (convex_segment (P.v j) (P.v (j + 1))).segment_subset (hseg a haC hza) (hseg b hbC hzb)

/-- The polygon satisfies the edge dichotomy `EdgeDich`. -/
theorem edgeDich (R : RegionDissection N) (hR : R.region = P.carrier) : R.EdgeDich := by
  intro e x hx h1 h2 hxn y hy
  rw [hR] at hxn ⊢
  obtain ⟨j, hj⟩ := P.edge_on_side R hR e hx h1 h2 hxn
  exact P.not_interior_of_sideSet (hj hy)

end ConvPoly

end Erdos634.Draft.LaczFormal.Thm21

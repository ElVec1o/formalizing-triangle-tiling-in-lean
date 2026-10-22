-- Draft/H1fNGEdge.lean — ATOM H1.f, second half: the form of NG that L1 (H1.g) consumes.
--   adjacency in `nbrGraph D` gives a positive-length segment lying on an EDGE of each tile, and the
--   two edges are parallel with the same supporting line (a common point and proportional vectors).
-- Formalization debt; NOT /goal progress.  Standard axioms, no sorry.
import Erdos634.Draft.H1fNG

open MeasureTheory Set

namespace Erdos634.H1fNG

open Erdos634.Geometry

/-- Nonnegative variant of `Tri.mem_edge_of_coord_zero`. -/
theorem mem_edge_of_coord_zero_nonneg (T : Tri) {m : Fin 3} {x : Plane}
    (hm : T.basis.coord m x = 0) (ho : ∀ j, 0 ≤ T.basis.coord j x) :
    x ∈ T.edge (m + 1) := by
  have hsum := T.basis.sum_coord_apply_eq_one x
  have hcomb := T.basis.linear_combination_coord_eq_self x
  refine ⟨T.basis.coord (m + 1) x, T.basis.coord (m + 1 + 1) x, ho _, ho _, ?_, ?_⟩
  · have hthree : ∀ c : Fin 3 → ℝ, ∑ i, c i = c m + c (m + 1) + c (m + 1 + 1) := by
      intro c; fin_cases m <;> simp [Fin.sum_univ_three] <;> ring
    rw [hthree] at hsum; rw [hm, zero_add] at hsum; exact hsum
  · have hthree : ∀ c : Fin 3 → Plane, ∑ i, c i = c m + c (m + 1) + c (m + 1 + 1) := by
      intro c; fin_cases m <;> simp [Fin.sum_univ_three] <;> abel
    rw [hthree] at hcomb
    simpa [hm, zero_smul] using hcomb

/-- Points of a triangle not in its interior have a vanishing barycentric coordinate. -/
theorem exists_coord_zero (T : Tri) {p : Plane} (hp : p ∈ T.carrier) (hn : p ∉ interior T.carrier) :
    ∃ m, T.basis.coord m p = 0 := by
  by_contra hcon
  push Not at hcon
  apply hn
  have hint : interior (convexHull ℝ (Set.range (T.basis : Fin 3 → Plane))) =
      {x | ∀ i, 0 < T.basis.coord i x} := T.basis.interior_convexHull
  have h : Set.range T.pts = Set.range (T.basis : Fin 3 → Plane) := rfl
  rw [Tri.carrier, h, hint]
  intro i
  have hp' := hp
  rw [T.carrier_eq_nonneg_coord] at hp'
  exact lt_of_le_of_ne (hp' i) (Ne.symm (hcon i))

theorem lineMap_mem_segment' (x y : Plane) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    x + t • (y - x) ∈ segment ℝ x y := by
  refine ⟨1 - t, t, by linarith, h0, by ring, ?_⟩
  module

/-- **A boundary segment lies in an edge** (after shrinking to a positive-length subsegment). -/
theorem seg_boundary_in_edge (T : Tri) {x y : Plane} (hxy : x ≠ y)
    (hs : segment ℝ x y ⊆ T.carrier) (hb : ∀ p ∈ segment ℝ x y, p ∉ interior T.carrier) :
    ∃ (k : Fin 3) (u v : Plane), u ≠ v ∧ segment ℝ u v ⊆ segment ℝ x y ∧
      segment ℝ u v ⊆ T.edge k := by
  classical
  let P : Fin 4 → Plane := fun n => x + ((n : ℕ) / 3 : ℝ) • (y - x)
  have hPmem : ∀ n, P n ∈ segment ℝ x y := by
    intro n
    apply lineMap_mem_segment'
    · positivity
    · have : ((n : ℕ) : ℝ) ≤ 3 := by exact_mod_cast Nat.lt_succ_iff.mp n.2
      rw [div_le_one (by norm_num)]; exact this
  have hPinj : Function.Injective P := by
    intro a b hab
    have h1 : (((a : ℕ) / 3 : ℝ)) • (y - x) = (((b : ℕ) / 3 : ℝ)) • (y - x) := add_left_cancel hab
    have hne : y - x ≠ 0 := sub_ne_zero.mpr hxy.symm
    have h2 := smul_left_injective ℝ hne h1
    have : ((a : ℕ) : ℝ) = ((b : ℕ) : ℝ) := by linarith
    exact Fin.ext (by exact_mod_cast this)
  have hex : ∀ n, ∃ m, T.basis.coord m (P n) = 0 := fun n =>
    exists_coord_zero T (hs (hPmem n)) (hb _ (hPmem n))
  choose f hf using hex
  obtain ⟨a, b, hab, hfab⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
  refine ⟨f a + 1, P a, P b, fun h => hab (hPinj h), ?_, ?_⟩
  · exact (convex_segment x y).segment_subset (hPmem a) (hPmem b)
  · have hconv : Convex ℝ ((T.basis.coord (f a)) ⁻¹' {(0 : ℝ)}) :=
      (convex_singleton (0 : ℝ)).affine_preimage _
    intro w hw
    have hw0 : T.basis.coord (f a) w = 0 := by
      have := hconv.segment_subset (by simpa using hf a) (by simpa [hfab] using hf b) hw
      simpa using this
    have hwc : w ∈ T.carrier := hs ((convex_segment x y).segment_subset (hPmem a) (hPmem b) hw)
    have hwn : ∀ j, 0 ≤ T.basis.coord j w := by
      have := hwc; rw [T.carrier_eq_nonneg_coord] at this; exact this
    exact mem_edge_of_coord_zero_nonneg T hw0 hwn

/-- Parameter form of an edge point. -/
theorem edge_param (T : Tri) {k : Fin 3} {u : Plane} (hu : u ∈ T.edge k) :
    ∃ b : ℝ, u = T.pts k + b • (T.pts (k + 1) - T.pts k) := by
  obtain ⟨a, b, _, _, hab, rfl⟩ := hu
  refine ⟨b, ?_⟩
  have : a = 1 - b := by linarith
  subst this
  module

/-- **Two edges sharing a positive-length segment are parallel**, with proportional vectors. -/
theorem edge_parallel_of_shared (T T' : Tri) {k l : Fin 3} {u v : Plane} (huv : u ≠ v)
    (h1 : segment ℝ u v ⊆ T.edge k) (h2 : segment ℝ u v ⊆ T'.edge l) :
    ∃ r : ℝ, r ≠ 0 ∧ T.pts (k + 1) - T.pts k = r • (T'.pts (l + 1) - T'.pts l) := by
  obtain ⟨b1, hb1⟩ := edge_param T (h1 (left_mem_segment ℝ u v))
  obtain ⟨b2, hb2⟩ := edge_param T (h1 (right_mem_segment ℝ u v))
  obtain ⟨c1, hc1⟩ := edge_param T' (h2 (left_mem_segment ℝ u v))
  obtain ⟨c2, hc2⟩ := edge_param T' (h2 (right_mem_segment ℝ u v))
  have e1 : u - v = (b1 - b2) • (T.pts (k + 1) - T.pts k) := by
    rw [hb1, hb2]; module
  have e2 : u - v = (c1 - c2) • (T'.pts (l + 1) - T'.pts l) := by
    rw [hc1, hc2]; module
  have hne : u - v ≠ 0 := sub_ne_zero.mpr huv
  have hb : b1 - b2 ≠ 0 := fun h => hne (by rw [e1, h, zero_smul])
  have hc : c1 - c2 ≠ 0 := fun h => hne (by rw [e2, h, zero_smul])
  refine ⟨(c1 - c2) / (b1 - b2), div_ne_zero hc hb, ?_⟩
  have : (b1 - b2) • (T.pts (k + 1) - T.pts k) = (c1 - c2) • (T'.pts (l + 1) - T'.pts l) :=
    e1.symm.trans e2
  calc T.pts (k + 1) - T.pts k
      = (b1 - b2)⁻¹ • ((b1 - b2) • (T.pts (k + 1) - T.pts k)) := by
        rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
    _ = ((c1 - c2) / (b1 - b2)) • (T'.pts (l + 1) - T'.pts l) := by
        rw [this, smul_smul]; congr 1; field_simp

/-- **NG in the form L1 consumes.**  Adjacent tiles have edges `k`, `l` containing a common
positive-length segment (hence on one line, with proportional edge vectors). -/
theorem adj_shared_edge {N : ℕ} (D : Dissection N) {i j : Fin N} (h : (nbrGraph D).Adj i j) :
    ∃ (k l : Fin 3) (u v : Plane), u ≠ v ∧
      segment ℝ u v ⊆ (D.tile i).edge k ∧ segment ℝ u v ⊆ (D.tile j).edge l := by
  obtain ⟨hij, x, y, hxy, hs⟩ := h
  have hsi : segment ℝ x y ⊆ (D.tile i).carrier := fun p hp => (hs hp).1
  have hsj : segment ℝ x y ⊆ (D.tile j).carrier := fun p hp => (hs hp).2
  have hbi : ∀ p ∈ segment ℝ x y, p ∉ interior (D.tile i).carrier := fun p hp hint =>
    Dissection'.not_mem_of_mem_interior D hij hint (hsj hp)
  have hbj : ∀ p ∈ segment ℝ x y, p ∉ interior (D.tile j).carrier := fun p hp hint =>
    Dissection'.not_mem_of_mem_interior D hij.symm hint (hsi hp)
  obtain ⟨k, u, v, huv, hsub, hk⟩ := seg_boundary_in_edge (D.tile i) hxy hsi hbi
  have hsj' : segment ℝ u v ⊆ (D.tile j).carrier := hsub.trans hsj
  have hbj' : ∀ p ∈ segment ℝ u v, p ∉ interior (D.tile j).carrier := fun p hp => hbj p (hsub hp)
  obtain ⟨l, u', v', huv', hsub', hl⟩ := seg_boundary_in_edge (D.tile j) huv hsj' hbj'
  exact ⟨k, l, u', v', huv', (hsub'.trans hk), hl⟩

/-- Corollary: adjacent tiles have an edge each, parallel (proportional vectors). -/
theorem adj_edges_parallel {N : ℕ} (D : Dissection N) {i j : Fin N} (h : (nbrGraph D).Adj i j) :
    ∃ (k l : Fin 3) (r : ℝ), r ≠ 0 ∧
      (D.tile i).pts (k + 1) - (D.tile i).pts k = r • ((D.tile j).pts (l + 1) - (D.tile j).pts l) := by
  obtain ⟨k, l, u, v, huv, h1, h2⟩ := adj_shared_edge D h
  obtain ⟨r, hr, e⟩ := edge_parallel_of_shared _ _ huv h1 h2
  exact ⟨k, l, r, hr, e⟩

end Erdos634.H1fNG

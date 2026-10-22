import Erdos634.AngleSumDissection
import Erdos634.WallChain

/-!
# Band junction rules: the chord geometry inside a triangle

Erdős #634, base-`β` band; companion of `LaczFormalJunctionAngle.lean`.  Credit: AI assistant (band lemma
/ item-3 proposal), Beeson–Roșu, Beeson, Laczkovich, Paliy.

A chord `[P,G]` of a triangle `T` joining a point `P` strictly inside side `[A₀,A₁]` to a point `G`
strictly inside side `[A₀,A₂]` has its open part in the interior of `T`, and the line through it
leaves `T` immediately beyond each end.  Pure barycentric computation.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.LaczJunction

open Erdos634.Geometry

theorem coord_combo (T : Tri) (k : Fin 3) {x y : Plane} {s t : ℝ} (h : s + t = 1) :
    T.basis.coord k (s • x + t • y) = s * T.basis.coord k x + t * T.basis.coord k y := by
  have := Convex.combo_affine_apply (f := T.basis.coord k) h (x := x) (y := y)
  simpa using this

theorem coord_vertex (T : Tri) (k j : Fin 3) :
    T.basis.coord k (T.pts j) = if k = j then 1 else 0 := by
  have : T.pts j = T.basis j := rfl
  rw [this, AffineBasis.coord_apply]

theorem fin3_cover (p q r j : Fin 3) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    j = p ∨ j = q ∨ j = r := by
  revert p q r j; decide

/-- Barycentric coordinates of a point strictly inside side `[A_p, A_q]` (`r` the third vertex). -/
theorem coords_side (T : Tri) {p q r : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {P : Plane} (hP : P ∈ openSegment ℝ (T.pts p) (T.pts q)) :
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧ T.basis.coord p P = 1 - s ∧ T.basis.coord q P = s ∧
      T.basis.coord r P = 0 := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hP
  refine ⟨b, hb, by linarith, ?_, ?_, ?_⟩ <;> rw [coord_combo T _ hab] <;>
    simp [coord_vertex, hpq, hpq.symm, hpr, hpr.symm, hqr, hqr.symm] <;> linarith

/-- Coordinates along the line through `P` and `G`. -/
theorem coord_lineMap (T : Tri) (k : Fin 3) (P G : Plane) (t : ℝ) :
    T.basis.coord k (AffineMap.lineMap P G t)
      = (1 - t) * T.basis.coord k P + t * T.basis.coord k G := by
  rw [AffineMap.apply_lineMap, AffineMap.lineMap_apply]
  simp [smul_eq_mul]; ring

/-- **Chord geometry**: `P` strictly inside side `[A_p,A_q]`, `G` strictly inside side `[A_p,A_r]`. -/
theorem chord_geometry (T : Tri) {p q r : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {P G : Plane}
    (hP : P ∈ openSegment ℝ (T.pts p) (T.pts q)) (hG : G ∈ openSegment ℝ (T.pts p) (T.pts r)) :
    (∀ t : ℝ, 0 < t → t < 1 → AffineMap.lineMap P G t ∈ interior T.carrier) ∧
    (∀ t : ℝ, t < 0 → AffineMap.lineMap P G t ∉ T.carrier) ∧
    (∀ t : ℝ, 1 < t → AffineMap.lineMap P G t ∉ T.carrier) := by
  obtain ⟨s, hs0, hs1, p0, p1, p2⟩ := coords_side T hpq hpr hqr hP
  obtain ⟨u, hu0, hu1, g0, g2, g1⟩ := coords_side T hpr hpq hqr.symm hG
  refine ⟨?_, ?_, ?_⟩
  · intro t ht0 ht1
    rw [T.mem_interior_iff_coord_pos]
    intro j
    rw [coord_lineMap]
    rcases fin3_cover p q r j hpq hpr hqr with rfl | rfl | rfl
    · rw [p0, g0]; nlinarith
    · rw [p1, g1]; nlinarith
    · rw [p2, g2]; nlinarith
  · intro t ht h
    rw [T.carrier_eq_nonneg_coord] at h
    have := h r
    rw [coord_lineMap, p2, g2] at this
    nlinarith
  · intro t ht h
    rw [T.carrier_eq_nonneg_coord] at h
    have := h q
    rw [coord_lineMap, p1, g1] at this
    nlinarith

/-- **Chord geometry, `G` off the base line**: `P` strictly inside side `[A_p,A_q]`, `G` in the
target with positive `r`-coordinate (`r` the vertex opposite that side). -/
theorem chord_geometry_int (T : Tri) {p q r : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {P G : Plane} (hP : P ∈ openSegment ℝ (T.pts p) (T.pts q)) (hGc : G ∈ T.carrier)
    (hGr : 0 < T.basis.coord r G) :
    (∀ t : ℝ, 0 < t → t < 1 → AffineMap.lineMap P G t ∈ interior T.carrier) ∧
    (∀ t : ℝ, t < 0 → AffineMap.lineMap P G t ∉ T.carrier) := by
  obtain ⟨s, hs0, hs1, p0, p1, p2⟩ := coords_side T hpq hpr hqr hP
  rw [T.carrier_eq_nonneg_coord] at hGc
  refine ⟨?_, ?_⟩
  · intro t ht0 ht1
    rw [T.mem_interior_iff_coord_pos]
    intro j
    rw [coord_lineMap]
    have h1 := hGc j
    rcases fin3_cover p q r j hpq hpr hqr with rfl | rfl | rfl
    · rw [p0]; nlinarith
    · rw [p1]; nlinarith
    · rw [p2]; nlinarith
  · intro t ht h
    rw [T.carrier_eq_nonneg_coord] at h
    have := h r
    rw [coord_lineMap, p2] at this
    nlinarith

end Erdos634.LaczJunction

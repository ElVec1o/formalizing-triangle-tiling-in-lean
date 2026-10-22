-- Draft/LaczFormalIVcRatB3.lean -- Laczkovich DCG 48 (2012), Sect. 8.3 (Subcase IVc, rational branch), BLUEPRINT Part B, item B3: the two piece shapes.
--   Cells are the triangles `ct g u w` of `LaczFormalHexCell` (vertices (g+u, g+w, g)).  With vectors s, w (|s| = |w| = b, s.w = b^2/2 for the equilateral cells):
--   * Kite(v; s, w)    : the equilateral triangle of side 2b with apex V = v and vertices v, v+2s, v+2w, cut into 4 cells of side b;  W = v+s+w is the base midpoint
--                        (the base is v+2s .. v+2w).  `kiteCell : Fin 4 -> Tri`, `kiteSet` = the big triangle = convex hull of its three vertices (`kiteSet_eq_hull`).
--   * Rhombus(x; s, w) : the parallelogram Par x s w cut into 2 cells (the cells of `cellD`).  `rhombCell : Fin 2 -> Tri`, region `Par`.
--   Proved: `kiteDiss : RegionDissection 4` (cells cover kiteSet, interiors pairwise disjoint), `rhombDiss : RegionDissection 2`, and, under the equilateral hypotheses,
--   `kiteC`, `rhombC : CongruentRegionDissection` with the common model `eqT b` (equilateral triangle of side b).  Witness `eq_hyps_witness` (b = 1, s = (1,0), w = (1/2, sqrt 3/2)),
--   control `eq_hyps_control` ((1,0),(0,1) violate s.w = b^2/2).
--   Blueprint deviation: shapes are parametrized by the two half-side vectors (v; s, w) instead of (v, direction d): the blueprint's `Kite b v d` is the case s = b d, w = b R_{60} d.
--   NOT done here: the VWTiling structure (B4).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 8.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalHexCell

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

theorem hD4 {s0 s1 w0 w1 : ℝ} (hD : s0 * w1 - s1 * w0 ≠ 0) : (2 * s0) * (2 * w1) - (2 * s1) * (2 * w0) ≠ 0 := by
  have e : (2 * s0) * (2 * w1) - (2 * s1) * (2 * w0) = 4 * (s0 * w1 - s1 * w0) := by ring
  rw [e]; exact mul_ne_zero (by norm_num) hD

/-- Separation by a functional in the coordinates `x = v + a s + b w`. -/
theorem sep_coords {t u : Tri} {v0 v1 s0 s1 w0 w1 : ℝ} (hD : s0 * w1 - s1 * w0 ≠ 0) (p q c : ℝ) (hpq : p ≠ 0 ∨ q ≠ 0)
    (h1 : ∀ x ∈ t.carrier, ∃ a b : ℝ, x 0 = v0 + a * s0 + b * w0 ∧ x 1 = v1 + a * s1 + b * w1 ∧ p * a + q * b ≤ c)
    (h2 : ∀ x ∈ u.carrier, ∃ a b : ℝ, x 0 = v0 + a * s0 + b * w0 ∧ x 1 = v1 + a * s1 + b * w1 ∧ c ≤ p * a + q * b) :
    Disjoint (interior t.carrier) (interior u.carrier) := by
  set D := s0 * w1 - s1 * w0 with hDdef
  set A := (p * w1 - q * s1) / D with hA
  set B := (q * s0 - p * w0) / D with hB
  have eS : A * s0 + B * s1 = p := by rw [hA, hB]; field_simp; ring
  have eW : A * w0 + B * w1 = q := by rw [hA, hB]; field_simp; ring
  have key : ∀ a b : ℝ, A * (v0 + a * s0 + b * w0) + B * (v1 + a * s1 + b * w1) = A * v0 + B * v1 + a * p + b * q := by
    intro a b
    have : A * (v0 + a * s0 + b * w0) + B * (v1 + a * s1 + b * w1) = A * v0 + B * v1 + a * (A * s0 + B * s1) + b * (A * w0 + B * w1) := by ring
    rw [this, eS, eW]
  have hf : (linF A B).linear ≠ 0 := by
    rcases hpq with h | h
    · exact linF_ne (c := s0) (d := s1) (by rw [eS]; exact h)
    · exact linF_ne (c := w0) (d := w1) (by rw [eW]; exact h)
  refine Erdos634.CertGeom.interiors_disjoint_of_separating (linF A B) hf (A * v0 + B * v1 + c) ?_ ?_
  · intro x hx
    obtain ⟨a, b, h0, h1', hle⟩ := h1 x hx
    rw [linF_apply, h0, h1', key]; nlinarith
  · intro x hx
    obtain ⟨a, b, h0, h1', hle⟩ := h2 x hx
    rw [linF_apply, h0, h1', key]; nlinarith

/-! ## Kite -/

/-- The four cells of the kite with apex `v` and half-sides `s`, `w`: apex cell, the two corner cells, the inverted middle cell. -/
noncomputable def kiteCell (v0 v1 s0 s1 w0 w1 : ℝ) (hD : s0 * w1 - s1 * w0 ≠ 0) : Fin 4 → Tri :=
  ![ct v0 v1 s0 s1 w0 w1 hD, ct (v0 + s0) (v1 + s1) s0 s1 w0 w1 hD, ct (v0 + w0) (v1 + w1) s0 s1 w0 w1 hD,
    ct (v0 + s0 + w0) (v1 + s1 + w1) (-s0) (-s1) (-w0) (-w1) (hD2 hD)]

/-- The kite as a set: the triangle `v, v+2s, v+2w` (convex hull of its vertices). -/
noncomputable def kiteSet (v0 v1 s0 s1 w0 w1 : ℝ) (hD : s0 * w1 - s1 * w0 ≠ 0) : Set Plane :=
  (ct v0 v1 (2 * s0) (2 * s1) (2 * w0) (2 * w1) (hD4 hD)).carrier

theorem kiteSet_eq_hull (v0 v1 s0 s1 w0 w1 : ℝ) (hD : s0 * w1 - s1 * w0 ≠ 0) :
    kiteSet v0 v1 s0 s1 w0 w1 hD = convexHull ℝ {mkPt v0 v1, mkPt (v0 + 2 * s0) (v1 + 2 * s1), mkPt (v0 + 2 * w0) (v1 + 2 * w1)} := by
  unfold kiteSet Tri.carrier
  congr 1
  ext y
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, rfl⟩
    fin_cases k
    · right; left; rfl
    · right; right; rfl
    · left; rfl
  · rintro (rfl | rfl | rfl)
    · exact ⟨2, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

theorem kiteCell_coords0 {v0 v1 s0 s1 w0 w1 : ℝ} (hD : s0 * w1 - s1 * w0 ≠ 0) (x : Plane) (hx : x ∈ (kiteCell v0 v1 s0 s1 w0 w1 hD 0).carrier) :
    ∃ a b : ℝ, x 0 = v0 + a * s0 + b * w0 ∧ x 1 = v1 + a * s1 + b * w1 ∧ 0 ≤ a ∧ 0 ≤ b ∧ a + b ≤ 1 := by
  obtain ⟨l, m, hl, hm, hlm, h0, h1⟩ := (ct_carrier hD x).mp hx
  exact ⟨l, m, h0, h1, hl, hm, hlm⟩

theorem kiteCell_coords1 {v0 v1 s0 s1 w0 w1 : ℝ} (hD : s0 * w1 - s1 * w0 ≠ 0) (x : Plane) (hx : x ∈ (kiteCell v0 v1 s0 s1 w0 w1 hD 1).carrier) :
    ∃ a b : ℝ, x 0 = v0 + a * s0 + b * w0 ∧ x 1 = v1 + a * s1 + b * w1 ∧ 1 ≤ a ∧ 0 ≤ b ∧ a + b ≤ 2 := by
  obtain ⟨l, m, hl, hm, hlm, h0, h1⟩ := (ct_carrier hD x).mp hx
  exact ⟨1 + l, m, by rw [h0]; ring, by rw [h1]; ring, by linarith, hm, by linarith⟩

theorem kiteCell_coords2 {v0 v1 s0 s1 w0 w1 : ℝ} (hD : s0 * w1 - s1 * w0 ≠ 0) (x : Plane) (hx : x ∈ (kiteCell v0 v1 s0 s1 w0 w1 hD 2).carrier) :
    ∃ a b : ℝ, x 0 = v0 + a * s0 + b * w0 ∧ x 1 = v1 + a * s1 + b * w1 ∧ 0 ≤ a ∧ 1 ≤ b ∧ a + b ≤ 2 := by
  obtain ⟨l, m, hl, hm, hlm, h0, h1⟩ := (ct_carrier hD x).mp hx
  exact ⟨l, 1 + m, by rw [h0]; ring, by rw [h1]; ring, hl, by linarith, by linarith⟩

theorem kiteCell_coords3 {v0 v1 s0 s1 w0 w1 : ℝ} (hD : s0 * w1 - s1 * w0 ≠ 0) (x : Plane) (hx : x ∈ (kiteCell v0 v1 s0 s1 w0 w1 hD 3).carrier) :
    ∃ a b : ℝ, x 0 = v0 + a * s0 + b * w0 ∧ x 1 = v1 + a * s1 + b * w1 ∧ a ≤ 1 ∧ b ≤ 1 ∧ 1 ≤ a + b := by
  obtain ⟨l, m, hl, hm, hlm, h0, h1⟩ := (ct_carrier (hD2 hD) x).mp hx
  exact ⟨1 - l, 1 - m, by rw [h0]; ring, by rw [h1]; ring, by linarith, by linarith, by linarith⟩

theorem kiteCell_disjoint {v0 v1 s0 s1 w0 w1 : ℝ} (hD : s0 * w1 - s1 * w0 ≠ 0) :
    Pairwise fun i j : Fin 4 => Disjoint (interior (kiteCell v0 v1 s0 s1 w0 w1 hD i).carrier) (interior (kiteCell v0 v1 s0 s1 w0 w1 hD j).carrier) := by
  have d01 : Disjoint (interior (kiteCell v0 v1 s0 s1 w0 w1 hD 0).carrier) (interior (kiteCell v0 v1 s0 s1 w0 w1 hD 1).carrier) :=
    sep_coords hD 1 0 1 (Or.inl one_ne_zero)
      (fun x hx => by obtain ⟨a, b, h0, h1, ha, hb, hab⟩ := kiteCell_coords0 hD x hx; exact ⟨a, b, h0, h1, by linarith⟩)
      (fun x hx => by obtain ⟨a, b, h0, h1, ha, hb, hab⟩ := kiteCell_coords1 hD x hx; exact ⟨a, b, h0, h1, by linarith⟩)
  have d02 : Disjoint (interior (kiteCell v0 v1 s0 s1 w0 w1 hD 0).carrier) (interior (kiteCell v0 v1 s0 s1 w0 w1 hD 2).carrier) :=
    sep_coords hD 0 1 1 (Or.inr one_ne_zero)
      (fun x hx => by obtain ⟨a, b, h0, h1, ha, hb, hab⟩ := kiteCell_coords0 hD x hx; exact ⟨a, b, h0, h1, by linarith⟩)
      (fun x hx => by obtain ⟨a, b, h0, h1, ha, hb, hab⟩ := kiteCell_coords2 hD x hx; exact ⟨a, b, h0, h1, by linarith⟩)
  have d03 : Disjoint (interior (kiteCell v0 v1 s0 s1 w0 w1 hD 0).carrier) (interior (kiteCell v0 v1 s0 s1 w0 w1 hD 3).carrier) :=
    sep_coords hD 1 1 1 (Or.inl one_ne_zero)
      (fun x hx => by obtain ⟨a, b, h0, h1, ha, hb, hab⟩ := kiteCell_coords0 hD x hx; exact ⟨a, b, h0, h1, by linarith⟩)
      (fun x hx => by obtain ⟨a, b, h0, h1, ha, hb, hab⟩ := kiteCell_coords3 hD x hx; exact ⟨a, b, h0, h1, by linarith⟩)
  have d12 : Disjoint (interior (kiteCell v0 v1 s0 s1 w0 w1 hD 1).carrier) (interior (kiteCell v0 v1 s0 s1 w0 w1 hD 2).carrier) :=
    sep_coords hD (-1) 1 0 (Or.inl (by norm_num))
      (fun x hx => by obtain ⟨a, b, h0, h1, ha, hb, hab⟩ := kiteCell_coords1 hD x hx; exact ⟨a, b, h0, h1, by linarith⟩)
      (fun x hx => by obtain ⟨a, b, h0, h1, ha, hb, hab⟩ := kiteCell_coords2 hD x hx; exact ⟨a, b, h0, h1, by linarith⟩)
  have d31 : Disjoint (interior (kiteCell v0 v1 s0 s1 w0 w1 hD 3).carrier) (interior (kiteCell v0 v1 s0 s1 w0 w1 hD 1).carrier) :=
    sep_coords hD 1 0 1 (Or.inl one_ne_zero)
      (fun x hx => by obtain ⟨a, b, h0, h1, ha, hb, hab⟩ := kiteCell_coords3 hD x hx; exact ⟨a, b, h0, h1, by linarith⟩)
      (fun x hx => by obtain ⟨a, b, h0, h1, ha, hb, hab⟩ := kiteCell_coords1 hD x hx; exact ⟨a, b, h0, h1, by linarith⟩)
  have d32 : Disjoint (interior (kiteCell v0 v1 s0 s1 w0 w1 hD 3).carrier) (interior (kiteCell v0 v1 s0 s1 w0 w1 hD 2).carrier) :=
    sep_coords hD 0 1 1 (Or.inr one_ne_zero)
      (fun x hx => by obtain ⟨a, b, h0, h1, ha, hb, hab⟩ := kiteCell_coords3 hD x hx; exact ⟨a, b, h0, h1, by linarith⟩)
      (fun x hx => by obtain ⟨a, b, h0, h1, ha, hb, hab⟩ := kiteCell_coords2 hD x hx; exact ⟨a, b, h0, h1, by linarith⟩)
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hij
    | exact d01 | exact d01.symm | exact d02 | exact d02.symm | exact d03 | exact d03.symm
    | exact d12 | exact d12.symm | exact d31 | exact d31.symm | exact d32 | exact d32.symm

theorem kiteCell_cover {v0 v1 s0 s1 w0 w1 : ℝ} (hD : s0 * w1 - s1 * w0 ≠ 0) :
    (⋃ i, (kiteCell v0 v1 s0 s1 w0 w1 hD i).carrier) = kiteSet v0 v1 s0 s1 w0 w1 hD := by
  ext x
  simp only [Set.mem_iUnion, kiteSet]
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i
    · obtain ⟨a, b, h0, h1, ha, hb, hab⟩ := kiteCell_coords0 hD x hi
      exact (ct_carrier (hD4 hD) x).mpr ⟨a / 2, b / 2, by linarith, by linarith, by linarith, by rw [h0]; ring, by rw [h1]; ring⟩
    · obtain ⟨a, b, h0, h1, ha, hb, hab⟩ := kiteCell_coords1 hD x hi
      exact (ct_carrier (hD4 hD) x).mpr ⟨a / 2, b / 2, by linarith, by linarith, by linarith, by rw [h0]; ring, by rw [h1]; ring⟩
    · obtain ⟨a, b, h0, h1, ha, hb, hab⟩ := kiteCell_coords2 hD x hi
      exact (ct_carrier (hD4 hD) x).mpr ⟨a / 2, b / 2, by linarith, by linarith, by linarith, by rw [h0]; ring, by rw [h1]; ring⟩
    · obtain ⟨l, m, hl, hm, hlm, h0, h1⟩ := (ct_carrier (hD2 hD) x).mp hi
      exact (ct_carrier (hD4 hD) x).mpr ⟨(1 - l) / 2, (1 - m) / 2, by linarith, by linarith, by linarith, by rw [h0]; ring, by rw [h1]; ring⟩
  · intro hx
    obtain ⟨l, m, hl, hm, hlm, h0, h1⟩ := (ct_carrier (hD4 hD) x).mp hx
    by_cases c0 : 2 * l + 2 * m ≤ 1
    · exact ⟨0, (ct_carrier hD x).mpr ⟨2 * l, 2 * m, by linarith, by linarith, c0, by rw [h0]; ring, by rw [h1]; ring⟩⟩
    · by_cases c1 : 1 ≤ 2 * l
      · exact ⟨1, (ct_carrier hD x).mpr ⟨2 * l - 1, 2 * m, by linarith, by linarith, by linarith, by rw [h0]; ring, by rw [h1]; ring⟩⟩
      · by_cases c2 : 1 ≤ 2 * m
        · exact ⟨2, (ct_carrier hD x).mpr ⟨2 * l, 2 * m - 1, by linarith, by linarith, by linarith, by rw [h0]; ring, by rw [h1]; ring⟩⟩
        · exact ⟨3, (ct_carrier (hD2 hD) x).mpr ⟨1 - 2 * l, 1 - 2 * m, by linarith, by linarith, by linarith, by rw [h0]; ring, by rw [h1]; ring⟩⟩

/-- The kite as a region dissection into four cells. -/
noncomputable def kiteDiss (v0 v1 s0 s1 w0 w1 : ℝ) (hD : s0 * w1 - s1 * w0 ≠ 0) : RegionDissection 4 where
  region := kiteSet v0 v1 s0 s1 w0 w1 hD
  tile := kiteCell v0 v1 s0 s1 w0 w1 hD
  covers := kiteCell_cover hD
  interiors_disjoint := kiteCell_disjoint hD

/-! ## Rhombus -/

noncomputable def rhombCell (x0 x1 s0 s1 w0 w1 : ℝ) (hD : s0 * w1 - s1 * w0 ≠ 0) : Fin 2 → Tri :=
  ![ct x0 x1 s0 s1 w0 w1 hD, ct (x0 + s0 + w0) (x1 + s1 + w1) (-s0) (-s1) (-w0) (-w1) (hD2 hD)]

theorem rhombCell_disjoint {x0 x1 s0 s1 w0 w1 : ℝ} (hD : s0 * w1 - s1 * w0 ≠ 0) :
    Pairwise fun i j : Fin 2 => Disjoint (interior (rhombCell x0 x1 s0 s1 w0 w1 hD i).carrier) (interior (rhombCell x0 x1 s0 s1 w0 w1 hD j).carrier) := by
  have d : Disjoint (interior (rhombCell x0 x1 s0 s1 w0 w1 hD 0).carrier) (interior (rhombCell x0 x1 s0 s1 w0 w1 hD 1).carrier) :=
    sep_coords hD 1 1 1 (Or.inl one_ne_zero)
      (fun x hx => by
        obtain ⟨l, m, hl, hm, hlm, h0, h1⟩ := (ct_carrier hD x).mp hx
        exact ⟨l, m, h0, h1, by linarith⟩)
      (fun x hx => by
        obtain ⟨l, m, hl, hm, hlm, h0, h1⟩ := (ct_carrier (hD2 hD) x).mp hx
        exact ⟨1 - l, 1 - m, by rw [h0]; ring, by rw [h1]; ring, by linarith⟩)
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact d
  · exact d.symm
  · exact absurd rfl hij

/-- The rhombus (parallelogram) as a region dissection into two cells. -/
noncomputable def rhombDiss (x0 x1 s0 s1 w0 w1 : ℝ) (hD : s0 * w1 - s1 * w0 ≠ 0) : RegionDissection 2 where
  region := Par x0 x1 s0 s1 w0 w1
  tile := rhombCell x0 x1 s0 s1 w0 w1 hD
  covers := by
    rw [← cell_cover hD]
    ext x
    simp only [Set.mem_iUnion, Fin.exists_fin_two, Set.mem_union]
    rfl
  interiors_disjoint := rhombCell_disjoint hD

/-! ## Equilateral congruence -/

theorem det_eqT {b : ℝ} (hb : 0 < b) : det3 b 0 (b / 2) (Real.sqrt 3 * b / 2) 0 0 ≠ 0 := by
  have e : det3 b 0 (b / 2) (Real.sqrt 3 * b / 2) 0 0 = b * (Real.sqrt 3 * b / 2) := by unfold det3; ring
  rw [e]; positivity

/-- The equilateral model of side `b` (vertex order as `ct 0 0 (b,0) (b/2, sqrt 3 b/2)`). -/
noncomputable def eqT (b : ℝ) (hb : 0 < b) : Tri := mkTri b 0 (b / 2) (Real.sqrt 3 * b / 2) 0 0 (det_eqT hb)

theorem ct_iso_eq {b g0 g1 u0 u1 w0 w1 : ℝ} (hb : 0 < b) (hD : u0 * w1 - u1 * w0 ≠ 0)
    (hu : u0 ^ 2 + u1 ^ 2 = b ^ 2) (hw : w0 ^ 2 + w1 ^ 2 = b ^ 2) (huw : u0 * w0 + u1 * w1 = b ^ 2 / 2) :
    ∃ f : Plane ≃ᵢ Plane, ∀ k, f ((ct g0 g1 u0 u1 w0 w1 hD).pts k) = (eqT b hb).pts k := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hq : (Real.sqrt 3 * b / 2) ^ 2 = 3 * b ^ 2 / 4 := by rw [div_pow, mul_pow, hs]; ring
  refine iso_of_dist3 ?_ ?_ ?_
  · show dist (mkPt (g0 + u0) (g1 + u1)) (mkPt (g0 + w0) (g1 + w1)) = dist (mkPt b 0) (mkPt (b / 2) (Real.sqrt 3 * b / 2))
    refine Erdos634.SssCongruent.dist_of_sq ?_
    rw [sqd_mk, sqd_mk]; nlinarith
  · show dist (mkPt (g0 + w0) (g1 + w1)) (mkPt g0 g1) = dist (mkPt (b / 2) (Real.sqrt 3 * b / 2)) (mkPt 0 0)
    refine Erdos634.SssCongruent.dist_of_sq ?_
    rw [sqd_mk, sqd_mk]; nlinarith
  · show dist (mkPt g0 g1) (mkPt (g0 + u0) (g1 + u1)) = dist (mkPt 0 0) (mkPt b 0)
    refine Erdos634.SssCongruent.dist_of_sq ?_
    rw [sqd_mk, sqd_mk]; nlinarith

/-- The kite as a congruent dissection by equilateral triangles of side `b`. -/
noncomputable def kiteC {b : ℝ} (hb : 0 < b) (v0 v1 s0 s1 w0 w1 : ℝ) (hD : s0 * w1 - s1 * w0 ≠ 0)
    (hs : s0 ^ 2 + s1 ^ 2 = b ^ 2) (hw : w0 ^ 2 + w1 ^ 2 = b ^ 2) (hsw : s0 * w0 + s1 * w1 = b ^ 2 / 2) : CongruentRegionDissection 4 where
  toRegionDissection := kiteDiss v0 v1 s0 s1 w0 w1 hD
  model := eqT b hb
  tiles_congruent := by
    intro i
    have hs' : (-s0) ^ 2 + (-s1) ^ 2 = b ^ 2 := by nlinarith
    have hw' : (-w0) ^ 2 + (-w1) ^ 2 = b ^ 2 := by nlinarith
    have hsw' : (-s0) * (-w0) + (-s1) * (-w1) = b ^ 2 / 2 := by nlinarith
    fin_cases i
    · obtain ⟨f, hf⟩ := ct_iso_eq (g0 := v0) (g1 := v1) hb hD hs hw hsw
      exact ⟨f, Equiv.refl _, hf⟩
    · obtain ⟨f, hf⟩ := ct_iso_eq (g0 := v0 + s0) (g1 := v1 + s1) hb hD hs hw hsw
      exact ⟨f, Equiv.refl _, hf⟩
    · obtain ⟨f, hf⟩ := ct_iso_eq (g0 := v0 + w0) (g1 := v1 + w1) hb hD hs hw hsw
      exact ⟨f, Equiv.refl _, hf⟩
    · obtain ⟨f, hf⟩ := ct_iso_eq (g0 := v0 + s0 + w0) (g1 := v1 + s1 + w1) hb (hD2 hD) hs' hw' hsw'
      exact ⟨f, Equiv.refl _, hf⟩

/-- The rhombus as a congruent dissection by two equilateral triangles of side `b`. -/
noncomputable def rhombC {b : ℝ} (hb : 0 < b) (x0 x1 s0 s1 w0 w1 : ℝ) (hD : s0 * w1 - s1 * w0 ≠ 0)
    (hs : s0 ^ 2 + s1 ^ 2 = b ^ 2) (hw : w0 ^ 2 + w1 ^ 2 = b ^ 2) (hsw : s0 * w0 + s1 * w1 = b ^ 2 / 2) : CongruentRegionDissection 2 where
  toRegionDissection := rhombDiss x0 x1 s0 s1 w0 w1 hD
  model := eqT b hb
  tiles_congruent := by
    intro i
    have hs' : (-s0) ^ 2 + (-s1) ^ 2 = b ^ 2 := by nlinarith
    have hw' : (-w0) ^ 2 + (-w1) ^ 2 = b ^ 2 := by nlinarith
    have hsw' : (-s0) * (-w0) + (-s1) * (-w1) = b ^ 2 / 2 := by nlinarith
    fin_cases i
    · obtain ⟨f, hf⟩ := ct_iso_eq (g0 := x0) (g1 := x1) hb hD hs hw hsw
      exact ⟨f, Equiv.refl _, hf⟩
    · obtain ⟨f, hf⟩ := ct_iso_eq (g0 := x0 + s0 + w0) (g1 := x1 + s1 + w1) hb (hD2 hD) hs' hw' hsw'
      exact ⟨f, Equiv.refl _, hf⟩

/-- Vertices: the apex `V` is a corner of cell 0 only among the kite cells it lies in; the base midpoint `W` is a corner of cells 1, 2, 3. -/
theorem kite_apex_vertex {v0 v1 s0 s1 w0 w1 : ℝ} (hD : s0 * w1 - s1 * w0 ≠ 0) : (kiteCell v0 v1 s0 s1 w0 w1 hD 0).pts 2 = mkPt v0 v1 := rfl

theorem kite_W_vertices {v0 v1 s0 s1 w0 w1 : ℝ} (hD : s0 * w1 - s1 * w0 ≠ 0) :
    (kiteCell v0 v1 s0 s1 w0 w1 hD 1).pts 1 = mkPt (v0 + s0 + w0) (v1 + s1 + w1) ∧
    (kiteCell v0 v1 s0 s1 w0 w1 hD 2).pts 0 = mkPt (v0 + s0 + w0) (v1 + s1 + w1) ∧
    (kiteCell v0 v1 s0 s1 w0 w1 hD 3).pts 2 = mkPt (v0 + s0 + w0) (v1 + s1 + w1) :=
  ⟨mkPt_congr (by ring) (by ring), mkPt_congr (by ring) (by ring), rfl⟩

/-- Witness of the equilateral hypotheses: `b = 1`, `s = (1,0)`, `w = (1/2, sqrt 3/2)`. -/
theorem eq_hyps_witness : ∃ s0 s1 w0 w1 : ℝ, s0 * w1 - s1 * w0 ≠ 0 ∧ s0 ^ 2 + s1 ^ 2 = (1 : ℝ) ^ 2 ∧ w0 ^ 2 + w1 ^ 2 = (1 : ℝ) ^ 2 ∧
    s0 * w0 + s1 * w1 = (1 : ℝ) ^ 2 / 2 := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have h4 : (Real.sqrt 3 / 2) ^ 2 = 3 / 4 := by rw [div_pow, hs]; norm_num
  refine ⟨1, 0, 1 / 2, Real.sqrt 3 / 2, by intro h; linarith, by norm_num, by rw [h4]; norm_num, by norm_num⟩

/-- Control: the orthogonal pair `(1,0), (0,1)` violates the equilateral hypotheses (the shape would not be a kite of equilateral cells). -/
theorem eq_hyps_control : ¬ ((1 : ℝ) * 0 + 0 * 1 = (1 : ℝ) ^ 2 / 2) := by norm_num

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.kiteSet_eq_hull
#print axioms Erdos634.Draft.LaczFormal.RG.kiteCell_disjoint
#print axioms Erdos634.Draft.LaczFormal.RG.kiteDiss
#print axioms Erdos634.Draft.LaczFormal.RG.rhombDiss
#print axioms Erdos634.Draft.LaczFormal.RG.kiteC
#print axioms Erdos634.Draft.LaczFormal.RG.rhombC
#print axioms Erdos634.Draft.LaczFormal.RG.eq_hyps_witness

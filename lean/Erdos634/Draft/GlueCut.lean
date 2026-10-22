import Erdos634.RegionDissection
import Erdos634.CertCoord
import Erdos634.CertGeom

/-!
# Gluing region dissections along a cutting line (general lemma for Zhang Lemma 1)

Erdős #634, Beeson/Zhang constructions.  `RegionDissection.unionCongruentRegion` needs
`Disjoint (interior R1.region) (interior R2.region)`.  This file supplies that hypothesis for the
case every polygon cut produces: the two carriers lie on opposite closed sides of a line.

* `hull_subset_halfplane` : a convex hull lies in a closed half-plane as soon as its generators do.
* `interiors_disjoint_of_cut` : two *arbitrary sets* on opposite closed sides of a line (the line
  functional being an affine map with nonzero linear part) have disjoint interiors.
* `glueByLine` : `unionCongruentRegion` with that hypothesis discharged; the region is the union.
* `mem_carrier_mkTri_iff` : a coordinate triangle with positive determinant is exactly the set of
  points on the nonnegative side of its three edge lines (the "intersection of half-planes" form).

Axiom-clean target; no `sorry`.  Credit: Zhang (arXiv 2512.22696), Beeson, Beeson-Rosu, Laczkovich.
-/

namespace Erdos634.GlueCut

open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.RegionDissection

/-- A convex hull lies on the nonnegative side of an affine functional if its generators do. -/
theorem hull_subset_halfplane (S : Set Plane) (f : Plane →ᵃ[ℝ] ℝ) (h : ∀ x ∈ S, 0 ≤ f x) :
    ∀ x ∈ convexHull ℝ S, 0 ≤ f x := by
  have hconv : Convex ℝ (f ⁻¹' Set.Ici 0) := (convex_Ici (0:ℝ)).affine_preimage f
  have hsub : S ⊆ f ⁻¹' Set.Ici 0 := fun x hx => h x hx
  exact fun x hx => convexHull_min hsub hconv hx

/-- Two sets on opposite closed sides of a line have disjoint interiors. -/
theorem interiors_disjoint_of_cut {S1 S2 : Set Plane} (f : Plane →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0)
    (h1 : ∀ x ∈ S1, f x ≤ 0) (h2 : ∀ x ∈ S2, 0 ≤ f x) :
    Disjoint (interior S1) (interior S2) := by
  rw [Set.disjoint_left]
  intro x hx1 hx2
  have hxc : f x = 0 := le_antisymm (h1 x (interior_subset hx1)) (h2 x (interior_subset hx2))
  set g : Plane →ᵃ[ℝ] ℝ := AffineMap.const ℝ Plane 0 - f with hg
  have hglin : g.linear ≠ 0 := by
    intro hcon
    apply hf
    have : (AffineMap.const ℝ Plane (0:ℝ)).linear - f.linear = 0 := hcon
    have hzero : (AffineMap.const ℝ Plane (0:ℝ)).linear = 0 := rfl
    rw [hzero, zero_sub, neg_eq_zero] at this
    exact this
  have hgx : g x = 0 := by simp [hg, hxc]
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx1)
  obtain ⟨y, hy, hyneg⟩ := Erdos634.Geometry.exists_neg_near_of_affine_zero g hglin hgx hr
  have hyS : y ∈ S1 := hball hy
  have : 0 < f y := by
    have hgy : g y = 0 - f y := rfl
    rw [hgy] at hyneg
    linarith
  exact absurd (h1 y hyS) (not_le.mpr this)

/-- **Gluing along a line.**  `unionCongruentRegion` with the interior hypothesis supplied by a
separating line: `C1.region` on the `≤ 0` side, `C2.region` on the `≥ 0` side. -/
noncomputable def glueByLine {M N : ℕ} (C1 : CongruentRegionDissection M)
    (C2 : CongruentRegionDissection N) (hmodel : C1.model = C2.model)
    (f : Plane →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0)
    (h1 : ∀ x ∈ C1.region, f x ≤ 0) (h2 : ∀ x ∈ C2.region, 0 ≤ f x) :
    CongruentRegionDissection (M + N) :=
  unionCongruentRegion C1 C2 hmodel (interiors_disjoint_of_cut f hf h1 h2)

@[simp] theorem glueByLine_region {M N : ℕ} (C1 : CongruentRegionDissection M)
    (C2 : CongruentRegionDissection N) (hmodel : C1.model = C2.model)
    (f : Plane →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0)
    (h1 : ∀ x ∈ C1.region, f x ≤ 0) (h2 : ∀ x ∈ C2.region, 0 ≤ f x) :
    (glueByLine C1 C2 hmodel f hf h1 h2).region = C1.region ∪ C2.region := rfl

@[simp] theorem glueByLine_model {M N : ℕ} (C1 : CongruentRegionDissection M)
    (C2 : CongruentRegionDissection N) (hmodel : C1.model = C2.model)
    (f : Plane →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0)
    (h1 : ∀ x ∈ C1.region, f x ≤ 0) (h2 : ∀ x ∈ C2.region, 0 ≤ f x) :
    (glueByLine C1 C2 hmodel f hf h1 h2).model = C1.model := rfl

/-- `lineFun` with the two points swapped is the negative: the "≤ 0" version of a "≥ 0" cut. -/
theorem lineFun_swap (px py qx qy : ℝ) (v : Plane) :
    lineFun qx qy px py v = - lineFun px py qx qy v := by
  simp only [lineFun_apply]; ring

/-! ## Coordinate triangles as intersections of three half-planes -/

theorem mkPt_eta (p : Plane) : mkPt (p 0) (p 1) = p := by
  ext i
  fin_cases i <;> simp

theorem lineFun_mkPt (px py qx qy a b : ℝ) :
    lineFun px py qx qy (mkPt a b) = det3 px py qx qy a b := by
  simp only [lineFun_apply, mkPt_zero, mkPt_one, det3]

/-- **A positively oriented coordinate triangle is the intersection of its three edge half-planes.** -/
theorem mem_carrier_mkTri_iff {x₀ y₀ x₁ y₁ x₂ y₂ : ℝ} (hD : 0 < det3 x₀ y₀ x₁ y₁ x₂ y₂)
    (p : Plane) :
    p ∈ (mkTri x₀ y₀ x₁ y₁ x₂ y₂ hD.ne').carrier ↔
      0 ≤ det3 (p 0) (p 1) x₁ y₁ x₂ y₂ ∧ 0 ≤ det3 x₀ y₀ (p 0) (p 1) x₂ y₂ ∧
        0 ≤ det3 x₀ y₀ x₁ y₁ (p 0) (p 1) := by
  constructor
  · intro hp
    have key : ∀ (qx qy rx ry : ℝ), (0 ≤ lineFun qx qy rx ry (mkPt x₀ y₀)) →
        (0 ≤ lineFun qx qy rx ry (mkPt x₁ y₁)) → (0 ≤ lineFun qx qy rx ry (mkPt x₂ y₂)) →
        0 ≤ lineFun qx qy rx ry p := by
      intro qx qy rx ry h0 h1 h2
      refine hull_subset_halfplane (Set.range (mkTri x₀ y₀ x₁ y₁ x₂ y₂ hD.ne').pts)
        (lineFun qx qy rx ry) ?_ p hp
      rintro _ ⟨k, rfl⟩
      fin_cases k
      · exact h0
      · exact h1
      · exact h2
    have e1 := key x₁ y₁ x₂ y₂
    have e2 := key x₂ y₂ x₀ y₀
    have e3 := key x₀ y₀ x₁ y₁
    simp only [lineFun_mkPt, det3] at e1 e2 e3 ⊢
    have hDd := hD; simp only [det3] at hDd
    refine ⟨?_, ?_, ?_⟩
    · have := e1 (by nlinarith) (by nlinarith) (by nlinarith)
      have hp' : lineFun x₁ y₁ x₂ y₂ p = lineFun x₁ y₁ x₂ y₂ (mkPt (p 0) (p 1)) := by rw [mkPt_eta]
      simp only [lineFun_apply] at this; nlinarith
    · have := e2 (by nlinarith) (by nlinarith) (by nlinarith)
      simp only [lineFun_apply] at this; nlinarith
    · have := e3 (by nlinarith) (by nlinarith) (by nlinarith)
      simp only [lineFun_apply] at this; nlinarith
  · rintro ⟨h0, h1, h2⟩
    have := mem_carrier_of_dets hD h0 h1 h2
    rwa [mkPt_eta] at this

end Erdos634.GlueCut

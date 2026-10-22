import Erdos634.Draft.ZhangRat
import Erdos634.Draft.ZhangRegionDilate

/-!
# Transport of a triangle dissection by a dilation and an isometry (for Zhang Prop 11)

`Dis_scale_congr`: if a triangle `T` is dissected into `n` model tiles (`Dis R T.carrier n`) and a
triangle `U` is congruent to the `t`-fold dilate `T1` of `T` (`T1.pts i = t • T.pts i`), then `U` is
dissected into `t*t*n` model tiles.  Uses `ZhangRegionDilate.dilate_region` and the ambient
isometry of `Tri.Congruent`.  UNAUDITED.  Credit Zhang (arXiv 2512.22696), Beeson, Beeson-Zhang,
Laczkovich.
-/

namespace Erdos634.ZhangRat2

open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.RegionDissection
  Erdos634.SssCongruent Erdos634.ZhangPara Erdos634.ZhangRegionDilate Erdos634.Realizable

theorem carrier_image_congruent {T U : Tri} (h : T.Congruent U) :
    ∃ f : Plane ≃ᵢ Plane, f '' T.carrier = U.carrier := by
  obtain ⟨f, σ, hf⟩ := h
  refine ⟨f, ?_⟩
  have haff : ⇑f.toRealAffineIsometryEquiv.toAffineMap = ⇑f := rfl
  have h1 := (f.toRealAffineIsometryEquiv.toAffineMap).image_convexHull (Set.range T.pts)
  rw [haff] at h1
  unfold Tri.carrier
  rw [h1, ← Set.range_comp]
  congr 1
  have : (f ∘ T.pts) = U.pts ∘ σ := funext hf
  rw [this, Set.range_comp, Equiv.range_eq_univ, Set.image_univ]

theorem hom_carrier {T T1 : Tri} (t : ℕ) (ht : 0 < t) (h1 : ∀ i, T1.pts i = (t : ℝ) • T.pts i) :
    (homothetyEquiv 0 (t : ℝ) (by exact_mod_cast ht.ne')) '' T.carrier = T1.carrier := by
  have hm := (AffineMap.homothety (0 : Plane) (t : ℝ)).image_convexHull (Set.range T.pts)
  have hh : ∀ x, homothetyEquiv 0 (t : ℝ) (by exact_mod_cast ht.ne') x = (t : ℝ) • x := by
    intro x; rw [homothetyEquiv_apply, AffineMap.homothety_apply]; simp
  have hh2 : ∀ x, AffineMap.homothety (0 : Plane) (t : ℝ) x = (t : ℝ) • x := by
    intro x; rw [AffineMap.homothety_apply]; simp
  unfold Tri.carrier
  simp only [hh]
  simp only [hh2] at hm
  rw [hm, ← Set.range_comp]
  have : ((fun a : Plane => (t : ℝ) • a) ∘ T.pts) = T1.pts := funext fun i => (h1 i).symm
  rw [this]

theorem Dis_scale_congr {R T T1 U : Tri} {n t : ℕ} (ht : 0 < t) (hD : Dis R T.carrier n)
    (h1 : ∀ i, T1.pts i = (t : ℝ) • T.pts i) (hU : T1.Congruent U) : Dis R U.carrier (t * t * n) := by
  obtain ⟨C, hr, hm⟩ := hD
  obtain ⟨C', hr', hm'⟩ := dilate_region C 0 t ht
  obtain ⟨f, hf⟩ := carrier_image_congruent hU
  refine ⟨mapCongruentRegionDissection f.toRealAffineIsometryEquiv C', ?_, ?_⟩
  · show f.toRealAffineIsometryEquiv.toAffineEquiv '' C'.region = U.carrier
    rw [hr', hr, hom_carrier t ht h1]
    exact hf
  · exact hm'.trans hm

end Erdos634.ZhangRat2

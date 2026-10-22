import Erdos634.Ladder
import Erdos634.RegionDissection
import Erdos634.TranslateDissection
import Erdos634.Realizable
import Erdos634.Draft.ZhangL1Aux

/-!
# Natural dilation of an arbitrary congruent region dissection

`dilate_region`: a `CongruentRegionDissection N` of a region `S` with model `T` yields, for every
natural `k ≥ 1` and every centre `p`, a `CongruentRegionDissection (k*k*N)` of the homothetic image
`h_{p,k}(S)` with the SAME model `T` (not scaled).  Each tile `t` (congruent to `T`) is dilated to
`h(t)` and cut into `k*k` copies of `T` by `Erdos634.Ladder.ladder` (applied to the one-tile
dissection of `t`), translated onto `h(t)`.  This generalises `ZhangThm7.Dis_dilate` (triangles
only) to arbitrary regions.  UNAUDITED.  Credit Zhang (arXiv 2512.22696), Beeson, Laczkovich.
-/

namespace Erdos634.ZhangRegionDilate

open Erdos634.Geometry Erdos634.RegionDissection Erdos634.DissectionMap Erdos634.Realizable
  Erdos634.ZhangL1 Erdos634.TranslateDissection

theorem tile_dilate (t T : Tri) (hc : t.Congruent T) (p : Plane) (k : ℕ) (hk : 0 < k) :
    ∃ F : CongruentDissection (k * k * 1),
      F.target = mapTri (homothetyEquiv p (k : ℝ) (by exact_mod_cast hk.ne')) t ∧ F.model = T := by
  classical
  have hfun : (![t.pts 0, t.pts 1, t.pts 2] : Fin 3 → Plane) = t.pts := by
    funext x; fin_cases x <;> rfl
  have hind : AffineIndependent ℝ (![t.pts 0, t.pts 1, t.pts 2] : Fin 3 → Plane) := by
    rw [hfun]; exact t.indep
  have ht : t = (⟨![t.pts 0, t.pts 1, t.pts 2], hind⟩ : Tri) := tri_ext_pts hfun.symm
  let D : CongruentDissection 1 :=
    { target := t
      tile := fun _ => t
      covers := Set.iUnion_const _
      interiors_disjoint := fun i j h => absurd (Subsingleton.elim i j) h
      model := T
      tiles_congruent := fun _ => hc }
  obtain ⟨E, hEt, hEm⟩ := Erdos634.Ladder.ladder (t.pts 0) (t.pts 1) (t.pts 2) hind D ht k hk
  refine ⟨translateCongruentDissection (((k : ℝ) - 1) • (t.pts 0 - p)) E, ?_, hEm⟩
  rw [translateCongruentDissection_target, hEt]
  apply tri_ext_pts
  funext x
  fin_cases x
  · simp [mapTri, Erdos634.Subdivision.P, transEquiv, homothetyEquiv_apply,
      AffineMap.homothety_apply, Erdos634.Subdivision.bigTri, Erdos634.Subdivision.P]
    module
  · simp [mapTri, Erdos634.Subdivision.P, transEquiv, homothetyEquiv_apply,
      AffineMap.homothety_apply, Erdos634.Subdivision.bigTri, Erdos634.Subdivision.P]
    module
  · simp [mapTri, Erdos634.Subdivision.P, transEquiv, homothetyEquiv_apply,
      AffineMap.homothety_apply, Erdos634.Subdivision.bigTri, Erdos634.Subdivision.P]
    module

/-- **Natural dilation of a congruent region dissection (UNAUDITED).** -/
theorem dilate_region {N : ℕ} (C : CongruentRegionDissection N) (p : Plane) (k : ℕ) (hk : 0 < k) :
    ∃ C' : CongruentRegionDissection (k * k * N),
      C'.region = (homothetyEquiv p (k : ℝ) (by exact_mod_cast hk.ne')) '' C.region ∧
      C'.model = C.model := by
  classical
  set h := homothetyEquiv p (k : ℝ) (by exact_mod_cast hk.ne') with hh
  choose F hFt hFm using fun i => tile_dilate (C.tile i) C.model (C.tiles_congruent i) p k hk
  let e : Fin (k * k * N) ≃ Fin N × Fin (k * k * 1) :=
    (finCongr (by ring : k * k * N = N * (k * k * 1))).trans finProdFinEquiv.symm
  let tileP : Fin N × Fin (k * k * 1) → Tri := fun q => (F q.1).tile q.2
  have sub : ∀ q : Fin N × Fin (k * k * 1),
      (tileP q).carrier ⊆ (mapTri h (C.tile q.1)).carrier := by
    intro q x hx
    rw [← hFt q.1, ← (F q.1).covers]
    exact Set.mem_iUnion.mpr ⟨q.2, hx⟩
  refine ⟨
    { region := h '' C.region
      tile := fun n => tileP (e n)
      covers := ?_
      interiors_disjoint := ?_
      model := C.model
      tiles_congruent := ?_ }, rfl, rfl⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨n, hx⟩ := Set.mem_iUnion.mp hx
      have := sub (e n) hx
      rw [mapTri_carrier] at this
      obtain ⟨y, hy, rfl⟩ := this
      refine ⟨y, ?_, rfl⟩
      rw [← C.covers]
      exact Set.mem_iUnion.mpr ⟨(e n).1, hy⟩
    · rintro ⟨y, hy, rfl⟩
      rw [← C.covers] at hy
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
      have hx : h y ∈ (F i).target.carrier := by
        rw [hFt i, mapTri_carrier]; exact ⟨y, hi, rfl⟩
      rw [← (F i).covers] at hx
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨e.symm (i, j), by simpa [tileP] using hj⟩
  · intro n n' hn
    have hq : e n ≠ e n' := fun h' => hn (e.injective h')
    show Disjoint (interior (tileP (e n)).carrier) (interior (tileP (e n')).carrier)
    generalize e n = q at hq
    generalize e n' = q' at hq
    obtain ⟨i, j⟩ := q
    obtain ⟨i', j'⟩ := q'
    by_cases hi : i = i'
    · subst hi
      have hj : j ≠ j' := fun h' => hq (by rw [h'])
      exact (F i).interiors_disjoint hj
    · have hd := mapTri_interiors_disjoint h (C.interiors_disjoint hi)
      exact hd.mono (interior_mono (sub (i, j))) (interior_mono (sub (i', j')))
  · intro n
    have := (F (e n).1).tiles_congruent (e n).2
    rwa [hFm] at this

end Erdos634.ZhangRegionDilate

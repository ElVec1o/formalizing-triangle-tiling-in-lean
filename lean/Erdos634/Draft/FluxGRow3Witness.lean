-- Draft/FluxGRow3Witness.lean — a real `CongruentDissection 2` witness for row3's right-tile,
-- isosceles-target family (`row3/PROOF.md` Proposition RP: target angles (α, α, π − 2α), tile a
-- right triangle with legs `a`, `b`, hypotenuse `c`; here `tan α = 1/2`, i.e. `(a, b, c) = (1, 2,
-- √5)`), Formalization debt on an already paper-level-PROVED result; NOT progress on the three
-- /goal outcomes.
--
-- SOURCE OF THE TILING (Rule 0.5 / novelty): NOT invented here. It is `row3/PROOF.md` §5's own
-- table, first row: "`(α,α,2β)` | `tan α = 1/2` | `N=2` | `λ=1` | `s ≠ 0` | pass", produced by
-- `right_parity_check.py`'s `iso_target_tilings(1, 2, s5, half_quadratic(1), "iso(alpha,alpha,2beta)
-- tan=1/2, trivial 2-tiling")`, which builds exactly: target `B=(-2,0)`, `C=(2,0)`, `A=(0,1)`, split
-- by the altitude `M=(0,0)` into `tile0 = (B,M,A)` and `tile1 = mirror_x(tile0) = (C,M,A)`. This file
-- re-expresses that Python/exact-arithmetic tiling as a Lean `CongruentDissection 2` term, using
-- `CertBridge.ofCert` (the corpus's own certified-search-to-`CongruentDissection` bridge, already
-- used by `Tiling44`/`Tiling99`/etc.) as the structural template, per the task's survey instruction.
--
-- Rediscovery check: grepped `lean/Erdos634` for `FluxGRow3Witness`, `iso_target_tilings`,
-- `half_quadratic` — no hits outside this file and the Python script it transcribes.
--
-- Hazard H59: this is NOT the base-β family and NOT the tile `(3,4,5)` (never used here, matching
-- `right_parity_check.py`'s own instruction); `(e,f) = (3,4)` is never evaluated.
import Erdos634.CertBridge
import Erdos634.CertCoord

namespace Erdos634.Draft.FluxGRow3Witness

open Erdos634.Geometry Erdos634.CertCoord Erdos634.AreaDet

/-! ## §1 The three triangles, in coordinates -/

theorem hdet0 : det3 (-2) 0 0 0 0 1 ≠ 0 := by norm_num [det3]
theorem hdet1 : det3 2 0 0 0 0 1 ≠ 0 := by norm_num [det3]
theorem hDTpos : (0:ℝ) < det3 (-2) 0 2 0 0 1 := by norm_num [det3]

/-- `tile0 = (B, M, A) = ((-2,0), (0,0), (0,1))`: legs `BM = 2`, `MA = 1`, hypotenuse `AB = √5`. -/
noncomputable def tile0 : Tri := mkTri (-2) 0 0 0 0 1 hdet0

/-- `tile1 = (C, M, A) = ((2,0), (0,0), (0,1))`, the mirror image of `tile0` across `x = 0`. -/
noncomputable def tile1 : Tri := mkTri 2 0 0 0 0 1 hdet1

/-- `target = (B, C, A) = ((-2,0), (2,0), (0,1))`, the isosceles triangle `(α, α, π − 2α)`. -/
noncomputable def target : Tri := mkTri (-2) 0 2 0 0 1 hDTpos.ne'

/-- The model tile: `tile0` itself (every tile is congruent to it, `tile1` by an explicit isometry
below). -/
noncomputable def model : Tri := tile0

/-- The two-tile family. -/
noncomputable def tileF : Fin 2 → Tri := ![tile0, tile1]

/-! ## §2 Congruence — the (C1) check -/

theorem tile0_pts : tile0.pts = ![mkPt (-2) 0, mkPt 0 0, mkPt 0 1] := mkTri_pts _ _ _ _ _ _ _
theorem tile1_pts : tile1.pts = ![mkPt 2 0, mkPt 0 0, mkPt 0 1] := mkTri_pts _ _ _ _ _ _ _

theorem hd01 : ∀ i, dist ((tileF i).pts 0) ((tileF i).pts 1) = dist (model.pts 0) (model.pts 1) := by
  intro i
  fin_cases i
  · rfl
  · show dist ((tile1).pts 0) ((tile1).pts 1) = dist ((tile0).pts 0) ((tile0).pts 1)
    rw [tile0_pts, tile1_pts]
    show dist (mkPt 2 0) (mkPt 0 0) = dist (mkPt (-2) 0) (mkPt 0 0)
    apply Erdos634.SssCongruent.dist_of_sq
    rw [dist_sq_mkPt, dist_sq_mkPt]; ring

theorem hd12 : ∀ i, dist ((tileF i).pts 1) ((tileF i).pts 2) = dist (model.pts 1) (model.pts 2) := by
  intro i
  fin_cases i
  · rfl
  · show dist ((tile1).pts 1) ((tile1).pts 2) = dist ((tile0).pts 1) ((tile0).pts 2)
    rw [tile0_pts, tile1_pts]
    simp

theorem hd20 : ∀ i, dist ((tileF i).pts 2) ((tileF i).pts 0) = dist (model.pts 2) (model.pts 0) := by
  intro i
  fin_cases i
  · rfl
  · show dist ((tile1).pts 2) ((tile1).pts 0) = dist ((tile0).pts 2) ((tile0).pts 0)
    rw [tile0_pts, tile1_pts]
    show dist (mkPt 0 1) (mkPt 2 0) = dist (mkPt 0 1) (mkPt (-2) 0)
    apply Erdos634.SssCongruent.dist_of_sq
    rw [dist_sq_mkPt, dist_sq_mkPt]; ring

/-! ## §3 Containment in the target — the (C2) check -/

theorem memB : mkPt (-2 : ℝ) 0 ∈ target.carrier :=
  Erdos634.CertCoord.mem_carrier_of_dets hDTpos (by norm_num [det3]) (by norm_num [det3])
    (by norm_num [det3])

theorem memM : mkPt (0 : ℝ) 0 ∈ target.carrier :=
  Erdos634.CertCoord.mem_carrier_of_dets hDTpos (by norm_num [det3]) (by norm_num [det3])
    (by norm_num [det3])

theorem memA : mkPt (0 : ℝ) 1 ∈ target.carrier :=
  Erdos634.CertCoord.mem_carrier_of_dets hDTpos (by norm_num [det3]) (by norm_num [det3])
    (by norm_num [det3])

theorem memC : mkPt (2 : ℝ) 0 ∈ target.carrier :=
  Erdos634.CertCoord.mem_carrier_of_dets hDTpos (by norm_num [det3]) (by norm_num [det3])
    (by norm_num [det3])

theorem tile0_sub : tile0.carrier ⊆ target.carrier := by
  show Erdos634.Geometry.Tri.carrier tile0 ⊆ target.carrier
  unfold Erdos634.Geometry.Tri.carrier
  rw [tile0_pts]
  apply convexHull_min _ target.convex
  rintro p ⟨i, rfl⟩
  fin_cases i
  · exact memB
  · exact memM
  · exact memA

theorem tile1_sub : tile1.carrier ⊆ target.carrier := by
  show Erdos634.Geometry.Tri.carrier tile1 ⊆ target.carrier
  unfold Erdos634.Geometry.Tri.carrier
  rw [tile1_pts]
  apply convexHull_min _ target.convex
  rintro p ⟨i, rfl⟩
  fin_cases i
  · exact memC
  · exact memM
  · exact memA

theorem hsub : ∀ i, (tileF i).carrier ⊆ target.carrier := by
  intro i; fin_cases i
  · exact tile0_sub
  · exact tile1_sub

/-! ## §4 Disjoint interiors — the (C3) check

`tile0` lies in the closed half-plane `x ≤ 0`, `tile1` in `x ≥ 0`; a boundary point (`x = 0`) of
either tile's *interior* would have a whole ball around it inside the tile, but that ball always
contains a point strictly on the wrong side, contradiction. So each interior lies in the
corresponding *open* half-plane, and the two are disjoint. -/

theorem hlin0 : IsLinearMap ℝ (fun y : Plane => y 0) := ⟨fun _ _ => rfl, fun _ _ => rfl⟩

theorem convex_le0 : Convex ℝ {p : Plane | p 0 ≤ 0} := convex_halfSpace_le hlin0 0
theorem convex_ge0 : Convex ℝ {p : Plane | 0 ≤ p 0} := convex_halfSpace_ge hlin0 0

theorem tile0_le0 : tile0.carrier ⊆ {p : Plane | p 0 ≤ 0} := by
  show Erdos634.Geometry.Tri.carrier tile0 ⊆ _
  unfold Erdos634.Geometry.Tri.carrier
  rw [tile0_pts]
  apply convexHull_min _ convex_le0
  rintro p ⟨i, rfl⟩
  fin_cases i <;> simp [mkPt_zero]

theorem tile1_ge0 : tile1.carrier ⊆ {p : Plane | 0 ≤ p 0} := by
  show Erdos634.Geometry.Tri.carrier tile1 ⊆ _
  unfold Erdos634.Geometry.Tri.carrier
  rw [tile1_pts]
  apply convexHull_min _ convex_ge0
  rintro p ⟨i, rfl⟩
  fin_cases i <;> simp [mkPt_zero]

/-- A distance helper mirroring `SssCongruent.dist_of_sq`, specialised to a nonnegative target
value rather than another distance. -/
theorem dist_eq_of_sq {x y : Plane} {s : ℝ} (hs : 0 ≤ s) (h : dist x y ^ 2 = s ^ 2) :
    dist x y = s :=
  (pow_left_inj₀ dist_nonneg hs two_ne_zero).mp h

/-- **A boundary point of a closed half-plane is never interior to a set contained in it.** -/
theorem interior_lt0_of_le0 (T : Tri) (h : T.carrier ⊆ {p : Plane | p 0 ≤ 0}) :
    interior T.carrier ⊆ {p : Plane | p 0 < 0} := by
  intro p hp
  have hp' : p ∈ T.carrier := interior_subset hp
  have hle : p 0 ≤ 0 := h hp'
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exfalso
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior p hp
    set v : Plane := mkPt (r / 2) 0 with hv
    set q : Plane := p + v with hq
    have hq0 : q 0 = p 0 + r / 2 := by
      show p 0 + v 0 = p 0 + r / 2
      rw [hv, mkPt_zero]
    have hq1 : q 1 = p 1 := by
      show p 1 + v 1 = p 1
      rw [hv, mkPt_one]; ring
    have hdistsq : dist p q ^ 2 = (r / 2) ^ 2 := by
      rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two, Real.dist_eq,
        Real.dist_eq, hq0, hq1, sq_abs, sq_abs]
      ring
    have hdisteq : dist p q = r / 2 := dist_eq_of_sq (by linarith) hdistsq
    have hballmem : q ∈ Metric.ball p r := by
      rw [Metric.mem_ball, dist_comm, hdisteq]; linarith
    have hqT : q ∈ T.carrier := interior_subset (hball hballmem)
    have hqle : q 0 ≤ 0 := h hqT
    rw [hq0, ← heq] at hqle
    linarith

/-- The mirror-image statement, for the `x ≥ 0` half-plane. -/
theorem interior_gt0_of_ge0 (T : Tri) (h : T.carrier ⊆ {p : Plane | 0 ≤ p 0}) :
    interior T.carrier ⊆ {p : Plane | 0 < p 0} := by
  intro p hp
  have hp' : p ∈ T.carrier := interior_subset hp
  have hge : 0 ≤ p 0 := h hp'
  rcases lt_or_eq_of_le hge with hlt | heq
  · exact hlt
  · exfalso
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior p hp
    set v : Plane := mkPt (-(r / 2)) 0 with hv
    set q : Plane := p + v with hq
    have hq0 : q 0 = p 0 - r / 2 := by
      show p 0 + v 0 = p 0 - r / 2
      rw [hv, mkPt_zero]; ring
    have hq1 : q 1 = p 1 := by
      show p 1 + v 1 = p 1
      rw [hv, mkPt_one]; ring
    have hdistsq : dist p q ^ 2 = (r / 2) ^ 2 := by
      rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two, Real.dist_eq,
        Real.dist_eq, hq0, hq1, sq_abs, sq_abs]
      ring
    have hdisteq : dist p q = r / 2 := dist_eq_of_sq (by linarith) hdistsq
    have hballmem : q ∈ Metric.ball p r := by
      rw [Metric.mem_ball, dist_comm, hdisteq]; linarith
    have hqT : q ∈ T.carrier := interior_subset (hball hballmem)
    have hqge : 0 ≤ q 0 := h hqT
    rw [hq0, ← heq] at hqge
    linarith

theorem tiles01_disjoint : Disjoint (interior tile0.carrier) (interior tile1.carrier) := by
  rw [Set.disjoint_left]
  intro p hp0 hp1
  have h0 : p 0 < 0 := interior_lt0_of_le0 tile0 tile0_le0 hp0
  have h1 : 0 < p 0 := interior_gt0_of_ge0 tile1 tile1_ge0 hp1
  linarith

theorem hdisj :
    Pairwise fun i j => Disjoint (interior ((tileF i)).carrier) (interior ((tileF j)).carrier) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first
    | exact absurd rfl hij
    | exact tiles01_disjoint
    | exact tiles01_disjoint.symm

/-! ## §5 The area identity — the (C4) check -/

theorem hdet : ∑ i, |Erdos634.AreaDet.detTri (tileF i)| = |Erdos634.AreaDet.detTri target| := by
  have e0 : Erdos634.AreaDet.detTri tile0 = det3 (-2) 0 0 0 0 1 := detTri_mkTri _ _ _ _ _ _ hdet0
  have e1 : Erdos634.AreaDet.detTri tile1 = det3 2 0 0 0 0 1 := detTri_mkTri _ _ _ _ _ _ hdet1
  have eT : Erdos634.AreaDet.detTri target = det3 (-2) 0 2 0 0 1 := detTri_mkTri _ _ _ _ _ _ hDTpos.ne'
  simp only [tileF, Fin.sum_univ_two]
  show |Erdos634.AreaDet.detTri tile0| + |Erdos634.AreaDet.detTri tile1| = _
  rw [e0, e1, eT]
  norm_num [det3]

/-! ## §6 The witness -/

/-- **The witness.** `CertBridge.ofCert` applied to the four checks above: a genuine
`CongruentDissection 2` of the isosceles right-tile target `(α, α, π − 2α)` at `tan α = 1/2`,
transcribing `row3/PROOF.md`'s own `N = 2` control exactly. -/
noncomputable def dissection : CongruentDissection 2 :=
  Erdos634.CertBridge.ofCert target model tileF hd01 hd12 hd20 hsub hdisj hdet

theorem dissection_target : dissection.target = target := rfl
theorem dissection_model : dissection.model = model := rfl

end Erdos634.Draft.FluxGRow3Witness

#print axioms Erdos634.Draft.FluxGRow3Witness.tile0_sub
#print axioms Erdos634.Draft.FluxGRow3Witness.tile1_sub
#print axioms Erdos634.Draft.FluxGRow3Witness.hdisj
#print axioms Erdos634.Draft.FluxGRow3Witness.hdet
#print axioms Erdos634.Draft.FluxGRow3Witness.dissection

-- Draft/LaczFormalRGCaseVWit.lean -- WITNESS for Case V (subcase Va): the rectangle [0,p] x [0,q] cut along a diagonal into two congruent right triangles (a point reflection of each other)
-- is a `PolyTiling 2 4`, `RegularPQ`, with `gamma = pi/2`.  For p = 1, q = sqrt 3 (the 30-60-90 triangle, a = sqrt 3, b = 1, c = 2) `NotComb a b c` holds, so `caseV_Va` fires.
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 9; Sect. 2 (i): parallelograms split along a diagonal), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRGCaseV2
import Erdos634.Draft.LaczFormalGraphWit2
import Erdos634.CertCoord

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

variable {p q : ℝ}

/-- The rectangle `[0,p] x [0,q]` as a convex quadrilateral. -/
noncomputable def rectPoly (p q : ℝ) (hp : 0 < p) (hq : 0 < q) : ConvPoly 4 where
  v := ![mkPt 0 0, mkPt p 0, mkPt p q, mkPt 0 q]
  three_le := by norm_num
  left := by
    intro i j hji hji1
    fin_cases i <;> fin_cases j <;> first | (exfalso; revert hji hji1; decide) | (simp [cross2, mkPt]; nlinarith [mul_pos hp hq])

theorem rectPoly_carrier (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (x : Plane) :
    x ∈ (rectPoly p q hp hq).carrier ↔ 0 ≤ x 0 ∧ x 0 ≤ p ∧ 0 ≤ x 1 ∧ x 1 ≤ q := by
  have hmem : x ∈ (rectPoly p q hp hq).carrier ↔ ∀ i : Fin 4, 0 ≤ cross2 ((rectPoly p q hp hq).v (i + 1) - (rectPoly p q hp hq).v i) (x - (rectPoly p q hp hq).v i) := Iff.rfl
  rw [hmem]
  constructor
  · intro h
    have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
    simp [rectPoly, cross2, mkPt] at h0 h1 h2 h3
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [mul_pos hp hq]
  · rintro ⟨a1, a2, a3, a4⟩ i
    fin_cases i <;> simp [rectPoly, cross2, mkPt] <;> nlinarith [mul_pos hp hq]

theorem det_rect0 (hp : 0 < p) (hq : 0 < q) : det3 p 0 0 q 0 0 ≠ 0 := by
  unfold det3; nlinarith [mul_pos hp hq]
theorem det_rect1 (hp : 0 < p) (hq : 0 < q) : det3 0 q p 0 p q ≠ 0 := by
  unfold det3; nlinarith [mul_pos hp hq]

/-- model tile: vertices `(p,0)`, `(0,q)`, `(0,0)`; the right angle is at vertex 2. -/
noncomputable def rT0 (p q : ℝ) (hp : 0 < p) (hq : 0 < q) : Tri := mkTri p 0 0 q 0 0 (det_rect0 hp hq)
/-- its point reflection through the centre: vertices `(0,q)`, `(p,0)`, `(p,q)`. -/
noncomputable def rT1 (p q : ℝ) (hp : 0 < p) (hq : 0 < q) : Tri := mkTri 0 q p 0 p q (det_rect1 hp hq)

/-- Point reflection `x ↦ (p,q) - x`. -/
noncomputable def rF (p q : ℝ) : Plane ≃ᵢ Plane := (IsometryEquiv.neg Plane).trans (IsometryEquiv.addLeft (mkPt p q))

theorem rF_pts (hp : 0 < p) (hq : 0 < q) (k : Fin 3) : rF p q ((rT1 p q hp hq).pts k) = (rT0 p q hp hq).pts k := by
  fin_cases k
  · show mkPt p q + -(mkPt 0 q) = mkPt p 0
    ext j; fin_cases j <;> simp [mkPt]
  · show mkPt p q + -(mkPt p 0) = mkPt 0 q
    ext j; fin_cases j <;> simp [mkPt]
  · show mkPt p q + -(mkPt p q) = mkPt 0 0
    ext j; fin_cases j <;> simp [mkPt]

theorem rT0_carrier (hp : 0 < p) (hq : 0 < q) (x : Plane) :
    x ∈ (rT0 p q hp hq).carrier ↔ 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ q * x 0 + p * x 1 ≤ p * q := by
  have hori : 0 < cross2 (mkPt 0 q - mkPt p 0) (mkPt 0 0 - mkPt p 0) := by
    simp [cross2, mkPt]; nlinarith [mul_pos hp hq]
  have h := triOf_carrier (mkPt p 0) (mkPt 0 q) (mkPt 0 0) hori x
  have e : (rT0 p q hp hq).carrier = (triOf (mkPt p 0) (mkPt 0 q) (mkPt 0 0) hori).carrier := rfl
  rw [e, h]
  simp [cross2, mkPt]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩ <;> nlinarith [mul_pos hp hq]
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩ <;> nlinarith [mul_pos hp hq]

theorem rT1_carrier (hp : 0 < p) (hq : 0 < q) (x : Plane) :
    x ∈ (rT1 p q hp hq).carrier ↔ x 0 ≤ p ∧ x 1 ≤ q ∧ p * q ≤ q * x 0 + p * x 1 := by
  have hori : 0 < cross2 (mkPt p 0 - mkPt 0 q) (mkPt p q - mkPt 0 q) := by
    simp [cross2, mkPt]; nlinarith [mul_pos hp hq]
  have h := triOf_carrier (mkPt 0 q) (mkPt p 0) (mkPt p q) hori x
  have e : (rT1 p q hp hq).carrier = (triOf (mkPt 0 q) (mkPt p 0) (mkPt p q) hori).carrier := rfl
  rw [e, h]
  simp [cross2, mkPt]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩ <;> nlinarith [mul_pos hp hq]
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩ <;> nlinarith [mul_pos hp hq]

/-- The separating affine functional `x ↦ q x₀ + p x₁`. -/
noncomputable def sepF (p q : ℝ) : Plane →ᵃ[ℝ] ℝ :=
  ((q • (EuclideanSpace.proj (0 : Fin 2) : Plane →L[ℝ] ℝ) + p • (EuclideanSpace.proj (1 : Fin 2) : Plane →L[ℝ] ℝ)) : Plane →L[ℝ] ℝ).toLinearMap.toAffineMap

theorem sepF_apply (p q : ℝ) (x : Plane) : sepF p q x = q * x 0 + p * x 1 := by
  simp [sepF]

theorem sepF_ne (hq : 0 < q) : (sepF p q).linear ≠ 0 := by
  intro h
  have := congrArg (fun l => l (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))) h
  simp [sepF] at this
  linarith

/-- **The rectangle `[0,p] × [0,q]` cut along a diagonal into two congruent right triangles.** -/
noncomputable def rDiss (p q : ℝ) (hp : 0 < p) (hq : 0 < q) : CongruentRegionDissection 2 where
  region := (rectPoly p q hp hq).carrier
  tile := ![rT0 p q hp hq, rT1 p q hp hq]
  covers := by
    ext x
    simp only [Set.mem_iUnion, Fin.exists_fin_two]
    show (x ∈ (rT0 p q hp hq).carrier ∨ x ∈ (rT1 p q hp hq).carrier) ↔ x ∈ (rectPoly p q hp hq).carrier
    rw [rT0_carrier hp hq, rT1_carrier hp hq, rectPoly_carrier p q hp hq]
    constructor
    · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
      · refine ⟨h1, ?_, h2, ?_⟩ <;> nlinarith [mul_pos hp hq]
      · refine ⟨?_, h1, ?_, h2⟩ <;> nlinarith [mul_pos hp hq]
    · rintro ⟨h1, h2, h3, h4⟩
      by_cases hc : q * x 0 + p * x 1 ≤ p * q
      · exact Or.inl ⟨h1, h3, hc⟩
      · exact Or.inr ⟨h2, h4, (not_le.mp hc).le⟩
  interiors_disjoint := by
    intro i j hij
    have hsep : ∀ x ∈ (rT0 p q hp hq).carrier, sepF p q x ≤ p * q := by
      intro x hx; rw [sepF_apply]; exact ((rT0_carrier hp hq x).mp hx).2.2
    have hsep' : ∀ x ∈ (rT1 p q hp hq).carrier, p * q ≤ sepF p q x := by
      intro x hx; rw [sepF_apply]; exact ((rT1_carrier hp hq x).mp hx).2.2
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact Erdos634.CertGeom.interiors_disjoint_of_separating (sepF p q) (sepF_ne hq) (p * q) hsep hsep'
    · exact (Erdos634.CertGeom.interiors_disjoint_of_separating (sepF p q) (sepF_ne hq) (p * q) hsep hsep').symm
    · exact absurd rfl hij
  model := rT0 p q hp hq
  tiles_congruent := by
    intro i
    fin_cases i
    · exact Tri.Congruent.refl _
    · exact ⟨rF p q, Equiv.refl _, rF_pts hp hq⟩

/-- The rectangle tiling as a `PolyTiling 2 4`. -/
noncomputable def rTiling (p q : ℝ) (hp : 0 < p) (hq : 0 < q) : PolyTiling 2 4 where
  C := rDiss p q hp hq
  P := rectPoly p q hp hq
  region_eq := rfl

theorem angleAt_of_iso' {T U : Tri} (f : Plane ≃ᵢ Plane) (hf : ∀ k, f (T.pts k) = U.pts k) (v : Fin 3) :
    angleAt U v = angleAt T v := by
  unfold angleAt cornerAngle
  rw [← hf (v + 1), ← hf v, ← hf (v + 2)]
  have := (f.toRealAffineIsometryEquiv.toAffineIsometry).angle_map (T.pts (v + 1)) (T.pts v) (T.pts (v + 2))
  simpa using this

theorem rDiss_swap0 (hp : 0 < p) (hq : 0 < q) (i : Fin 2) :
    ((rDiss p q hp hq).tile (i + 1)).pts 1 = ((rDiss p q hp hq).tile i).pts 0 := by
  fin_cases i
  · show mkPt p 0 = mkPt p 0; rfl
  · show mkPt 0 q = mkPt 0 q; rfl

theorem rDiss_swap1 (hp : 0 < p) (hq : 0 < q) (i : Fin 2) :
    ((rDiss p q hp hq).tile (i + 1)).pts 0 = ((rDiss p q hp hq).tile i).pts 1 := by
  fin_cases i
  · show mkPt 0 q = mkPt 0 q; rfl
  · show mkPt p 0 = mkPt p 0; rfl

/-- The rectangle tiling is regular. -/
theorem rDiss_regular (hp : 0 < p) (hq : 0 < q) : RegularPQ (rDiss p q hp hq) := by
  refine ⟨fun _ => 1, fun i v => ?_, fun X => ?_⟩
  · fin_cases i
    · rfl
    · exact angleAt_of_iso' (rF p q) (rF_pts hp hq) v
  · unfold cntR
    refine Finset.card_nbij' (fun x => (x.1 + 1, (1 : Fin 3))) (fun x => (x.1 + 1, (0 : Fin 3))) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, Equiv.Perm.coe_one, id_eq] at hx ⊢
      obtain ⟨h1, h2⟩ := hx
      rw [h2] at h1
      exact ⟨by rw [rDiss_swap0]; exact h1, trivial⟩
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, Equiv.Perm.coe_one, id_eq] at hx ⊢
      obtain ⟨h1, h2⟩ := hx
      rw [h2] at h1
      exact ⟨by rw [rDiss_swap1]; exact h1, trivial⟩
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, Equiv.Perm.coe_one, id_eq] at hx
      obtain ⟨i, k⟩ := x
      simp only at hx ⊢
      obtain ⟨h1, h2⟩ := hx
      subst h2
      ext
      · simp only; fin_cases i <;> rfl
      · rfl
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, Equiv.Perm.coe_one, id_eq] at hx
      obtain ⟨i, k⟩ := x
      simp only at hx ⊢
      obtain ⟨h1, h2⟩ := hx
      subst h2
      ext
      · simp only; fin_cases i <;> rfl
      · rfl

/-- The model's `γ`-angle (vertex 2, the origin) is a right angle. -/
theorem rDiss_gamma (hp : 0 < p) (hq : 0 < q) : angleAt (rDiss p q hp hq).model 2 = Real.pi / 2 := by
  show EuclideanGeometry.angle (mkPt p 0) (mkPt 0 0) (mkPt 0 q) = Real.pi / 2
  unfold EuclideanGeometry.angle
  rw [← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
  simp [PiLp.inner_apply, Fin.sum_univ_two, mkPt]

theorem rDiss_slen0 (hp : 0 < p) (hq : 0 < q) : slen (rDiss p q hp hq) 0 = q := by
  show dist (mkPt 0 q) (mkPt 0 0) = q
  rw [EuclideanSpace.dist_eq]
  simp [Fin.sum_univ_two, mkPt]
  exact Real.sqrt_sq hq.le

theorem rDiss_slen1 (hp : 0 < p) (hq : 0 < q) : slen (rDiss p q hp hq) 1 = p := by
  show dist (mkPt 0 0) (mkPt p 0) = p
  rw [EuclideanSpace.dist_eq]
  simp [Fin.sum_univ_two, mkPt]
  exact Real.sqrt_sq hp.le

theorem rDiss_slen2 (hp : 0 < p) (hq : 0 < q) : slen (rDiss p q hp hq) 2 = Real.sqrt (p ^ 2 + q ^ 2) := by
  show dist (mkPt p 0) (mkPt 0 q) = _
  rw [EuclideanSpace.dist_eq]
  simp [Fin.sum_univ_two, mkPt]

theorem notComb_sqrt3 : NotComb (Real.sqrt 3) 1 2 := by
  have := notComb_sqrt 3 2 (by exact_mod_cast (Nat.Prime.irrational_sqrt (by norm_num : Nat.Prime 3)))
  simpa using this

/-- The 30-60-90 rectangle tiling: `[0,1] × [0,√3]` cut along a diagonal. -/
noncomputable def rTilingSqrt3 : PolyTiling 2 4 :=
  rTiling 1 (Real.sqrt 3) one_pos (Real.sqrt_pos.mpr (by norm_num))

theorem rTilingSqrt3_notComb : NotComb (slen rTilingSqrt3.C 0) (slen rTilingSqrt3.C 1) (slen rTilingSqrt3.C 2) := by
  have h0 : slen rTilingSqrt3.C 0 = Real.sqrt 3 := rDiss_slen0 one_pos (Real.sqrt_pos.mpr (by norm_num))
  have h1 : slen rTilingSqrt3.C 1 = 1 := rDiss_slen1 one_pos (Real.sqrt_pos.mpr (by norm_num))
  have h2 : slen rTilingSqrt3.C 2 = 2 := by
    have := rDiss_slen2 (one_pos : (0:ℝ) < 1) (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 3))
    have e : (1:ℝ) ^ 2 + Real.sqrt 3 ^ 2 = 2 ^ 2 := by rw [Real.sq_sqrt (by norm_num)]; norm_num
    rw [e, Real.sqrt_sq (by norm_num)] at this
    exact this
  rw [h0, h1, h2]
  exact notComb_sqrt3

/-- **NON-VACUITY of `caseV_Va`**: on the 30-60-90 rectangle tiling all hypotheses hold (regular, `γ = π/2`, `NotComb a b c`) and conclusion (i) of Theorem 2.1 is obtained. -/
theorem caseV_Va_witness : Concl1 rTilingSqrt3.C rTilingSqrt3.P :=
  caseV_Va rTilingSqrt3 (rDiss_regular one_pos (Real.sqrt_pos.mpr (by norm_num)))
    (rDiss_gamma one_pos (Real.sqrt_pos.mpr (by norm_num))) rTilingSqrt3_notComb

end Erdos634.Draft.LaczFormal.RG

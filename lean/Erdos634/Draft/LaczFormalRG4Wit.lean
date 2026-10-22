-- Draft/LaczFormalRG4Wit.lean -- WITNESS for Case IVa (`caseIV_Va`): the parallelogram with vertices (0,0), (b,0), (b+s,t), (s,t) cut along the diagonal (b,0)-(s,t) into two congruent triangles (a point reflection of
-- each other) is a `PolyTiling 2 4`, `RegularPQ`.  For `b = 1`, `s = a/2`, `t = a sqrt 3 / 2`, `a = (1 + sqrt 13)/2` the tile has gamma = pi/3 at the origin and sides `(a, 1, 2)`, `a` irrational, so `NotComb a 1 2` holds and
-- `caseIV_Va` fires.  This is the two-tile parallelogram of Laczkovich's Theorem 2.1 (i).
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 2 (i), Sect. 8.1), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG4CaseIV
import Erdos634.Draft.LaczFormalRGCaseVWit
import Erdos634.Draft.LaczFormalGraphWit2
import Erdos634.CertCoord

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

variable {b s t : ℝ}

/-- The parallelogram `(0,0), (b,0), (b+s,t), (s,t)`. -/
noncomputable def parPoly (b s t : ℝ) (hb : 0 < b) (ht : 0 < t) : ConvPoly 4 where
  v := ![mkPt 0 0, mkPt b 0, mkPt (b + s) t, mkPt s t]
  three_le := by norm_num
  left := by
    intro i j hji hji1
    fin_cases i <;> fin_cases j <;> first | (exfalso; revert hji hji1; decide) | (simp [cross2, mkPt]; nlinarith [mul_pos hb ht])

theorem parPoly_carrier (hb : 0 < b) (ht : 0 < t) (x : Plane) :
    x ∈ (parPoly b s t hb ht).carrier ↔ 0 ≤ x 1 ∧ x 1 ≤ t ∧ 0 ≤ t * x 0 - s * x 1 ∧ 0 ≤ t * (b - x 0) + s * x 1 := by
  have hmem : x ∈ (parPoly b s t hb ht).carrier ↔ ∀ i : Fin 4, 0 ≤ cross2 ((parPoly b s t hb ht).v (i + 1) - (parPoly b s t hb ht).v i) (x - (parPoly b s t hb ht).v i) := Iff.rfl
  rw [hmem]
  constructor
  · intro h
    have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
    simp [parPoly, cross2, mkPt] at h0 h1 h2 h3
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [mul_pos hb ht]
  · rintro ⟨a1, a2, a3, a4⟩ i
    fin_cases i <;> simp [parPoly, cross2, mkPt] <;> nlinarith [mul_pos hb ht]

theorem det_par0 (hb : 0 < b) (ht : 0 < t) : det3 b 0 s t 0 0 ≠ 0 := by
  unfold det3; nlinarith [mul_pos hb ht]
theorem det_par1 (hb : 0 < b) (ht : 0 < t) : det3 s t b 0 (b + s) t ≠ 0 := by
  unfold det3; nlinarith [mul_pos hb ht]

/-- model tile: vertices `U = (b,0)`, `W = (s,t)`, `O = (0,0)`; the angle `gamma` is at vertex 2. -/
noncomputable def pT0 (b s t : ℝ) (hb : 0 < b) (ht : 0 < t) : Tri := mkTri b 0 s t 0 0 (det_par0 hb ht)
/-- its point reflection through the centre `(U+W)/2`: vertices `W`, `U`, `U + W`. -/
noncomputable def pT1 (b s t : ℝ) (hb : 0 < b) (ht : 0 < t) : Tri := mkTri s t b 0 (b + s) t (det_par1 hb ht)

noncomputable def pF (b s t : ℝ) : Plane ≃ᵢ Plane := (IsometryEquiv.neg Plane).trans (IsometryEquiv.addLeft (mkPt (b + s) t))

theorem pF_pts (hb : 0 < b) (ht : 0 < t) (k : Fin 3) : pF b s t ((pT1 b s t hb ht).pts k) = (pT0 b s t hb ht).pts k := by
  fin_cases k
  · show mkPt (b + s) t + -(mkPt s t) = mkPt b 0
    ext j; fin_cases j <;> simp [mkPt]
  · show mkPt (b + s) t + -(mkPt b 0) = mkPt s t
    ext j; fin_cases j <;> simp [mkPt]
  · show mkPt (b + s) t + -(mkPt (b + s) t) = mkPt 0 0
    ext j; fin_cases j <;> simp [mkPt]

theorem pT0_carrier (hb : 0 < b) (ht : 0 < t) (x : Plane) :
    x ∈ (pT0 b s t hb ht).carrier ↔ 0 ≤ x 1 ∧ 0 ≤ t * x 0 - s * x 1 ∧ t * x 0 + (b - s) * x 1 ≤ b * t := by
  have hori : 0 < cross2 (mkPt s t - mkPt b 0) (mkPt 0 0 - mkPt b 0) := by
    simp [cross2, mkPt]; nlinarith [mul_pos hb ht]
  have h := triOf_carrier (mkPt b 0) (mkPt s t) (mkPt 0 0) hori x
  have e : (pT0 b s t hb ht).carrier = (triOf (mkPt b 0) (mkPt s t) (mkPt 0 0) hori).carrier := rfl
  rw [e, h]
  simp [cross2, mkPt]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩ <;> nlinarith [mul_pos hb ht]
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩ <;> nlinarith [mul_pos hb ht]

theorem pT1_carrier (hb : 0 < b) (ht : 0 < t) (x : Plane) :
    x ∈ (pT1 b s t hb ht).carrier ↔ x 1 ≤ t ∧ 0 ≤ s * x 1 - t * (x 0 - b) ∧ b * t ≤ t * x 0 + (b - s) * x 1 := by
  have hori : 0 < cross2 (mkPt b 0 - mkPt s t) (mkPt (b + s) t - mkPt s t) := by
    simp [cross2, mkPt]; nlinarith [mul_pos hb ht]
  have h := triOf_carrier (mkPt s t) (mkPt b 0) (mkPt (b + s) t) hori x
  have e : (pT1 b s t hb ht).carrier = (triOf (mkPt s t) (mkPt b 0) (mkPt (b + s) t) hori).carrier := rfl
  rw [e, h]
  simp [cross2, mkPt]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩ <;> nlinarith [mul_pos hb ht]
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩ <;> nlinarith [mul_pos hb ht]

/-- The separating affine functional `x ↦ t x₀ + (b - s) x₁` (the diagonal `U W`). -/
noncomputable def sepP (b s t : ℝ) : Plane →ᵃ[ℝ] ℝ :=
  ((t • (EuclideanSpace.proj (0 : Fin 2) : Plane →L[ℝ] ℝ) + (b - s) • (EuclideanSpace.proj (1 : Fin 2) : Plane →L[ℝ] ℝ)) : Plane →L[ℝ] ℝ).toLinearMap.toAffineMap

theorem sepP_apply (b s t : ℝ) (x : Plane) : sepP b s t x = t * x 0 + (b - s) * x 1 := by
  simp [sepP]

theorem sepP_ne (ht : 0 < t) : (sepP b s t).linear ≠ 0 := by
  intro h
  have := congrArg (fun l => l (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))) h
  simp [sepP] at this
  linarith

/-- **The parallelogram cut along a diagonal into two congruent triangles.** -/
noncomputable def pDiss (b s t : ℝ) (hb : 0 < b) (ht : 0 < t) : CongruentRegionDissection 2 where
  region := (parPoly b s t hb ht).carrier
  tile := ![pT0 b s t hb ht, pT1 b s t hb ht]
  covers := by
    ext x
    simp only [Set.mem_iUnion, Fin.exists_fin_two]
    show (x ∈ (pT0 b s t hb ht).carrier ∨ x ∈ (pT1 b s t hb ht).carrier) ↔ x ∈ (parPoly b s t hb ht).carrier
    rw [pT0_carrier hb ht, pT1_carrier hb ht, parPoly_carrier hb ht]
    constructor
    · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
      · refine ⟨h1, ?_, h2, ?_⟩ <;> nlinarith [mul_pos hb ht]
      · refine ⟨?_, h1, ?_, ?_⟩ <;> nlinarith [mul_pos hb ht]
    · rintro ⟨h1, h2, h3, h4⟩
      by_cases hc : t * x 0 + (b - s) * x 1 ≤ b * t
      · exact Or.inl ⟨h1, h3, hc⟩
      · exact Or.inr ⟨h2, by nlinarith [mul_pos hb ht], (not_le.mp hc).le⟩
  interiors_disjoint := by
    intro i j hij
    have hsep : ∀ x ∈ (pT0 b s t hb ht).carrier, sepP b s t x ≤ b * t := by
      intro x hx; rw [sepP_apply]; exact ((pT0_carrier hb ht x).mp hx).2.2
    have hsep' : ∀ x ∈ (pT1 b s t hb ht).carrier, b * t ≤ sepP b s t x := by
      intro x hx; rw [sepP_apply]; exact ((pT1_carrier hb ht x).mp hx).2.2
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact Erdos634.CertGeom.interiors_disjoint_of_separating (sepP b s t) (sepP_ne ht) (b * t) hsep hsep'
    · exact (Erdos634.CertGeom.interiors_disjoint_of_separating (sepP b s t) (sepP_ne ht) (b * t) hsep hsep').symm
    · exact absurd rfl hij
  model := pT0 b s t hb ht
  tiles_congruent := by
    intro i
    fin_cases i
    · exact Tri.Congruent.refl _
    · exact ⟨pF b s t, Equiv.refl _, pF_pts hb ht⟩

noncomputable def pTiling (b s t : ℝ) (hb : 0 < b) (ht : 0 < t) : PolyTiling 2 4 where
  C := pDiss b s t hb ht
  P := parPoly b s t hb ht
  region_eq := rfl

theorem pDiss_swap0 (hb : 0 < b) (ht : 0 < t) (i : Fin 2) :
    ((pDiss b s t hb ht).tile (i + 1)).pts 1 = ((pDiss b s t hb ht).tile i).pts 0 := by
  fin_cases i
  · show mkPt b 0 = mkPt b 0; rfl
  · show mkPt s t = mkPt s t; rfl

theorem pDiss_swap1 (hb : 0 < b) (ht : 0 < t) (i : Fin 2) :
    ((pDiss b s t hb ht).tile (i + 1)).pts 0 = ((pDiss b s t hb ht).tile i).pts 1 := by
  fin_cases i
  · show mkPt s t = mkPt s t; rfl
  · show mkPt b 0 = mkPt b 0; rfl

theorem pDiss_regular (hb : 0 < b) (ht : 0 < t) : RegularPQ (pDiss b s t hb ht) := by
  refine ⟨fun _ => 1, fun i v => ?_, fun X => ?_⟩
  · fin_cases i
    · rfl
    · exact angleAt_of_iso' (pF b s t) (pF_pts hb ht) v
  · unfold cntR
    refine Finset.card_nbij' (fun x => (x.1 + 1, (1 : Fin 3))) (fun x => (x.1 + 1, (0 : Fin 3))) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, Equiv.Perm.coe_one, id_eq] at hx ⊢
      obtain ⟨h1, h2⟩ := hx
      rw [h2] at h1
      exact ⟨by rw [pDiss_swap0]; exact h1, trivial⟩
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, Equiv.Perm.coe_one, id_eq] at hx ⊢
      obtain ⟨h1, h2⟩ := hx
      rw [h2] at h1
      exact ⟨by rw [pDiss_swap1]; exact h1, trivial⟩
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

/-! ## The instance: `b = 1`, `a = (1 + √13)/2`, `s = a/2`, `t = a√3/2`: tile `(a, 1, 2)` with `γ = π/3` -/

noncomputable def wA : ℝ := (1 + Real.sqrt 13) / 2
noncomputable def wS : ℝ := wA / 2
noncomputable def wT : ℝ := wA * Real.sqrt 3 / 2

theorem sqrt13_sq : Real.sqrt 13 ^ 2 = 13 := Real.sq_sqrt (by norm_num)
theorem sqrt3_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

theorem wA_pos : 0 < wA := by unfold wA; positivity
theorem wA_sq : wA ^ 2 = wA + 3 := by
  unfold wA; nlinarith [sqrt13_sq]
theorem wT_pos : 0 < wT := by unfold wT; have := wA_pos; positivity

theorem wS_sq_add : wS ^ 2 + wT ^ 2 = wA ^ 2 := by
  unfold wS wT; nlinarith [sqrt3_sq]

theorem wA_irrational : Irrational wA := by
  rintro ⟨q, hq⟩
  have h : Irrational (Real.sqrt 13) := by exact_mod_cast Nat.Prime.irrational_sqrt (by norm_num : Nat.Prime 13)
  apply h
  refine ⟨2 * q - 1, ?_⟩
  unfold wA at hq
  push_cast
  linarith

theorem wA_notComb : NotComb wA 1 2 := by
  intro r p q hr h
  apply wA_irrational
  refine ⟨((p + 2 * q : ℕ) : ℚ) / r, ?_⟩
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  push_cast
  field_simp
  linarith

noncomputable def wTiling : PolyTiling 2 4 := pTiling 1 wS wT one_pos wT_pos

theorem wDiss_slen0 : slen wTiling.C 0 = wA := by
  show dist (mkPt wS wT) (mkPt 0 0) = wA
  rw [EuclideanSpace.dist_eq]
  simp [Fin.sum_univ_two, mkPt]
  rw [wS_sq_add]
  exact Real.sqrt_sq wA_pos.le

theorem wDiss_slen1 : slen wTiling.C 1 = 1 := by
  show dist (mkPt 0 0) (mkPt 1 0) = 1
  rw [EuclideanSpace.dist_eq]
  simp [Fin.sum_univ_two, mkPt]

theorem wDiss_slen2 : slen wTiling.C 2 = 2 := by
  show dist (mkPt 1 0) (mkPt wS wT) = 2
  rw [EuclideanSpace.dist_eq]
  simp [Fin.sum_univ_two, mkPt]
  have : (1 - wS) ^ 2 + wT ^ 2 = 2 ^ 2 := by
    have h1 := wS_sq_add
    have h2 := wA_sq
    have h3 : wS = wA / 2 := rfl
    nlinarith [h1, h2, h3]
  rw [Real.dist_eq, sq_abs, this]
  exact Real.sqrt_sq (by norm_num)

theorem wTiling_notComb : NotComb (slen wTiling.C 0) (slen wTiling.C 1) (slen wTiling.C 2) := by
  rw [wDiss_slen0, wDiss_slen1, wDiss_slen2]; exact wA_notComb

theorem wTiling_gamma : angleAt wTiling.C.model 2 = Real.pi / 3 := by
  show EuclideanGeometry.angle (mkPt 1 0) (mkPt 0 0) (mkPt wS wT) = Real.pi / 3
  unfold EuclideanGeometry.angle
  simp only [vsub_eq_sub]
  have hn : ‖mkPt wS wT - mkPt 0 0‖ = wA := by
    rw [← dist_eq_norm]
    have := wDiss_slen0
    unfold slen at this
    exact this
  have hn1 : ‖mkPt 1 0 - mkPt 0 0‖ = 1 := by
    rw [← dist_eq_norm]
    have := wDiss_slen1
    unfold slen at this
    rw [dist_comm]; exact this
  have hin : inner ℝ (mkPt 1 0 - mkPt 0 0) (mkPt wS wT - mkPt 0 0) = wS := by
    simp [PiLp.inner_apply, Fin.sum_univ_two, mkPt]
  unfold InnerProductGeometry.angle
  rw [hin, hn, hn1]
  have : wS / (1 * wA) = Real.cos (Real.pi / 3) := by
    rw [Real.cos_pi_div_three]; unfold wS; have := wA_pos; field_simp
  rw [this, Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])]

/-- **NON-VACUITY of `caseIV_Va`**: on the two-triangle parallelogram of the tile `(a, 1, 2)`, `a = (1+√13)/2`, `γ = π/3`, all hypotheses hold and conclusion (i) of Theorem 2.1 is obtained. -/
theorem caseIV_Va_witness : Concl1 wTiling.C wTiling.P :=
  caseIV_Va wTiling (pDiss_regular one_pos wT_pos) wTiling_gamma wTiling_notComb

end Erdos634.Draft.LaczFormal.RG

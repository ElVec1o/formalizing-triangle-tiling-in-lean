-- Draft/LaczFormalIVcRatWit2.lean -- NON-VACUITY of `ivc_rat_final` (Laczkovich DCG 48 (2012), Sect. 2 (vi), 8.3, Concl9; Thm 2.1 (ix)):
-- the REGULAR hexagon of side 2 (lattice vertices (0,0),(2,0),(2,2),(0,4),(-2,4),(-2,2) in the basis e0 = (1,0), e1 = (1/2, sqrt3/2)) is cut into three rhombi
-- (centre (0,2)), each into two 2 x 1 parallelogram cells (angle pi/3), each along a diagonal into two copies of the tile (1, 2, sqrt 3): 12 tiles, `RegularPQ`.
-- EXACT cover and disjointness (cells are lattice half-plane boxes `*_iff`, not sampled).  `rat_hex_witness` applies `ivc_rat_final` (M = 6 >= 5, gamma = pi/3,
-- a ~ b, c not ~ a, alpha = pi/6 rational) and obtains `Thm21Concl`.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 2 (vi), 8.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIVcRatWit1
import Erdos634.Draft.LaczFormalIVcRatBr8a

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

/-- lattice cell: `G = Gp e0 + Gq e1`, `u = ua e0 + ub e1`, `w = wa e0 + wb e1`, `|u|^2 = 4`, `|w|^2 = 1`, `u.w = 1`. -/
noncomputable def lcellE (Gp Gq ua ub wa wb : ℝ) (hD : ua * wb - ub * wa ≠ 0) (hu : ua ^ 2 + ua * ub + ub ^ 2 = 4)
    (hw : wa ^ 2 + wa * wb + wb ^ 2 = 1) (huw : ua * wa + (ua * wb + ub * wa) / 2 + ub * wb = 1) : CongruentRegionDissection 2 :=
  cellE (Gp + Gq / 2) (Gq * iT) (ua + ub / 2) (ub * iT) (wa + wb / 2) (wb * iT) (hDlat hD)
    (by linear_combination hu + ub ^ 2 * iT_sq) (by linear_combination hw + wb ^ 2 * iT_sq)
    (by linear_combination huw + (ub * wb) * iT_sq)

theorem lcellE_regular {Gp Gq ua ub wa wb : ℝ} (hD : ua * wb - ub * wa ≠ 0) (hu : ua ^ 2 + ua * ub + ub ^ 2 = 4)
    (hw : wa ^ 2 + wa * wb + wb ^ 2 = 1) (huw : ua * wa + (ua * wb + ub * wa) / 2 + ub * wb = 1) :
    RegularPQ (lcellE Gp Gq ua ub wa wb hD hu hw huw) := cellE_regular _ _ _ _

theorem lcellE_region {Gp Gq ua ub wa wb : ℝ} (hD : ua * wb - ub * wa ≠ 0) (hu : ua ^ 2 + ua * ub + ub ^ 2 = 4)
    (hw : wa ^ 2 + wa * wb + wb ^ 2 = 1) (huw : ua * wa + (ua * wb + ub * wa) / 2 + ub * wb = 1) :
    (lcellE Gp Gq ua ub wa wb hD hu hw huw).region = Par (Gp + Gq / 2) (Gq * iT) (ua + ub / 2) (ub * iT) (wa + wb / 2) (wb * iT) := rfl

theorem lcellE_model {Gp Gq ua ub wa wb : ℝ} (hD : ua * wb - ub * wa ≠ 0) (hu : ua ^ 2 + ua * ub + ub ^ 2 = 4)
    (hw : wa ^ 2 + wa * wb + wb ^ 2 = 1) (huw : ua * wa + (ua * wb + ub * wa) / 2 + ub * wb = 1) :
    (lcellE Gp Gq ua ub wa wb hD hu hw huw).model = rT.C.model := rfl

noncomputable def eC1 := lcellE (-2) 4 0 (-2) 1 (-1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
noncomputable def eC2 := lcellE (-1) 3 0 (-2) 1 (-1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
noncomputable def eA1 := lcellE 0 0 2 0 0 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
noncomputable def eA2 := lcellE 0 1 2 0 0 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
noncomputable def eB1 := lcellE 2 2 (-2) 0 (-1) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
noncomputable def eB2 := lcellE 1 3 (-2) 0 (-1) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem C1_iff (p q : ℝ) : Phi p q ∈ eC1.region ↔ -2 ≤ p ∧ p ≤ -1 ∧ 0 ≤ p + q ∧ p + q ≤ 2 := by
  show Phi p q ∈ Par _ _ _ _ _ _ ↔ _
  rw [par_lat]
  constructor
  · rintro ⟨l, m, hl, hl1, hm, hm1, h0, h1⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
  · rintro ⟨a, b, c, d⟩
    exact ⟨(2 - p - q) / 2, p + 2, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem C2_iff (p q : ℝ) : Phi p q ∈ eC2.region ↔ -1 ≤ p ∧ p ≤ 0 ∧ 0 ≤ p + q ∧ p + q ≤ 2 := by
  show Phi p q ∈ Par _ _ _ _ _ _ ↔ _
  rw [par_lat]
  constructor
  · rintro ⟨l, m, hl, hl1, hm, hm1, h0, h1⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
  · rintro ⟨a, b, c, d⟩
    exact ⟨(2 - p - q) / 2, p + 1, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem A1_iff (p q : ℝ) : Phi p q ∈ eA1.region ↔ 0 ≤ p ∧ p ≤ 2 ∧ 0 ≤ q ∧ q ≤ 1 := by
  show Phi p q ∈ Par _ _ _ _ _ _ ↔ _
  rw [par_lat]
  constructor
  · rintro ⟨l, m, hl, hl1, hm, hm1, h0, h1⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
  · rintro ⟨a, b, c, d⟩
    exact ⟨p / 2, q, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem A2_iff (p q : ℝ) : Phi p q ∈ eA2.region ↔ 0 ≤ p ∧ p ≤ 2 ∧ 1 ≤ q ∧ q ≤ 2 := by
  show Phi p q ∈ Par _ _ _ _ _ _ ↔ _
  rw [par_lat]
  constructor
  · rintro ⟨l, m, hl, hl1, hm, hm1, h0, h1⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
  · rintro ⟨a, b, c, d⟩
    exact ⟨p / 2, q - 1, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem B1_iff (p q : ℝ) : Phi p q ∈ eB1.region ↔ 2 ≤ q ∧ q ≤ 3 ∧ 2 ≤ p + q ∧ p + q ≤ 4 := by
  show Phi p q ∈ Par _ _ _ _ _ _ ↔ _
  rw [par_lat]
  constructor
  · rintro ⟨l, m, hl, hl1, hm, hm1, h0, h1⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
  · rintro ⟨a, b, c, d⟩
    exact ⟨(4 - p - q) / 2, q - 2, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem B2_iff (p q : ℝ) : Phi p q ∈ eB2.region ↔ 3 ≤ q ∧ q ≤ 4 ∧ 2 ≤ p + q ∧ p + q ≤ 4 := by
  show Phi p q ∈ Par _ _ _ _ _ _ ↔ _
  rw [par_lat]
  constructor
  · rintro ⟨l, m, hl, hl1, hm, hm1, h0, h1⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
  · rintro ⟨a, b, c, d⟩
    exact ⟨(4 - p - q) / 2, q - 3, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem C1C2 : Disjoint eC1.region (interior eC2.region) :=
  disj_p (-1) (fun p q h => by have := ((C1_iff p q).mp h); linarith [this.1, this.2.1, this.2.2.1, this.2.2.2]) (fun p q h => by have := ((C2_iff p q).mp h); linarith [this.1, this.2.1, this.2.2.1, this.2.2.2])
theorem C1A1 : Disjoint eC1.region (interior eA1.region) :=
  disj_p 0 (fun p q h => by have := ((C1_iff p q).mp h); linarith [this.1, this.2.1, this.2.2.1, this.2.2.2]) (fun p q h => by have := ((A1_iff p q).mp h); linarith [this.1, this.2.1, this.2.2.1, this.2.2.2])
theorem C1A2 : Disjoint eC1.region (interior eA2.region) :=
  disj_p 0 (fun p q h => by have := ((C1_iff p q).mp h); linarith [this.1, this.2.1, this.2.2.1, this.2.2.2]) (fun p q h => by have := ((A2_iff p q).mp h); linarith [this.1, this.2.1, this.2.2.1, this.2.2.2])
theorem C1B1 : Disjoint eC1.region (interior eB1.region) :=
  disj_pq 2 (fun p q h => by have := ((C1_iff p q).mp h); linarith [this.1, this.2.1, this.2.2.1, this.2.2.2]) (fun p q h => by have := ((B1_iff p q).mp h); linarith [this.1, this.2.1, this.2.2.1, this.2.2.2])
theorem C1B2 : Disjoint eC1.region (interior eB2.region) :=
  disj_pq 2 (fun p q h => by have := ((C1_iff p q).mp h); linarith [this.1, this.2.1, this.2.2.1, this.2.2.2]) (fun p q h => by have := ((B2_iff p q).mp h); linarith [this.1, this.2.1, this.2.2.1, this.2.2.2])
theorem C2A1 : Disjoint eC2.region (interior eA1.region) :=
  disj_p 0 (fun p q h => by have := ((C2_iff p q).mp h); linarith [this.1, this.2.1, this.2.2.1, this.2.2.2]) (fun p q h => by have := ((A1_iff p q).mp h); linarith [this.1, this.2.1, this.2.2.1, this.2.2.2])
theorem C2A2 : Disjoint eC2.region (interior eA2.region) :=
  disj_p 0 (fun p q h => by have := ((C2_iff p q).mp h); linarith [this.1, this.2.1, this.2.2.1, this.2.2.2]) (fun p q h => by have := ((A2_iff p q).mp h); linarith [this.1, this.2.1, this.2.2.1, this.2.2.2])
theorem C2B1 : Disjoint eC2.region (interior eB1.region) :=
  disj_pq 2 (fun p q h => by have := ((C2_iff p q).mp h); linarith [this.1, this.2.1, this.2.2.1, this.2.2.2]) (fun p q h => by have := ((B1_iff p q).mp h); linarith [this.1, this.2.1, this.2.2.1, this.2.2.2])
theorem C2B2 : Disjoint eC2.region (interior eB2.region) :=
  disj_pq 2 (fun p q h => by have := ((C2_iff p q).mp h); linarith [this.1, this.2.1, this.2.2.1, this.2.2.2]) (fun p q h => by have := ((B2_iff p q).mp h); linarith [this.1, this.2.1, this.2.2.1, this.2.2.2])
theorem A1A2 : Disjoint eA1.region (interior eA2.region) :=
  disj_q 1 (fun p q h => by have := ((A1_iff p q).mp h); linarith [this.1, this.2.1, this.2.2.1, this.2.2.2]) (fun p q h => by have := ((A2_iff p q).mp h); linarith [this.1, this.2.1, this.2.2.1, this.2.2.2])
theorem A1B1 : Disjoint eA1.region (interior eB1.region) :=
  disj_q 2 (fun p q h => by have := ((A1_iff p q).mp h); linarith [this.1, this.2.1, this.2.2.1, this.2.2.2]) (fun p q h => by have := ((B1_iff p q).mp h); linarith [this.1, this.2.1, this.2.2.1, this.2.2.2])
theorem A1B2 : Disjoint eA1.region (interior eB2.region) :=
  disj_q 2 (fun p q h => by have := ((A1_iff p q).mp h); linarith [this.1, this.2.1, this.2.2.1, this.2.2.2]) (fun p q h => by have := ((B2_iff p q).mp h); linarith [this.1, this.2.1, this.2.2.1, this.2.2.2])
theorem A2B1 : Disjoint eA2.region (interior eB1.region) :=
  disj_q 2 (fun p q h => by have := ((A2_iff p q).mp h); linarith [this.1, this.2.1, this.2.2.1, this.2.2.2]) (fun p q h => by have := ((B1_iff p q).mp h); linarith [this.1, this.2.1, this.2.2.1, this.2.2.2])
theorem A2B2 : Disjoint eA2.region (interior eB2.region) :=
  disj_q 2 (fun p q h => by have := ((A2_iff p q).mp h); linarith [this.1, this.2.1, this.2.2.1, this.2.2.2]) (fun p q h => by have := ((B2_iff p q).mp h); linarith [this.1, this.2.1, this.2.2.1, this.2.2.2])
theorem B1B2 : Disjoint eB1.region (interior eB2.region) :=
  disj_q 3 (fun p q h => by have := ((B1_iff p q).mp h); linarith [this.1, this.2.1, this.2.2.1, this.2.2.2]) (fun p q h => by have := ((B2_iff p q).mp h); linarith [this.1, this.2.1, this.2.2.1, this.2.2.2])

noncomputable def rU1 : CongruentRegionDissection (2 + 2) :=
  unionCongruentRegion eC1 eC2 rfl (disj_int C1C2)
noncomputable def rU2 : CongruentRegionDissection (2 + 2 + 2) :=
  unionCongruentRegion rU1 eA1 rfl (disj_int (disj_union C1A1 C2A1))
noncomputable def rU3 : CongruentRegionDissection (2 + 2 + 2 + 2) :=
  unionCongruentRegion rU2 eA2 rfl (disj_int (disj_union (disj_union C1A2 C2A2) A1A2))
noncomputable def rU4 : CongruentRegionDissection (2 + 2 + 2 + 2 + 2) :=
  unionCongruentRegion rU3 eB1 rfl (disj_int (disj_union (disj_union (disj_union C1B1 C2B1) A1B1) A2B1))
noncomputable def rhexC : CongruentRegionDissection (2 + 2 + 2 + 2 + 2 + 2) :=
  unionCongruentRegion rU4 eB2 rfl (disj_int (disj_union (disj_union (disj_union (disj_union C1B2 C2B2) A1B2) A2B2) B1B2))

theorem rhexC_region : rhexC.region = eC1.region ∪ eC2.region ∪ eA1.region ∪ eA2.region ∪ eB1.region ∪ eB2.region := rfl

theorem rhexC_regular : RegularPQ rhexC :=
  regular_union _ _ _ _ (regular_union _ _ _ _ (regular_union _ _ _ _ (regular_union _ _ _ _ (regular_union _ _ _ _ (lcellE_regular _ _ _ _) (lcellE_regular _ _ _ _)) (lcellE_regular _ _ _ _)) (lcellE_regular _ _ _ _)) (lcellE_regular _ _ _ _)) (lcellE_regular _ _ _ _)

theorem rhexC_model : rhexC.model = rT.C.model := rfl

/-- The regular hexagon of side 2. -/
noncomputable def rhexPoly : ConvPoly 6 where
  v := ![Phi 0 0, Phi 2 0, Phi 2 2, Phi 0 4, Phi (-2) 4, Phi (-2) 2]
  three_le := by norm_num
  left := by
    intro i j hji hji1
    fin_cases i <;> fin_cases j <;>
      first | (exfalso; revert hji hji1; decide) | (simp [cross2, mkPt, Phi]; nlinarith [iT_pos])

theorem rhex_iff (p q : ℝ) : Phi p q ∈ rhexPoly.carrier ↔ 0 ≤ q ∧ p ≤ 2 ∧ p + q ≤ 4 ∧ q ≤ 4 ∧ -2 ≤ p ∧ 0 ≤ p + q := by
  have hh := iT_pos
  have hmem : Phi p q ∈ rhexPoly.carrier ↔ ∀ i : Fin 6, 0 ≤ cross2 (rhexPoly.v (i + 1) - rhexPoly.v i) (Phi p q - rhexPoly.v i) := Iff.rfl
  rw [hmem]
  constructor
  · intro h
    have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3; have h4 := h 4; have h5 := h 5
    simp [rhexPoly, cross2, mkPt, Phi] at h0 h1 h2 h3 h4 h5
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith
  · rintro ⟨a1, a2, a3, a4, a5, a6⟩ i
    fin_cases i <;> simp [rhexPoly, cross2, mkPt, Phi] <;>
      nlinarith [mul_nonneg hh.le (sub_nonneg.2 a1), mul_nonneg hh.le (sub_nonneg.2 a2), mul_nonneg hh.le (sub_nonneg.2 a3),
        mul_nonneg hh.le (sub_nonneg.2 a4), mul_nonneg hh.le (sub_nonneg.2 a5), mul_nonneg hh.le (sub_nonneg.2 a6)]

theorem rhexC_region_eq : rhexC.region = rhexPoly.carrier := by
  rw [rhexC_region]
  ext x
  obtain ⟨p, q, rfl⟩ := exists_lat x
  simp only [Set.mem_union]
  rw [C1_iff, C2_iff, A1_iff, A2_iff, B1_iff, B2_iff, rhex_iff]
  constructor
  · rintro (((((h | h) | h) | h) | h) | h) <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith [h.1, h.2.1, h.2.2.1, h.2.2.2]
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    by_cases hB : 2 ≤ q ∧ 2 ≤ p + q
    · obtain ⟨hq2, hs2⟩ := hB
      by_cases hp : p ≤ 0
      · by_cases hs : p + q ≤ 2
        · have hp2 : p ≤ 0 := hp
          by_cases hp1 : p ≤ -1
          · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨h5, hp1, h6, hs⟩))))
          · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨by linarith, hp, h6, hs⟩))))
        · by_cases hq3 : q ≤ 3
          · exact Or.inl (Or.inr ⟨hq2, hq3, hs2, h3⟩)
          · exact Or.inr ⟨by linarith, h4, hs2, h3⟩
      · by_cases hq3 : q ≤ 3
        · exact Or.inl (Or.inr ⟨hq2, hq3, hs2, h3⟩)
        · exact Or.inr ⟨by linarith, h4, hs2, h3⟩
    · by_cases hp : p ≤ 0
      · by_cases hp1 : p ≤ -1
        · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨h5, hp1, h6, by by_contra hc; exact hB ⟨by linarith, by linarith⟩⟩))))
        · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨by linarith, hp, h6, by by_contra hc; exact hB ⟨by linarith, by linarith⟩⟩))))
      · have hq2 : q ≤ 2 := by by_contra hc; exact hB ⟨by linarith, by linarith⟩
        by_cases hq1 : q ≤ 1
        · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨by linarith, h2, h1, hq1⟩)))
        · exact Or.inl (Or.inl (Or.inr ⟨by linarith, h2, by linarith, hq2⟩))

end Erdos634.Draft.LaczFormal.RG

-- Draft/LaczFormalIVcHexWit.lean -- NON-VACUITY of the M = 6 branch of `ivc_final_ge5` (Laczkovich Case IV irrational, DCG 48 (2012), Sect. 2 (vi), 8.3):
-- the equiangular hexagon (all angles 2 pi/3) with sides 1, 3, 3, 1, 3, 3 (lattice vertices (0,0),(1,0),(1,3),(-2,6),(-3,6),(-3,3) in the basis e0 = (1,0), e1 = (1/2, sqrt3/2))
-- is cut into FIVE parallelogram cells (the (1,3), (3,1) parallelograms and the (3,3) rhombus as three (1,3) strips), each cut along its short diagonal into two copies of the
-- tile (1, 3, sqrt7), gamma = pi/3: 10 tiles, `RegularPQ`.  `hex_witness` applies `ivc_final_ge5` to this `PolyTiling` and obtains `Concl6`.
-- So EVERY hypothesis of `ivc_final_ge5` (including 5 <= M, here M = 6) is witnessed; the branch is not vacuous.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 2 (vi), 8.3), Beeson-Zhang.
import Erdos634.Draft.LaczFormalHexCell
import Erdos634.Draft.LaczFormalIVcFinal

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

/-- lattice point `(p, q)` -> plane point `p e0 + q e1`. -/
noncomputable def Phi (p q : ℝ) : Plane := mkPt (p + q / 2) (q * iT)

theorem exists_lat (x : Plane) : ∃ p q : ℝ, x = Phi p q := by
  have hh := iT_pos
  refine ⟨x 0 - x 1 / iT / 2, x 1 / iT, ?_⟩
  ext j
  fin_cases j
  · simp [Phi, mkPt]
  · simp [Phi, mkPt]; field_simp

theorem Phi_0 (p q : ℝ) : Phi p q 0 = p + q / 2 := by simp [Phi, mkPt]
theorem Phi_1 (p q : ℝ) : Phi p q 1 = q * iT := by simp [Phi, mkPt]

/-! ## lattice cells -/

theorem hDlat {ua ub wa wb : ℝ} (h : ua * wb - ub * wa ≠ 0) :
    (ua + ub / 2) * (wb * iT) - (ub * iT) * (wa + wb / 2) ≠ 0 := by
  have e : (ua + ub / 2) * (wb * iT) - (ub * iT) * (wa + wb / 2) = iT * (ua * wb - ub * wa) := by ring
  rw [e]; exact mul_ne_zero iT_pos.ne' h

/-- A lattice cell: `G = Gp e0 + Gq e1`, `u = ua e0 + ub e1`, `w = wa e0 + wb e1`, with `|u|^2 = 9`, `|w|^2 = 1`, `u.w = 3/2`. -/
noncomputable def lcell (Gp Gq ua ub wa wb : ℝ) (hD : ua * wb - ub * wa ≠ 0) (hu : ua ^ 2 + ua * ub + ub ^ 2 = 9)
    (hw : wa ^ 2 + wa * wb + wb ^ 2 = 1) (huw : ua * wa + (ua * wb + ub * wa) / 2 + ub * wb = 3 / 2) : CongruentRegionDissection 2 :=
  cellD (Gp + Gq / 2) (Gq * iT) (ua + ub / 2) (ub * iT) (wa + wb / 2) (wb * iT) (hDlat hD)
    (by linear_combination hu + ub ^ 2 * iT_sq) (by linear_combination hw + wb ^ 2 * iT_sq)
    (by linear_combination huw + (ub * wb) * iT_sq)

theorem lcell_regular {Gp Gq ua ub wa wb : ℝ} (hD : ua * wb - ub * wa ≠ 0) (hu : ua ^ 2 + ua * ub + ub ^ 2 = 9)
    (hw : wa ^ 2 + wa * wb + wb ^ 2 = 1) (huw : ua * wa + (ua * wb + ub * wa) / 2 + ub * wb = 3 / 2) :
    RegularPQ (lcell Gp Gq ua ub wa wb hD hu hw huw) := cellD_regular _ _ _ _

theorem lcell_region {Gp Gq ua ub wa wb : ℝ} (hD : ua * wb - ub * wa ≠ 0) (hu : ua ^ 2 + ua * ub + ub ^ 2 = 9)
    (hw : wa ^ 2 + wa * wb + wb ^ 2 = 1) (huw : ua * wa + (ua * wb + ub * wa) / 2 + ub * wb = 3 / 2) :
    (lcell Gp Gq ua ub wa wb hD hu hw huw).region = Par (Gp + Gq / 2) (Gq * iT) (ua + ub / 2) (ub * iT) (wa + wb / 2) (wb * iT) := rfl

theorem lcell_model {Gp Gq ua ub wa wb : ℝ} (hD : ua * wb - ub * wa ≠ 0) (hu : ua ^ 2 + ua * ub + ub ^ 2 = 9)
    (hw : wa ^ 2 + wa * wb + wb ^ 2 = 1) (huw : ua * wa + (ua * wb + ub * wa) / 2 + ub * wb = 3 / 2) :
    (lcell Gp Gq ua ub wa wb hD hu hw huw).model = iTiling.C.model := rfl

theorem par_lat (Gp Gq ua ub wa wb p q : ℝ) :
    Phi p q ∈ Par (Gp + Gq / 2) (Gq * iT) (ua + ub / 2) (ub * iT) (wa + wb / 2) (wb * iT) ↔
      ∃ l m : ℝ, 0 ≤ l ∧ l ≤ 1 ∧ 0 ≤ m ∧ m ≤ 1 ∧ p = Gp + l * ua + m * wa ∧ q = Gq + l * ub + m * wb := by
  have hh := iT_pos
  constructor
  · rintro ⟨l, m, hl, hl1, hm, hm1, h0, h1⟩
    rw [Phi_0] at h0
    rw [Phi_1] at h1
    have hq : q = Gq + l * ub + m * wb := by
      have : (q - (Gq + l * ub + m * wb)) * iT = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · exact absurd h hh.ne'
    refine ⟨l, m, hl, hl1, hm, hm1, ?_, hq⟩
    rw [hq] at h0; linarith
  · rintro ⟨l, m, hl, hl1, hm, hm1, h0, h1⟩
    refine ⟨l, m, hl, hl1, hm, hm1, ?_, ?_⟩
    · rw [Phi_0, h0, h1]; ring
    · rw [Phi_1, h1]; ring

/-! ## the five cells -/

noncomputable def cR0 := lcell (-3) 6 0 (-3) 1 (-1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
noncomputable def cR1 := lcell (-2) 5 0 (-3) 1 (-1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
noncomputable def cR2 := lcell (-1) 4 0 (-3) 1 (-1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
noncomputable def cP1 := lcell 0 0 0 3 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
noncomputable def cP2 := lcell 1 3 (-3) 3 (-1) 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem R0_iff (p q : ℝ) : Phi p q ∈ cR0.region ↔ -3 ≤ p ∧ p ≤ -2 ∧ 0 ≤ p + q ∧ p + q ≤ 3 := by
  show Phi p q ∈ Par _ _ _ _ _ _ ↔ _
  rw [par_lat]
  constructor
  · rintro ⟨l, m, hl, hl1, hm, hm1, h0, h1⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
  · rintro ⟨a, b, c, d⟩
    exact ⟨(3 - p - q) / 3, p + 3, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem R1_iff (p q : ℝ) : Phi p q ∈ cR1.region ↔ -2 ≤ p ∧ p ≤ -1 ∧ 0 ≤ p + q ∧ p + q ≤ 3 := by
  show Phi p q ∈ Par _ _ _ _ _ _ ↔ _
  rw [par_lat]
  constructor
  · rintro ⟨l, m, hl, hl1, hm, hm1, h0, h1⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
  · rintro ⟨a, b, c, d⟩
    exact ⟨(3 - p - q) / 3, p + 2, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem R2_iff (p q : ℝ) : Phi p q ∈ cR2.region ↔ -1 ≤ p ∧ p ≤ 0 ∧ 0 ≤ p + q ∧ p + q ≤ 3 := by
  show Phi p q ∈ Par _ _ _ _ _ _ ↔ _
  rw [par_lat]
  constructor
  · rintro ⟨l, m, hl, hl1, hm, hm1, h0, h1⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
  · rintro ⟨a, b, c, d⟩
    exact ⟨(3 - p - q) / 3, p + 1, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem P1_iff (p q : ℝ) : Phi p q ∈ cP1.region ↔ 0 ≤ p ∧ p ≤ 1 ∧ 0 ≤ q ∧ q ≤ 3 := by
  show Phi p q ∈ Par _ _ _ _ _ _ ↔ _
  rw [par_lat]
  constructor
  · rintro ⟨l, m, hl, hl1, hm, hm1, h0, h1⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
  · rintro ⟨a, b, c, d⟩
    exact ⟨q / 3, p, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem P2_iff (p q : ℝ) : Phi p q ∈ cP2.region ↔ 3 ≤ q ∧ q ≤ 6 ∧ 3 ≤ p + q ∧ p + q ≤ 4 := by
  show Phi p q ∈ Par _ _ _ _ _ _ ↔ _
  rw [par_lat]
  constructor
  · rintro ⟨l, m, hl, hl1, hm, hm1, h0, h1⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
  · rintro ⟨a, b, c, d⟩
    exact ⟨(q - 3) / 3, 4 - p - q, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-! ## separation of cells (interior of the right set avoids the left set) -/

theorem disj_aff {A B : Set Plane} (f : Plane →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0) (c : ℝ)
    (h1 : ∀ x ∈ A, f x ≤ c) (h2 : ∀ x ∈ B, c ≤ f x) : Disjoint A (interior B) := by
  rw [Set.disjoint_left]
  intro x hxA hxB
  have hxB' : x ∈ B := interior_subset hxB
  have hxc : f x = c := le_antisymm (h1 x hxA) (h2 x hxB')
  set g : Plane →ᵃ[ℝ] ℝ := f - AffineMap.const ℝ Plane c with hg
  have hglin : g.linear ≠ 0 := by
    intro hcon
    apply hf
    have : f.linear - (AffineMap.const ℝ Plane c).linear = 0 := hcon
    have hzero : (AffineMap.const ℝ Plane c).linear = 0 := rfl
    rwa [hzero, sub_zero] at this
  have hgx : g x = 0 := by simp [hg, hxc]
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hxB)
  obtain ⟨y, hy, hyneg⟩ := Erdos634.Geometry.exists_neg_near_of_affine_zero g hglin hgx hr
  have hyB : y ∈ B := hball hy
  have : f y < c := by
    have hgy : g y = f y - c := rfl
    rw [hgy] at hyneg
    linarith
  exact absurd (h2 y hyB) (not_le.mpr this)

theorem disj_p {A B : Set Plane} (c : ℝ) (hA : ∀ p q, Phi p q ∈ A → p ≤ c) (hB : ∀ p q, Phi p q ∈ B → c ≤ p) :
    Disjoint A (interior B) := by
  have hh := iT_pos
  refine disj_aff (linF (2 * iT) (-1)) (linF_ne (c := 1) (d := 0) (by simp; exact hh.ne')) (2 * iT * c) ?_ ?_
  · intro x hx
    obtain ⟨p, q, rfl⟩ := exists_lat x
    rw [linF_apply, Phi_0, Phi_1]
    have := hA p q hx
    nlinarith
  · intro x hx
    obtain ⟨p, q, rfl⟩ := exists_lat x
    rw [linF_apply, Phi_0, Phi_1]
    have := hB p q hx
    nlinarith

theorem disj_q {A B : Set Plane} (c : ℝ) (hA : ∀ p q, Phi p q ∈ A → q ≤ c) (hB : ∀ p q, Phi p q ∈ B → c ≤ q) :
    Disjoint A (interior B) := by
  have hh := iT_pos
  refine disj_aff (linF 0 1) (linF_ne (c := 0) (d := 1) (by simp)) (iT * c) ?_ ?_
  · intro x hx
    obtain ⟨p, q, rfl⟩ := exists_lat x
    rw [linF_apply, Phi_1]
    have := hA p q hx
    nlinarith
  · intro x hx
    obtain ⟨p, q, rfl⟩ := exists_lat x
    rw [linF_apply, Phi_1]
    have := hB p q hx
    nlinarith

theorem disj_pq {A B : Set Plane} (c : ℝ) (hA : ∀ p q, Phi p q ∈ A → p + q ≤ c) (hB : ∀ p q, Phi p q ∈ B → c ≤ p + q) :
    Disjoint A (interior B) := by
  have hh := iT_pos
  refine disj_aff (linF (2 * iT) 1) (linF_ne (c := 1) (d := 0) (by simp; exact hh.ne')) (2 * iT * c) ?_ ?_
  · intro x hx
    obtain ⟨p, q, rfl⟩ := exists_lat x
    rw [linF_apply, Phi_0, Phi_1]
    have := hA p q hx
    nlinarith
  · intro x hx
    obtain ⟨p, q, rfl⟩ := exists_lat x
    rw [linF_apply, Phi_0, Phi_1]
    have := hB p q hx
    nlinarith

theorem disj_union {A B C : Set Plane} (hA : Disjoint A (interior C)) (hB : Disjoint B (interior C)) :
    Disjoint (A ∪ B) (interior C) := Set.disjoint_union_left.mpr ⟨hA, hB⟩

theorem disj_int {A C : Set Plane} (hA : Disjoint A (interior C)) : Disjoint (interior A) (interior C) :=
  hA.mono_left interior_subset

theorem R0R1 : Disjoint cR0.region (interior cR1.region) :=
  disj_p (-2) (fun p q h => ((R0_iff p q).mp h).2.1) (fun p q h => ((R1_iff p q).mp h).1)
theorem R0R2 : Disjoint cR0.region (interior cR2.region) :=
  disj_p (-1) (fun p q h => by have := ((R0_iff p q).mp h).2.1; linarith) (fun p q h => ((R2_iff p q).mp h).1)
theorem R1R2 : Disjoint cR1.region (interior cR2.region) :=
  disj_p (-1) (fun p q h => ((R1_iff p q).mp h).2.1) (fun p q h => ((R2_iff p q).mp h).1)
theorem R0P1 : Disjoint cR0.region (interior cP1.region) :=
  disj_p 0 (fun p q h => by have := ((R0_iff p q).mp h).2.1; linarith) (fun p q h => ((P1_iff p q).mp h).1)
theorem R1P1 : Disjoint cR1.region (interior cP1.region) :=
  disj_p 0 (fun p q h => by have := ((R1_iff p q).mp h).2.1; linarith) (fun p q h => ((P1_iff p q).mp h).1)
theorem R2P1 : Disjoint cR2.region (interior cP1.region) :=
  disj_p 0 (fun p q h => ((R2_iff p q).mp h).2.1) (fun p q h => ((P1_iff p q).mp h).1)
theorem R0P2 : Disjoint cR0.region (interior cP2.region) :=
  disj_pq 3 (fun p q h => ((R0_iff p q).mp h).2.2.2) (fun p q h => ((P2_iff p q).mp h).2.2.1)
theorem R1P2 : Disjoint cR1.region (interior cP2.region) :=
  disj_pq 3 (fun p q h => ((R1_iff p q).mp h).2.2.2) (fun p q h => ((P2_iff p q).mp h).2.2.1)
theorem R2P2 : Disjoint cR2.region (interior cP2.region) :=
  disj_pq 3 (fun p q h => ((R2_iff p q).mp h).2.2.2) (fun p q h => ((P2_iff p q).mp h).2.2.1)
theorem P1P2 : Disjoint cP1.region (interior cP2.region) :=
  disj_q 3 (fun p q h => ((P1_iff p q).mp h).2.2.2) (fun p q h => ((P2_iff p q).mp h).1)

/-! ## assembly of the 10-tile dissection -/

noncomputable def hU1 : CongruentRegionDissection (2 + 2) :=
  unionCongruentRegion cR0 cR1 rfl (disj_int R0R1)
noncomputable def hU2 : CongruentRegionDissection (2 + 2 + 2) :=
  unionCongruentRegion hU1 cR2 rfl (disj_int (disj_union R0R2 R1R2))
noncomputable def hU3 : CongruentRegionDissection (2 + 2 + 2 + 2) :=
  unionCongruentRegion hU2 cP1 rfl (disj_int (disj_union (disj_union R0P1 R1P1) R2P1))
noncomputable def hexC : CongruentRegionDissection (2 + 2 + 2 + 2 + 2) :=
  unionCongruentRegion hU3 cP2 rfl (disj_int (disj_union (disj_union (disj_union R0P2 R1P2) R2P2) P1P2))

theorem hexC_region : hexC.region = cR0.region ∪ cR1.region ∪ cR2.region ∪ cP1.region ∪ cP2.region := rfl

theorem hexC_regular : RegularPQ hexC :=
  regular_union _ _ _ _ (regular_union _ _ _ _ (regular_union _ _ _ _ (regular_union _ _ _ _ (lcell_regular _ _ _ _) (lcell_regular _ _ _ _)) (lcell_regular _ _ _ _)) (lcell_regular _ _ _ _)) (lcell_regular _ _ _ _)

theorem hexC_model : hexC.model = iTiling.C.model := rfl

/-! ## the hexagon polygon and the final application -/

/-- The equiangular hexagon, lattice vertices `(0,0),(1,0),(1,3),(-2,6),(-3,6),(-3,3)` (sides 1,3,3,1,3,3). -/
noncomputable def hexPoly : ConvPoly 6 where
  v := ![Phi 0 0, Phi 1 0, Phi 1 3, Phi (-2) 6, Phi (-3) 6, Phi (-3) 3]
  three_le := by norm_num
  left := by
    intro i j hji hji1
    fin_cases i <;> fin_cases j <;>
      first | (exfalso; revert hji hji1; decide) | (simp [cross2, mkPt, Phi]; nlinarith [iT_pos])

theorem hex_iff (p q : ℝ) : Phi p q ∈ hexPoly.carrier ↔ 0 ≤ q ∧ p ≤ 1 ∧ p + q ≤ 4 ∧ q ≤ 6 ∧ -3 ≤ p ∧ 0 ≤ p + q := by
  have hh := iT_pos
  have hmem : Phi p q ∈ hexPoly.carrier ↔ ∀ i : Fin 6, 0 ≤ cross2 (hexPoly.v (i + 1) - hexPoly.v i) (Phi p q - hexPoly.v i) := Iff.rfl
  rw [hmem]
  constructor
  · intro h
    have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3; have h4 := h 4; have h5 := h 5
    simp [hexPoly, cross2, mkPt, Phi] at h0 h1 h2 h3 h4 h5
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith
  · rintro ⟨a1, a2, a3, a4, a5, a6⟩ i
    fin_cases i <;> simp [hexPoly, cross2, mkPt, Phi] <;>
      nlinarith [mul_nonneg hh.le (sub_nonneg.2 a1), mul_nonneg hh.le (sub_nonneg.2 a2), mul_nonneg hh.le (sub_nonneg.2 a3),
        mul_nonneg hh.le (sub_nonneg.2 a4), mul_nonneg hh.le (sub_nonneg.2 a5), mul_nonneg hh.le (sub_nonneg.2 a6)]

theorem hexC_region_eq : hexC.region = hexPoly.carrier := by
  rw [hexC_region]
  ext x
  obtain ⟨p, q, rfl⟩ := exists_lat x
  simp only [Set.mem_union]
  rw [R0_iff, R1_iff, R2_iff, P1_iff, P2_iff, hex_iff]
  constructor
  · rintro ((((h | h) | h) | h) | h) <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith [h.1, h.2.1, h.2.2.1, h.2.2.2]
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    by_cases hp : p ≤ 0
    · by_cases hs : p + q ≤ 3
      · by_cases hp2 : p ≤ -2
        · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨h5, hp2, h6, hs⟩)))
        · by_cases hp1 : p ≤ -1
          · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨by linarith, hp1, h6, hs⟩)))
          · exact Or.inl (Or.inl (Or.inr ⟨by linarith, hp, h6, hs⟩))
      · exact Or.inr ⟨by linarith, h4, by linarith, h3⟩
    · by_cases hq : q ≤ 3
      · exact Or.inl (Or.inr ⟨by linarith, h2, h1, hq⟩)
      · exact Or.inr ⟨by linarith, h4, by linarith, h3⟩

/-- The hexagon tiling: 10 congruent triangles (the tile (1, 3, sqrt 7)) of the equiangular hexagon with sides 1,3,3,1,3,3. -/
noncomputable def hexT : PolyTiling (2 + 2 + 2 + 2 + 2) 6 where
  C := hexC
  P := hexPoly
  region_eq := hexC_region_eq

/-- **NON-VACUITY, M = 6 branch of `ivc_final_ge5`:** all hypotheses hold on the hexagon tiling of the tile (1, 3, sqrt 7) and `Concl6` is obtained. -/
theorem hex_witness : Concl6 hexT.C hexT.P := by
  have hsum : angleAt hexT.C.model 0 + angleAt hexT.C.model 1 + angleAt hexT.C.model 2 = Real.pi :=
    Erdos634.Draft.LaczFormal.angleAt_sum hexT.C.model
  have hγ : angleAt hexT.C.model 2 = Real.pi / 3 := iTiling_gamma
  have hm1 : angleAt hexT.C.model 1 = 2 * Real.pi / 3 - angleAt hexT.C.model 0 := by linarith
  exact Erdos634.Draft.LaczFormal.IIIc.ivc_final_ge5 hexT hexC_regular (α := angleAt hexT.C.model 0) iTiling_alpha_irr rfl hm1 hγ
    iTiling_comm iTiling_notComm (by norm_num)

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.hex_witness
#print axioms Erdos634.Draft.LaczFormal.RG.hexC_region_eq

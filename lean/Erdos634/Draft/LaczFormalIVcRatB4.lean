-- Draft/LaczFormalIVcRatB4.lean -- Laczkovich DCG 48 (2012), Sect. 8.3 (Subcase IVc, rational branch), BLUEPRINT Part B, item B4: the VWTiling structure.
--   `KiteData b`, `RhombData b`: the parameters (position; half-side vectors s, w with |s| = |w| = b, s.w = b^2/2) of one piece; `.cell`, `.set`, `.V` (apex), `.W` (base midpoint).
--   `VWTiling b A ιK ιR`: finitely many kites (index ιK) and rhombi (index ιR) whose union is `A`, with pairwise disjoint interiors, and the V/W clause
--   (every kite's apex V is the base midpoint W of some kite, and every kite's W is the apex V of some kite).
--   `VWTiling.cellDiss hb` : the equilateral cells (4 per kite, 2 per rhombus) as a `CongruentRegionDissection` of `A` with model `eqT b hb` (the blueprint's field `E`, here DERIVED from the pieces).
--   `VWTiling.restrict S` : removal of a Finset of RHOMBI (kites cannot be removed: the type forbids it); the remaining pieces form a VWTiling of their union
--   (`restrict_union`: A = region' union (union of the removed rhombi); `restrict_sdiff`: A \ union S subset region').
--   Blueprint deviations: (1) pieces are the primary data and the cell dissection is derived (the blueprint had the cells primary with a grouping); (2) the region of the restriction is the union of the
--   remaining closed pieces, NOT the literal set difference A \ union S (which drops shared boundary); `restrict_sdiff` gives the one inclusion that is true and needed.
--   Witness `vw_witness` (one rhombus, no kites; the V/W clause is vacuous): the structure is inhabited.  A witness WITH kites is NOT given (a finite VW cycle of two kites
--   forces overlapping interiors; whether any finite VWTiling has a kite is not decided here).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 8.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIVcRatB3

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

/-- Parameters of a kite piece: apex `v`, half-side vectors `s`, `w` of equilateral cells of side `b`. -/
structure KiteData (b : ℝ) where
  v0 : ℝ
  v1 : ℝ
  s0 : ℝ
  s1 : ℝ
  w0 : ℝ
  w1 : ℝ
  hD : s0 * w1 - s1 * w0 ≠ 0
  hs : s0 ^ 2 + s1 ^ 2 = b ^ 2
  hw : w0 ^ 2 + w1 ^ 2 = b ^ 2
  hsw : s0 * w0 + s1 * w1 = b ^ 2 / 2

/-- Parameters of a rhombus piece: corner `x`, side vectors `s`, `w`. -/
structure RhombData (b : ℝ) where
  x0 : ℝ
  x1 : ℝ
  s0 : ℝ
  s1 : ℝ
  w0 : ℝ
  w1 : ℝ
  hD : s0 * w1 - s1 * w0 ≠ 0
  hs : s0 ^ 2 + s1 ^ 2 = b ^ 2
  hw : w0 ^ 2 + w1 ^ 2 = b ^ 2
  hsw : s0 * w0 + s1 * w1 = b ^ 2 / 2

namespace KiteData
variable {b : ℝ} (K : KiteData b)

noncomputable def cell : Fin 4 → Tri := kiteCell K.v0 K.v1 K.s0 K.s1 K.w0 K.w1 K.hD
noncomputable def set : Set Plane := kiteSet K.v0 K.v1 K.s0 K.s1 K.w0 K.w1 K.hD
/-- The apex. -/
noncomputable def V : Plane := mkPt K.v0 K.v1
/-- The midpoint of the base. -/
noncomputable def W : Plane := mkPt (K.v0 + K.s0 + K.w0) (K.v1 + K.s1 + K.w1)

theorem set_eq_iUnion : (⋃ i, (K.cell i).carrier) = K.set := kiteCell_cover K.hD

theorem cell_subset (i : Fin 4) : (K.cell i).carrier ⊆ K.set := by
  intro x hx
  rw [← K.set_eq_iUnion]
  exact Set.mem_iUnion.mpr ⟨i, hx⟩

theorem cell_disjoint : Pairwise fun i j : Fin 4 => Disjoint (interior (K.cell i).carrier) (interior (K.cell j).carrier) :=
  kiteCell_disjoint K.hD

/-- Apex and base midpoint differ. -/
theorem V_ne_W : K.V ≠ K.W := by
  intro h
  have h0 : (K.V) 0 = (K.W) 0 := by rw [h]
  have h1 : (K.V) 1 = (K.W) 1 := by rw [h]
  simp only [V, W, mkPt_zero, mkPt_one] at h0 h1
  have a0 : K.s0 + K.w0 = 0 := by linarith
  have a1 : K.s1 + K.w1 = 0 := by linarith
  apply K.hD
  have e0 : K.w0 = -K.s0 := by linarith
  have e1 : K.w1 = -K.s1 := by linarith
  rw [e0, e1]; ring

end KiteData

namespace RhombData
variable {b : ℝ} (R : RhombData b)

noncomputable def cell : Fin 2 → Tri := rhombCell R.x0 R.x1 R.s0 R.s1 R.w0 R.w1 R.hD
noncomputable def set : Set Plane := Par R.x0 R.x1 R.s0 R.s1 R.w0 R.w1

theorem set_eq_iUnion : (⋃ i, (R.cell i).carrier) = R.set :=
  (rhombDiss R.x0 R.x1 R.s0 R.s1 R.w0 R.w1 R.hD).covers

theorem cell_subset (i : Fin 2) : (R.cell i).carrier ⊆ R.set := by
  intro x hx
  rw [← R.set_eq_iUnion]
  exact Set.mem_iUnion.mpr ⟨i, hx⟩

theorem cell_disjoint : Pairwise fun i j : Fin 2 => Disjoint (interior (R.cell i).carrier) (interior (R.cell j).carrier) :=
  rhombCell_disjoint R.hD

end RhombData

/-- **A V/W tiling** of `A` by kites (index `ιK`) and rhombi (index `ιR`), all built from equilateral cells of side `b`. -/
structure VWTiling (b : ℝ) (A : Set Plane) (ιK ιR : Type) where
  K : ιK → KiteData b
  R : ιR → RhombData b
  cover : ((⋃ k, (K k).set) ∪ ⋃ r, (R r).set) = A
  disjKK : ∀ k k', k ≠ k' → Disjoint (interior (K k).set) (interior (K k').set)
  disjRR : ∀ r r', r ≠ r' → Disjoint (interior (R r).set) (interior (R r').set)
  disjKR : ∀ k r, Disjoint (interior (K k).set) (interior (R r).set)
  vwV : ∀ k, ∃ k', (K k).V = (K k').W
  vwW : ∀ k, ∃ k', (K k).W = (K k').V

namespace VWTiling
variable {b : ℝ} {A : Set Plane} {ιK ιR : Type} (T : VWTiling b A ιK ιR)

/-- The cells: four per kite, two per rhombus. -/
abbrev CellIdx (ιK ιR : Type) : Type := (ιK × Fin 4) ⊕ (ιR × Fin 2)

noncomputable def cellT : CellIdx ιK ιR → Tri
  | Sum.inl p => (T.K p.1).cell p.2
  | Sum.inr p => (T.R p.1).cell p.2

theorem cellT_inl (k : ιK) (i : Fin 4) : T.cellT (Sum.inl (k, i)) = (T.K k).cell i := rfl
theorem cellT_inr (r : ιR) (i : Fin 2) : T.cellT (Sum.inr (r, i)) = (T.R r).cell i := rfl

theorem cell_interiors_disjoint : ∀ c c' : CellIdx ιK ιR, c ≠ c' →
    Disjoint (interior (T.cellT c).carrier) (interior (T.cellT c').carrier) := by
  rintro (⟨k, i⟩ | ⟨r, i⟩) (⟨k', i'⟩ | ⟨r', i'⟩) hne
  · by_cases hk : k = k'
    · subst hk
      have hi : i ≠ i' := fun h => hne (by rw [h])
      exact (T.K k).cell_disjoint hi
    · exact (T.disjKK k k' hk).mono (interior_mono ((T.K k).cell_subset i)) (interior_mono ((T.K k').cell_subset i'))
  · exact (T.disjKR k r').mono (interior_mono ((T.K k).cell_subset i)) (interior_mono ((T.R r').cell_subset i'))
  · exact ((T.disjKR k' r).mono (interior_mono ((T.K k').cell_subset i')) (interior_mono ((T.R r).cell_subset i))).symm
  · by_cases hr : r = r'
    · subst hr
      have hi : i ≠ i' := fun h => hne (by rw [h])
      exact (T.R r).cell_disjoint hi
    · exact (T.disjRR r r' hr).mono (interior_mono ((T.R r).cell_subset i)) (interior_mono ((T.R r').cell_subset i'))

theorem cells_cover : (⋃ c, (T.cellT c).carrier) = A := by
  refine Eq.trans ?_ T.cover
  ext x
  simp only [Set.mem_iUnion, Set.mem_union]
  constructor
  · rintro ⟨(⟨k, i⟩ | ⟨r, i⟩), hx⟩
    · exact Or.inl ⟨k, (T.K k).cell_subset i hx⟩
    · exact Or.inr ⟨r, (T.R r).cell_subset i hx⟩
  · rintro (⟨k, hx⟩ | ⟨r, hx⟩)
    · rw [← (T.K k).set_eq_iUnion] at hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact ⟨Sum.inl (k, i), hi⟩
    · rw [← (T.R r).set_eq_iUnion] at hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact ⟨Sum.inr (r, i), hi⟩

theorem cell_congruent (hb : 0 < b) : ∀ c, (T.cellT c).Congruent (eqT b hb) := by
  rintro (⟨k, i⟩ | ⟨r, i⟩)
  · exact (kiteC hb (T.K k).v0 (T.K k).v1 (T.K k).s0 (T.K k).s1 (T.K k).w0 (T.K k).w1 (T.K k).hD (T.K k).hs (T.K k).hw (T.K k).hsw).tiles_congruent i
  · exact (rhombC hb (T.R r).x0 (T.R r).x1 (T.R r).s0 (T.R r).s1 (T.R r).w0 (T.R r).w1 (T.R r).hD (T.R r).hs (T.R r).hw (T.R r).hsw).tiles_congruent i

/-- The derived equilateral cell dissection of `A`. -/
noncomputable def cellDiss [Fintype ιK] [Fintype ιR] (hb : 0 < b) : CongruentRegionDissection (Fintype.card (CellIdx ιK ιR)) where
  region := A
  tile := fun i => T.cellT ((Fintype.equivFin (CellIdx ιK ιR)).symm i)
  covers := by
    refine Eq.trans ?_ T.cells_cover
    exact ((Fintype.equivFin (CellIdx ιK ιR)).symm.surjective.iUnion_comp (fun c => (T.cellT c).carrier))
  interiors_disjoint := fun i j hij =>
    T.cell_interiors_disjoint _ _ (fun h => hij ((Fintype.equivFin (CellIdx ιK ιR)).symm.injective h))
  model := eqT b hb
  tiles_congruent := fun i => T.cell_congruent hb _

/-! ## Restriction: removing rhombi -/

/-- Remove the rhombi in `S`: the kites and the remaining rhombi form a V/W tiling of their union. -/
noncomputable def restrict (S : Finset ιR) :
    VWTiling b ((⋃ k, (T.K k).set) ∪ ⋃ r : {r // r ∉ S}, (T.R r.1).set) ιK {r // r ∉ S} where
  K := T.K
  R := fun r => T.R r.1
  cover := rfl
  disjKK := T.disjKK
  disjRR := fun r r' h => T.disjRR r.1 r'.1 (fun e => h (Subtype.ext e))
  disjKR := fun k r => T.disjKR k r.1
  vwV := T.vwV
  vwW := T.vwW

theorem restrict_union (S : Finset ιR) :
    A = ((⋃ k, (T.K k).set) ∪ ⋃ r : {r // r ∉ S}, (T.R r.1).set) ∪ ⋃ r ∈ S, (T.R r).set := by
  refine Eq.trans T.cover.symm ?_
  ext x
  simp only [Set.mem_union, Set.mem_iUnion, exists_prop]
  constructor
  · rintro (h | ⟨r, hr⟩)
    · exact Or.inl (Or.inl h)
    · by_cases hrS : r ∈ S
      · exact Or.inr ⟨r, hrS, hr⟩
      · exact Or.inl (Or.inr ⟨⟨r, hrS⟩, hr⟩)
  · rintro ((h | ⟨r, hr⟩) | ⟨r, _, hr⟩)
    · exact Or.inl h
    · exact Or.inr ⟨r.1, hr⟩
    · exact Or.inr ⟨r, hr⟩

theorem restrict_sdiff (S : Finset ιR) :
    A \ (⋃ r ∈ S, (T.R r).set) ⊆ ((⋃ k, (T.K k).set) ∪ ⋃ r : {r // r ∉ S}, (T.R r.1).set) := by
  intro x ⟨hxA, hxS⟩
  rw [T.restrict_union S] at hxA
  rcases hxA with h | h
  · exact h
  · exact absurd h hxS

end VWTiling

/-! ## Witness (no kites) -/

private theorem s3pos : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)

/-- One rhombus, side 1: `x = 0`, `s = (1,0)`, `w = (1/2, sqrt 3 / 2)`. -/
noncomputable def witRhomb : RhombData 1 where
  x0 := 0
  x1 := 0
  s0 := 1
  s1 := 0
  w0 := 1 / 2
  w1 := Real.sqrt 3 / 2
  hD := by have := s3pos; intro h; nlinarith
  hs := by norm_num
  hw := by
    have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have h4 : (Real.sqrt 3 / 2) ^ 2 = 3 / 4 := by rw [div_pow, hs]; norm_num
    rw [h4]; norm_num
  hsw := by norm_num

/-- The structure is inhabited (zero kites; the V/W clause is vacuous). -/
noncomputable def vw_witness : VWTiling 1 witRhomb.set Empty Unit where
  K := fun e => nomatch e
  R := fun _ => witRhomb
  cover := by ext x; simp
  disjKK := fun k => nomatch k
  disjRR := fun r r' h => absurd (Subsingleton.elim r r') h
  disjKR := fun k => nomatch k
  vwV := fun k => nomatch k
  vwW := fun k => nomatch k

/-- The derived cell dissection of the witness has two cells. -/
theorem vw_witness_cells : Fintype.card (VWTiling.CellIdx Empty Unit) = 2 := by
  simp [VWTiling.CellIdx]

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.VWTiling.cell_interiors_disjoint
#print axioms Erdos634.Draft.LaczFormal.RG.VWTiling.cellDiss
#print axioms Erdos634.Draft.LaczFormal.RG.VWTiling.restrict
#print axioms Erdos634.Draft.LaczFormal.RG.VWTiling.restrict_union
#print axioms Erdos634.Draft.LaczFormal.RG.vw_witness
#print axioms Erdos634.Draft.LaczFormal.RG.KiteData.V_ne_W

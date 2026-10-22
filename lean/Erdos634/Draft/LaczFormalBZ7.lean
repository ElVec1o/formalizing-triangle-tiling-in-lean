-- Draft/LaczFormalBZ7.lean -- what the Beeson-Zhang repair gives for Laczkovich's Theorem 2.1, Case III (gamma = 2 pi/3), polygon targets.
--  * `caseIII_count`   : for a regular tiling of a convex M-gon (PolyTiling) with gamma = 2 pi/3, `NotComb a b c` (IIIa) or `NotComb b a c` (IIIb) forces R >= M - 2, R = number of tiles with their
--                        gamma-corner at a vertex of the polygon (the repaired substitute for Lemma 7.1 (i)-(iii): no balance is used);
--  * `caseIII_tri_no_IIIab` : for M = 3 (triangle targets) IIIa and IIIb are IMPOSSIBLE (R = 0 < 1), with NO hypothesis on alpha;
--  * `caseIII_tri_irr`      : M = 3, alpha not in Q pi: Theorem 2.1's conclusion (conclusion (iv)) -- Beeson-Zhang Theorem 5.2 in the language of PolyTiling.
-- NOT closed here: Case III for M >= 4 when R >= M - 2 (the polygons of Theorem 2.1 (ii)); and M = 3 with alpha rational and IIIc -- see PLAN_THM21.md.
-- UNAUDITED.  Credit: Beeson-Zhang (arXiv 2604.01314v1), Laczkovich (DCG 48 (2012), Thm 2.1, Sect. 7).
import Erdos634.Draft.LaczFormalBZ4b
import Erdos634.Draft.LaczFormalBZ6

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

/-- All corner angles of a polygon of a regular `γ = 2π/3` tiling are `π/3` or `2π/3`. -/
theorem poly_angles_2pi3 (T : PolyTiling N M) (hγ : angleAt T.C.model 2 = 2 * Real.pi / 3)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hA : ∀ i v, angleAt T.C.model (idx i v) = angleAt (T.C.tile i) v)
    (hcnt : ∀ X, cnt T.C idx X 0 = cnt T.C idx X 1) (i : Fin M) : T.P.angle i = Real.pi / 3 ∨ T.P.angle i = 2 * Real.pi / 3 := by
  haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  have hαβ : T.C.model.angleAt 0 + T.C.model.angleAt 1 = Real.pi / 3 := by
    have := Erdos634.Draft.LaczFormal.angleAt_sum T.C.model
    have hγ' : T.C.model.angleAt 2 = 2 * Real.pi / 3 := hγ
    linarith
  have := polygon_angle_2pi3 T.C T.P T.region_eq idx hA hγ hαβ (fun X => hcnt X) (i - 1)
  rwa [sub_add_cancel] at this

/-- **Case III, subcases IIIa/IIIb, counting form.**  For a regular tiling of a convex `M`-gon by a tile with `γ = 2π/3`: if `a` is not a nonnegative rational combination of `b, c`, then at least `M - 2` of the
tiles have their `γ`-corner at a vertex of the polygon. -/
theorem caseIII_count (T : PolyTiling N M) (hreg : RegularPQ T.C) (hγ : angleAt T.C.model 2 = 2 * Real.pi / 3)
    (hnc : NotComb (slen T.C 0) (slen T.C 1) (slen T.C 2)) :
    ∃ idx : Fin N → Equiv.Perm (Fin 3), (∀ i v, angleAt T.C.model (idx i v) = angleAt (T.C.tile i) v) ∧
      (∀ X, cnt T.C idx X 0 = cnt T.C idx X 1) ∧ ((M : ℤ) - 2) ≤ ∑ k : Fin M, (cnt T.C idx (T.P.v (k + 1)) 2 : ℤ) := by
  classical
  obtain ⟨idx, hA, hcnt⟩ := hreg
  refine ⟨idx, hA, fun X => hcnt X, ?_⟩
  have hidx := idx_dist_of_angle T.C idx hA
  haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  have hαβ : T.C.model.angleAt 0 + T.C.model.angleAt 1 = Real.pi / 3 := by
    have := Erdos634.Draft.LaczFormal.angleAt_sum T.C.model
    have hγ' : T.C.model.angleAt 2 = 2 * Real.pi / 3 := hγ
    linarith
  exact bz_count_poly T.C T.P T.region_eq idx hidx hA hnc hγ hαβ (fun X => hcnt X) (poly_angles_2pi3 T hγ idx hA hcnt)

/-- The same count for `b` (Subcase IIIb), by exchanging the roles of `α` and `β`. -/
theorem caseIII_count' (T : PolyTiling N M) (hreg : RegularPQ T.C) (hγ : angleAt T.C.model 2 = 2 * Real.pi / 3)
    (hnc : NotComb (slen T.C 1) (slen T.C 0) (slen T.C 2)) :
    ∃ idx : Fin N → Equiv.Perm (Fin 3), (∀ i v, angleAt T.C.model (idx i v) = angleAt (T.C.tile i) v) ∧
      (∀ X, cnt T.C idx X 0 = cnt T.C idx X 1) ∧ ((M : ℤ) - 2) ≤ ∑ k : Fin M, (cnt T.C idx (T.P.v (k + 1)) 2 : ℤ) := by
  classical
  obtain ⟨idx, hA, hcnt⟩ := hreg
  refine ⟨idx, hA, fun X => hcnt X, ?_⟩
  set σ : Equiv.Perm (Fin 3) := Equiv.swap 0 1 with hσ
  set Dr := relabel T.C σ with hDr
  have hs0 : σ 0 = 1 := by decide
  have hs1 : σ 1 = 0 := by decide
  have hs2 : σ 2 = 2 := by decide
  have hang : ∀ j, Dr.model.angleAt j = T.C.model.angleAt (σ j) := fun j => relabel_angleAt T.C σ j
  have hsl : ∀ t, slen Dr t = slen T.C (σ t) := fun t => relabel_slen T.C σ t
  have hreg' : Dr.region = T.P.carrier := T.region_eq
  haveI : HasFansC Dr.toRegionDissection := hasFansC_poly _ T.P hreg'
  set idx' := relabelIdx idx σ with hidx'
  have hA' : ∀ i v, angleAt Dr.model (idx' i v) = angleAt (Dr.tile i) v := relabel_hidxA T.C idx σ hA
  have hidxd := idx_dist_of_angle Dr idx' hA'
  have hγ' : Dr.model.angleAt 2 = 2 * Real.pi / 3 := by rw [hang, hs2]; exact hγ
  have hαβ0 : T.C.model.angleAt 0 + T.C.model.angleAt 1 = Real.pi / 3 := by
    have := Erdos634.Draft.LaczFormal.angleAt_sum T.C.model
    have hγ'' : T.C.model.angleAt 2 = 2 * Real.pi / 3 := hγ
    linarith
  have hαβ : Dr.model.angleAt 0 + Dr.model.angleAt 1 = Real.pi / 3 := by
    rw [hang, hang, hs0, hs1]; linarith
  have hregc : ∀ X, cnt Dr idx' X 0 = cnt Dr idx' X 1 := by
    intro X
    rw [relabel_cnt, relabel_cnt, hs0, hs1]
    exact (hcnt X).symm
  have hnc' : NotComb (slen Dr 0) (slen Dr 1) (slen Dr 2) := by
    rw [hsl, hsl, hsl, hs0, hs1, hs2]; exact hnc
  have hall := poly_angles_2pi3 T hγ idx hA hcnt
  have key := bz_count_poly Dr T.P hreg' idx' hidxd hA' hnc' hγ' hαβ hregc hall
  refine le_trans key (le_of_eq ?_)
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [relabel_cnt, hs2]

/-- A regular `γ = 2π/3` tiling of a triangle has all three polygon angles `π/3`, and no corner carries a `γ`. -/
theorem tri_corners (T : PolyTiling N 3) (hγ : angleAt T.C.model 2 = 2 * Real.pi / 3)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hA : ∀ i v, angleAt T.C.model (idx i v) = angleAt (T.C.tile i) v)
    (hcnt : ∀ X, cnt T.C idx X 0 = cnt T.C idx X 1) :
    (∀ i : Fin 3, T.P.angle i = Real.pi / 3) ∧ ∑ k : Fin 3, (cnt T.C idx (T.P.v (k + 1)) 2 : ℤ) = 0 := by
  classical
  haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  have hαβ : T.C.model.angleAt 0 + T.C.model.angleAt 1 = Real.pi / 3 := by
    have := Erdos634.Draft.LaczFormal.angleAt_sum T.C.model
    have hγ' : T.C.model.angleAt 2 = 2 * Real.pi / 3 := hγ
    linarith
  have hall := poly_angles_2pi3 T hγ idx hA hcnt
  have hsum := poly_angle_sum T.P
  have hpi := Real.pi_pos
  have h3 : ∀ i : Fin 3, T.P.angle i = Real.pi / 3 := by
    have e : ∑ i : Fin 3, T.P.angle i = Real.pi := by rw [hsum]; norm_num
    rw [Fin.sum_univ_three] at e
    have a0 := hall 0
    have a1 := hall 1
    have a2 := hall 2
    intro i
    fin_cases i
    · show T.P.angle 0 = _
      rcases a0 with h | h
      · exact h
      · rcases a1 with h1 | h1 <;> rcases a2 with h2 | h2 <;> linarith
    · show T.P.angle 1 = _
      rcases a1 with h | h
      · exact h
      · rcases a0 with h1 | h1 <;> rcases a2 with h2 | h2 <;> linarith
    · show T.P.angle 2 = _
      rcases a2 with h | h
      · exact h
      · rcases a0 with h1 | h1 <;> rcases a1 with h2 | h2 <;> linarith
  refine ⟨h3, Finset.sum_eq_zero fun k _ => ?_⟩
  have hv0 : ∃ j k', (T.C.tile j).pts k' = T.P.v (k + 1) := poly_vertex_is_tile_vertex T.C.toRegionDissection T.P T.region_eq (k + 1)
  have hcA := corner_A T.C T.P T.region_eq idx hA k hv0
  have hexp : Asum T.C idx (T.P.v (k + 1)) = (cnt T.C idx (T.P.v (k + 1)) 0 : ℝ) * T.C.model.angleAt 0 + (cnt T.C idx (T.P.v (k + 1)) 1 : ℝ) * T.C.model.angleAt 1 + (cnt T.C idx (T.P.v (k + 1)) 2 : ℝ) * T.C.model.angleAt 2 := by
    unfold Asum; rw [Fin.sum_univ_three]
  have hr : ((cnt T.C idx (T.P.v (k + 1)) 0 : ℕ) : ℝ) = (cnt T.C idx (T.P.v (k + 1)) 1 : ℕ) := by exact_mod_cast hcnt _
  have hγ' : T.C.model.angleAt 2 = 2 * Real.pi / 3 := hγ
  have := type_arith_reg hαβ hγ' (cnt T.C idx (T.P.v (k + 1)) 0) (cnt T.C idx (T.P.v (k + 1)) 2) 1
    (by rw [hexp, ← hr] at hcA; rw [hcA, h3]; push_cast; ring)
  have h0 : cnt T.C idx (T.P.v (k + 1)) 2 = 0 := by omega
  simp [h0]

/-- **For a TRIANGLE target, Subcases IIIa and IIIb of Theorem 2.1 do not occur** (regular tiling, `γ = 2π/3`; no hypothesis on `α`): `R = 0 < 1 = M - 2`. -/
theorem caseIII_tri_no_IIIab (T : PolyTiling N 3) (hreg : RegularPQ T.C) (hγ : angleAt T.C.model 2 = 2 * Real.pi / 3) :
    ¬ NotComb (slen T.C 0) (slen T.C 1) (slen T.C 2) ∧ ¬ NotComb (slen T.C 1) (slen T.C 0) (slen T.C 2) := by
  constructor
  · intro hnc
    obtain ⟨idx, hA, hcnt, hge⟩ := caseIII_count T hreg hγ hnc
    rw [(tri_corners T hγ idx hA hcnt).2] at hge
    norm_num at hge
  · intro hnc
    obtain ⟨idx, hA, hcnt, hge⟩ := caseIII_count' T hreg hγ hnc
    rw [(tri_corners T hγ idx hA hcnt).2] at hge
    norm_num at hge

/-- **Case III for a triangle target** reduces to `IIIc`: Theorem 2.1's conclusion, or `a, b` commensurable and `c` not commensurable with `a`. -/
theorem caseIII_reduce_tri (T : PolyTiling N 3) (hreg : RegularPQ T.C) (hγ : angleAt T.C.model 2 = 2 * Real.pi / 3) :
    Thm21Concl T.C T.P ∨ (Comm (slen T.C 0) (slen T.C 1) ∧ ¬ Comm (slen T.C 0) (slen T.C 2)) := by
  rcases caseIII_reduce T hreg hγ with h | h | h | h
  · exact Or.inl h
  · exact absurd h (caseIII_tri_no_IIIab T hreg hγ).1
  · exact absurd h (caseIII_tri_no_IIIab T hreg hγ).2
  · exact Or.inr h

/-- The triangle `T.P` as a `CongruentDissection` target. -/
noncomputable def triDissection (T : PolyTiling N 3) : CongruentDissection N :=
  have h : 0 < cross2 (T.P.v 1 - T.P.v 0) (T.P.v 2 - T.P.v 0) := T.P.left 0 2 (by decide) (by decide)
  { target := triOf (T.P.v 0) (T.P.v 1) (T.P.v 2) h
    tile := T.C.tile
    covers := by
      rw [T.C.covers, T.region_eq]
      ext y
      rw [triOf_carrier]
      unfold ConvPoly.carrier
      simp only [Set.mem_setOf_eq]
      constructor
      · intro hh
        exact ⟨by simpa using hh 0, by simpa using hh 1, by simpa using hh 2⟩
      · rintro ⟨h1, h2, h3⟩ i
        fin_cases i
        · simpa using h1
        · simpa using h2
        · simpa using h3
    interiors_disjoint := T.C.interiors_disjoint
    model := T.C.model
    tiles_congruent := T.C.tiles_congruent }

/-- **Theorem 2.1, Case III, triangle target, `α` irrational (Beeson-Zhang Theorem 5.2 for `PolyTiling`):** the conclusion of Theorem 2.1 holds (here (iv)). -/
theorem caseIII_tri_irr (T : PolyTiling N 3) (hreg : RegularPQ T.C) (hγ : angleAt T.C.model 2 = 2 * Real.pi / 3)
    (hα : ¬ ∃ r : ℚ, angleAt T.C.model 0 = (r : ℝ) * Real.pi) : Thm21Concl T.C T.P := by
  classical
  obtain ⟨idx, hA, hcnt⟩ := hreg
  have hall := tri_corners T hγ idx hA hcnt
  have hside := triangle_equilateral T.P hall.1
  have hαβ : T.C.model.angleAt 0 + T.C.model.angleAt 1 = Real.pi / 3 := by
    have := Erdos634.Draft.LaczFormal.angleAt_sum T.C.model
    have hγ' : T.C.model.angleAt 2 = 2 * Real.pi / 3 := hγ
    linarith
  have hγ' : T.C.model.angleAt 2 = 2 * Real.pi / 3 := hγ
  have hα' : ¬ ∃ r : ℚ, T.C.model.angleAt 0 = (r : ℝ) * Real.pi := hα
  have hdata : (triDissection T).model.TwoPiThreeData (T.C.model.angleAt 0) (slen T.C 0) (slen T.C 1) (slen T.C 2) :=
    ⟨1, rfl, rfl, by show T.C.model.angleAt 1 = _; linarith, rfl, hγ', rfl⟩
  have heq : ∀ j : Fin 3, dist ((triDissection T).target.pts j) ((triDissection T).target.pts (j + 1)) =
      dist ((triDissection T).target.pts 0) ((triDissection T).target.pts 1) := by
    intro j
    have h1 := hside j
    have e : ∀ i : Fin 3, (triDissection T).target.pts i = T.P.v i := by
      intro i; fin_cases i <;> rfl
    rw [e, e, e, e]
    unfold ConvPoly.side at h1
    exact h1
  obtain ⟨hab, hac⟩ := bz_thm52 (triDissection T) hα' hdata heq
  rcases caseIII_comm T ⟨idx, hA, hcnt⟩ hγ hab hac with h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.caseIII_count
#print axioms Erdos634.Draft.LaczFormal.RG.caseIII_count'
#print axioms Erdos634.Draft.LaczFormal.RG.caseIII_tri_no_IIIab
#print axioms Erdos634.Draft.LaczFormal.RG.caseIII_reduce_tri
#print axioms Erdos634.Draft.LaczFormal.RG.caseIII_tri_irr

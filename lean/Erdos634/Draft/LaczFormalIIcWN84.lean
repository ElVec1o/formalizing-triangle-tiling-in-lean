-- Draft/LaczFormalIIcWN84.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3, p. 359), Lemma 6.2, R1: `r1_outermost_cycle`.
-- Hypothesis `hz` (NOT proved here; the printed "C1deg and C2deg contain the exceptional points", counting (d4) of WN69 + chord direction (d2) and non-crossing (d3)): one point `z` of nonzero winding number off every Gamma_kite cycle.
-- Conclusion: a closed injective Gamma_kite chain `C` such that every Gamma_kite vertex is a vertex of `C` or lies in the degree region `{wind (toC o C) <> 0}`.  `C` is the cycle through the edge of maximal real part.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN83
import Erdos634.Draft.LaczFormalIIcWN75

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG
open Erdos634.Draft.LaczFormal.WN (edgeSet wind)

variable {N M : ℕ}

local notation "tc" => Erdos634.Draft.LaczFormal.WN.toC

theorem isCompact_seg_c (a b : ℂ) : IsCompact (segment ℝ a b) := by
  rw [segment_eq_image]; exact isCompact_Icc.image (by fun_prop)

/-- **R1 (tile level).** -/
theorem r1_outermost_cycle [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3)
    (hz : ∃ z : ℂ, ∀ (m : ℕ) [NeZero m] (C : Fin m → Plane), (∀ k : Fin m, GKite D idx (C k) (C (k + 1))) → Function.Injective C →
      z ∉ Erdos634.Draft.LaczFormal.WN.edgeSet (fun k => tc (C k)) ∧
        Erdos634.Draft.LaczFormal.WN.wind (fun k => tc (C k)) z ≠ 0)
    {X0 Y0 : Plane} (h0 : GKite D idx X0 Y0) :
    ∃ (m : ℕ) (_ : NeZero m) (C : Fin m → Plane), (∀ k : Fin m, GKite D idx (C k) (C (k + 1))) ∧ Function.Injective C ∧
      ∀ v Y, GKite D idx v Y → v ∈ Set.range C ∨
        (tc v ∉ edgeSet (fun k => tc (C k)) ∧ Erdos634.Draft.LaczFormal.WN.wind (fun k => tc (C k)) (tc v) ≠ 0) := by
  obtain ⟨z, hz⟩ := hz
  set K : Set Plane := {X | ∃ Y, GKite D idx X Y} with hK
  have hKfin : K.Finite := gkite_tails_finite D idx
  set E : Set (Plane × Plane) := {p | GKite D idx p.1 p.2} with hE
  have hEfin : E.Finite := by
    apply (hKfin.prod hKfin).subset
    rintro ⟨a, b⟩ hab'
    exact ⟨⟨b, hab'⟩, gkite_succ_exists D P hreg idx hC hab hac h1 h3 hab'⟩
  set U : Set ℂ := ⋃ p ∈ E, segment ℝ (tc p.1) (tc p.2) with hU
  have hUc : IsCompact U := hEfin.isCompact_biUnion (fun p _ => isCompact_seg_c _ _)
  have hUne : U.Nonempty := ⟨tc X0, Set.mem_iUnion₂.2 ⟨(X0, Y0), h0, left_mem_segment ℝ _ _⟩⟩
  obtain ⟨e, he, hmax⟩ := hUc.exists_isMaxOn hUne Complex.continuous_re.continuousOn
  obtain ⟨⟨A, B⟩, hAB, heAB⟩ := Set.mem_iUnion₂.1 he
  have hAB' : GKite D idx A B := hAB
  obtain ⟨m, hm, C, hC0, hCinj, hCy⟩ := gkite_cycle_exists D P hreg idx hC hab hac h1 h3 hAB'
  refine ⟨m, hm, C, hCy, hCinj, ?_⟩
  haveI : NeZero N := by
    obtain ⟨i, -⟩ := h0
    exact ⟨fun h => by subst h; exact i.elim0⟩
  have hCB : C 1 = B := by
    have := hCy 0
    rw [hC0] at this
    simpa using gkite_succ_le_one D P hreg idx hC.hidxA hC.hregc h1 h3 this hAB'
  have heC : e ∈ edgeSet (fun k => tc (C k)) := by
    refine Set.mem_iUnion.2 ⟨0, ?_⟩
    simp only [zero_add, hC0, hCB]
    exact heAB
  intro v Y hvY
  obtain ⟨m', hm', C', hC'0, hC'inj, hC'y⟩ := gkite_cycle_exists D P hreg idx hC hab hac h1 h3 hvY
  by_cases hsh : ∃ j k, C' j = C k
  · left
    obtain ⟨j, k, hjk⟩ := hsh
    have := chain_mem_of_share D P hreg idx hC h1 h3 C C' hCy hC'y hjk
    rwa [hC'0] at this
  · right
    push Not at hsh
    have hd := gkite_cycles_edge_disjoint D idx C C' hCy hC'y hsh
    have hmaxq : ∀ w ∈ edgeSet (fun k => tc (C' k)), w.re ≤ e.re := by
      intro w hw
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hw
      exact hmax (Set.mem_iUnion₂.2 ⟨(C' i, C' (i + 1)), hC'y i, hi⟩)
    have hzC := hz m C hCy hCinj
    have hzC' := hz m' C' hC'y hC'inj
    have hv : tc v ∈ edgeSet (fun k => tc (C' k)) :=
      Set.mem_iUnion.2 ⟨0, by rw [← hC'0]; exact left_mem_segment ℝ _ _⟩
    exact ⟨Set.disjoint_right.1 hd hv, Erdos634.Draft.LaczFormal.WN.outer_of_maxre _ _ hd heC hmaxq hzC.1 hzC'.1 hzC.2 hzC'.2 _ hv⟩

#print axioms r1_outermost_cycle

end Erdos634.Draft.LaczFormal.RG

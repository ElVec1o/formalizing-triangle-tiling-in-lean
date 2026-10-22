-- Draft/LaczFormalIIcWN125.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3, p. 358), Lemma 6.2: `exc_inside_of_innermost`, the BASE CASE of `ExcInsideAll`.
-- A closed injective Gamma_kite chain `C` with no Gamma_kite vertex strictly inside (every Gamma_kite vertex lies on the polygon or has winding number `0`) has every exceptional point strictly inside.
-- Printed: "we may assume that C-degree does not contain any vertex of Gamma_kite ... there are at least N convex vertices of C such that the corresponding edge VW arrives at an exceptional point belonging to C-degree ... both E and F must be in C-degree".
-- Counting: `Xs` = convex vertices, `Ys` = concave vertices, `#Xs = #Ys + M` (`convex_count`); each convex vertex sends a chord (`r2c_chord_core`) ending at a concave vertex (injective by `gexc_arrive_kite_unique`) or at an exceptional point (`r2c_chord_end`);
-- capacities `cnt gamma - cnt alpha` (`gexc_exc_interior_exact`) sum to `M` (`exc_census`); `exc_all_inside_gen` (WN120) puts every exceptional point inside.
-- NOTE, UNAUDITED.  Hypotheses: the Case IIc block + AngGen.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN124

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG
open Erdos634.Draft.LaczFormal.WN (edgeSet wind extAng OrientOK)

local notation "tc" => Erdos634.Draft.LaczFormal.WN.toC

variable {N M : ℕ}

set_option maxHeartbeats 6400000 in
theorem exc_inside_of_innermost [NeZero N] [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (G : AngGen (fun l => D.model.angleAt l))
    (hcor : ∀ j : Fin M, cnt D idx (P.v j) 0 = 1 ∧ cnt D idx (P.v j) 1 = 1 ∧ cnt D idx (P.v j) 2 = 0)
    {m : ℕ} [NeZero m] (C : Fin m → Plane) (hCy : ∀ k : Fin m, GKite D idx (C k) (C (k + 1))) (hinj : Function.Injective C)
    (hK : ∀ v Y, GKite D idx v Y → tc v ∈ edgeSet (cyc C) ∨ wind (cyc C) (tc v) = 0) :
    ∀ E ∈ excVerts2 D idx P, tc E ∉ edgeSet (cyc C) ∧ wind (cyc C) (tc E) ≠ 0 := by
  obtain ⟨hm3, hs⟩ := gkite_cycle_simple D idx C hCy hinj
  have hsC := (Erdos634.Draft.LaczFormal.WN.simplePolyP_iff C).1 hs
  have hinjC : Function.Injective (fun k => tc (C k)) :=
    fun a b h => hinj (Erdos634.Draft.LaczFormal.WN.toC.injective h)
  obtain ⟨σ, hO⟩ := Erdos634.Draft.LaczFormal.WN.orient_exists hsC hinjC hm3
  have hσ : σ = 1 ∨ σ = -1 := hO.1.1
  have hσ0 : σ ≠ 0 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have hcard := convex_count D P hreg idx hC h1 h3 G hcor C hCy hinj hO
  set Xs := Finset.univ.filter (fun k : Fin m => 0 < σ * extAng (cyc C) k) with hXs
  set Ys := Finset.univ.filter (fun k : Fin m => σ * extAng (cyc C) k < 0) with hYs
  have hch : ∀ k ∈ Xs, ∃ W, GExc D idx (C k) W ∧ ∀ s : ℝ, 0 < s → s < 1 →
      tc (C k + s • (W - C k)) ∉ edgeSet (cyc C) ∧ wind (cyc C) (tc (C k + s • (W - C k))) = σ := by
    intro k hk
    exact r2c_chord_core D P hreg idx hC hab hac h1 h3 G C hCy hO k (Finset.mem_filter.1 hk).2
  choose! W hWE hWch using hch
  have hend : ∀ k ∈ Xs, (∃ k', W k = C k' ∧ σ * extAng (cyc C) k' < 0) ∨ W k ∈ excVerts2 D idx P := fun k hk =>
    r2c_chord_end D P hreg idx hC hab hac h1 h3 G hcor C hCy hO hK k (hWE k hk) (hWch k hk)
  let PP : Fin m → Prop := fun x => ∃ k', W x = C k' ∧ σ * extAng (cyc C) k' < 0
  let toY : Fin m → Fin m := fun x => if h : PP x then h.choose else x
  have hWx : ∀ x, ∀ h : PP x, W x = C (toY x) := by
    intro x h
    simp only [toY, dif_pos h]
    exact h.choose_spec.1
  have hYx : ∀ x, ∀ h : PP x, σ * extAng (cyc C) (toY x) < 0 := by
    intro x h
    simp only [toY, dif_pos h]
    exact h.choose_spec.2
  have hkex : ∀ x ∈ Xs, ¬ PP x → W x ∈ excVerts2 D idx P := by
    intro x hx hn
    rcases hend x hx with h | h
    · exact absurd h hn
    · exact h
  have hgood : ∀ x ∈ Xs, ¬ PP x → tc (W x) ∉ edgeSet (cyc C) ∧ wind (cyc C) (tc (W x)) ≠ 0 := by
    intro x hx hn
    have hexc := hkex x hx hn
    have hoff : tc (W x) ∉ edgeSet (cyc C) := by
      intro hmem
      obtain ⟨i, hi⟩ := (mem_edgeSet_cyc C _).1 hmem
      exact exc_not_on_kite_edge D P hreg idx hC hab hac h1 h3 G hcor hexc (hCy i) hi
    refine ⟨hoff, ?_⟩
    rw [wind_end_eq C (C x) (W x) σ (hWch x hx) hoff]
    exact hσ0
  have hmem_vtx : ∀ x : Fin m, C x ∈ vtxSet D.toRegionDissection := by
    intro x
    obtain ⟨i, j, d, kk, f, kk', f', -, -, -, hk, -⟩ := hCy x
    exact mem_vtxSet.mpr ⟨i, kk, hk⟩
  have key := Erdos634.Draft.LaczFormal.WN.exc_all_inside_gen (X := Xs) (Y := Ys) (E := excVerts2 D idx P)
    (Ein := (excVerts2 D idx P).filter (fun e => tc e ∉ edgeSet (cyc C) ∧ wind (cyc C) (tc e) ≠ 0))
    (Finset.filter_subset _ _) (fun e => cnt D idx e 2 - cnt D idx e 0)
    (fun e he => by have := (Finset.mem_filter.mp he).2; simp only; omega)
    toY W PP M hcard (exc_census D P hreg idx hC h1 h3 hcor)
    (fun x hx hp => Finset.mem_filter.2 ⟨Finset.mem_univ _, hYx x hp⟩)
    (by
      intro x hx x' hx' hp hp' he
      have e1 := hWx x hp
      have e2 := hWx x' hp'
      have hW' : W x = W x' := by rw [e1, e2, he]
      have hYZ : GKite D idx (W x) (C (toY x + 1)) := by rw [e1]; exact hCy (toY x)
      have hX' : GExc D idx (C x') (W x) := by rw [hW']; exact hWE x' hx'
      exact hinj (gexc_arrive_kite_unique D P hreg idx hC h1 h3 G hYZ (hWE x hx) hX'))
    (fun x hx hn => Finset.mem_filter.2 ⟨hkex x hx hn, hgood x hx hn⟩)
    (by
      intro e he
      have hex := (gexc_exc_interior_exact D P hreg idx hC hab hac h1 h3 G hcor e he).2
      show _ ≤ cnt D idx e 2 - cnt D idx e 0
      rw [← hex]
      apply Finset.card_le_card_of_injOn (fun x => C x)
      · intro x hx
        simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx
        obtain ⟨hxX, -, hxe⟩ := hx
        simp only [Finset.coe_filter, Set.mem_setOf_eq]
        refine ⟨hmem_vtx x, ?_⟩
        rw [← hxe]; exact hWE x hxX
      · intro x _ x' _ h
        exact hinj h)
  intro E hE
  rw [← key] at hE
  exact (Finset.mem_filter.1 hE).2

#print axioms exc_inside_of_innermost

end Erdos634.Draft.LaczFormal.RG

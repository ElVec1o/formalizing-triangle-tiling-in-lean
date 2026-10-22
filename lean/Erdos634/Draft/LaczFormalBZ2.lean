-- Draft/LaczFormalBZ2.lean -- Beeson-Zhang (arXiv 2604.01314v1) Table 2: the vertex types of a dissection of a convex polygon (with angles pi/3) by the tile (alpha, beta, 2 pi/3), alpha not in Q pi.
--   `type_arith`: c0 alpha + c1 beta + c2 gamma = m pi/3  =>  c0 = c1 and c0 + 2 c2 = m   (regularity is DERIVED from the irrationality of alpha);
--   `sum_cnt_vtx`: the total number of corners of each model type is N;   `vertex_type`: at every tiling vertex #alpha = #beta and p + 2 r in {6 (interior), 3, 1 (a polygon vertex)}, p = #alpha, r = #gamma.
-- UNAUDITED.  Credit: Beeson-Zhang (Sect. 2.2, Table 2), Laczkovich (DCG 48 (2012), Sect. 7).
import Erdos634.Draft.LaczFormalBZ1

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

theorem type_arith {α β γ : ℝ} (hαβ : α + β = Real.pi / 3) (hγ : γ = 2 * Real.pi / 3)
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (c0 c1 c2 m : ℕ)
    (h : (c0 : ℝ) * α + c1 * β + c2 * γ = m * (Real.pi / 3)) : c0 = c1 ∧ c0 + 2 * c2 = m := by
  have hpi := Real.pi_pos
  have hβ : β = Real.pi / 3 - α := by linarith
  subst hγ
  subst hβ
  have e : ((c0 : ℝ) - c1) * α = ((m : ℝ) - c1 - 2 * c2) * (Real.pi / 3) := by linear_combination h
  by_cases hne : c0 = c1
  · subst hne
    refine ⟨rfl, ?_⟩
    have e2 : ((m : ℝ) - c0 - 2 * c2) * (Real.pi / 3) = 0 := by rw [← e]; ring
    have e3 : (m : ℝ) - c0 - 2 * c2 = 0 := by
      rcases mul_eq_zero.mp e2 with h1 | h1
      · exact h1
      · exfalso; linarith
    have e4 : ((c0 + 2 * c2 : ℕ) : ℝ) = m := by push_cast; linarith
    exact_mod_cast e4
  · exfalso
    apply hα
    have hd : ((c0 : ℝ) - c1) ≠ 0 := by
      intro h0
      apply hne
      have : (c0 : ℝ) = c1 := by linarith
      exact_mod_cast this
    refine ⟨((m : ℚ) - c1 - 2 * c2) / (3 * ((c0 : ℚ) - c1)), ?_⟩
    push_cast
    field_simp
    linarith

theorem sum_cnt_vtx (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (l : Fin 3) :
    ∑ v ∈ vtxSet D.toRegionDissection, cnt D idx v l = N := by
  classical
  set s : Finset (Fin N × Fin 3) := Finset.univ.filter (fun p => idx p.1 p.2 = l) with hs
  have hcard : s.card = N := by
    have : s.card = (Finset.univ : Finset (Fin N)).card := by
      refine Finset.card_bij (fun p _ => p.1) (fun _ _ => Finset.mem_univ _) ?_ ?_
      · intro p hp q hq hpq
        simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
        have h1 : p.1 = q.1 := hpq
        have h2 : idx p.1 p.2 = idx p.1 q.2 := by rw [hp, h1, hq]
        exact Prod.ext h1 ((idx p.1).injective h2)
      · intro i _
        refine ⟨(i, (idx i).symm l), ?_, rfl⟩
        simp [hs]
    rw [this]; simp
  have hfib := Finset.card_eq_sum_card_fiberwise (f := fun p : Fin N × Fin 3 => (D.tile p.1).pts p.2) (s := s) (t := vtxSet D.toRegionDissection)
    (fun p _ => mem_vtxSet.mpr ⟨p.1, p.2, rfl⟩)
  refine Eq.trans ?_ hcard
  rw [hfib]
  refine Finset.sum_congr rfl fun v _ => ?_
  unfold cnt
  congr 1
  ext p
  simp [hs, and_comm]

/-- **Table 2 of Beeson-Zhang**, for a convex polygon with all angles `π/3` (the equilateral triangle). -/
theorem vertex_type (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hγ : D.model.angleAt 2 = 2 * Real.pi / 3) (hαβ : D.model.angleAt 0 + D.model.angleAt 1 = Real.pi / 3)
    (hα : ¬ ∃ r : ℚ, D.model.angleAt 0 = (r : ℝ) * Real.pi) (hPang : ∀ i, P.angle i = Real.pi / 3) {X : Plane}
    (hvert : ∃ j k, (D.tile j).pts k = X) :
    cnt D idx X 0 = cnt D idx X 1 ∧
      ((X ∈ interior D.region ∧ cnt D idx X 0 + 2 * cnt D idx X 2 = 6) ∨ cnt D idx X 0 + 2 * cnt D idx X 2 = 3 ∨
        (X ∉ interior D.region ∧ cnt D idx X 0 + 2 * cnt D idx X 2 = 1 ∧ ∃ k : Fin M, X = P.v (k + 1))) := by
  have hA : Asum D idx X = ((Asum D idx X) / (Real.pi / 3)) * (Real.pi / 3) := by
    have := Real.pi_pos; field_simp
  have hAexp : Asum D idx X = (cnt D idx X 0 : ℝ) * D.model.angleAt 0 + (cnt D idx X 1 : ℝ) * D.model.angleAt 1 + (cnt D idx X 2 : ℝ) * D.model.angleAt 2 := by
    unfold Asum; rw [Fin.sum_univ_three]
  have hpi := Real.pi_pos
  have key : ∀ m : ℕ, Asum D idx X = m * (Real.pi / 3) → cnt D idx X 0 = cnt D idx X 1 ∧ cnt D idx X 0 + 2 * cnt D idx X 2 = m := by
    intro m hm
    exact type_arith hαβ hγ hα _ _ _ m (by rw [← hAexp]; exact hm)
  rcases vertex_A D P hreg idx hidxA hvert with ⟨hi, h2 | h1⟩ | ⟨hni, h1 | ⟨k, hXk, hk⟩⟩
  · have := key 6 (by rw [h2]; push_cast; ring)
    exact ⟨this.1, Or.inl ⟨hi, this.2⟩⟩
  · have := key 3 (by rw [h1]; push_cast; ring)
    exact ⟨this.1, Or.inr (Or.inl this.2)⟩
  · have := key 3 (by rw [h1]; push_cast; ring)
    exact ⟨this.1, Or.inr (Or.inl this.2)⟩
  · have := key 1 (by rw [hk, hPang]; push_cast; ring)
    exact ⟨this.1, Or.inr (Or.inr ⟨hni, this.2, k, hXk⟩)⟩

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.type_arith
#print axioms Erdos634.Draft.LaczFormal.RG.sum_cnt_vtx
#print axioms Erdos634.Draft.LaczFormal.RG.vertex_type

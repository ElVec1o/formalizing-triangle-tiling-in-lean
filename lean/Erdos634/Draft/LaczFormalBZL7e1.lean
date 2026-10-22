-- Draft/LaczFormalBZL7e1.lean -- Beeson, "Tilings of an isosceles triangle" (arXiv 1206.1974v7), Section 10.1: vertex types of a dissection of a triangle ABC with base angles alpha (vertex angle pi - 2 alpha = alpha + beta)
-- by a tile with angles (alpha, beta, 2 alpha), alpha not in Q pi (so 3 alpha + beta = pi).  (Beeson-Zhang cite this as "Thm 10.5"; in v7 the commensurability theorem is Theorem 10.7.)
--   `vtype_arith`     : c0 alpha + c1 beta + c2 (2 alpha) = p alpha + q pi  =>  c1 = q and c0 + 2 c2 - 3 c1 = p   (Lemma 10.1 and the list of normal vertices / stars / centres are special cases);
--   `exists_center_a2`: Lemma 10.2 (at least one centre, counts (0,2,3)) for a target polygon whose corner angles are alpha or pi - 2 alpha with at least one of the latter;
--                       proof: sum over the vertices of (#beta - #gamma) is 0 (every type occurs N times); it is >= 0 at every non-centre vertex and = 1 at the vertex B.
-- NOT here: the link graphs Gamma_a, Gamma_b, Gamma_c, Lemmas 10.3-10.6, Theorem 10.7 (see (private working notes, not included)).  NOTE, UNAUDITED.
-- Credit: Beeson (arXiv 1206.1974v7, Lemmas 10.1, 10.2), Beeson-Zhang (arXiv 2604.01314, Table 5), Laczkovich.
import Erdos634.Draft.LaczFormalBZL7d1

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

theorem vtype_arith {α β : ℝ} (hβ : β = Real.pi - 3 * α) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (c0 c1 c2 : ℕ) (p : ℤ) (q : ℕ)
    (h : (c0 : ℝ) * α + c1 * β + c2 * (2 * α) = p * α + q * Real.pi) :
    (c1 : ℤ) = q ∧ (c0 : ℤ) + 2 * c2 - 3 * c1 = p := by
  have hpi := Real.pi_pos
  subst hβ
  have e : (((c0 : ℝ) + 2 * c2 - 3 * c1 - p)) * α = ((q : ℝ) - c1) * Real.pi := by linear_combination h
  by_cases hx : (c0 : ℤ) + 2 * c2 - 3 * c1 - p = 0
  · have hxr : ((c0 : ℝ) + 2 * c2 - 3 * c1 - p) = 0 := by exact_mod_cast hx
    rw [hxr, zero_mul] at e
    have : ((q : ℝ) - c1) = 0 := by
      rcases mul_eq_zero.mp e.symm with h1 | h1
      · exact h1
      · exact absurd h1 hpi.ne'
    refine ⟨?_, by omega⟩
    have : (c1 : ℝ) = q := by linarith
    exact_mod_cast this
  · exfalso
    apply hα
    have hxr : ((c0 : ℝ) + 2 * c2 - 3 * c1 - p) ≠ 0 := by exact_mod_cast hx
    refine ⟨((q : ℚ) - c1) / ((c0 : ℚ) + 2 * c2 - 3 * c1 - p), ?_⟩
    push_cast
    rw [div_mul_eq_mul_div, eq_div_iff hxr]
    linarith [e]

/-- **Beeson Lemma 10.2 (at least one centre).**  Target polygon `P` (a triangle, `M = 3`, or any polygon) all of whose corner angles are `alpha` or `pi - 2 alpha`, at least one of the latter
(the vertex B).  Then some vertex of the tiling has corner counts `(0,2,3)` (a centre: two `beta`, three `gamma`). -/
theorem exists_center_a2 (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hβ : D.model.angleAt 1 = Real.pi - 3 * D.model.angleAt 0) (hγ : D.model.angleAt 2 = 2 * D.model.angleAt 0)
    (hα : ¬ ∃ r : ℚ, D.model.angleAt 0 = (r : ℝ) * Real.pi)
    (hPang : ∀ k : Fin M, P.angle (k + 1) = D.model.angleAt 0 ∨ P.angle (k + 1) = Real.pi - 2 * D.model.angleAt 0)
    (k0 : Fin M) (hk0 : P.angle (k0 + 1) = Real.pi - 2 * D.model.angleAt 0) :
    ∃ v ∈ vtxSet D.toRegionDissection, cnt D idx v 0 = 0 ∧ cnt D idx v 1 = 2 ∧ cnt D idx v 2 = 3 := by
  classical
  by_contra hnc
  push Not at hnc
  set V := vtxSet D.toRegionDissection with hVdef
  have hs1 : ∑ v ∈ V, (cnt D idx v 1 : ℤ) = N := by exact_mod_cast sum_cnt_vtx D idx 1
  have hs2 : ∑ v ∈ V, (cnt D idx v 2 : ℤ) = N := by exact_mod_cast sum_cnt_vtx D idx 2
  have hsum : ∑ v ∈ V, ((cnt D idx v 1 : ℤ) - cnt D idx v 2) = 0 := by
    rw [Finset.sum_sub_distrib, hs1, hs2]; ring
  have hAexp : ∀ X, Asum D idx X = (cnt D idx X 0 : ℝ) * D.model.angleAt 0 + (cnt D idx X 1 : ℝ) * (Real.pi - 3 * D.model.angleAt 0)
      + (cnt D idx X 2 : ℝ) * (2 * D.model.angleAt 0) := by
    intro X
    unfold Asum; rw [Fin.sum_univ_three, hβ, hγ]
  have key : ∀ X, ∀ p : ℤ, ∀ q : ℕ, Asum D idx X = p * D.model.angleAt 0 + q * Real.pi →
      (cnt D idx X 1 : ℤ) = q ∧ (cnt D idx X 0 : ℤ) + 2 * cnt D idx X 2 - 3 * cnt D idx X 1 = p := by
    intro X p q h
    refine vtype_arith (α := D.model.angleAt 0) (β := D.model.angleAt 1) hβ hα _ _ _ p q ?_
    rw [hβ]; rw [← hAexp X]; exact h
  have hge : ∀ v ∈ V, 0 ≤ (cnt D idx v 1 : ℤ) - cnt D idx v 2 := by
    intro v hv
    have hvert : ∃ j k, (D.tile j).pts k = v := mem_vtxSet.mp hv
    have hn := hnc v hv
    rcases vertex_A D P hreg idx hidxA hvert with ⟨_, h2 | h1⟩ | ⟨_, h1 | ⟨k, hXk, hk⟩⟩
    · have := key v 0 2 (by rw [h2]; push_cast; ring)
      have h0 : cnt D idx v 1 = 2 := by omega
      have h2' : cnt D idx v 2 ≠ 3 := fun h3 => hn (by omega) h0 |> fun hh => hh h3
      omega
    · have := key v 0 1 (by rw [h1]; push_cast; ring)
      omega
    · have := key v 0 1 (by rw [h1]; push_cast; ring)
      omega
    · rcases hPang k with hk1 | hk1
      · have := key v 1 0 (by rw [hk, hk1]; push_cast; ring)
        omega
      · have := key v (-2) 1 (by rw [hk, hk1]; push_cast; ring)
        omega
  have hv0 : ∃ j k, (D.tile j).pts k = P.v (k0 + 1) := poly_vertex_is_tile_vertex D.toRegionDissection P hreg (k0 + 1)
  have hvV : P.v (k0 + 1) ∈ V := mem_vtxSet.mpr hv0
  have hcA := corner_A D P hreg idx hidxA k0 hv0
  have hB := key (P.v (k0 + 1)) (-2) 1 (by rw [hcA, hk0]; push_cast; ring)
  have h1B : (1 : ℤ) ≤ (cnt D idx (P.v (k0 + 1)) 1 : ℤ) - cnt D idx (P.v (k0 + 1)) 2 := by omega
  have := Finset.single_le_sum (f := fun v => ((cnt D idx v 1 : ℤ) - cnt D idx v 2)) hge hvV
  simp only at this
  omega

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.vtype_arith
#print axioms Erdos634.Draft.LaczFormal.RG.exists_center_a2

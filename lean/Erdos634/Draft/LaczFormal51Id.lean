-- Draft/LaczFormal51Id.lean -- Laczkovich (Discrete Math 140 (1995)) Thm 4.1 / Thm 5.1: the TILE IDENTITY, proved from the vertex angle-sum count.
--   `tile_identity` : for ANY CongruentDissection D of a triangle (tile angles m_0,m_1,m_2 = D.model.angleAt, any N, reflections allowed):
--     (a) the three target angles are, up to a permutation rho, `sum_l c i l * m_l` with c i l the numbers of tile angles of type l at the i-th corner of the target;
--     (b) for any two tile angle types l, l' with  P_l' < P_l  (P_l = sum_i c i l = number of type-l angles used at the three corners)
--         there is a vertex of the dissection that is NOT a corner of the target, carrying x_k angles of type k, with x_l < x_l'
--         and  sum_k x_k m_k = v * pi  with v = 1 or 2.
--   This is the sentence "these equations, together with p a + q b = pi, must contain exactly N a's, N b's, N c's; consequently there is an equation with x < z" of Laczkovich's proof of Thm 4.1.
-- Proof: sum over all vertices of cnt = N (sum_cnt_vtx); corners are vertices; non-corner vertex sums are pi or 2 pi (vertex_A).
-- NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) Thm 4.1, 5.1), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalBZL7d5b
import Erdos634.Draft.LaczFormalBZ2

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

theorem fin3_ne1 : ∀ i : Fin 3, i ≠ i + 1 := by decide
theorem fin3_ne2 : ∀ i : Fin 3, i ≠ i + 1 + 1 := by decide
theorem fin3_cases2 : ∀ a b : Fin 3, a + 1 ≠ b + 1 → (b + 1 = a + 1 + 1 ∨ a + 1 = b + 1 + 1) := by decide

theorem convpoly3_inj (P : ConvPoly 3) : Function.Injective (fun k : Fin 3 => P.v (k + 1)) := by
  have key : ∀ i : Fin 3, P.v i ≠ P.v (i + 1) := by
    intro i h
    have h1 : i ≠ i + 1 := fin3_ne1 i
    have h2 : i ≠ i + 1 + 1 := fin3_ne2 i
    have := P.left (i + 1) i h1.symm.symm h2
    rw [← h] at this
    simp [cross2] at this
  intro a b hab
  simp only at hab
  by_contra hne
  have hn : a + 1 ≠ b + 1 := fun h => hne (add_right_cancel h)
  have hc := fin3_cases2 a b hn
  rcases hc with hc | hc
  · exact key (a + 1) (by rw [hab, ← hc])
  · exact key (b + 1) (by rw [← hab, ← hc])

/-- **The tile identity (Laczkovich 1995, proof of Thm 4.1).** -/
theorem tile_identity (D : CongruentDissection N) :
    ∃ (c : Fin 3 → Fin 3 → ℕ) (ρ : Equiv.Perm (Fin 3)),
      (∀ i, D.target.angleAt (ρ i) = ∑ l, (c i l : ℝ) * D.model.angleAt l) ∧
      (∀ l l' : Fin 3, ∑ i, c i l' < ∑ i, c i l →
        ∃ (x : Fin 3 → ℕ) (v : ℕ), (v = 1 ∨ v = 2) ∧ x l < x l' ∧ ∑ k, (x k : ℝ) * D.model.angleAt k = v * Real.pi) := by
  classical
  obtain ⟨P, hPc, τ, hτ, hτv⟩ := exists_convpoly_of_tri' D.target
  set Dr := D.toRegion with hDr
  have hreg : Dr.region = P.carrier := by rw [hPc]; rfl
  haveI : HasFansC Dr.toRegionDissection := hasFansC_poly _ P hreg
  obtain ⟨idx, hidx, hidxA⟩ := exists_idx_both Dr
  set V := vtxSet Dr.toRegionDissection with hV
  set cor : Fin 3 → Plane := fun k => P.v (k + 1) with hcor
  have hcorV : ∀ k, cor k ∈ V := fun k =>
    mem_vtxSet.mpr (poly_vertex_is_tile_vertex Dr.toRegionDissection P hreg (k + 1))
  set S : Finset Plane := Finset.univ.image cor with hS
  have hSV : S ⊆ V := by
    intro x hx
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hx
    exact hcorV k
  have hinj : Function.Injective cor := convpoly3_inj P
  have hcorA : ∀ k, Asum Dr idx (cor k) = D.target.angleAt (τ (k + 1)) := fun k => by
    rw [hcor]; simp only
    rw [corner_A Dr P hreg idx hidxA k (poly_vertex_is_tile_vertex Dr.toRegionDissection P hreg (k + 1)), hτ]
  refine ⟨fun i l => cnt Dr idx (cor i) l, (Equiv.addRight (1 : Fin 3)).trans τ, ?_, ?_⟩
  · intro i
    have := hcorA i
    unfold Asum at this
    simpa using this.symm
  · intro l l' hlt
    have hsumS : ∀ m, ∑ v ∈ S, cnt Dr idx v m = ∑ i, cnt Dr idx (cor i) m := fun m => by
      rw [hS, Finset.sum_image (fun a _ b _ h => hinj h)]
    have hsplit : ∀ m, ∑ v ∈ V \ S, cnt Dr idx v m + ∑ i, cnt Dr idx (cor i) m = N := fun m => by
      rw [← hsumS, Finset.sum_sdiff hSV]; exact sum_cnt_vtx Dr idx m
    have hlt2 : ∑ v ∈ V \ S, cnt Dr idx v l < ∑ v ∈ V \ S, cnt Dr idx v l' := by
      have h1 := hsplit l; have h2 := hsplit l'
      simp only at hlt
      omega
    obtain ⟨v, hvmem, hv⟩ := Finset.exists_lt_of_sum_lt hlt2
    have hvV : v ∈ V := (Finset.mem_sdiff.mp hvmem).1
    have hvS : v ∉ S := (Finset.mem_sdiff.mp hvmem).2
    have hvert : ∃ j k, (Dr.tile j).pts k = v := mem_vtxSet.mp hvV
    refine ⟨fun k => cnt Dr idx v k, ?_⟩
    have hA : ∑ k, (cnt Dr idx v k : ℝ) * D.model.angleAt k = Asum Dr idx v := rfl
    have hmain : Asum Dr idx v = Real.pi ∨ Asum Dr idx v = 2 * Real.pi := by
      rcases vertex_A Dr P hreg idx hidxA hvert with ⟨-, h | h⟩ | ⟨-, h | ⟨k, hk, -⟩⟩
      · exact Or.inr h
      · exact Or.inl h
      · exact Or.inl h
      · exact absurd (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk.symm⟩) hvS
    rcases hmain with h | h
    · exact ⟨1, Or.inl rfl, hv, by rw [hA, h]; simp⟩
    · exact ⟨2, Or.inr rfl, hv, by rw [hA, h]; push_cast; ring⟩

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.tile_identity

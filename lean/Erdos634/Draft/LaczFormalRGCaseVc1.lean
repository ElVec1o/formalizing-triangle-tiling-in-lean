-- Draft/LaczFormalRGCaseVc1.lean -- Case V, subcase Vc (a, b commensurable): every side of the polygon is a sum of tile sides `a, b, c`; and, when `c` is not a nonnegative rational
-- combination of `a, b`, every side is EITHER an integer multiple of `c` OR a combination of `a, b` only (the Gamma_c argument of Laczkovich's Lemmas 4.4-4.7 for a rectangle,
-- obtained from the Gamma_a machinery by relabeling the model 0 <-> 2: all vertices have an even number of corners of type alpha/beta).
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Lemmas 4.4-4.7, Sect. 9.1), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRGCaseVb

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

theorem list_sum_decomp2 (a b : ℝ) (l : List ℝ) (h : ∀ x ∈ l, x = a ∨ x = b) :
    ∃ na nb : ℕ, l.sum = na * a + nb * b ∧ na + nb = l.length := by
  induction l with
  | nil => exact ⟨0, 0, by simp⟩
  | cons x l ih =>
    obtain ⟨na, nb, h1, h2⟩ := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    rcases h x (List.mem_cons_self ..) with hx | hx
    · exact ⟨na + 1, nb, by simp [hx, h1]; ring, by simp; omega⟩
    · exact ⟨na, nb + 1, by simp [hx, h1]; ring, by simp; omega⟩

theorem list_sum_decomp (a b c : ℝ) (l : List ℝ) (h : ∀ x ∈ l, x = a ∨ x = b ∨ x = c) :
    ∃ na nb nc : ℕ, l.sum = na * a + nb * b + nc * c ∧ na + nb + nc = l.length := by
  induction l with
  | nil => exact ⟨0, 0, 0, by simp⟩
  | cons x l ih =>
    obtain ⟨na, nb, nc, h1, h2⟩ := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    rcases h x (List.mem_cons_self ..) with hx | hx | hx
    · exact ⟨na + 1, nb, nc, by simp [hx, h1]; ring, by simp; omega⟩
    · exact ⟨na, nb + 1, nc, by simp [hx, h1]; ring, by simp; omega⟩
    · exact ⟨na, nb, nc + 1, by simp [hx, h1]; ring, by simp; omega⟩

/-- **A side of the polygon is a sum of tile sides**: `m` steps, each of length `a, b` or `c`. -/
theorem edge_decomp (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (P : ConvPoly M) (hreg : D.region = P.carrier) (i : Fin M) :
    ∃ na nb nc : ℕ, 0 < na + nb + nc ∧ P.side i = na * slen D 0 + nb * slen D 1 + nc * slen D 2 := by
  obtain ⟨L, W⟩ := side_walk_exists_poly D.toRegionDissection P hreg i
  have hne : P.v i ≠ P.v (i + 1) := by
    intro he
    apply P.e_ne_zero P.three_le i
    unfold ConvPoly.e; rw [← he]; simp
  have hL : L ≠ [] := by
    rintro rfl
    exact hne (walkT_nil_eq W)
  have hsum := walkT_dist_sum W
  have hmem := walkT_mem_step W
  obtain ⟨na, nb, nc, h1, h2⟩ := list_sum_decomp (slen D 0) (slen D 1) (slen D 2) (L.map fun e => dist e.2.1 e.2.2) (by
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    exact side_len_mem D idx hidx (hmem e he))
  refine ⟨na, nb, nc, ?_, ?_⟩
  · rw [h2, List.length_map]; exact List.length_pos_of_ne_nil hL
  · rw [ConvPoly.side, ← hsum, h1]

/-- **The `Γ_c` dichotomy for a side** (`c` is not a nonnegative rational combination of `a, b`; `γ`-independent): the side is `m · c` or a combination of `a, b` only. -/
theorem edge_c_dichotomy (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) (hregc : ∀ X, cnt D idx X 0 = cnt D idx X 1)
    (hnc : NotComb (slen D 2) (slen D 1) (slen D 0)) (P : ConvPoly M) (hreg : D.region = P.carrier) (i : Fin M) :
    (∃ m : ℕ, 0 < m ∧ P.side i = m * slen D 2) ∨ (∃ na nb : ℕ, 0 < na + nb ∧ P.side i = na * slen D 0 + nb * slen D 1) := by
  classical
  set σ : Equiv.Perm (Fin 3) := Equiv.swap 0 2 with hσ
  have s0 : σ 0 = 2 := by simp [hσ]
  have s1 : σ 1 = 1 := by rw [hσ]; exact Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
  have s2 : σ 2 = 0 := by simp [hσ]
  set D' := relabel D σ with hD'
  set idx' := relabelIdx idx σ with hidx'
  haveI : HasFansC D'.toRegionDissection := (inferInstance : HasFansC D.toRegionDissection)
  have hnc' : NotComb (slen D' 0) (slen D' 1) (slen D' 2) := by
    rw [hD', relabel_slen, relabel_slen, relabel_slen, s0, s1, s2]; exact hnc
  have hhp : HalfPar D' idx' := by
    intro X _
    have e1 := relabel_cnt D idx σ X 1
    have e2 := relabel_cnt D idx σ X 2
    rw [s1] at e1; rw [s2] at e2
    show (cnt D' idx' X 1 + cnt D' idx' X 2) % 2 = 0
    rw [hD', hidx', e1, e2, ← hregc X]
    omega
  have hG : CaseG D' idx' := ⟨relabel_hidx D idx σ hidx, relabel_hidxA D idx σ hidxA, hnc', hhp⟩
  obtain ⟨L, W⟩ := side_walk_exists_poly D.toRegionDissection P hreg i
  have hne : P.v i ≠ P.v (i + 1) := by
    intro he
    apply P.e_ne_zero P.three_le i
    unfold ConvPoly.e; rw [← he]; simp
  have hL : L ≠ [] := by
    rintro rfl
    exact hne (walkT_nil_eq W)
  have hU : ∃ s : ℝ, 0 ≤ s ∧ toV2 (P.v i - P.v i) = (s * (toV2 (P.e i)).1, s * (toV2 (P.e i)).2) :=
    ⟨0, le_rfl, by unfold toV2; ext <;> simp⟩
  have hchain := walk_status_chain D' idx' hG P hreg i rfl W hU
  obtain ⟨e0, L0, hL0⟩ : ∃ e0 L0, L = e0 :: L0 := by
    cases L with
    | nil => exact absurd rfl hL
    | cons e0 L0 => exact ⟨e0, L0, rfl⟩
  have hsum := walkT_dist_sum W
  have hmem := walkT_mem_step W
  have hD'0 : slen D' 0 = slen D 2 := by rw [hD', relabel_slen, s0]
  by_cases hc0 : dist e0.2.1 e0.2.2 = slen D 2
  · left
    have hall : ∀ e ∈ L, dist e.2.1 e.2.2 = slen D 2 := by
      intro e he
      have := (hchain e0 (by rw [hL0]; simp) e he)
      rw [hD'0] at this
      exact this.mpr hc0
    have hsumA : (L.map fun e => dist e.2.1 e.2.2).sum = (L.map fun e => dist e.2.1 e.2.2).length • slen D 2 :=
      List.sum_eq_card_nsmul _ _ (fun x hx => by
        obtain ⟨e', he', rfl⟩ := List.mem_map.mp hx
        exact hall e' he')
    rw [List.length_map, nsmul_eq_mul] at hsumA
    refine ⟨L.length, List.length_pos_of_ne_nil hL, ?_⟩
    rw [ConvPoly.side, ← hsum, hsumA]
  · right
    have hall : ∀ e ∈ L, dist e.2.1 e.2.2 ≠ slen D 2 := by
      intro e he h
      have := (hchain e0 (by rw [hL0]; simp) e he)
      rw [hD'0] at this
      exact hc0 (this.mp h)
    obtain ⟨na, nb, h1, h2⟩ := list_sum_decomp2 (slen D 0) (slen D 1) (L.map fun e => dist e.2.1 e.2.2) (by
      intro x hx
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
      rcases side_len_mem D idx hidx (hmem e he) with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h (hall e he))
    refine ⟨na, nb, ?_, ?_⟩
    · rw [h2, List.length_map]; exact List.length_pos_of_ne_nil hL
    · rw [ConvPoly.side, ← hsum, h1]

end Erdos634.Draft.LaczFormal.RG

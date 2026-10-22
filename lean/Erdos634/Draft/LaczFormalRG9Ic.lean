-- Draft/LaczFormalRG9Ic.lean -- **Theorem 2.1, Case I (gamma > pi/2, gamma != 2 pi/3), Subcase Ic** (Laczkovich DCG 48 (2012), Sect. 5.3): `a, b` commensurable and `c` not a rational multiple of `a`.
-- Then `A` is a parallelogram with an angle `gamma` and side ratio a rational multiple of `sin alpha / sin beta` (conclusion (i)).
-- Route: corner counting (`caseI_exc_count`: `R >= M-2`, exceptional vertices `<= R-M+2`), the `gamma` rule along a side (`no_adjacent_gamma`, Lemma 4.4 (i)) on a side with both ends single `gamma` and no exceptional
-- vertex (exists unless `R = M - 2`), `M <= 4` by non-adjacency, the parallelogram `quad_parallelogram_gen`, rationality (Lemma 4.7: `polytiling_rational`).  UNAUDITED.
-- Credit: Laczkovich (DCG 48 (2012), Sect. 5 and Lemmas 4.4, 4.7), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG9Sides

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

/-- A side without exceptional vertex whose two ends are single `γ` corners is impossible (Lemma 4.4 (i)). -/
theorem caseI_no_good_gg_side (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseC D idx) (h1 : Real.pi / 2 < D.model.angleAt 2) (h3 : D.model.angleAt 2 ≠ 2 * Real.pi / 3)
    (i : Fin M) (hSi : ¬ SideBad D idx P i)
    (g1 : cnt D idx (P.v i) 0 = 0 ∧ cnt D idx (P.v i) 1 = 0) (g2 : cnt D idx (P.v (i + 1)) 0 = 0 ∧ cnt D idx (P.v (i + 1)) 1 = 0) : False := by
  have hnorm : ∀ V : Plane, (∃ j k', (D.tile j).pts k' = V) → (∃ t : ℝ, 0 < t ∧ t < 1 ∧ V = (1 - t) • P.v (i - 1 + 1) + t • P.v (i - 1 + 1 + 1)) →
      cnt D idx V 0 = 1 ∧ cnt D idx V 1 = 1 ∧ cnt D idx V 2 = 1 := by
    intro V hv ⟨t, ht0, ht1, hVt⟩
    rw [sub_add_cancel] at hVt
    have hne : V ∉ excVerts D idx P := fun hex => hSi ⟨V, hex, t, ht0, ht1, hVt⟩
    exact caseI_normal_side D P hreg idx h.hidxA h.hregc h1 h3 ht0 ht1 hVt hv hne
  exact no_adjacent_gamma D P hreg idx h (i - 1) hnorm (by rw [sub_add_cancel]; exact g1) (by rw [sub_add_cancel]; exact g2)

/-- **Case I core (any `a, b, c`, hypotheses `CaseC`):** the polygon is a quadrilateral whose angles at `v_{a+1}, v_{a+2}, v_{a+3}` are `γ, π - γ, γ`. -/
theorem caseI_core (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseC D idx) (h1 : Real.pi / 2 < D.model.angleAt 2) (h3 : D.model.angleAt 2 ≠ 2 * Real.pi / 3) :
    M = 4 ∧ ∃ a : Fin M, P.angle (a + 1) = D.model.angleAt 2 ∧ P.angle (a + 2) = Real.pi - D.model.angleAt 2 ∧ P.angle (a + 3) = D.model.angleAt 2 := by
  classical
  have hpi := Real.pi_pos
  have hγ := model_gamma_lt_pi D
  have hw : 0 < Real.pi - D.model.angleAt 2 := by linarith
  have hw2 : Real.pi - D.model.angleAt 2 < Real.pi / 2 := by linarith
  have hM3 := P.three_le
  have hpoly := caseI_polyvertex D P hreg idx h.hidxA h.hregc h1
  obtain ⟨hPR, hRM2, hexc⟩ := caseI_exc_count D P hreg idx h.hidxA h.hregc h1 h3
  have hang := caseI_angle_sum D P hreg idx h.hidxA h.hregc
  set S : Finset (Fin M) := Finset.univ.filter (fun k => cnt D idx (P.v (k + 1)) 2 = 1) with hS
  have ht01 : ∀ k : Fin M, cnt D idx (P.v (k + 1)) 2 = 0 ∨ cnt D idx (P.v (k + 1)) 2 = 1 := by
    intro k; rcases hpoly k with ⟨-, h2, -⟩ | ⟨h2, -, -⟩ <;> omega
  have hR : cntR2 D idx P = S.card := by
    unfold cntR2
    rw [hS, Finset.card_filter]
    apply Finset.sum_congr rfl
    intro k _
    rcases ht01 k with h0 | h0 <;> simp [h0]
  have hRM : S.card ≤ M := by
    have := Finset.card_le_univ S
    simpa using this
  have hsumPR : M ≤ cntP0 D idx P + cntR2 D idx P := by
    unfold cntP0 cntR2
    rw [← Finset.sum_add_distrib]
    have : ∑ _k : Fin M, 1 ≤ ∑ k : Fin M, (cnt D idx (P.v (k + 1)) 0 + cnt D idx (P.v (k + 1)) 2) := by
      apply Finset.sum_le_sum
      intro k _
      rcases hpoly k with ⟨-, h2, -⟩ | ⟨h2, h0, -⟩ <;> omega
    simpa using this
  -- the sides with two single-γ ends
  set G : Finset (Fin M) := Finset.univ.filter (fun i => (i - 1) ∈ S ∧ i ∈ S) with hG
  have hGcard : 2 * S.card ≤ G.card + M := by
    set S' : Finset (Fin M) := S.image (fun k => k + 1) with hS'
    have hS'card : S'.card = S.card := Finset.card_image_of_injective _ (add_left_injective 1)
    have hG' : G = S' ∩ S := by
      ext i
      simp only [hG, hS', Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter, Finset.mem_image]
      constructor
      · rintro ⟨h1', h2'⟩; exact ⟨⟨i - 1, h1', sub_add_cancel i 1⟩, h2'⟩
      · rintro ⟨⟨k, hk, rfl⟩, h2'⟩; exact ⟨by rw [add_sub_cancel_right]; exact hk, h2'⟩
    have hU : (S' ∪ S).card ≤ M := by simpa using Finset.card_le_univ (S' ∪ S)
    have := Finset.card_union_add_card_inter S' S
    rw [hG']
    omega
  -- a good side with both ends single `γ` does not exist
  have hgg : ∀ i : Fin M, i ∈ G → ¬ SideBad D idx P i → False := by
    intro i hi hSi
    simp only [hG, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨hi1, hi2⟩ := hi
    have c1 : cnt D idx (P.v (i - 1 + 1)) 2 = 1 := by simpa [hS] using hi1
    have c2 : cnt D idx (P.v (i + 1)) 2 = 1 := by simpa [hS] using hi2
    have z1 : cnt D idx (P.v i) 0 = 0 := by
      rcases hpoly (i - 1) with ⟨a, -, -⟩ | ⟨a, -, -⟩
      · rw [sub_add_cancel] at a; exact a
      · omega
    have z2 : cnt D idx (P.v (i + 1)) 0 = 0 := by
      rcases hpoly i with ⟨a, -, -⟩ | ⟨a, -, -⟩
      · exact a
      · omega
    exact caseI_no_good_gg_side D P hreg idx h h1 h3 i hSi ⟨z1, by rw [← h.hregc]; exact z1⟩ ⟨z2, by rw [← h.hregc]; exact z2⟩
  have hexcR : (excVerts D idx P).card + M ≤ S.card + 2 := by omega
  have hRreal : ((S.card : ℝ) - cntP0 D idx P) * (Real.pi - D.model.angleAt 2) = ((S.card : ℝ) - M + 2) * Real.pi := by
    rw [← hR]; exact hang
  have hsumPR' : M ≤ cntP0 D idx P + S.card := by rw [← hR]; exact hsumPR
  have hRlow : M ≤ S.card + 2 := by omega
  by_cases hRM2' : S.card + 2 = M
  · -- `R = M - 2`: no exceptional vertex, no good side with two single-γ ends
    have hexc0 : (excVerts D idx P).card = 0 := by omega
    have hGempty : ∀ i, i ∉ G := by
      intro i hi
      apply hgg i hi
      rintro ⟨X, hX, -⟩
      rw [Finset.card_eq_zero] at hexc0
      rw [hexc0] at hX
      simp at hX
    have hG0 : G.card = 0 := by
      rw [Finset.card_eq_zero]; ext i; simp [hGempty i]
    have hM4 : M ≤ 4 := by omega
    -- P = R
    have hPeq : cntP0 D idx P = S.card := by
      have h0 : ((S.card : ℝ) - M + 2) = 0 := by
        have : (S.card : ℝ) + 2 = M := by exact_mod_cast hRM2'
        linarith
      rw [h0, zero_mul] at hRreal
      have := mul_eq_zero.mp hRreal
      rcases this with h0' | h0'
      · have : (S.card : ℝ) = cntP0 D idx P := by linarith
        exact_mod_cast this.symm
      · linarith
    have hM4' : M = 4 := by omega
    subst hM4'
    refine ⟨rfl, ?_⟩
    -- explicit analysis in `Fin 4`
    have hS4 : S.card = 2 := by omega
    have hP4 : cntP0 D idx P = 2 := by omega
    have hsumR : ∑ k : Fin 4, cnt D idx (P.v (k + 1)) 2 = 2 := by
      have h' : ∑ k : Fin 4, cnt D idx (P.v (k + 1)) 2 = S.card := hR
      omega
    have hsumP : ∑ k : Fin 4, cnt D idx (P.v (k + 1)) 0 = 2 := by
      have h' : ∑ k : Fin 4, cnt D idx (P.v (k + 1)) 0 = cntP0 D idx P := rfl
      omega
    rw [Fin.sum_univ_four] at hsumR hsumP
    have hadj : ∀ i : Fin 4, ¬ (cnt D idx (P.v (i - 1 + 1)) 2 = 1 ∧ cnt D idx (P.v (i + 1)) 2 = 1) := by
      intro i ⟨c1, c2⟩
      apply hGempty i
      simp only [hG, hS, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨c1, c2⟩
    have a0 := hadj 0
    have a1 := hadj 1
    have a2 := hadj 2
    have a3 := hadj 3
    have e30 : (0 : Fin 4) - 1 + 1 = 0 := by decide
    have e01 : (1 : Fin 4) - 1 + 1 = 1 := by decide
    have e12 : (2 : Fin 4) - 1 + 1 = 2 := by decide
    have e23 : (3 : Fin 4) - 1 + 1 = 3 := by decide
    rw [e30] at a0
    rw [e01] at a1
    rw [e12] at a2
    rw [e23] at a3
    have e3 : (3 : Fin 4) + 1 = 0 := by decide
    have n0 := hpoly 0
    have n1 := hpoly 1
    have n2 := hpoly 2
    have n3 := hpoly 3
    have eA : (0 : Fin 4) + 1 = 1 := by decide
    have eB : (1 : Fin 4) + 1 = 2 := by decide
    have eC : (2 : Fin 4) + 1 = 3 := by decide
    simp only [eA, eB, eC, e3] at n0 n1 n2 n3 a0 a1 a2 a3 hsumR hsumP
    -- pure arithmetic on the corner counts
    have key : (cnt D idx (P.v 1) 2 = 1 ∧ cnt D idx (P.v 2) 2 = 0 ∧ cnt D idx (P.v 3) 2 = 1 ∧ cnt D idx (P.v 0) 2 = 0 ∧ cnt D idx (P.v 2) 0 = 1) ∨
        (cnt D idx (P.v 1) 2 = 0 ∧ cnt D idx (P.v 2) 2 = 1 ∧ cnt D idx (P.v 3) 2 = 0 ∧ cnt D idx (P.v 0) 2 = 1 ∧ cnt D idx (P.v 3) 0 = 1) := by
      rcases n0 with ⟨x0, y0, -⟩ | ⟨x0, y0, -⟩ <;> rcases n1 with ⟨x1, y1, -⟩ | ⟨x1, y1, -⟩ <;> rcases n2 with ⟨x2, y2, -⟩ | ⟨x2, y2, -⟩ <;>
        rcases n3 with ⟨x3, y3, -⟩ | ⟨x3, y3, -⟩ <;> omega
    rcases key with ⟨k1, k2, k3, k0, ku⟩ | ⟨k1, k2, k3, k0, ku⟩
    · refine ⟨0, ?_, ?_, ?_⟩
      · rcases n0 with ⟨-, -, ang⟩ | ⟨x, -, -⟩
        · simpa using ang
        · omega
      · rcases n1 with ⟨x, -, -⟩ | ⟨-, -, ang⟩
        · omega
        · simpa [ku] using ang
      · rcases n2 with ⟨-, -, ang⟩ | ⟨x, -, -⟩
        · simpa using ang
        · omega
    · refine ⟨1, ?_, ?_, ?_⟩
      · rcases n1 with ⟨-, -, ang⟩ | ⟨x, -, -⟩
        · simpa using ang
        · omega
      · rcases n2 with ⟨x, -, -⟩ | ⟨-, -, ang⟩
        · omega
        · simpa [ku] using ang
      · rcases n3 with ⟨-, -, ang⟩ | ⟨x, -, -⟩
        · simpa using ang
        · omega
  · -- `R ≥ M - 1`: a good side with two single-γ ends exists
    exfalso
    have hM4 : 4 ≤ M ∨ M = 3 := by omega
    rcases hM4 with hM4 | hM3'
    · have hlt : (excVerts D idx P).card < G.card := by omega
      obtain ⟨i, hi, hgood⟩ := exists_good_side D idx P G hlt
      exact hgg i hi hgood
    · subst hM3'
      -- `R = 2` (since `R ≥ M - 1`, `R ≤ M` and `R ≠ M - 2`) or `R = 3`
      rcases (by omega : S.card = 2 ∨ S.card = 3) with h2 | h3'
      · -- `(2 - P) w = π`, `P ≥ 1`
        rw [h2] at hRreal hsumPR'
        have hP1 : (1 : ℝ) ≤ cntP0 D idx P := by exact_mod_cast (by omega : 1 ≤ cntP0 D idx P)
        push_cast at hRreal
        nlinarith
      · have hlt : (excVerts D idx P).card < G.card := by omega
        obtain ⟨i, hi, hgood⟩ := exists_good_side D idx P G hlt
        exact hgg i hi hgood

/-- **Theorem 2.1, Case I, Subcase Ic** (Laczkovich DCG 48 (2012), Sect. 5.3): a regular tiling of a convex `M`-gon by a triangle with `γ > π/2`, `γ ≠ 2π/3`, `a, b` commensurable and `c`
not a rational multiple of `a`: conclusion (i), the polygon is a parallelogram with an angle `γ` and side ratio a rational multiple of `sin α / sin β`. -/
theorem caseI_c {N M : ℕ} [NeZero M] (T : PolyTiling N M) (hreg : RegularPQ T.C) (h1 : Real.pi / 2 < angleAt T.C.model 2) (h3 : angleAt T.C.model 2 ≠ 2 * Real.pi / 3)
    (hab : Comm (slen T.C 0) (slen T.C 1)) (hac : ¬ Comm (slen T.C 0) (slen T.C 2)) : Concl1 T.C T.P := by
  classical
  have hRat := polytiling_rational T hreg hab hac
  obtain ⟨idx, hA, hcnt⟩ := hreg
  haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  have hC : CaseC T.C idx := ⟨idx_dist_of_angle T.C idx hA, hA, fun X => hcnt X, notComb_c_of_comm (slen_pos T.C 2) hab hac⟩
  obtain ⟨hM4, a, ha1, ha2, ha3⟩ := caseI_core T.C T.P T.region_eq idx hC h1 h3
  have hratio : ∃ q : ℚ, T.P.side 0 / T.P.side 1 = q * (Real.sin (angleAt T.C.model 0) / Real.sin (angleAt T.C.model 1)) := by
    obtain ⟨m1, n1, hm1, hn1, e1⟩ := hRat 0 1
    obtain ⟨m2, n2, hm2, hn2, e2⟩ := hab
    have hs1 : 0 < T.P.side 1 := side_pos T.P 1
    have hsb : 0 < slen T.C 1 := slen_pos T.C 1
    refine ⟨((n1 * m2 : ℕ) : ℚ) / ((m1 * n2 : ℕ) : ℚ), ?_⟩
    have hsr : Real.sin (angleAt T.C.model 0) / Real.sin (angleAt T.C.model 1) = slen T.C 0 / slen T.C 1 := sin_ratio_eq T.C
    rw [hsr]
    have hm1' : (m1 : ℝ) ≠ 0 := by positivity
    have hn2' : (n2 : ℝ) ≠ 0 := by positivity
    have hm2' : (m2 : ℝ) ≠ 0 := by positivity
    push_cast
    rw [div_eq_iff hs1.ne']
    field_simp
    linear_combination ((n2 : ℝ) * slen T.C 1) * e1 - ((n1 : ℝ) * T.P.side 1) * e2
  subst hM4
  have hpg : ∀ i : Fin 4, T.P.v i + T.P.v (i + 2) = T.P.v (i + 1) + T.P.v (i + 3) :=
    par_all T.P a (quad_parallelogram_gen T.P a (angleAt T.C.model 2) ha1 ha2 ha3)
  exact ⟨⟨rfl, hpg⟩, ⟨a + 1, ha1⟩, Or.inl hratio⟩

end Erdos634.Draft.LaczFormal.RG

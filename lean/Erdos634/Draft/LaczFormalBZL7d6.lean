-- Draft/LaczFormalBZL7d6.lean -- Beeson-Zhang (arXiv 2604.01314v1) THEOREM 3.7 and THEOREM 1.1 for every triangle ABC not similar to the tile (alpha not in Q pi), formal:
--   `bz_allc_false` : Comm a b, c not commensurable with a, NotSim  ==>  False.
--   `bz_thm11`      : D : CongruentDissection N (any N, reflections allowed, not edge-to-edge) of a triangle by the tile (alpha, pi/3 - alpha, 2 pi/3), alpha not in Q pi, target not similar to the tile
--                     ==>  Comm a b /\ Comm a c    (the sides of the tile are pairwise commensurable).
-- Route differs from the print: Lemmas 3.5, 3.6 (d1-d3) give Comm a b; if c were not commensurable with a, `NotComb c b a`; Lemma 3.4 (d4a, d4b: status chain along each side of the triangle without the regularity of the corners,
-- `side_has_c`, `sides_all_c`) makes every boundary tile edge a c-edge; the flux invariant of f_alpha (as in BZ Sect. 5, `bz_phi_gen`) then contradicts the strict triangle inequality for ANY sign pattern (BZ treat only the
-- two exceptional targets (equilateral, (2alpha,2beta,pi/3)) this way and the others by a c-relation).  NOTE, UNAUDITED.
-- Credit: Beeson-Zhang (arXiv 2604.01314v1, Lemmas 3.4-3.6, Thm 3.7, Thm 1.1, Thm 5.2, 5.3), Laczkovich (DCG 48 (2012), Sect. 4, 7.3; invariant Phi), Beeson.
import Erdos634.Draft.LaczFormalBZL7d5b

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

theorem comm_of_ratmul {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (r : ℚ) (hr : c = (r : ℝ) * a) : Comm a c := by
  have hrpos : (0 : ℚ) < r := by
    by_contra hneg
    push Not at hneg
    have : (r : ℝ) ≤ 0 := by exact_mod_cast hneg
    nlinarith
  have hnum : 0 < r.num := Rat.num_pos.mpr hrpos
  refine ⟨r.num.toNat, r.den, ?_, r.den_pos, ?_⟩
  · omega
  · have h1' : ((r.num.toNat : ℕ) : ℝ) = (r.num : ℝ) := by
      have : ((r.num.toNat : ℕ) : ℤ) = r.num := Int.toNat_of_nonneg hnum.le
      exact_mod_cast this
    have h2' : (r : ℝ) * (r.den : ℝ) = (r.num : ℝ) := by
      have := Rat.mul_den_eq_num r
      exact_mod_cast this
    rw [h1', hr, ← h2']
    ring

/-- Corner decomposition: every angle of the target is `u α + v β` with `u, v` naturals. -/
theorem target_angle_form (D : CongruentDissection N) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : D.model.TwoPiThreeData α a b c) (hNS : NotSim D) :
    ∀ j, ∃ u v : ℕ, D.target.angleAt j = u * α + v * (Real.pi / 3 - α) := by
  refine tri_setup2 D h ?_
  intro Dr _ P hreg idx hidx hidxA e0 e1 e2 hA0 hA1 hA2 hsum hpos hlt hns τ hτv hτa
  have hcorn := corner_gamma_zero Dr P hreg idx hidxA hα hA0 hA1 hA2 hsum hpos (hns hNS)
  intro j
  obtain ⟨i, rfl⟩ := τ.surjective j
  have hk : i - 1 + 1 = i := (ConvPoly.fin_facts P.three_le i).2.2.2.2.1
  have hv : ∃ j' k', (Dr.tile j').pts k' = P.v (i - 1 + 1) := poly_vertex_is_tile_vertex Dr.toRegionDissection P hreg (i - 1 + 1)
  have hA := corner_A Dr P hreg idx hidxA (i - 1) hv
  rw [hk] at hA
  have h2 := hcorn (i - 1)
  rw [hk] at h2
  refine ⟨cnt Dr idx (P.v i) 0, cnt Dr idx (P.v i) 1, ?_⟩
  rw [← hτa i, ← hA]
  unfold Asum
  rw [Fin.sum_univ_three, h2, hA0, hA1]
  simp

/-- **All boundary edges are c-edges: contradiction.**  `a, b` commensurable, `c` not commensurable with `a`, target not similar to the tile. -/
theorem bz_allc_false (D : CongruentDissection N) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : D.model.TwoPiThreeData α a b c) (hNS : NotSim D) (hab : Comm a b) (hac : ¬ Comm a c) : False := by
  have ha : 0 < a := by
    obtain ⟨σ, -, o0, -⟩ := h
    rw [← o0]; exact D.model.oppLen_pos' _
  have hb : 0 < b := by
    obtain ⟨σ, -, -, -, o1, -⟩ := h
    rw [← o1]; exact D.model.oppLen_pos' _
  have hc : 0 < c := by
    obtain ⟨σ, -, -, -, -, -, o2⟩ := h
    rw [← o2]; exact D.model.oppLen_pos' _
  -- the sides of the target are positive multiples of c
  have hsides : ∀ j : Fin 3, ∃ m : ℕ, 0 < m ∧ dist (D.target.pts j) (D.target.pts (j + 1)) = m * c := by
    refine tri_setup2 D h ?_
    intro Dr _ P hreg idx hidx hidxA e0 e1 e2 hA0 hA1 hA2 hsum hpos hlt hns τ hτv hτa
    have hcorn := corner_gamma_zero Dr P hreg idx hidxA hα hA0 hA1 hA2 hsum hpos (hns hNS)
    have hnc : NotComb (slen Dr 2) (slen Dr 1) (slen Dr 0) := by
      rw [e0, e1, e2]; exact notComb_c_of_comm hc hab hac
    have hall := sides_all_c Dr P hreg idx hidx hidxA hnc hA2 (by rw [hA0, hA1]; ring) (by rw [hA0]; exact hα) hcorn
    intro j
    obtain ⟨i, hi⟩ := target_side_eq D.target P τ hτv j
    obtain ⟨m, hm, hmi⟩ := hall i
    exact ⟨m, hm, by rw [← hi, hmi, e2]⟩
  choose m hm hmeq using hsides
  -- each side of the target carries exactly m_j tile edges, all of length c
  have hcard : ∀ j : Fin 3, ((D.sideEdges j).filter (fun e => D.eLen e = c)).card = m j := by
    intro j
    have hlen : ∀ e ∈ D.sideEdges j, D.eLen e = a ∨ D.eLen e = b ∨ D.eLen e = c := by
      intro e _
      rcases D.edge_class h e with ⟨-, h2⟩ | ⟨-, h2 | h2⟩
      · exact Or.inr (Or.inr h2)
      · exact Or.inl h2
      · exact Or.inr (Or.inl h2)
    obtain ⟨hall, hcd⟩ := sideEdges_all_c (D.sideEdges j) D.eLen ha hb hc hab hac hlen (m j) (hm j)
      (by rw [D.side_len_sum j, hmeq j])
    rw [Finset.filter_true_of_mem hall]
    exact hcd
  -- the flux identity of f_alpha
  have hcr : ¬ ∃ r : ℚ, c = (r : ℝ) * a := fun ⟨r, hr⟩ => hac (comm_of_ratmul ha hc r hr)
  have e1 := bz_phi_gen D hα h hab hcr (fAlpha α hα) (GridChar.rankn_sq _ _ _ _ _ _ _) (c + a - b)
    (fun T kg hT hkg => T.flux_cedge hα hT kg hkg)
  -- target angles in the lattice
  have hform := target_angle_form D hα h hNS
  have hmem : ∀ k, ((D.target.angleAt k : ℝ) : Real.Angle) ∈ (fAlpha α hα).L := by
    intro k
    obtain ⟨u, v, hk⟩ := hform k
    rw [hk, show (u : ℝ) * α + v * (Real.pi / 3 - α) = ((v : ℤ) : ℝ) * (Real.pi / ((3 : ℕ) : ℝ)) + ((((u : ℤ) - v : ℤ)) : ℝ) * α by push_cast; ring]
    exact GridChar.rankn_mem _ _ _ _ _ _ _ _ _
  have hsq := GridChar.rankn_sq 3 (by norm_num) (by decide) α hα 0 0
  obtain ⟨s, hw, -⟩ := D.target.weight_form (fAlpha α hα) hsq hmem
  have hw1 : ∀ d : Dir, (fAlpha α hα).weight d * (fAlpha α hα).weight d = 1 := fun d => (fAlpha α hα).val_sq hsq _
  have hs : s ≠ 0 := by
    intro hs0
    have := hw1 (D.target.leftUnit 0)
    rw [hw 0, hs0] at this
    simp at this
  have hprod := D.target.chi_prod (fAlpha α hα) hmem
  set n : Fin 3 → ℝ := fun j => (m j : ℝ) with hn
  have hcardR : ∀ j, ((((D.sideEdges j).filter (fun e => D.eLen e = c)).card : ℕ) : ℝ) = n j := by
    intro j; rw [hcard j]
  simp only [hcardR] at e1
  have hfl : D.target.flux (fAlpha α hα).weight = ∑ j : Fin 3, dist (D.target.pts j) (D.target.pts (j + 1)) * (fAlpha α hα).weight (D.target.leftUnit j) := by
    unfold Tri.flux; simp only [smul_eq_mul]
  rw [hfl] at e1
  have hfm : ∀ j : Fin 3, dist (D.target.pts j) (D.target.pts (j + 1)) = c * n j := by
    intro j; rw [hmeq j]; simp only [hn]; ring
  simp only [hfm] at e1
  have habne : a - b ≠ 0 := sub_ne_zero.mpr (h.a_ne_b hα)
  have hsum0 : ∑ j : Fin 3, n j * (fAlpha α hα).weight (D.target.leftUnit j) = 0 := by
    have : (a - b) * ∑ j : Fin 3, n j * (fAlpha α hα).weight (D.target.leftUnit j) = 0 := by
      have e2 : ∑ j : Fin 3, c * n j * (fAlpha α hα).weight (D.target.leftUnit j) = c * ∑ j : Fin 3, n j * (fAlpha α hα).weight (D.target.leftUnit j) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
      rw [e2] at e1
      linear_combination e1
    exact (mul_eq_zero.mp this).resolve_left habne
  -- signs
  set ε : Fin 3 → ℝ := fun j => (fAlpha α hα).chi ((Real.pi - D.target.angleAt (j + 2) : ℝ) : Real.Angle) with hε
  have hε2 : ∀ j, ε j * ε j = 1 := fun j => hsq _ (D.target.pi_sub_angleAt_mem _ hmem _)
  have hsum1 : s * (ε 0 * n 0 + ε 1 * n 1 + ε 2 * n 2) = 0 := by
    have := hsum0
    rw [Fin.sum_univ_three, hw 0, hw 1, hw 2] at this
    simp only [hε]
    linear_combination this
  have hsum2 : ε 0 * n 0 + ε 1 * n 1 + ε 2 * n 2 = 0 := (mul_eq_zero.mp hsum1).resolve_left hs
  have hprod' : ε 0 * ε 1 * ε 2 = 1 := by
    simp only [hε]
    have e0 : (0 : Fin 3) + 2 = 2 := by decide
    have e1' : (1 : Fin 3) + 2 = 0 := by decide
    have e2' : (2 : Fin 3) + 2 = 1 := by decide
    rw [e0, e1', e2']
    linear_combination hprod
  -- triangle inequalities
  have hk : ∀ k : Fin 3, dist (D.target.pts (k + 1)) (D.target.pts (k + 1 + 1)) = D.target.oppLen k := by
    intro k
    simp only [Tri.oppLen]
    rw [show k + 1 + 1 = k + 2 from by revert k; decide]
  have t0 := D.target.oppLen_lt_add 0
  have t1 := D.target.oppLen_lt_add 1
  have t2 := D.target.oppLen_lt_add 2
  have o0 := hk 0
  have o1 := hk 1
  have o2 := hk 2
  have f0 := hfm 0
  have f1 := hfm 1
  have f2 := hfm 2
  have r0 : (0 : Fin 3) + 1 = 1 := by decide
  have r1 : (1 : Fin 3) + 1 = 2 := by decide
  have r2 : (2 : Fin 3) + 1 = 0 := by decide
  have r00 : (0 : Fin 3) + 1 + 1 = 2 := by decide
  have r11 : (1 : Fin 3) + 1 + 1 = 0 := by decide
  have r22 : (2 : Fin 3) + 1 + 1 = 1 := by decide
  rw [r00, r0] at o0
  rw [r11, r1] at o1
  rw [r22, r2] at o2
  have hp0 : (0 : ℝ) < n 0 := by simp only [hn]; exact_mod_cast hm 0
  have hp1 : (0 : ℝ) < n 1 := by simp only [hn]; exact_mod_cast hm 1
  have hp2 : (0 : ℝ) < n 2 := by simp only [hn]; exact_mod_cast hm 2
  -- oppLen 0 = F 1 = c n1, oppLen 1 = F 2 = c n2, oppLen 2 = F 0 = c n0
  have u0 : D.target.oppLen 0 = c * n 1 := by rw [← o0]; exact f1
  have u1 : D.target.oppLen 1 = c * n 2 := by rw [← o1]; exact f2
  have u2 : D.target.oppLen 2 = c * n 0 := by rw [← o2]; exact f0
  rw [show (0 : Fin 3) + 1 = 1 from r0, show (0 : Fin 3) + 2 = 2 from by decide, u0, u1, u2] at t0
  rw [show (1 : Fin 3) + 1 = 2 from r1, show (1 : Fin 3) + 2 = 0 from by decide, u0, u1, u2] at t1
  rw [show (2 : Fin 3) + 1 = 0 from r2, show (2 : Fin 3) + 2 = 1 from by decide, u0, u1, u2] at t2
  have T1 : n 1 < n 2 + n 0 := by nlinarith
  have T2 : n 2 < n 0 + n 1 := by nlinarith
  have T0 : n 0 < n 1 + n 2 := by nlinarith
  exact sign_contradiction (ε 0) (ε 1) (ε 2) (hε2 0) (hε2 1) (hε2 2) hprod' (n 0) (n 1) (n 2) hp0 hp1 hp2 T0 T1 T2 hsum2

/-- **Beeson-Zhang Theorem 1.1** (Theorem 3.7 with Theorems 5.2, 5.3), triangle targets not similar to the tile: the sides of the tile are pairwise commensurable. -/
theorem bz_thm11 (D : CongruentDissection N) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : D.model.TwoPiThreeData α a b c) (hNS : NotSim D) : Comm a b ∧ Comm a c := by
  have hab := bz_ab_comm_notsim D hα h hNS
  refine ⟨hab, ?_⟩
  by_contra hac
  exact bz_allc_false D hα h hNS hab hac

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.target_angle_form
#print axioms Erdos634.Draft.LaczFormal.RG.bz_allc_false
#print axioms Erdos634.Draft.LaczFormal.RG.bz_thm11

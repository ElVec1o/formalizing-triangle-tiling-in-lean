-- Draft/LaczFormalRG9Ia3.lean -- Case I, Subcase Ia: the core (generalization of `caseI_core` to an abstract notion of blocked side) and the assembly: `caseI_a`.  UNAUDITED.
-- Credit: Laczkovich (DCG 48 (2012), Sect. 5.1, Lemma 4.3, Lemma 4.1), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG9Ia2
import Erdos634.Draft.LaczFormalRG9Ic

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

/-- **Case I core (any `a, b, c`, hypotheses `CaseC`):** the polygon is a quadrilateral whose angles at `v_{a+1}, v_{a+2}, v_{a+3}` are `γ, π - γ, γ`. -/
theorem caseI_core_gen (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) (hregc : ∀ X, cnt D idx X 0 = cnt D idx X 1)
    (h1 : Real.pi / 2 < D.model.angleAt 2) (h3 : D.model.angleAt 2 ≠ 2 * Real.pi / 3)
    (Blk : Fin M → Prop) (hBlk : (Finset.univ.filter Blk).card ≤ (excVerts D idx P).card)
    (hgg' : ∀ i : Fin M, cnt D idx (P.v (i - 1 + 1)) 2 = 1 → cnt D idx (P.v (i + 1)) 2 = 1 → ¬ Blk i → False) :
    M = 4 ∧ (∃ a : Fin M, P.angle (a + 1) = D.model.angleAt 2 ∧ P.angle (a + 2) = Real.pi - D.model.angleAt 2 ∧ P.angle (a + 3) = D.model.angleAt 2 ∧
      cnt D idx (P.v (a + 1)) 0 = 0 ∧ cnt D idx (P.v (a + 1)) 2 = 1) ∧ (excVerts D idx P).card = 0 := by
  classical
  have hpi := Real.pi_pos
  have hγ := model_gamma_lt_pi D
  have hw : 0 < Real.pi - D.model.angleAt 2 := by linarith
  have hw2 : Real.pi - D.model.angleAt 2 < Real.pi / 2 := by linarith
  have hM3 := P.three_le
  have hpoly := caseI_polyvertex D P hreg idx hidxA hregc h1
  obtain ⟨hPR, hRM2, hexc⟩ := caseI_exc_count D P hreg idx hidxA hregc h1 h3
  have hang := caseI_angle_sum D P hreg idx hidxA hregc
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
  have hgg : ∀ i : Fin M, i ∈ G → ¬ Blk i → False := by
    intro i hi hb
    simp only [hG, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨hi1, hi2⟩ := hi
    exact hgg' i (by simpa [hS] using hi1) (by simpa [hS] using hi2) hb
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
      intro hb
      have hz : (Finset.univ.filter Blk).card = 0 := by omega
      rw [Finset.card_eq_zero] at hz
      have hmem : i ∈ Finset.univ.filter Blk := by simp [hb]
      rw [hz] at hmem
      simp at hmem
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
    refine ⟨rfl, ?_, hexc0⟩
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
    · refine ⟨0, ?_, ?_, ?_, ?_, ?_⟩
      · rcases n0 with ⟨-, -, ang⟩ | ⟨x, -, -⟩
        · simpa using ang
        · omega
      · rcases n1 with ⟨x, -, -⟩ | ⟨-, -, ang⟩
        · omega
        · simpa [ku] using ang
      · rcases n2 with ⟨-, -, ang⟩ | ⟨x, -, -⟩
        · simpa using ang
        · omega
      · rcases n0 with ⟨c0, -, -⟩ | ⟨x, -, -⟩
        · simpa using c0
        · omega
      · rcases n0 with ⟨-, c2, -⟩ | ⟨x, -, -⟩
        · simpa using c2
        · omega
    · refine ⟨1, ?_, ?_, ?_, ?_, ?_⟩
      · rcases n1 with ⟨-, -, ang⟩ | ⟨x, -, -⟩
        · simpa using ang
        · omega
      · rcases n2 with ⟨x, -, -⟩ | ⟨-, -, ang⟩
        · omega
        · simpa [ku] using ang
      · rcases n3 with ⟨-, -, ang⟩ | ⟨x, -, -⟩
        · simpa using ang
        · omega
      · rcases n1 with ⟨c0, -, -⟩ | ⟨x, -, -⟩
        · simpa using c0
        · omega
      · rcases n1 with ⟨-, c2, -⟩ | ⟨x, -, -⟩
        · simpa using c2
        · omega
  · -- `R ≥ M - 1`: a good side with two single-γ ends exists
    exfalso
    have hM4 : 4 ≤ M ∨ M = 3 := by omega
    rcases hM4 with hM4 | hM3'
    · have hlt : (Finset.univ.filter Blk).card < G.card := by omega
      obtain ⟨i, hi, hgood⟩ : ∃ i ∈ G, ¬ Blk i := by
        by_contra hall
        push Not at hall
        have hsub : G ⊆ Finset.univ.filter Blk := by
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact hall i hi
        have := Finset.card_le_card hsub
        omega
      exact hgg i hi hgood
    · subst hM3'
      -- `R = 2` (since `R ≥ M - 1`, `R ≤ M` and `R ≠ M - 2`) or `R = 3`
      rcases (by omega : S.card = 2 ∨ S.card = 3) with h2 | h3'
      · -- `(2 - P) w = π`, `P ≥ 1`
        rw [h2] at hRreal hsumPR'
        have hP1 : (1 : ℝ) ≤ cntP0 D idx P := by exact_mod_cast (by omega : 1 ≤ cntP0 D idx P)
        push_cast at hRreal
        nlinarith
      · have hlt : (Finset.univ.filter Blk).card < G.card := by omega
        obtain ⟨i, hi, hgood⟩ : ∃ i ∈ G, ¬ Blk i := by
          by_contra hall
          push Not at hall
          have hsub : G ⊆ Finset.univ.filter Blk := by
            intro i hi
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact hall i hi
          have := Finset.card_le_card hsub
          omega
        exact hgg i hi hgood


/-- **Conclusion (i) from a parallelogram with angles `γ, π-γ, γ` and a side adjacent to a `γ` vertex that is an integer multiple of `a`** (Lemma 4.1). -/
theorem concl1_of_gamma_para {N : ℕ} (T : PolyTiling N 4) (a : Fin 4) (hang1 : T.P.angle (a + 1) = angleAt T.C.model 2)
    (hang2 : T.P.angle (a + 2) = Real.pi - angleAt T.C.model 2) (hang3 : T.P.angle (a + 3) = angleAt T.C.model 2)
    (hside : (∃ m : ℕ, 0 < m ∧ T.P.side a = m * slen T.C 0) ∨ (∃ m : ℕ, 0 < m ∧ T.P.side (a + 1) = m * slen T.C 0)) : Concl1 T.C T.P := by
  have hpar : T.P.v a + T.P.v (a + 2) = T.P.v (a + 1) + T.P.v (a + 3) := quad_parallelogram_gen T.P a (angleAt T.C.model 2) hang1 hang2 hang3
  have hpg := par_all T.P a hpar
  have ee2 : a + 1 + 3 = a := by
    have : ∀ e : Fin 4, e + 1 + 3 = e := by decide
    exact this a
  let T' : PolyTiling N 4 := ⟨T.C, polyRot T.P (a + 1), by rw [polyRot_carrier]; exact T.region_eq⟩
  have hpg' : T'.P.v 0 + T'.P.v 2 = T'.P.v 1 + T'.P.v 3 := by
    show T.P.v (0 + (a + 1)) + T.P.v (2 + (a + 1)) = T.P.v (1 + (a + 1)) + T.P.v (3 + (a + 1))
    rw [zero_add, add_comm 2, add_comm 1, add_comm 3]
    exact hpg (a + 1)
  have hang' : T'.P.angle 0 = angleAt T'.C.model 2 ∨ T'.P.angle 0 = Real.pi - angleAt T'.C.model 2 := by
    left
    show (polyRot T.P (a + 1)).angle 0 = angleAt T.C.model 2
    rw [polyRot_angle, zero_add, hang1]
  have hs0 : T'.P.side 0 = T.P.side (a + 1) := by
    show (polyRot T.P (a + 1)).side 0 = _
    rw [polyRot_side, zero_add]
  have hs3 : T'.P.side 3 = T.P.side a := by
    show (polyRot T.P (a + 1)).side 3 = _
    rw [polyRot_side, add_comm 3, ee2]
  have hratio : (∃ q : ℚ, T.P.side (a + 1) / T.P.side a = q * (Real.sin (angleAt T.C.model 0) / Real.sin (angleAt T.C.model 1))) ∨
      (∃ q : ℚ, T.P.side a / T.P.side (a + 1) = q * (Real.sin (angleAt T.C.model 0) / Real.sin (angleAt T.C.model 1))) := by
    rcases hside with ⟨m, hm, hm'⟩ | ⟨m, hm, hm'⟩
    · have := lemma41_poly T' hpg' hang' m hm (Or.inr (by rw [hs3]; exact hm'))
      rw [hs0, hs3] at this
      exact this
    · have := lemma41_poly T' hpg' hang' m hm (Or.inl (by rw [hs0]; exact hm'))
      rw [hs0, hs3] at this
      exact this
  have h02 : T.P.side 2 = T.P.side 0 := by simpa using side_alt T.P hpg 0
  have h13 : T.P.side 3 = T.P.side 1 := by simpa using side_alt T.P hpg 1
  have hkey : (T.P.side 0 = T.P.side a ∧ T.P.side 1 = T.P.side (a + 1)) ∨ (T.P.side 0 = T.P.side (a + 1) ∧ T.P.side 1 = T.P.side a) := by
    fin_cases a <;> simp [h02, h13]
  refine ⟨⟨rfl, hpg⟩, ⟨a + 1, hang1⟩, ?_⟩
  rcases hkey with ⟨k0, k1⟩ | ⟨k0, k1⟩
  · rcases hratio with ⟨q, hq⟩ | ⟨q, hq⟩
    · right; exact ⟨q, by rw [k0, k1]; exact hq⟩
    · left; exact ⟨q, by rw [k0, k1]; exact hq⟩
  · rcases hratio with ⟨q, hq⟩ | ⟨q, hq⟩
    · left; exact ⟨q, by rw [k0, k1]; exact hq⟩
    · right; exact ⟨q, by rw [k0, k1]; exact hq⟩

/-- Normality of the vertices in the relative interior of side `i` (for the `Γ_a` side lemmas). -/
def NormSide (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (P : ConvPoly M) (i : Fin M) : Prop :=
  ∀ V : Plane, (∃ j k, (D.tile j).pts k = V) → (∃ t : ℝ, 0 < t ∧ t < 1 ∧ V = (1 - t) • P.v i + t • P.v (i + 1)) →
    cnt D idx V 0 = 1 ∧ cnt D idx V 1 = 1 ∧ cnt D idx V 2 = 1

/-- No `Γ_a` edge starts at a tiling vertex in the relative interior of side `i`. -/
def NoEdgeSide (D : CongruentRegionDissection N) (P : ConvPoly M) (i : Fin M) : Prop :=
  ∀ V : Plane, (∃ j k, (D.tile j).pts k = V) → (∃ t : ℝ, 0 < t ∧ t < 1 ∧ V = (1 - t) • P.v i + t • P.v (i + 1)) →
    ∀ H', ¬ GaEdge D.toRegionDissection (slen D 0) V H'

theorem side_hyps (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseA D idx) (h1 : Real.pi / 2 < D.model.angleAt 2) (h3 : D.model.angleAt 2 ≠ 2 * Real.pi / 3)
    (i : Fin M) (hb : ¬ (SideBad D idx P i ∨ ZSide D P i)) : NormSide D idx P i ∧ NoEdgeSide D P i := by
  refine ⟨?_, ?_⟩
  · intro V hv ⟨t, ht0, ht1, hVt⟩
    have hne : V ∉ excVerts D idx P := fun hex => hb (Or.inl ⟨V, hex, t, ht0, ht1, hVt⟩)
    exact caseI_normal_side D P hreg idx h.hidxA h.hregc h1 h3 ht0 ht1 hVt hv hne
  · intro V hv ⟨t, ht0, ht1, hVt⟩ H' hH'
    apply hb
    right
    refine ⟨V, ?_, t, ht0, ht1, hVt⟩
    simp only [gaZ, Finset.mem_filter]
    refine ⟨mem_vtxSet.mpr hv, ?_, H', hH'⟩
    rw [hreg, hVt]
    exact not_interior_of_c_zero P (c_on_edge P i t)

/-- **Theorem 2.1, Case I, Subcase Ia** (Laczkovich DCG 48 (2012), Sect. 5.1): `a` is not a nonnegative rational combination of `b, c`. -/
theorem caseI_a {N M : ℕ} [NeZero M] (T : PolyTiling N M) (hreg : RegularPQ T.C) (h1 : Real.pi / 2 < angleAt T.C.model 2) (h3 : angleAt T.C.model 2 ≠ 2 * Real.pi / 3)
    (hnc : NotComb (slen T.C 0) (slen T.C 1) (slen T.C 2)) : Concl1 T.C T.P := by
  classical
  obtain ⟨idx, hA, hcnt⟩ := hreg
  haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  have hregc : ∀ X, cnt T.C idx X 0 = cnt T.C idx X 1 := fun X => hcnt X
  have hidx := idx_dist_of_angle T.C idx hA
  have hCA : CaseA T.C idx := ⟨hidx, hA, hnc, hregc⟩
  have hBlkcard : (Finset.univ.filter (fun i => SideBad T.C idx T.P i ∨ ZSide T.C T.P i)).card ≤ (excVerts T.C idx T.P).card := by
    convert blk_card T.C T.P T.region_eq idx hCA h1 h3
  have hpoly := caseI_polyvertex T.C T.P T.region_eq idx hA hregc h1
  have hgg' : ∀ i : Fin M, cnt T.C idx (T.P.v (i - 1 + 1)) 2 = 1 → cnt T.C idx (T.P.v (i + 1)) 2 = 1 →
      ¬ (SideBad T.C idx T.P i ∨ ZSide T.C T.P i) → False := by
    intro i c1 c2 hb
    obtain ⟨hn, hno⟩ := side_hyps T.C T.P T.region_eq idx hCA h1 h3 i hb
    obtain ⟨L, e0, el, hW, hh, hl, hs1, hs2, hT0, hT1⟩ := edge_data T.C T.P T.region_eq i
    rw [sub_add_cancel] at c1
    have z1 : cnt T.C idx (T.P.v i) 0 = 0 := by
      rcases hpoly (i - 1) with ⟨a, -, -⟩ | ⟨a, -, -⟩
      · rw [sub_add_cancel] at a; exact a
      · rw [sub_add_cancel] at a; omega
    have z2 : cnt T.C idx (T.P.v (i + 1)) 0 = 0 := by
      rcases hpoly i with ⟨a, -, -⟩ | ⟨a, -, -⟩
      · exact a
      · omega
    have t0 : TyAt T.C idx e0.1 e0.2.1 2 := fun kk hkk => idx_two_of_cnt T.C idx z1 (by rw [← hregc]; exact z1) (hkk.trans hs1)
    have t1 : TyAt T.C idx el.1 el.2.2 2 := fun kk hkk => idx_two_of_cnt T.C idx z2 (by rw [← hregc]; exact z2) (hkk.trans hs2)
    exact side_no_gg_a T.C T.P T.region_eq idx hCA i hn hno hW hh hl t0 t1
  obtain ⟨hM4, ⟨a, ang1, ang2, ang3, c0, c2⟩, hexc0⟩ := caseI_core_gen T.C T.P T.region_eq idx hA hregc h1 h3 (fun i => SideBad T.C idx T.P i ∨ ZSide T.C T.P i)
    (by convert hBlkcard) hgg'
  have hall : ∀ i : Fin M, ¬ (SideBad T.C idx T.P i ∨ ZSide T.C T.P i) := by
    intro i hb
    have hz : (Finset.univ.filter (fun i => SideBad T.C idx T.P i ∨ ZSide T.C T.P i)).card = 0 := by omega
    rw [Finset.card_eq_zero] at hz
    have hmem : i ∈ Finset.univ.filter (fun i => SideBad T.C idx T.P i ∨ ZSide T.C T.P i) := by simp [hb]
    rw [hz] at hmem
    simp at hmem
  subst hM4
  have hI := side_hyps T.C T.P T.region_eq idx hCA h1 h3 a (hall a)
  have hO := side_hyps T.C T.P T.region_eq idx hCA h1 h3 (a + 1) (hall (a + 1))
  have hside := gamma_vertex_multiple T.C T.P T.region_eq idx hCA a c0 (by rw [← hregc]; exact c0) c2 hI.1 hI.2 hO.1 hO.2
  exact concl1_of_gamma_para T a ang1 ang2 ang3 hside

end Erdos634.Draft.LaczFormal.RG

-- Draft/LaczFormalRG4CaseIV.lean -- Laczkovich DCG 48 (2012), Theorem 2.1, Case IV (gamma = pi/3), SUBCASE IVa, for an ARBITRARY convex polygon `A`:
-- if `a` is not a nonnegative rational combination of `b, c` then `A` is a parallelogram with an angle gamma and conclusion (i) holds.
-- The number of sides is derived from the angle sum of a convex polygon (`poly_angle_sum`), not assumed.
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 8.1, Lemmas 4.1 and 8.1), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG4IVa
import Erdos634.Draft.LaczFormalRG4Geo

open scoped Classical Fin.NatCast Fin.CommRing
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

theorem par_all (P : ConvPoly 4) (a : Fin 4) (h : P.v a + P.v (a + 2) = P.v (a + 1) + P.v (a + 3)) :
    ∀ i, P.v i + P.v (i + 2) = P.v (i + 1) + P.v (i + 3) := by
  intro i
  have k0 := congrArg (fun v : Plane => v 0) h
  have k1 := congrArg (fun v : Plane => v 1) h
  simp only [PiLp.add_apply] at k0 k1
  ext j
  fin_cases a <;> fin_cases i <;> fin_cases j <;> simp at k0 k1 ⊢ <;> linarith

theorem two_ne_zero_fin {M : ℕ} [NeZero M] (hM : 3 ≤ M) (e : Fin M) : e + 2 ≠ e := by
  intro h
  have h2 : (2 : Fin M) = 0 := by
    have := congrArg (fun x => x - e) h
    simpa using this
  have h3 := congrArg Fin.val h2
  have h4 : ((2 : Fin M) : ℕ) = 2 := by
    simp; exact Nat.mod_eq_of_lt (by omega)
  rw [h4] at h3
  simp at h3

/-- In a parallelogram opposite sides are equal. -/
theorem side_alt (P : ConvPoly 4) (hpg : ∀ i, P.v i + P.v (i + 2) = P.v (i + 1) + P.v (i + 3)) (i : Fin 4) : P.side (i + 2) = P.side i := by
  have h := hpg i
  have hrect : (polyRot P i).v 0 + (polyRot P i).v 2 = (polyRot P i).v 1 + (polyRot P i).v 3 := by
    simp only [polyRot]
    rw [zero_add, add_comm 2 i, add_comm 1 i, add_comm 3 i]
    exact h
  have := (side_rect (polyRot P i) hrect).1
  rw [polyRot_side, polyRot_side, zero_add, add_comm 2 i] at this
  exact this

/-- **Subcase IVa** (`γ = π/3`, `a` not a nonnegative rational combination of `b, c`): conclusion (i) of Theorem 2.1. -/
theorem caseIV_Va {N M : ℕ} [NeZero M] (T : PolyTiling N M) (hreg : RegularPQ T.C) (hγ : angleAt T.C.model 2 = Real.pi / 3)
    (hnc : NotComb (slen T.C 0) (slen T.C 1) (slen T.C 2)) : Concl1 T.C T.P := by
  classical
  obtain ⟨idx, hA, hcnt⟩ := hreg
  have hidx := idx_dist_of_angle T.C idx hA
  haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  have hC : CaseIV T.C idx := ⟨hidx, hA, hnc, hγ, fun X => hcnt X⟩
  obtain ⟨hall, e, h1, h2, h3, hside⟩ := caseIV_shape T.C T.P T.region_eq idx hC
  have hM3 : 3 ≤ M := T.P.three_le
  have hsum := poly_angle_sum T.P
  have hpi := Real.pi_pos
  have e12 : e + 1 + 1 = e + 2 := fin_e12 M e
  have hne2 : e + 2 ≠ e := two_ne_zero_fin hM3 e
  -- the angle sum
  have hsum' : ∑ k : Fin M, T.P.angle (k + 1) = ((M - 2 : ℕ) : ℝ) * Real.pi := by
    rw [← hsum]
    exact Equiv.sum_comp (Equiv.addRight (1 : Fin M)) (fun i => T.P.angle i)
  have hlow : (M : ℝ) * (Real.pi / 3) + Real.pi / 3 ≤ ∑ k : Fin M, T.P.angle (k + 1) := by
    have : ∀ k : Fin M, Real.pi / 3 + (if k = e + 1 then Real.pi / 3 else 0) ≤ T.P.angle (k + 1) := by
      intro k
      by_cases hk : k = e + 1
      · subst hk; rw [if_pos rfl, e12, h2]; linarith
      · rw [if_neg hk]
        rcases hall k with h | h <;> linarith
    calc (M : ℝ) * (Real.pi / 3) + Real.pi / 3 = ∑ k : Fin M, (Real.pi / 3 + (if k = e + 1 then Real.pi / 3 else 0)) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, Finset.sum_ite_eq']
          simp
      _ ≤ _ := Finset.sum_le_sum (fun k _ => this k)
  have hup : ∑ k : Fin M, T.P.angle (k + 1) ≤ (M : ℝ) * (2 * Real.pi / 3) - 2 * (Real.pi / 3) := by
    have : ∀ k : Fin M, T.P.angle (k + 1) ≤ 2 * Real.pi / 3 - (if k = e then Real.pi / 3 else 0) - (if k = e + 2 then Real.pi / 3 else 0) := by
      intro k
      by_cases hk1 : k = e
      · subst hk1
        rw [if_pos rfl, if_neg (Ne.symm hne2), h1]; linarith
      · by_cases hk2 : k = e + 2
        · subst hk2
          rw [if_neg hk1, if_pos rfl]
          have : e + 2 + 1 = e + 3 := fin_e23 M e
          rw [this, h3]; linarith
        · rw [if_neg hk1, if_neg hk2]
          rcases hall k with h | h <;> linarith
    calc ∑ k : Fin M, T.P.angle (k + 1) ≤ ∑ k : Fin M, (2 * Real.pi / 3 - (if k = e then Real.pi / 3 else 0) - (if k = e + 2 then Real.pi / 3 else 0)) :=
          Finset.sum_le_sum (fun k _ => this k)
      _ = (M : ℝ) * (2 * Real.pi / 3) - 2 * (Real.pi / 3) := by
          rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, Finset.sum_ite_eq', Finset.sum_ite_eq']
          simp; ring
  have hMr : ((M - 2 : ℕ) : ℝ) = (M : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  rw [hsum', hMr] at hlow hup
  have hM4 : M = 4 := by
    have a1 : (3 : ℝ) < M := by nlinarith
    have a2 : (M : ℝ) < 5 := by nlinarith
    have b1 : 3 < M := by exact_mod_cast a1
    have b2 : M < 5 := by exact_mod_cast a2
    omega
  subst hM4
  -- the fourth angle
  have hsum4 : ∑ i : Fin 4, T.P.angle i = 2 * Real.pi := by rw [hsum]; norm_num
  have hs4 : ∑ i : Fin 4, T.P.angle (i + e) = ∑ i : Fin 4, T.P.angle i := Equiv.sum_comp (Equiv.addRight e) (fun i => T.P.angle i)
  rw [Fin.sum_univ_four] at hs4
  have c1 : (1 : Fin 4) + e = e + 1 := add_comm _ _
  have c2 : (2 : Fin 4) + e = e + 2 := add_comm _ _
  have c3 : (3 : Fin 4) + e = e + 3 := add_comm _ _
  rw [zero_add, c1, c2, c3, hsum4, h1, h2, h3] at hs4
  have hang0 : T.P.angle e = 2 * Real.pi / 3 := by linarith
  -- the parallelogram
  have ee1 : e + 1 + 2 = e + 3 := by have : ∀ e : Fin 4, e + 1 + 2 = e + 3 := by decide
                                     exact this e
  have ee2 : e + 1 + 3 = e := by have : ∀ e : Fin 4, e + 1 + 3 = e := by decide
                                 exact this e
  have hpar : T.P.v (e + 1) + T.P.v (e + 1 + 2) = T.P.v (e + 1 + 1) + T.P.v (e + 1 + 3) :=
    quad_parallelogram T.P (e + 1) (by rw [e12, h2]) (by rw [ee1, h3]) (by rw [ee2, hang0])
  have hpg := par_all T.P (e + 1) hpar
  -- Lemma 4.1 on the rotated polygon
  let T' : PolyTiling N 4 := ⟨T.C, polyRot T.P (e + 1), by rw [polyRot_carrier]; exact T.region_eq⟩
  have hpg' : T'.P.v 0 + T'.P.v 2 = T'.P.v 1 + T'.P.v 3 := by
    show T.P.v (0 + (e + 1)) + T.P.v (2 + (e + 1)) = T.P.v (1 + (e + 1)) + T.P.v (3 + (e + 1))
    rw [zero_add, add_comm 2, add_comm 1, add_comm 3]
    exact hpar
  have hang' : T'.P.angle 0 = angleAt T'.C.model 2 ∨ T'.P.angle 0 = Real.pi - angleAt T'.C.model 2 := by
    left
    show (polyRot T.P (e + 1)).angle 0 = angleAt T.C.model 2
    rw [polyRot_angle, zero_add, h1, hγ]
  have hs0 : T'.P.side 0 = T.P.side (e + 1) := by
    show (polyRot T.P (e + 1)).side 0 = _
    rw [polyRot_side, zero_add]
  have hs3 : T'.P.side 3 = T.P.side e := by
    show (polyRot T.P (e + 1)).side 3 = _
    rw [polyRot_side, add_comm 3, ee2]
  have hratio : (∃ q : ℚ, T.P.side (e + 1) / T.P.side e = q * (Real.sin (angleAt T.C.model 0) / Real.sin (angleAt T.C.model 1))) ∨
      (∃ q : ℚ, T.P.side e / T.P.side (e + 1) = q * (Real.sin (angleAt T.C.model 0) / Real.sin (angleAt T.C.model 1))) := by
    rcases hside with ⟨m, hm, hm'⟩ | ⟨m, hm, hm'⟩
    · have := lemma41_poly T' hpg' hang' m hm (Or.inl (by rw [hs0]; exact hm'))
      rw [hs0, hs3] at this
      exact this
    · have := lemma41_poly T' hpg' hang' m hm (Or.inr (by rw [hs3]; exact hm'))
      rw [hs0, hs3] at this
      exact this
  have h02 : T.P.side 2 = T.P.side 0 := by simpa using side_alt T.P hpg 0
  have h13 : T.P.side 3 = T.P.side 1 := by simpa using side_alt T.P hpg 1
  have hkey : (T.P.side 0 = T.P.side e ∧ T.P.side 1 = T.P.side (e + 1)) ∨ (T.P.side 0 = T.P.side (e + 1) ∧ T.P.side 1 = T.P.side e) := by
    fin_cases e <;> simp [h02, h13]
  refine ⟨⟨rfl, hpg⟩, ⟨e + 1, by rw [h1, hγ]⟩, ?_⟩
  rcases hkey with ⟨k0, k1⟩ | ⟨k0, k1⟩
  · rcases hratio with ⟨q, hq⟩ | ⟨q, hq⟩
    · right; exact ⟨q, by rw [k0, k1]; exact hq⟩
    · left; exact ⟨q, by rw [k0, k1]; exact hq⟩
  · rcases hratio with ⟨q, hq⟩ | ⟨q, hq⟩
    · left; exact ⟨q, by rw [k0, k1]; exact hq⟩
    · right; exact ⟨q, by rw [k0, k1]; exact hq⟩

/-- **Subcase IVb** (`b` not a nonnegative rational combination of `a, c`): relabel `α ↔ β` ("this subcase can be treated similarly to Subcase IVa"). -/
theorem caseIV_Vb {N M : ℕ} [NeZero M] (T : PolyTiling N M) (hreg : RegularPQ T.C) (hγ : angleAt T.C.model 2 = Real.pi / 3)
    (hnc : NotComb (slen T.C 1) (slen T.C 0) (slen T.C 2)) : Concl1 T.C T.P := by
  set σ : Equiv.Perm (Fin 3) := Equiv.swap 0 1 with hσ
  have s0 : σ 0 = 1 := by simp [hσ]
  have s1 : σ 1 = 0 := by simp [hσ]
  have s2 : σ 2 = 2 := by rw [hσ]; exact Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
  let T' : PolyTiling N M := ⟨relabel T.C σ, T.P, T.region_eq⟩
  obtain ⟨idx, hA, hcnt⟩ := hreg
  have hreg' : RegularPQ T'.C := by
    refine ⟨relabelIdx idx σ, relabel_hidxA T.C idx σ hA, fun X => ?_⟩
    have e0 := relabel_cnt T.C idx σ X 0
    have e1 := relabel_cnt T.C idx σ X 1
    rw [s0] at e0; rw [s1] at e1
    show cnt (relabel T.C σ) (relabelIdx idx σ) X 0 = cnt (relabel T.C σ) (relabelIdx idx σ) X 1
    rw [e0, e1]
    exact (hcnt X).symm
  have hγ' : angleAt T'.C.model 2 = Real.pi / 3 := by
    show angleAt (relabel T.C σ).model 2 = _
    rw [relabel_angleAt, s2]; exact hγ
  have hnc' : NotComb (slen T'.C 0) (slen T'.C 1) (slen T'.C 2) := by
    show NotComb (slen (relabel T.C σ) 0) (slen (relabel T.C σ) 1) (slen (relabel T.C σ) 2)
    rw [relabel_slen, relabel_slen, relabel_slen, s0, s1, s2]; exact hnc
  have h := caseIV_Va T' hreg' hγ' hnc'
  obtain ⟨⟨h4, hpar⟩, ⟨i, hi⟩, hratio⟩ := h
  have e2 : angleAt (relabel T.C σ).model 2 = angleAt T.C.model 2 := by rw [relabel_angleAt, s2]
  have e0 : angleAt (relabel T.C σ).model 0 = angleAt T.C.model 1 := by rw [relabel_angleAt, s0]
  have e1 : angleAt (relabel T.C σ).model 1 = angleAt T.C.model 0 := by rw [relabel_angleAt, s1]
  refine ⟨⟨h4, hpar⟩, ⟨i, ?_⟩, ?_⟩
  · rw [← e2]; exact hi
  · have hsA := Erdos634.Draft.LaczFormal.Thm21.sin_angleAt_pos T.C.model 0
    have hsB := Erdos634.Draft.LaczFormal.Thm21.sin_angleAt_pos T.C.model 1
    have p0 := side_pos T.P 0
    have p1 := side_pos T.P 1
    rcases hratio with ⟨q, hq⟩ | ⟨q, hq⟩
    · have hq' : T.P.side 0 / T.P.side 1 = q * (Real.sin (angleAt T.C.model 1) / Real.sin (angleAt T.C.model 0)) := by
        have := hq; simp only [T'] at this; rw [e0, e1] at this; exact this
      obtain ⟨q', hq''⟩ := ratio_flip p0 p1 hsB hsA hq'
      right; exact ⟨q', hq''⟩
    · have hq' : T.P.side 1 / T.P.side 0 = q * (Real.sin (angleAt T.C.model 1) / Real.sin (angleAt T.C.model 0)) := by
        have := hq; simp only [T'] at this; rw [e0, e1] at this; exact this
      obtain ⟨q', hq''⟩ := ratio_flip p1 p0 hsB hsA hq'
      left; exact ⟨q', hq''⟩


end Erdos634.Draft.LaczFormal.RG

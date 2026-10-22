-- Draft/LaczFormalIVcRatBr8a.lean -- Laczkovich DCG 48 (2012), Sect. 8.3 (Subcase IVc, rational branch): BRIDGE glue, B10 = `ivc_rat_final`.
--   Thm21Excluded3's second disjunct (gamma = pi/3, a ~ b, c not ~ a, M >= 5, alpha/pi rational) ==> Thm21Concl (Concl9, the rational hexagon).
--   Route: alpha in {pi/6, pi/2} (`ivc_rat_alpha`), tile shape (`ivc_rat_tile`: a = 2b or b = 2a, c = sqrt 3 s); B1 dichotomy `hint_or_allc` (Br5c);
--   branch "all boundary tile edges have length c": `ivc_rat_all_c_hexagon` (B2) = Concl9;
--   branch "hint": `BrHyp` + `vwOf` (Br4b), no polygon angle is pi/3 (else `vw_star` (B9b) with the area corner `polygon_corner_vol_pi3` (Br6a) gives a parallelogram,
--   contradicting M >= 5 by `polygon_not_parallelogram` (Br7a)), so every angle is 2pi/3 (`polygon_angle_cnt`), M = 6 by the angle sum, RationalPoly by Lemma 4.7: Concl9.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 8.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIVcRatBr5c
import Erdos634.Draft.LaczFormalIVcRatBr6a
import Erdos634.Draft.LaczFormalIVcRatBr7a
import Erdos634.Draft.LaczFormalIVcRatBr4b
import Erdos634.Draft.LaczFormalIVcRatB2
import Erdos634.Draft.LaczFormalThm21Partial3

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord MeasureTheory

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

theorem fin3_012 : ∀ l : Fin 3, l = 0 ∨ l = 1 ∨ l = 2 := by decide

theorem ivc_rat_final (T : PolyTiling N M) (hreg : RegularPQ T.C) (hγ : angleAt T.C.model 2 = Real.pi / 3)
    (hab : Comm (slen T.C 0) (slen T.C 1)) (hac : ¬ Comm (slen T.C 0) (slen T.C 2)) (hM5 : 5 ≤ M)
    (hα : ∃ s : ℚ, angleAt T.C.model 0 = (s : ℝ) * Real.pi) : Thm21Concl T.C T.P := by
  classical
  have hpi := Real.pi_pos
  have hα6 := ivc_rat_alpha T hγ hab hac hα
  have hsum : angleAt T.C.model 0 + angleAt T.C.model 1 + angleAt T.C.model 2 = Real.pi := Erdos634.Draft.LaczFormal.angleAt_sum T.C.model
  have hm1 : angleAt T.C.model 1 = 2 * Real.pi / 3 - angleAt T.C.model 0 := by linarith
  have hαβ : (angleAt T.C.model 0 = Real.pi / 6 ∧ angleAt T.C.model 1 = Real.pi / 2) ∨
      (angleAt T.C.model 0 = Real.pi / 2 ∧ angleAt T.C.model 1 = Real.pi / 6) := by
    rcases hα6 with h | h
    · left; exact ⟨h, by rw [hm1, h]; ring⟩
    · right; exact ⟨h, by rw [hm1, h]; ring⟩
  have hRat := polytiling_rational T hreg hab hac
  have hreg' := hreg
  obtain ⟨idx, hA, hcnt⟩ := hreg
  haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  have hC : CaseC T.C idx := ⟨idx_dist_of_angle T.C idx hA, hA, fun X => hcnt X, notComb_c_of_comm (slen_pos T.C 2) hab hac⟩
  have hcnt' : ∀ X, cnt T.C idx X 0 = cnt T.C idx X 1 := fun X => hcnt X
  rcases hint_or_allc T.C idx hC T.P T.region_eq with hint | ⟨L, hW, hLne, hc⟩
  · -- tile shape
    obtain ⟨ρ, π', s, hρπ, hρ, hπ, hs, hlρ, hlπ, hl2⟩ : ∃ ρ π' : Fin 3, ∃ s : ℝ, ρ ≠ π' ∧ ρ ≠ 2 ∧ π' ≠ 2 ∧ 0 < s ∧ slen T.C ρ = 2 * s ∧
        slen T.C π' = s ∧ slen T.C 2 ^ 2 = 3 * s ^ 2 := by
      obtain ⟨h1, h2⟩ := slen_sin_rel' T.C
      have h1 : Real.sin (angleAt T.C.model 1) * slen T.C 0 = Real.sin (angleAt T.C.model 0) * slen T.C 1 := h1
      have h2 : Real.sin (angleAt T.C.model 0) * slen T.C 2 = Real.sin (angleAt T.C.model 2) * slen T.C 0 := h2
      have hb : slen T.C 0 * Real.sin (2 * Real.pi / 3 - angleAt T.C.model 0) = slen T.C 1 * Real.sin (angleAt T.C.model 0) := by
        rw [← hm1]; linarith
      have hc2 : slen T.C 0 * Real.sin (Real.pi / 3) = slen T.C 2 * Real.sin (angleAt T.C.model 0) := by
        rw [hγ] at h2; linarith
      have hirr : ¬ ∃ r : ℚ, slen T.C 2 = (r : ℝ) * slen T.C 0 :=
        fun ⟨r, hr⟩ => hac (comm_of_rat (slen_pos T.C 0) (slen_pos T.C 2) r hr)
      have hα3 : angleAt T.C.model 0 = Real.pi / 6 ∨ angleAt T.C.model 0 = Real.pi / 3 ∨ angleAt T.C.model 0 = Real.pi / 2 := by
        rcases hα6 with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      rcases ivc_rat_tile (angleAt T.C.model 0) (slen T.C 0) (slen T.C 1) (slen T.C 2) (slen_pos T.C 0) hα3 hb hc2 hirr with ⟨h, ha, hc'⟩ | ⟨h, hb', hc'⟩
      · exact ⟨0, 1, slen T.C 1, by decide, by decide, by decide, slen_pos T.C 1, by rw [ha], rfl,
          by rw [hc', mul_pow, Real.sq_sqrt (by norm_num)]⟩
      · exact ⟨1, 0, slen T.C 0, by decide, by decide, by decide, slen_pos T.C 0, by rw [hb'], rfl,
          by rw [hc', mul_pow, Real.sq_sqrt (by norm_num)]⟩
    have hBr : BrHyp T.C T.P idx s ρ π' := ⟨hC, T.region_eq, hab, hac, hs, hρπ, hρ, hπ, hlρ, hlπ, hl2, hint⟩
    have hsum2 : T.C.model.angleAt 0 + T.C.model.angleAt 1 = 2 * Real.pi / 3 := by
      show angleAt T.C.model 0 + angleAt T.C.model 1 = _
      rcases hαβ with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> rw [h0, h1] <;> ring
    have hγ' : T.C.model.angleAt 2 = Real.pi / 3 := hγ
    -- no corner of angle pi/3
    have hno3 : ∀ m : Fin M, T.P.angle m ≠ Real.pi / 3 := by
      intro m hm
      obtain ⟨ρ0, hρ0, hX⟩ := polygon_corner_vol_pi3 T.P m hm
      have hX' : ∀ r, 0 < r → r ≤ ρ0 → volume (T.C.region ∩ Metric.ball (T.P.v m) r) = ENNReal.ofReal (Real.pi / 3 / 2 * r ^ 2) := by
        intro r hr hle; rw [T.region_eq]; exact hX r hr hle
      have hconv : Convex ℝ T.C.region := by rw [T.region_eq]; exact convPoly_convex T.P
      obtain ⟨F, -, k, m', hk, hm', hAeq⟩ := VWTiling.vw_star (vwOf hBr) hs hconv hρ0 hX'
      exact polygon_not_parallelogram T.P hM5 hs F hk hm' (by rw [← T.region_eq]; exact hAeq)
    have hall : ∀ i : Fin M, T.P.angle i = 2 * Real.pi / 3 := by
      intro i
      have hk : i - 1 + 1 = i := sub_add_cancel i 1
      obtain ⟨hang, hlt⟩ := polygon_angle_cnt T.C T.P T.region_eq idx hA hγ' hsum2 hcnt' (i - 1)
      rw [hk] at hang hlt
      obtain ⟨j, kk, hjk⟩ := poly_vertex_is_tile_vertex T.C.toRegionDissection T.P T.region_eq i
      have hlow : 1 ≤ 2 * cnt T.C idx (T.P.v i) 1 + cnt T.C idx (T.P.v i) 2 := by
        have hc01 := hcnt' (T.P.v i)
        rcases fin3_012 (idx j kk) with h | h | h
        · have := cnt_one T.C idx 0 hjk h; omega
        · have := cnt_one T.C idx 1 hjk h; omega
        · have := cnt_one T.C idx 2 hjk h; omega
      have hne := hno3 i
      rw [hang] at hne ⊢
      have h2 : 2 * cnt T.C idx (T.P.v i) 1 + cnt T.C idx (T.P.v i) 2 = 2 := by
        by_contra h2
        have h1 : 2 * cnt T.C idx (T.P.v i) 1 + cnt T.C idx (T.P.v i) 2 = 1 := by omega
        rw [h1] at hne
        apply hne; push_cast; ring
      rw [h2]; push_cast; ring
    have hsumP := poly_angle_sum T.P
    have hM3 : 3 ≤ M := T.P.three_le
    have hM6 : M = 6 := by
      have e1 : ∑ i, T.P.angle i = ∑ _i : Fin M, 2 * Real.pi / 3 := Finset.sum_congr rfl (fun i _ => hall i)
      rw [hsumP] at e1
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at e1
      rw [Nat.cast_sub (by omega)] at e1
      push_cast at e1
      have : (M : ℝ) = 6 := by nlinarith
      exact_mod_cast this
    subst hM6
    right; right; right; right; right; right; right; right
    exact ⟨rfl, hRat, hall, hγ, hαβ⟩
  · right; right; right; right; right; right; right; right
    exact ivc_rat_all_c_hexagon T hreg' hγ hαβ hab hac L hW hLne hc

#print axioms Erdos634.Draft.LaczFormal.RG.ivc_rat_final

end Erdos634.Draft.LaczFormal.RG

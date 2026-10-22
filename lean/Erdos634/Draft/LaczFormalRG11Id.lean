-- Draft/LaczFormalRG11Id.lean -- **Theorem 2.1, Case II (gamma < pi/2, gamma != pi/3), Subcase IIb** (Laczkovich DCG 48 (2012), Sect. 6.2): `a, b, c` pairwise commensurable => conclusion (iii).
-- `cos gamma` rational (law of cosines, `cos_gamma_rat`); `(P - R) gamma = (P - M + 2) pi` (`caseII_exc_count`); if `P > M - 2` then `gamma` is a rational multiple of `pi` and Niven excludes it. So `P = M - 2`:
-- `M - 2` corners equal `alpha + beta`, the other two are integer multiples of `gamma`.  NOTE, UNAUDITED.
-- Credit: Laczkovich (DCG 48 (2012), Sect. 6.2; Discrete Math 140 (1995)), Beeson, Beeson-Zhang; Niven's theorem as formalized in Mathlib.
import Erdos634.Draft.LaczFormalRG11Final
import Erdos634.Draft.LaczFormalRG9Id

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

/-- **`P = M - 2`** in Case II when `cos γ` is rational (Niven). -/
theorem caseII_P_eq (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) (hregc : ∀ X, cnt D idx X 0 = cnt D idx X 1)
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (hcos : ∃ q : ℚ, Real.cos (D.model.angleAt 2) = q) :
    (cntP0 D idx P : ℤ) = M - 2 := by
  have hpi := Real.pi_pos
  have hγ0 := model_angle_pos' D 2
  obtain ⟨hRP, hPM2, -, hang⟩ := caseII_exc_count D P hreg idx hidxA hregc h1 h3
  by_contra hne
  have hk1 : (1 : ℤ) ≤ (cntP0 D idx P : ℤ) - M + 2 := by omega
  set k : ℕ := cntP0 D idx P + 2 - M with hkdef
  have hkR : ((cntP0 D idx P : ℝ) - M + 2) = (k : ℝ) := by
    rw [hkdef]; have : M ≤ cntP0 D idx P + 2 := by omega
    rw [Nat.cast_sub this]; push_cast; ring
  have hk1' : (1 : ℝ) ≤ (k : ℝ) := by
    have : 1 ≤ k := by omega
    exact_mod_cast this
  rw [hkR] at hang
  have hl : (0 : ℝ) < (cntP0 D idx P : ℝ) - cntR2 D idx P := by
    by_contra hle
    push Not at hle
    nlinarith
  have hl' : cntR2 D idx P < cntP0 D idx P := by
    have : (cntR2 D idx P : ℝ) < cntP0 D idx P := by linarith
    exact_mod_cast this
  set l : ℕ := cntP0 D idx P - cntR2 D idx P with hldef
  have hlR : (l : ℝ) = (cntP0 D idx P : ℝ) - cntR2 D idx P := by
    rw [hldef, Nat.cast_sub hl'.le]
  have hl0 : (l : ℝ) ≠ 0 := by rw [hlR]; exact hl.ne'
  have hγrat : ∃ r : ℚ, D.model.angleAt 2 = r * Real.pi := by
    refine ⟨(k : ℚ) / l, ?_⟩
    push_cast
    rw [hlR] at hl0 ⊢
    field_simp
    linarith
  have hmem := niven_angle_eq hγrat hcos ⟨hγ0.le, by linarith⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h | h | h | h
  · linarith
  · exact h3 h
  · linarith
  · linarith
  · linarith

/-- **Theorem 2.1, Case II, `a, b, c` pairwise commensurable**: conclusion (iii). -/
theorem caseII_b {N M : ℕ} [NeZero M] (T : PolyTiling N M) (hreg : RegularPQ T.C) (h1 : angleAt T.C.model 2 < Real.pi / 2) (h3 : angleAt T.C.model 2 ≠ Real.pi / 3)
    (hab : Comm (slen T.C 0) (slen T.C 1)) (hac : Comm (slen T.C 0) (slen T.C 2)) : Concl3 T.C T.P := by
  classical
  obtain ⟨idx, hA, hcnt⟩ := hreg
  haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  have hregc : ∀ X, cnt T.C idx X 0 = cnt T.C idx X 1 := fun X => hcnt X
  have hcos := cos_gamma_rat T.C hab hac
  have hP := caseII_P_eq T.C T.P T.region_eq idx hA hregc h1 h3 hcos
  have hpoly := caseII_polyvertex T.C T.P T.region_eq idx hA hregc h1
  have hidx := idx_dist_of_angle T.C idx hA
  refine ⟨fun i j => comm_trans' (side_comm T.C T.P T.region_eq idx hidx hab hac i) (comm_symm' (side_comm T.C T.P T.region_eq idx hidx hab hac j)), ?_,
    sinComm_of_comm T.C hab hac⟩
  set S : Finset (Fin M) := Finset.univ.filter (fun k => cnt T.C idx (T.P.v (k + 1)) 0 = 1) with hS
  have hPS : cntP0 T.C idx T.P = S.card := cntP0_eq_card T.C T.P T.region_eq idx hA hregc h1
  have hM3 := T.P.three_le
  have hScard : Sᶜ.card = 2 := by
    rw [Finset.card_compl]
    simp only [Fintype.card_fin]
    omega
  obtain ⟨i0, j0, hij0, hSc⟩ := Finset.card_eq_two.mp hScard
  have hγS : ∀ k : Fin M, k ∈ S → T.P.angle (k + 1) = angleAt T.C.model 0 + angleAt T.C.model 1 := by
    intro k hk
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hk
    rcases hpoly k with ⟨-, -, ang⟩ | ⟨h0, -, -⟩
    · have hs : angleAt T.C.model 0 + angleAt T.C.model 1 + angleAt T.C.model 2 = Real.pi := Erdos634.Draft.LaczFormal.angleAt_sum T.C.model
      have e : T.C.model.angleAt 2 = angleAt T.C.model 2 := rfl
      rw [ang, e]; linarith
    · omega
  have hnS : ∀ k : Fin M, k ∉ S → ∃ m : ℕ, T.P.angle (k + 1) = m * angleAt T.C.model 2 := by
    intro k hk
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hk
    rcases hpoly k with ⟨h0, -, -⟩ | ⟨-, -, ang⟩
    · omega
    · exact ⟨cnt T.C idx (T.P.v (k + 1)) 2, ang⟩
  have hi0 : i0 ∈ Sᶜ := by rw [hSc]; simp
  have hj0 : j0 ∈ Sᶜ := by rw [hSc]; simp
  obtain ⟨m, hm⟩ := hnS i0 (Finset.mem_compl.mp hi0)
  obtain ⟨n, hn⟩ := hnS j0 (Finset.mem_compl.mp hj0)
  refine ⟨i0 + 1, j0 + 1, fun e => hij0 (add_right_cancel e), ?_, m, n, hm, hn⟩
  intro k hki hkj
  have hk1 : k - 1 ∈ S := by
    by_contra hnot
    have : k - 1 ∈ Sᶜ := Finset.mem_compl.mpr hnot
    rw [hSc] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with e | e
    · apply hki; rw [← e, sub_add_cancel]
    · apply hkj; rw [← e, sub_add_cancel]
  have := hγS (k - 1) hk1
  rwa [sub_add_cancel] at this

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.caseII_b

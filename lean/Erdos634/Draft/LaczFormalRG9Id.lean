-- Draft/LaczFormalRG9Id.lean -- **Theorem 2.1, Case I, the commensurable branch** (Laczkovich DCG 48 (2012), Sect. 5.2, last paragraph): `a, b, c` pairwise commensurable, `gamma > pi/2`, `gamma != 2pi/3`.
-- Then `cos gamma` is rational (law of cosines); if `R >= M - 1`, `gamma` is a rational multiple of `pi` (`(R-P)(pi-gamma) = (R-M+2) pi`) and Niven's theorem (Mathlib) gives `gamma in {0, pi/3, pi/2, 2pi/3, pi}`, excluded.
-- So `R = M - 2`: `M - 2` corners equal `gamma`, the two others are integer multiples of `alpha + beta`; the polygon is rational (`side_comm`), the sines commensurable: conclusion (ii).  UNAUDITED.
-- Credit: Laczkovich (DCG 48 (2012), Sect. 5), Beeson, Beeson-Zhang; Niven's theorem as formalized in Mathlib.
import Erdos634.Draft.LaczFormalRG9Sides

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

/-- Law of cosines in the model: `c² = a² + b² - 2 a b cos γ`. -/
theorem model_cos_gamma (D : CongruentRegionDissection N) :
    slen D 2 * slen D 2 = slen D 0 * slen D 0 + slen D 1 * slen D 1 - 2 * slen D 0 * slen D 1 * Real.cos (D.model.angleAt 2) := by
  have := EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1)
  have e2 : slen D 2 = dist (D.model.pts 0) (D.model.pts 1) := rfl
  have e0 : slen D 0 = dist (D.model.pts 1) (D.model.pts 2) := rfl
  have e1 : slen D 1 = dist (D.model.pts 2) (D.model.pts 0) := rfl
  have hang : D.model.angleAt 2 = EuclideanGeometry.angle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) := rfl
  rw [e2, e0, e1, hang, dist_comm (D.model.pts 2) (D.model.pts 0)]
  rw [dist_comm (D.model.pts 1) (D.model.pts 2)] at this ⊢
  linarith

/-- If `a, b, c` are pairwise commensurable, `cos γ` is rational. -/
theorem cos_gamma_rat (D : CongruentRegionDissection N) (hab : Comm (slen D 0) (slen D 1)) (hac : Comm (slen D 0) (slen D 2)) :
    ∃ q : ℚ, Real.cos (D.model.angleAt 2) = q := by
  obtain ⟨p, q, hp, hq, e1⟩ := hab
  obtain ⟨p', q', hp', hq', e2⟩ := hac
  have ha := slen_pos D 0
  have hlaw := model_cos_gamma D
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hq0' : (q' : ℝ) ≠ 0 := by exact_mod_cast hq'.ne'
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hb : slen D 1 = (p : ℝ) / q * slen D 0 := by field_simp; linarith
  have hc : slen D 2 = (p' : ℝ) / q' * slen D 0 := by field_simp; linarith
  refine ⟨(1 + ((p : ℚ) / q) ^ 2 - ((p' : ℚ) / q') ^ 2) / (2 * ((p : ℚ) / q)), ?_⟩
  push_cast
  rw [hb, hc] at hlaw
  have hb0 : (p : ℝ) / q ≠ 0 := div_ne_zero hp0 hq0
  field_simp at hlaw ⊢
  have : slen D 0 * slen D 0 * (2 * p * q' ^ 2 * Real.cos (D.model.angleAt 2) * q ) = slen D 0 * slen D 0 * ((q' ^ 2 * (q ^ 2 + p ^ 2)) - p' ^ 2 * q ^ 2) := by
    nlinarith [hlaw]
  have haa : slen D 0 * slen D 0 ≠ 0 := by positivity
  have := mul_left_cancel₀ haa this
  nlinarith [this]

/-- **`R = M - 2`** when `cos γ` is rational (Niven). -/
theorem caseI_R_eq (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) (hregc : ∀ X, cnt D idx X 0 = cnt D idx X 1)
    (h1 : Real.pi / 2 < D.model.angleAt 2) (h3 : D.model.angleAt 2 ≠ 2 * Real.pi / 3) (hcos : ∃ q : ℚ, Real.cos (D.model.angleAt 2) = q) :
    (cntR2 D idx P : ℤ) = M - 2 ∧ cntP0 D idx P = cntR2 D idx P := by
  have hpi := Real.pi_pos
  have hγ := model_gamma_lt_pi D
  have hw : 0 < Real.pi - D.model.angleAt 2 := by linarith
  obtain ⟨hPR, hRM2, -⟩ := caseI_exc_count D P hreg idx hidxA hregc h1 h3
  have hang := caseI_angle_sum D P hreg idx hidxA hregc
  have hpoly := caseI_polyvertex D P hreg idx hidxA hregc h1
  have hRM : cntR2 D idx P ≤ M := by
    unfold cntR2
    calc ∑ k : Fin M, cnt D idx (P.v (k + 1)) 2 ≤ ∑ _k : Fin M, 1 := by
          apply Finset.sum_le_sum
          intro k _
          rcases hpoly k with ⟨-, h2, -⟩ | ⟨h2, -, -⟩ <;> omega
      _ = M := by simp
  have hk : (cntR2 D idx P : ℤ) = M - 2 := by
    by_contra hne
    have hk1 : (1 : ℤ) ≤ (cntR2 D idx P : ℤ) - M + 2 := by omega
    -- `(R - P) w = k π` with `k ≥ 1`: `γ` is a rational multiple of `π`
    set k : ℕ := cntR2 D idx P + 2 - M with hkdef
    have hkR : ((cntR2 D idx P : ℝ) - M + 2) = (k : ℝ) := by
      rw [hkdef]; have : M ≤ cntR2 D idx P + 2 := by omega
      rw [Nat.cast_sub this]; push_cast; ring
    have hk1' : (1 : ℝ) ≤ (k : ℝ) := by
      have : 1 ≤ k := by omega
      exact_mod_cast this
    rw [hkR] at hang
    have hl : (0 : ℝ) < (cntR2 D idx P : ℝ) - cntP0 D idx P := by
      by_contra hle
      push Not at hle
      nlinarith
    have hl' : cntP0 D idx P < cntR2 D idx P := by
      have : (cntP0 D idx P : ℝ) < cntR2 D idx P := by linarith
      exact_mod_cast this
    set l : ℕ := cntR2 D idx P - cntP0 D idx P with hldef
    have hlR : (l : ℝ) = (cntR2 D idx P : ℝ) - cntP0 D idx P := by
      rw [hldef, Nat.cast_sub hl'.le]
    have hl0 : (l : ℝ) ≠ 0 := by rw [hlR]; exact hl.ne'
    have hwl : Real.pi - D.model.angleAt 2 = (k : ℝ) / l * Real.pi := by
      rw [hlR] at hl0 ⊢
      field_simp
      linarith
    have hγrat : ∃ r : ℚ, D.model.angleAt 2 = r * Real.pi := by
      refine ⟨1 - (k : ℚ) / l, ?_⟩
      push_cast
      have : (l : ℝ) ≠ 0 := hl0
      linarith [hwl]
    have hmem := niven_angle_eq hγrat hcos ⟨(model_angle_pos' D 2).le, hγ.le⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h | h | h | h
    · linarith
    · linarith
    · linarith
    · apply h3; rw [h]; ring
    · linarith
  refine ⟨hk, ?_⟩
  -- `P = R`
  have h0 : ((cntR2 D idx P : ℝ) - M + 2) = 0 := by
    have : ((cntR2 D idx P : ℤ) : ℝ) = (M : ℝ) - 2 := by exact_mod_cast hk
    push_cast at this; linarith
  rw [h0, zero_mul] at hang
  rcases mul_eq_zero.mp hang with h | h
  · have : (cntR2 D idx P : ℝ) = cntP0 D idx P := by linarith
    exact_mod_cast this.symm
  · linarith

/-- **Theorem 2.1, Case I, `a, b, c` pairwise commensurable**: conclusion (ii). -/
theorem caseI_d {N M : ℕ} [NeZero M] (T : PolyTiling N M) (hreg : RegularPQ T.C) (h1 : Real.pi / 2 < angleAt T.C.model 2) (h3 : angleAt T.C.model 2 ≠ 2 * Real.pi / 3)
    (hab : Comm (slen T.C 0) (slen T.C 1)) (hac : Comm (slen T.C 0) (slen T.C 2)) : Concl2 T.C T.P := by
  classical
  obtain ⟨idx, hA, hcnt⟩ := hreg
  haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  have hregc : ∀ X, cnt T.C idx X 0 = cnt T.C idx X 1 := fun X => hcnt X
  have hcos := cos_gamma_rat T.C hab hac
  obtain ⟨hR, hPeq⟩ := caseI_R_eq T.C T.P T.region_eq idx hA hregc h1 h3 hcos
  have hpoly := caseI_polyvertex T.C T.P T.region_eq idx hA hregc h1
  have hidx := idx_dist_of_angle T.C idx hA
  refine ⟨fun i j => comm_trans' (side_comm T.C T.P T.region_eq idx hidx hab hac i) (comm_symm' (side_comm T.C T.P T.region_eq idx hidx hab hac j)), ?_,
    sinComm_of_comm T.C hab hac⟩
  set S : Finset (Fin M) := Finset.univ.filter (fun k => cnt T.C idx (T.P.v (k + 1)) 2 = 1) with hS
  have ht01 : ∀ k : Fin M, cnt T.C idx (T.P.v (k + 1)) 2 = 0 ∨ cnt T.C idx (T.P.v (k + 1)) 2 = 1 := by
    intro k; rcases hpoly k with ⟨-, h2, -⟩ | ⟨h2, -, -⟩ <;> omega
  have hRS : cntR2 T.C idx T.P = S.card := by
    unfold cntR2
    rw [hS, Finset.card_filter]
    apply Finset.sum_congr rfl
    intro k _
    rcases ht01 k with h0 | h0 <;> simp [h0]
  have hM3 := T.P.three_le
  have hScard : Sᶜ.card = 2 := by
    rw [Finset.card_compl]
    simp only [Fintype.card_fin]
    omega
  obtain ⟨i0, j0, hij0, hSc⟩ := Finset.card_eq_two.mp hScard
  have hγS : ∀ k : Fin M, k ∈ S → T.P.angle (k + 1) = angleAt T.C.model 2 := by
    intro k hk
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hk
    rcases hpoly k with ⟨-, -, ang⟩ | ⟨h2, -, -⟩
    · exact ang
    · omega
  have hnS : ∀ k : Fin M, k ∉ S → ∃ m : ℕ, T.P.angle (k + 1) = m * (angleAt T.C.model 0 + angleAt T.C.model 1) := by
    intro k hk
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hk
    rcases hpoly k with ⟨-, h2, -⟩ | ⟨-, -, ang⟩
    · omega
    · refine ⟨cnt T.C idx (T.P.v (k + 1)) 0, ?_⟩
      have hs := Erdos634.Draft.LaczFormal.angleAt_sum T.C.model
      have hs' : angleAt T.C.model 0 + angleAt T.C.model 1 + angleAt T.C.model 2 = Real.pi := hs
      have hw : Real.pi - T.C.model.angleAt 2 = angleAt T.C.model 0 + angleAt T.C.model 1 := by
        have e : T.C.model.angleAt 2 = angleAt T.C.model 2 := rfl
        rw [e]; linarith
      rw [ang, hw]
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

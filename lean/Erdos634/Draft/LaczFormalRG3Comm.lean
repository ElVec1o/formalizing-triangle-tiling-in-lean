-- Draft/LaczFormalRG3Comm.lean -- Theorem 2.1, Case III (gamma = 2pi/3): (a) every polygon angle is `pi/3` or `2pi/3`; (b) the COMMENSURABLE branch (`a, b, c` pairwise commensurable): conclusion (ii) for
-- `4 <= M <= 6`, (iv) (regular triangle) for `M = 3`; (c) the reduction of Case III to (IIIa/IIIb: `a` or `b` outside the rational cone of the other two sides) and IIIc (`a, b` commensurable, `c` not).
-- NOTE ON THE PRINTED PROOF OF IIIa/IIIb: Lemma 7.1 (i) of Laczkovich (DCG 48 (2012), p. 364) is NOT proved as printed (Beeson-Zhang, arXiv 2604.01314, Appendix A): at a vertex with equation
-- `3 alpha + 3 beta = pi` the claim "an edge of Gamma_a starts from X" fails; see `LaczFormalRG3Gap`.  Hence the subcases IIIa/IIIb are NOT formalized; they appear as an explicit disjunct of `caseIII_reduce`.
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 7), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG4Comm

open scoped Classical Fin.NatCast Fin.CommRing
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

set_option maxHeartbeats 3200000 in
/-- **Every angle of the polygon is `π/3` or `2π/3`** (`γ = 2π/3`, regular corner counts; no hypothesis on `a, b, c`). -/
theorem polygon_angle_2pi3 (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) (hγ : D.model.angleAt 2 = 2 * Real.pi / 3)
    (hαβ : D.model.angleAt 0 + D.model.angleAt 1 = Real.pi / 3) (hregc : ∀ X, cnt D idx X 0 = cnt D idx X 1) (k : Fin M) :
    P.angle (k + 1) = Real.pi / 3 ∨ P.angle (k + 1) = 2 * Real.pi / 3 := by
  classical
  set V := P.v (k + 1) with hVdef
  have hvert : ∃ j k', (D.tile j).pts k' = V := poly_vertex_is_tile_vertex D.toRegionDissection P hreg (k + 1)
  obtain ⟨pT, qT, F, hpd, hqd, hcr, h1, h2, h3, h4, h5⟩ := fan_vertex_poly D.toRegionDissection P hreg k hvert
  have hqT : qT ≠ 0 := by intro h; rw [h] at hcr; unfold crs at hcr; simp at hcr
  have hpT : pT ≠ 0 := hpd.ne_left
  obtain ⟨i0, k0, hk0⟩ := hvert
  have hmem0 : V ∈ (D.tile i0).carrier := hk0 ▸ subset_convexHull ℝ _ ⟨k0, rfl⟩
  have hAt : 0 < Fintype.card (AtV D.toRegionDissection V) := Fintype.card_pos_iff.mpr ⟨⟨i0, hmem0⟩⟩
  obtain ⟨c, hc1, hcn, hadj, hsurjc, hinjc⟩ := corner_chain F hcr h1 h2 h3 h4 h5 hAt
  set n := Fintype.card (AtV D.toRegionDissection V) with hn
  have hsumT := corner_tile_sum D.toRegionDissection F hcr h1 h2 h3 h4
  have hwlt := wd_lt_pi_of_crs_pos hcr
  have hwpos := wd_pos (Or.inl hcr : SecOK pT qT)
  have hnostr : ∀ x : AtV D.toRegionDissection V, ∃ k, (D.tile x.1).pts k = V := by
    intro x
    rcases F.hspec x with ⟨k, hk, -⟩ | ⟨hnv, m', -, -, hq, -⟩
    · exact ⟨k, hk⟩
    · exfalso
      have hw : wd (F.p x) (F.q x) = Real.pi := by rw [hq]; exact wd_straight (F.hok x).ne_p
      have hle : wd (F.p x) (F.q x) ≤ ∑ y : AtV D.toRegionDissection V, wd (F.p y) (F.q y) :=
        Finset.single_le_sum (f := fun y => wd (F.p y) (F.q y)) (fun y _ => (wd_pos (F.hok y)).le) (Finset.mem_univ x)
      linarith
  have hcrall : ∀ x : AtV D.toRegionDissection V, 0 < crs (F.p x) (F.q x) :=
    fun x => crs_pos_of_corner (F.hok x) (F.hspec x) (hnostr x)
  have hStrn : Strn D.toRegionDissection V = ∅ := by
    ext j
    simp only [Strn, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, not_and, not_forall, not_not]
    intro hj
    exact hnostr ⟨j, hj⟩
  have hang := head_angle_sum_gen D idx hidxA F
  have hvirt : ∑ j : Bool, wd (F.pe j) (F.qe j) = Real.pi + (Real.pi - wd pT qT) := by
    rw [Fintype.sum_bool, h1, h2, h3, h4, wd_straight hqT, wd_neg_left hcr]; ring
  rw [hStrn, hvirt] at hang
  simp only [Finset.card_empty, Nat.cast_zero, mul_zero, add_zero] at hang
  rw [Fin.sum_univ_three] at hang
  have hsum' : ((cnt D idx V 0 : ℕ) : ℝ) * D.model.angleAt 0 + (cnt D idx V 1 : ℕ) * D.model.angleAt 1 + (cnt D idx V 2 : ℕ) * D.model.angleAt 2 = wd pT qT := by
    linarith
  -- the polygon angle
  have hθ : P.angle (k + 1) = wd pT qT := by
    obtain ⟨ρ, hρ, hiff⟩ := P.vertex_local_T P.three_le k
    have hN : 0 < N := Fin.pos i0
    have hT1 : (P.locTri P.three_le k).pts 1 = V := rfl
    have hiffD : ∀ y, dist y ((P.locTri P.three_le k).pts 1) < ρ → (y ∈ D.region ↔ y ∈ (P.locTri P.three_le k).carrier) := by
      intro y hy; rw [hreg]; exact hiff y hy
    have hs := sum_localAngle_tri D.toRegionDissection hN (P.locTri P.three_le k) hρ hiffD
    have hwdt := tiles_angle_sum D.toRegionDissection V F.p F.q F.hwd
    have hwdT : wd pT qT = (P.locTri P.three_le k).localAngle V := by
      rw [← hsumT, hwdt]; exact hs
    have hloc : (P.locTri P.three_le k).localAngle V = P.angle (k + 1) := by
      have := Tri.localAngle_vertex (P.locTri P.three_le k) 1
      rw [hT1] at this
      rw [this]
      unfold ConvPoly.angle cornerAngle
      have e1 : k + 1 - 1 = k := by simp
      have e2 : k + 1 + 1 = k + 2 := (ConvPoly.fin_facts P.three_le k).2.2.2.2.2
      rw [e1, e2, EuclideanGeometry.angle_comm (P.v k)]
      rfl
    rw [← hloc, hwdT]
  -- counts
  have hpi := Real.pi_pos
  have hr : ((cnt D idx V 0 : ℕ) : ℝ) = (cnt D idx V 1 : ℕ) := by exact_mod_cast hregc V
  have hN2 : ((cnt D idx V 1 + 2 * cnt D idx V 2 : ℕ) : ℝ) * (Real.pi / 3) = wd pT qT := by
    rw [← hsum', hr, hγ]
    have := hαβ
    push_cast
    nlinarith [this]
  have hN2pos : 0 < cnt D idx V 1 + 2 * cnt D idx V 2 := by
    by_contra hz
    have : cnt D idx V 1 + 2 * cnt D idx V 2 = 0 := by omega
    rw [this] at hN2
    simp at hN2; linarith
  have hN2lt : cnt D idx V 1 + 2 * cnt D idx V 2 < 3 := by
    by_contra hz
    push Not at hz
    have : (3 : ℝ) ≤ ((cnt D idx V 1 + 2 * cnt D idx V 2 : ℕ) : ℝ) := by exact_mod_cast hz
    nlinarith
  have hang3 : P.angle (k + 1) = ((cnt D idx V 1 + 2 * cnt D idx V 2 : ℕ) : ℝ) * (Real.pi / 3) := by rw [hθ, hN2]
  have hc : cnt D idx V 1 + 2 * cnt D idx V 2 = 1 ∨ cnt D idx V 1 + 2 * cnt D idx V 2 = 2 := by omega
  rcases hc with hc | hc
  · left; rw [hang3, hc]; push_cast; ring
  · right; rw [hang3, hc]; push_cast; ring


/-- **Case III, `a, b, c` pairwise commensurable**: conclusion (ii) (for `M ≥ 4`) or (iv) (for `M = 3`) of Theorem 2.1. -/
theorem caseIII_comm {N M : ℕ} [NeZero M] (T : PolyTiling N M) (hreg : RegularPQ T.C) (hγ : angleAt T.C.model 2 = 2 * Real.pi / 3)
    (hab : Comm (slen T.C 0) (slen T.C 1)) (hac : Comm (slen T.C 0) (slen T.C 2)) : Concl2 T.C T.P ∨ Concl4 T.C T.P := by
  classical
  obtain ⟨idx, hA, hcnt⟩ := hreg
  have hidx := idx_dist_of_angle T.C idx hA
  haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  have hαβ : T.C.model.angleAt 0 + T.C.model.angleAt 1 = Real.pi / 3 := by
    have := Erdos634.Draft.LaczFormal.angleAt_sum T.C.model
    have hγ' : T.C.model.angleAt 2 = 2 * Real.pi / 3 := hγ
    linarith
  have hall : ∀ i : Fin M, T.P.angle i = Real.pi / 3 ∨ T.P.angle i = 2 * Real.pi / 3 := by
    intro i
    have := polygon_angle_2pi3 T.C T.P T.region_eq idx hA hγ hαβ (fun X => hcnt X) (i - 1)
    rwa [sub_add_cancel] at this
  have hsum := poly_angle_sum T.P
  have hM3 : 3 ≤ M := T.P.three_le
  have hpi := Real.pi_pos
  set S : Finset (Fin M) := Finset.univ.filter (fun i => T.P.angle i = Real.pi / 3) with hS
  have hSc : (S.card : ℝ) + M = 6 := by
    have h1 : ∑ i : Fin M, T.P.angle i = ∑ i ∈ S, T.P.angle i + ∑ i ∈ Finset.univ.filter (fun i => ¬ T.P.angle i = Real.pi / 3), T.P.angle i :=
      (Finset.sum_filter_add_sum_filter_not Finset.univ _ _).symm
    have h2 : ∑ i ∈ S, T.P.angle i = (S.card : ℝ) * (Real.pi / 3) := by
      rw [Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2), Finset.sum_const, nsmul_eq_mul]
    have h3 : ∑ i ∈ Finset.univ.filter (fun i => ¬ T.P.angle i = Real.pi / 3), T.P.angle i =
        ((Finset.univ.filter (fun i => ¬ T.P.angle i = Real.pi / 3)).card : ℝ) * (2 * Real.pi / 3) := by
      rw [Finset.sum_congr rfl (fun i hi => (hall i).resolve_left (Finset.mem_filter.mp hi).2), Finset.sum_const, nsmul_eq_mul]
    have h4 : S.card + (Finset.univ.filter (fun i => ¬ T.P.angle i = Real.pi / 3)).card = M := by
      have := Finset.filter_card_add_filter_neg_card_eq_card (s := (Finset.univ : Finset (Fin M))) (fun i => T.P.angle i = Real.pi / 3)
      simpa using this
    have h4' : (S.card : ℝ) + ((Finset.univ.filter (fun i => ¬ T.P.angle i = Real.pi / 3)).card : ℝ) = M := by exact_mod_cast h4
    have hMr : ((M - 2 : ℕ) : ℝ) = (M : ℝ) - 2 := by rw [Nat.cast_sub (by omega)]; norm_num
    have e : ((M - 2 : ℕ) : ℝ) * Real.pi = (S.card : ℝ) * (Real.pi / 3) +
        ((Finset.univ.filter (fun i => ¬ T.P.angle i = Real.pi / 3)).card : ℝ) * (2 * Real.pi / 3) := by
      rw [← hsum, h1, h2, h3]
    rw [hMr] at e
    have e2 : ((S.card : ℝ) + M - 6) * Real.pi = 0 := by
      have hc' : ((Finset.univ.filter (fun i => ¬ T.P.angle i = Real.pi / 3)).card : ℝ) = M - S.card := by linarith
      rw [hc'] at e
      linear_combination (3 : ℝ) * e
    rcases mul_eq_zero.mp e2 with h | h
    · linarith
    · exact absurd h hpi.ne'
  have hSn : S.card + M = 6 := by exact_mod_cast hSc
  have hαβ' : angleAt T.C.model 0 + angleAt T.C.model 1 = Real.pi / 3 := hαβ
  have hmulti : ∀ i : Fin M, ∃ m : ℕ, T.P.angle i = m * (angleAt T.C.model 0 + angleAt T.C.model 1) := by
    intro i
    rcases hall i with h | h
    · exact ⟨1, by rw [h, hαβ']; ring⟩
    · exact ⟨2, by rw [h, hαβ']; ring⟩
  have hRat : RationalPoly T.P := by
    intro i j
    exact comm_trans' (side_comm T.C T.P T.region_eq idx hidx hab hac i) (comm_symm' (side_comm T.C T.P T.region_eq idx hidx hab hac j))
  have hSin : SinComm T.C := sinComm_of_comm T.C hab hac
  by_cases hM : M = 3
  · -- all angles are π/3: regular triangle
    right
    subst hM
    have hS3 : S.card = 3 := by omega
    have hall3 : ∀ i : Fin 3, T.P.angle i = Real.pi / 3 := by
      intro i
      have : S = Finset.univ := Finset.eq_univ_of_card S (by simpa using hS3)
      have hi : i ∈ S := by rw [this]; exact Finset.mem_univ i
      exact (Finset.mem_filter.mp hi).2
    exact ⟨rfl, triangle_equilateral T.P hall3, Or.inr hγ, hSin⟩
  · left
    have hM4 : 4 ≤ M := by omega
    have hS2 : S.card ≤ 2 := by omega
    obtain ⟨t, hSt, -, htc⟩ := Finset.exists_subsuperset_card_eq (s := S) (t := (Finset.univ : Finset (Fin M))) (Finset.subset_univ S) hS2
      (by simp; omega)
    obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp htc
    obtain ⟨mi, hmi⟩ := hmulti i
    obtain ⟨mj, hmj⟩ := hmulti j
    refine ⟨hRat, ⟨i, j, hij, ?_, mi, mj, hmi, hmj⟩, hSin⟩
    intro k hki hkj
    have hk : k ∉ S := by
      intro hk
      have := hSt hk
      simp at this
      rcases this with h | h
      · exact hki h
      · exact hkj h
    have : ¬ T.P.angle k = Real.pi / 3 := fun h => hk (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    rw [(hall k).resolve_left this, hγ]



/-- **Case III reduced.**  For `γ = 2π/3`, either Theorem 2.1's conclusion holds, or `a` (resp. `b`) is not a nonnegative rational combination of the other two sides (IIIa, IIIb: the printed
proof via Lemma 7.1 is not valid, Beeson-Zhang Appendix A; NOT formalized), or `a, b` are commensurable and `c` is not commensurable with `a` (IIIc). -/
theorem caseIII_reduce {N M : ℕ} [NeZero M] (T : PolyTiling N M) (hreg : RegularPQ T.C) (hγ : angleAt T.C.model 2 = 2 * Real.pi / 3) :
    Thm21Concl T.C T.P ∨ NotComb (slen T.C 0) (slen T.C 1) (slen T.C 2) ∨ NotComb (slen T.C 1) (slen T.C 0) (slen T.C 2) ∨
      (Comm (slen T.C 0) (slen T.C 1) ∧ ¬ Comm (slen T.C 0) (slen T.C 2)) := by
  classical
  by_cases h1 : NotComb (slen T.C 0) (slen T.C 1) (slen T.C 2)
  · exact Or.inr (Or.inl h1)
  by_cases h2 : NotComb (slen T.C 1) (slen T.C 0) (slen T.C 2)
  · exact Or.inr (Or.inr (Or.inl h2))
  unfold NotComb at h1 h2
  push Not at h1 h2
  obtain ⟨r, p, q, hr, e1⟩ := h1
  obtain ⟨r', p', q', hr', e2⟩ := h2
  have hcomm : Comm (slen T.C 0) (slen T.C 1) := comm_of_two_combs (slen_pos T.C 0) (slen_pos T.C 1) hr e1 hr' e2
  by_cases hc : Comm (slen T.C 0) (slen T.C 2)
  · rcases caseIII_comm T hreg hγ hcomm hc with h | h
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr ⟨hcomm, hc⟩))

end Erdos634.Draft.LaczFormal.RG

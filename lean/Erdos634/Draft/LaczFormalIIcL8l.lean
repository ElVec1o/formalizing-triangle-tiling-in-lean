-- Draft/LaczFormalIIcL8l.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.3, L8 `gexc_disjoint`, step 5: `gexc_inner_split`.
-- For an edge `X -> Y` of Gamma_except and an INNER point `V` of it, the local data at `V`: on BOTH sides of the line, `V` is the head of a `gamma`-headed element or an inner point of a tile side
-- (with `gamma` at the head `B` of that side); the left walk is a walk passing strictly beyond `V`.  (Same proof as `gexc_end_split_fullG`, with `V` strictly before the end of the `gamma`-runs.)
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcSharp1
import Erdos634.Draft.LaczFormalRG12GExcWalk

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

/-- a walk can be cut after any of its elements. -/
theorem walkU_prefix_at_head {D : RegionDissection N} {b : Bool} {d : V2} {X Z : Plane} {L : List (Fin N × Plane × Plane)} (W : WalkU D b d X Z L)
    {e : Fin N × Plane × Plane} (he : e ∈ L) : ∃ P, WalkU D b d X e.2.2 P ∧ P ≠ [] := by
  obtain ⟨P, Q, hPQ⟩ := List.mem_iff_append.mp he
  obtain ⟨i, A, B⟩ := e
  obtain ⟨w1, w2⟩ := walkU_split W hPQ
  simp only at w1 w2 ⊢
  cases w2 with
  | cons hS W' =>
    refine ⟨P ++ [(i, A, B)], ?_, by simp⟩
    rw [walkU_append]
    exact ⟨A, w1, WalkU.cons hS (WalkU.nil B)⟩

theorem par_of_param {u d : V2} {t : ℝ} (hd : d ≠ 0) (ht : 0 < t) (h : u = (t * d.1, t * d.2)) : Par u d := by
  subst h
  refine ⟨by unfold crs; ring, ?_⟩
  have := nsq_pos hd
  unfold dt; unfold nsq at this; nlinarith

theorem gexc_inner_split (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3)) {X Y V : Plane}
    (h : GExc D idx X Y) (hV : V ∈ openSegment ℝ X Y) :
    ∃ d : V2, d ≠ 0 ∧ NoBack D.toRegionDissection d X ∧ Par (toV2 (Y - X)) d ∧
      (∃ (Z : Plane) (L : List (Fin N × Plane × Plane)) (T v : ℝ), WalkU D.toRegionDissection true d X Z L ∧ toV2 (Z - X) = (T * d.1, T * d.2) ∧
        toV2 (V - X) = (v * d.1, v * d.2) ∧ 0 < v ∧ v < T) ∧
      EndLeftG D idx d V ∧ EndRightG D idx d V ∧
      ((∃ P, WalkU D.toRegionDissection true d X V P ∧ P ≠ []) ∨ ∃ (iL : Fin N) (A B : Plane), TriStep (D.tile iL) d A B ∧ V ∈ openSegment ℝ A B) ∧
      ((∃ P, WalkU D.toRegionDissection false d X V P ∧ P ≠ []) ∨ ∃ (iR : Fin N) (A B : Plane), TriStep (D.tile iR) (neg2 d) B A ∧ V ∈ openSegment ℝ A B) := by
  obtain ⟨d, Z, L1, L2, H1, H2, hd, hnb, W1, W2, hL1, hL2, hnoL, hnoR, hr1, hr2, hY⟩ := h
  have WU1 := walkU_of_T W1
  have WU2 := walkU_of_R W2
  obtain ⟨P1, Q1, e1, -, hP1, w1, s1, hall1, hhead1, he1, he1H⟩ := grun_split' D idx WU1 hr1
  obtain ⟨P2, Q2, e2, -, hP2, w2, s2, hall2, hhead2, he2, he2H⟩ := grun_split' D idx WU2 hr2
  obtain ⟨T1, hT1n, hT1, hT1p, -⟩ := walkU_pos w1
  obtain ⟨T2, hT2n, hT2, hT2p, -⟩ := walkU_pos w2
  have hT1pos := hT1p hP1
  have hT2pos := hT2p hP2
  obtain ⟨TL, hTL0, hTL, -, -⟩ := walkU_pos WU1
  obtain ⟨S1, hS10, hS1, -, -⟩ := walkU_pos s1
  have hTLe : T1 ≤ TL := by
    have e1' := toV2_sub3 Z H1 X
    rw [hTL, hT1, hS1] at e1'
    simp only at e1'
    have := scal_unique hd (a := TL) (b := S1 + T1) (by rw [e1']; ext <;> simp only <;> ring)
    linarith
  obtain ⟨v, hv0, hv1, hv2, hvpos⟩ : ∃ v : ℝ, 0 < v ∧ v < T1 ∧ v < T2 ∧ toV2 (V - X) = (v * d.1, v * d.2) ∧ True := by
    rcases hY with ⟨rfl, hle⟩ | ⟨rfl, hle⟩
    · obtain ⟨b, hb0, hb1, hbv⟩ := seg_param hV hT1
      have := pos_le_of_dist_le hd hT1n hT2n hT1 hT2 hle
      exact ⟨b * T1, by positivity, by nlinarith, by nlinarith, hbv, trivial⟩
    · obtain ⟨b, hb0, hb1, hbv⟩ := seg_param hV hT2
      have := pos_le_of_dist_le hd hT2n hT1n hT2 hT1 hle
      exact ⟨b * T2, by positivity, by nlinarith, by nlinarith, hbv, trivial⟩
  obtain ⟨hvV, -⟩ := hvpos
  have otherL : EndLeftG D idx d V ∧ ((∃ P, WalkU D.toRegionDissection true d X V P ∧ P ≠ []) ∨ ∃ (iL : Fin N) (A B : Plane), TriStep (D.tile iL) d A B ∧ V ∈ openSegment ℝ A B) := by
    obtain ⟨e, he, hS, hcase⟩ := run_contains D.toRegionDissection hd w1 hT1 hvV hv0 hv1.le
    obtain ⟨iL, A, B⟩ := e
    have hS0 := hS
    simp only [StepU, if_true] at hS
    obtain ⟨k, hk, hk2⟩ := hall1 _ he
    simp only at hk
    rcases hcase with hh | hh
    · simp only at hh
      refine ⟨⟨iL, A, B, hS, Or.inl ⟨hh, k, by rw [hh]; exact hk, hk2⟩⟩, Or.inl ?_⟩
      obtain ⟨P, hP, hPne⟩ := walkU_prefix_at_head w1 he
      exact ⟨P, by simpa [hh] using hP, hPne⟩
    · exact ⟨⟨iL, A, B, hS, Or.inr ⟨hh, k, hk, hk2⟩⟩, Or.inr ⟨iL, A, B, hS, hh⟩⟩
  have otherR : EndRightG D idx d V ∧ ((∃ P, WalkU D.toRegionDissection false d X V P ∧ P ≠ []) ∨ ∃ (iR : Fin N) (A B : Plane), TriStep (D.tile iR) (neg2 d) B A ∧ V ∈ openSegment ℝ A B) := by
    obtain ⟨e, he, hS, hcase⟩ := run_contains D.toRegionDissection hd w2 hT2 hvV hv0 hv2.le
    obtain ⟨iR, A, B⟩ := e
    simp only [StepU, Bool.false_eq_true, if_false] at hS
    obtain ⟨k, hk, hk2⟩ := hall2 _ he
    simp only at hk
    rcases hcase with hh | hh
    · simp only at hh
      refine ⟨⟨iR, A, B, hS, Or.inl ⟨hh, k, by rw [hh]; exact hk, hk2⟩⟩, Or.inl ?_⟩
      obtain ⟨P, hP, hPne⟩ := walkU_prefix_at_head w2 he
      exact ⟨P, by simpa [hh] using hP, hPne⟩
    · exact ⟨⟨iR, A, B, hS, Or.inr ⟨hh, k, hk, hk2⟩⟩, Or.inr ⟨iR, A, B, hS, hh⟩⟩
  refine ⟨d, hd, hnb, ?_, ⟨Z, L1, TL, v, WU1, hTL, hvV, hv0, lt_of_lt_of_le hv1 hTLe⟩, otherL.1, otherR.1, otherL.2, otherR.2⟩
  rcases hY with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact par_of_param hd hT1pos hT1
  · exact par_of_param hd hT2pos hT2

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.gexc_inner_split

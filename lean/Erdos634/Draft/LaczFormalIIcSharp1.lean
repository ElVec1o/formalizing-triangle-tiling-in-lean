-- Draft/LaczFormalIIcSharp1.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2-6.3, repair of the hStrn gap (AI assistant plan IIC_STRN.md, S1): `gexc_end_split_fullG` = `gexc_end_split_full` with the
-- `gamma`-at-head clause also in the INNER-point disjunct: the element `(i, A, B)` of either division with `Y` in the open side `A B` has `gamma` at `B` (the far end along `d`).
-- Proof: every element of the `gamma`-prefix of a run is `GammaHead` (`grun_split'`, `run_contains`); the proof of `gexc_end_split_full` is repeated with that clause kept.  The old statement is unchanged (no downstream rebuild).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2-6.3, Lemmas 4.4-4.8), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG12GExcEndSplit

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

/-- Left element containing `Y`: head with `gamma`, or inner point of its side, in which case `gamma` is at the head `B` (far end along `d`). -/
def EndLeftG (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (d : V2) (Y : Plane) : Prop :=
  ∃ (iL : Fin N) (A B : Plane), TriStep (D.tile iL) d A B ∧ ((Y = B ∧ ∃ k, (D.tile iL).pts k = Y ∧ idx iL k = 2) ∨ (Y ∈ openSegment ℝ A B ∧ ∃ k, (D.tile iL).pts k = B ∧ idx iL k = 2))

/-- Right element containing `Y`, same clause. -/
def EndRightG (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (d : V2) (Y : Plane) : Prop :=
  ∃ (iR : Fin N) (A B : Plane), TriStep (D.tile iR) (neg2 d) B A ∧ ((Y = B ∧ ∃ k, (D.tile iR).pts k = Y ∧ idx iR k = 2) ∨ (Y ∈ openSegment ℝ A B ∧ ∃ k, (D.tile iR).pts k = B ∧ idx iR k = 2))

/-- **STEP 1 of statement (ii)**: the local data at the end `Y` of an edge of Gamma_except (with `NoBack` at `X` and the nonempty walk from `X` to `Y`). -/
theorem gexc_end_split_fullG (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3)) {X Y : Plane} (h : GExc D idx X Y) :
    ∃ d : V2, d ≠ 0 ∧ NoBack D.toRegionDissection d X ∧ (∃ (b : Bool) (P : List (Fin N × Plane × Plane)), WalkU D.toRegionDissection b d X Y P ∧ P ≠ []) ∧
      EndLeftG D idx d Y ∧ EndRightG D idx d Y ∧ (RunEndL D idx d Y ∨ RunEndR D idx d Y) := by
  obtain ⟨d, Z, L1, L2, H1, H2, hd, hnb, W1, W2, hL1, hL2, hnoL, hnoR, hr1, hr2, hY⟩ := h
  have WU1 := walkU_of_T W1
  have WU2 := walkU_of_R W2
  obtain ⟨P1, Q1, e1, -, hP1, w1, s1, hall1, hhead1, he1, he1H⟩ := grun_split' D idx WU1 hr1
  obtain ⟨P2, Q2, e2, -, hP2, w2, s2, hall2, hhead2, he2, he2H⟩ := grun_split' D idx WU2 hr2
  obtain ⟨T1, hT1n, hT1, hT1p, -⟩ := walkU_pos w1
  obtain ⟨T2, hT2n, hT2, hT2p, -⟩ := walkU_pos w2
  have hT1pos := hT1p hP1
  have hT2pos := hT2p hP2
  have hmaxL : ∀ i U', ¬ StepU D.toRegionDissection true d (i, Z, U') := fun i U' => by simpa [StepU] using hnoL i U'
  have hmaxR : ∀ i U', ¬ StepU D.toRegionDissection false d (i, Z, U') := fun i U' => by simpa [StepU] using hnoR i U'
  -- the element ending the run, with gamma
  have extractL : ∃ (iL : Fin N) (A : Plane), TriStep (D.tile iL) d A H1 ∧ (∃ k, (D.tile iL).pts k = H1 ∧ idx iL k = 2) := by
    obtain ⟨iL, A, B⟩ := e1
    have hst : StepU D.toRegionDissection true d (iL, A, B) := walkU_mem_step w1 _ he1
    obtain ⟨k, hk, hk2⟩ := hall1 _ he1
    have hB : B = H1 := he1H
    simp only [StepU, if_true] at hst
    rw [hB] at hst
    exact ⟨iL, A, hst, k, by rw [← hB]; exact hk, hk2⟩
  have extractR : ∃ (iR : Fin N) (A : Plane), TriStep (D.tile iR) (neg2 d) H2 A ∧ (∃ k, (D.tile iR).pts k = H2 ∧ idx iR k = 2) := by
    obtain ⟨iR, A, B⟩ := e2
    have hst : StepU D.toRegionDissection false d (iR, A, B) := walkU_mem_step w2 _ he2
    obtain ⟨k, hk, hk2⟩ := hall2 _ he2
    have hB : B = H2 := he2H
    simp only [StepU, Bool.false_eq_true, if_false] at hst
    rw [hB] at hst
    exact ⟨iR, A, hst, k, by rw [← hB]; exact hk, hk2⟩
  have contL : ∀ i U', TriStep (D.tile i) d H1 U' → ¬ ∃ k, (D.tile i).pts k = U' ∧ idx i k = 2 := by
    intro i U' hS
    exact run_cont D idx s1 hhead1 hmaxL i U' (by simpa [StepU] using hS)
  have contR : ∀ i U', TriStep (D.tile i) (neg2 d) U' H2 → ¬ ∃ k, (D.tile i).pts k = U' ∧ idx i k = 2 := by
    intro i U' hS
    exact run_cont D idx s2 hhead2 hmaxR i U' (by simpa [StepU] using hS)
  -- containing elements on both sides
  have otherL : ∀ {Y' : Plane} {v : ℝ}, toV2 (Y' - X) = (v * d.1, v * d.2) → 0 < v → v ≤ T1 → EndLeftG D idx d Y' := by
    intro Y' v hv hv0 hvT
    obtain ⟨e, he, hS, hcase⟩ := run_contains D.toRegionDissection hd w1 hT1 hv hv0 hvT
    obtain ⟨iL, A, B⟩ := e
    simp only [StepU, if_true] at hS
    obtain ⟨k, hk, hk2⟩ := hall1 _ he
    simp only at hk
    rcases hcase with hh | hh
    · simp only at hh
      exact ⟨iL, A, B, hS, Or.inl ⟨hh, k, by rw [hh]; exact hk, hk2⟩⟩
    · exact ⟨iL, A, B, hS, Or.inr ⟨hh, k, hk, hk2⟩⟩
  have otherR : ∀ {Y' : Plane} {v : ℝ}, toV2 (Y' - X) = (v * d.1, v * d.2) → 0 < v → v ≤ T2 → EndRightG D idx d Y' := by
    intro Y' v hv hv0 hvT
    obtain ⟨e, he, hS, hcase⟩ := run_contains D.toRegionDissection hd w2 hT2 hv hv0 hvT
    obtain ⟨iR, A, B⟩ := e
    simp only [StepU, Bool.false_eq_true, if_false] at hS
    obtain ⟨k, hk, hk2⟩ := hall2 _ he
    simp only at hk
    rcases hcase with hh | hh
    · simp only at hh
      exact ⟨iR, A, B, hS, Or.inl ⟨hh, k, by rw [hh]; exact hk, hk2⟩⟩
    · exact ⟨iR, A, B, hS, Or.inr ⟨hh, k, hk, hk2⟩⟩
  refine ⟨d, hd, hnb, ?_⟩
  rcases hY with ⟨hYH, hle⟩ | ⟨hYH, hle⟩
  · have hT1Y : toV2 (Y - X) = (T1 * d.1, T1 * d.2) := by rw [hYH]; exact hT1
    have hle' : T1 ≤ T2 := pos_le_of_dist_le hd hT1n hT2n hT1 hT2 hle
    refine ⟨⟨true, P1, by rw [hYH]; exact w1, hP1⟩, otherL hT1Y hT1pos le_rfl, otherR hT1Y hT1pos hle', Or.inl ⟨?_, ?_⟩⟩
    · rw [hYH]; exact extractL
    · rw [hYH]; exact contL
  · have hT2Y : toV2 (Y - X) = (T2 * d.1, T2 * d.2) := by rw [hYH]; exact hT2
    have hle' : T2 ≤ T1 := pos_le_of_dist_le hd hT2n hT1n hT2 hT1 hle
    refine ⟨⟨false, P2, by rw [hYH]; exact w2, hP2⟩, otherL hT2Y hT2pos hle', otherR hT2Y hT2pos le_rfl, Or.inr ⟨?_, ?_⟩⟩
    · rw [hYH]; exact extractR
    · rw [hYH]; exact contR

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.gexc_end_split_fullG

-- Draft/LaczFormalRG12GExcEndSplit.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2, Gamma_except, lemma L7 (statement (ii)), STEP 1: the local data at the END `Y` of an edge `XY` of Gamma_except.
-- (a) `run_contains`: a point `Y` of the segment inside the prefix of a division is the head of an element, or an inner point of its side.
-- (b) `gexc_end_split`: for `GExc D idx X Y` there is a direction `d` such that on BOTH sides of the line `Y` is the head of a `gamma`-headed element or an inner point of a side of a tile (`EndLeft`, `EndRight`), and on the side of the run that ENDS at `Y`
--     the element ending at `Y` has `gamma` at `Y` and no tile starting at `Y` along the line has `gamma` at its far end (maximality of the run).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG12GExcArrive

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

/-- Parameters `t0 < v < t1` along `d` give an inner point of the segment. -/
theorem mem_openSegment_of_params {A B Y X : Plane} {d : V2} {t0 t1 v : ℝ} (hA : toV2 (A - X) = (t0 * d.1, t0 * d.2))
    (hB : toV2 (B - X) = (t1 * d.1, t1 * d.2)) (hY : toV2 (Y - X) = (v * d.1, v * d.2)) (h0 : t0 < v) (h1 : v < t1) : Y ∈ openSegment ℝ A B := by
  obtain ⟨a0, a1⟩ := coord_of hA
  obtain ⟨b0, b1⟩ := coord_of hB
  obtain ⟨y0, y1⟩ := coord_of hY
  have hne : t1 - t0 ≠ 0 := by linarith
  refine ⟨(t1 - v) / (t1 - t0), (v - t0) / (t1 - t0), div_pos (by linarith) (by linarith), div_pos (by linarith) (by linarith), by field_simp; ring, ?_⟩
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rw [a0, b0, y0]; field_simp; ring
  · simp only [Fin.mk_one, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rw [a1, b1, y1]; field_simp; ring

/-- A point `Y` at parameter `0 < v <= T` of a division prefix is the head of an element, or an inner point of its side. -/
theorem run_contains (D : RegionDissection N) {b : Bool} {d : V2} (hd : d ≠ 0) {X H Y : Plane} {P : List (Fin N × Plane × Plane)}
    (w : WalkU D b d X H P) {T v : ℝ} (hT : toV2 (H - X) = (T * d.1, T * d.2)) (hY : toV2 (Y - X) = (v * d.1, v * d.2)) (hv0 : 0 < v) (hvT : v ≤ T) :
    ∃ e ∈ P, StepU D b d e ∧ (Y = e.2.2 ∨ Y ∈ openSegment ℝ e.2.1 e.2.2) := by
  obtain ⟨e, he, t0, t1, h0, h1, ht0, ht1⟩ := walkU_cover' w hd hT v hv0 hvT
  refine ⟨e, he, walkU_mem_step w e he, ?_⟩
  rcases ht1.eq_or_lt with h | h
  · left; rw [← h] at h1; exact pt_eq_of_pos hY h1
  · right; exact mem_openSegment_of_params h0 h1 hY ht0 h

/-- `grun_split` keeping the last element of the run. -/
theorem grun_split' (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {b : Bool} {d : V2} {X Z : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkU D.toRegionDissection b d X Z L) {H : Plane} (hr : GRunEnd D idx L H) :
    ∃ (L' L'' : List (Fin N × Plane × Plane)) (e0 : Fin N × Plane × Plane), L = L' ++ L'' ∧ L' ≠ [] ∧ WalkU D.toRegionDissection b d X H L' ∧
      WalkU D.toRegionDissection b d H Z L'' ∧ (∀ x ∈ L', GammaHead D idx x) ∧ (∀ e ∈ L''.head?, ¬ GammaHead D idx e) ∧ e0 ∈ L' ∧ e0.2.2 = H := by
  obtain ⟨L', L'', hL, hne, hall, hhead, e0, hlast, he0⟩ := hr
  subst hL
  obtain ⟨M, w1, w2⟩ := walkU_append.mp W
  have hM : M = H := by
    obtain ⟨L0, hL0⟩ : ∃ L0, L' = L0 ++ [e0] := ⟨L'.dropLast, (List.dropLast_append_getLast? e0 (Option.mem_def.mpr hlast)).symm⟩
    rw [hL0] at w1
    obtain ⟨M', -, w3⟩ := walkU_append.mp w1
    rw [walkU_single_end w3, he0]
  subst hM
  exact ⟨L', L'', e0, rfl, hne, w1, w2, hall, hhead, List.mem_of_getLast? hlast, he0⟩

theorem stepU_unique (D : RegionDissection N) [HasFansC D] {b : Bool} {d : V2} {H U U' : Plane} {i i' : Fin N}
    (h : StepU D b d (i, H, U)) (h' : StepU D b d (i', H, U')) : i = i' ∧ U = U' := by
  cases b
  · simp only [StepU, Bool.false_eq_true, if_false] at h h'
    exact right_step_unique D h h'
  · simp only [StepU, if_true] at h h'
    exact left_step_unique D h h'

/-- Maximality of a `gamma`-run: no step of the division starting at the run end has `gamma` at its far end. -/
theorem run_cont (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3)) {b : Bool} {d : V2} {H Z : Plane}
    {L'' : List (Fin N × Plane × Plane)} (s1 : WalkU D.toRegionDissection b d H Z L'') (hhead : ∀ e ∈ L''.head?, ¬ GammaHead D idx e)
    (hmax : ∀ i U', ¬ StepU D.toRegionDissection b d (i, Z, U')) :
    ∀ i U', StepU D.toRegionDissection b d (i, H, U') → ¬ ∃ k, (D.tile i).pts k = U' ∧ idx i k = 2 := by
  intro i U' hS hk
  rcases L'' with _ | ⟨⟨j, A, B⟩, rest⟩
  · cases s1
    exact hmax i U' hS
  · cases s1 with
    | cons hS' W' =>
      obtain ⟨hij, hUB⟩ := stepU_unique D.toRegionDissection hS hS'
      subst hij; subst hUB
      exact hhead (i, H, U') (by simp) hk

/-- The element of the left division containing `Y` (head with `gamma`, or inner point of a side). -/
def EndLeft (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (d : V2) (Y : Plane) : Prop :=
  ∃ (iL : Fin N) (A B : Plane), TriStep (D.tile iL) d A B ∧ ((Y = B ∧ ∃ k, (D.tile iL).pts k = Y ∧ idx iL k = 2) ∨ Y ∈ openSegment ℝ A B)

/-- The element of the right division containing `Y` (head with `gamma`, or inner point of a side). -/
def EndRight (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (d : V2) (Y : Plane) : Prop :=
  ∃ (iR : Fin N) (A B : Plane), TriStep (D.tile iR) (neg2 d) B A ∧ ((Y = B ∧ ∃ k, (D.tile iR).pts k = Y ∧ idx iR k = 2) ∨ Y ∈ openSegment ℝ A B)

/-- The left run ends at `Y`. -/
def RunEndL (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (d : V2) (Y : Plane) : Prop :=
  (∃ (iL : Fin N) (A : Plane), TriStep (D.tile iL) d A Y ∧ (∃ k, (D.tile iL).pts k = Y ∧ idx iL k = 2)) ∧
    ∀ (i : Fin N) (U' : Plane), TriStep (D.tile i) d Y U' → ¬ ∃ k, (D.tile i).pts k = U' ∧ idx i k = 2

/-- The right run ends at `Y`. -/
def RunEndR (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (d : V2) (Y : Plane) : Prop :=
  (∃ (iR : Fin N) (A : Plane), TriStep (D.tile iR) (neg2 d) Y A ∧ (∃ k, (D.tile iR).pts k = Y ∧ idx iR k = 2)) ∧
    ∀ (i : Fin N) (U' : Plane), TriStep (D.tile i) (neg2 d) U' Y → ¬ ∃ k, (D.tile i).pts k = U' ∧ idx i k = 2

/-- **STEP 1 of statement (ii)**: the local data at the end `Y` of an edge of Gamma_except (with `NoBack` at `X` and the nonempty walk from `X` to `Y`). -/
theorem gexc_end_split_full (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3)) {X Y : Plane} (h : GExc D idx X Y) :
    ∃ d : V2, d ≠ 0 ∧ NoBack D.toRegionDissection d X ∧ (∃ (b : Bool) (P : List (Fin N × Plane × Plane)), WalkU D.toRegionDissection b d X Y P ∧ P ≠ []) ∧
      EndLeft D idx d Y ∧ EndRight D idx d Y ∧ (RunEndL D idx d Y ∨ RunEndR D idx d Y) := by
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
  have otherL : ∀ {Y' : Plane} {v : ℝ}, toV2 (Y' - X) = (v * d.1, v * d.2) → 0 < v → v ≤ T1 → EndLeft D idx d Y' := by
    intro Y' v hv hv0 hvT
    obtain ⟨e, he, hS, hcase⟩ := run_contains D.toRegionDissection hd w1 hT1 hv hv0 hvT
    obtain ⟨iL, A, B⟩ := e
    simp only [StepU, if_true] at hS
    rcases hcase with hh | hh
    · obtain ⟨k, hk, hk2⟩ := hall1 _ he
      simp only at hh hk
      exact ⟨iL, A, B, hS, Or.inl ⟨hh, k, by rw [hh]; exact hk, hk2⟩⟩
    · exact ⟨iL, A, B, hS, Or.inr hh⟩
  have otherR : ∀ {Y' : Plane} {v : ℝ}, toV2 (Y' - X) = (v * d.1, v * d.2) → 0 < v → v ≤ T2 → EndRight D idx d Y' := by
    intro Y' v hv hv0 hvT
    obtain ⟨e, he, hS, hcase⟩ := run_contains D.toRegionDissection hd w2 hT2 hv hv0 hvT
    obtain ⟨iR, A, B⟩ := e
    simp only [StepU, Bool.false_eq_true, if_false] at hS
    rcases hcase with hh | hh
    · obtain ⟨k, hk, hk2⟩ := hall2 _ he
      simp only at hh hk
      exact ⟨iR, A, B, hS, Or.inl ⟨hh, k, by rw [hh]; exact hk, hk2⟩⟩
    · exact ⟨iR, A, B, hS, Or.inr hh⟩
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

/-- The local data at the end `Y` of an edge of Gamma_except. -/
theorem gexc_end_split (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3)) {X Y : Plane} (h : GExc D idx X Y) :
    ∃ d : V2, d ≠ 0 ∧ EndLeft D idx d Y ∧ EndRight D idx d Y ∧ (RunEndL D idx d Y ∨ RunEndR D idx d Y) := by
  obtain ⟨d, hd, -, -, h1, h2, h3⟩ := gexc_end_split_full D idx h
  exact ⟨d, hd, h1, h2, h3⟩

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.gexc_end_split

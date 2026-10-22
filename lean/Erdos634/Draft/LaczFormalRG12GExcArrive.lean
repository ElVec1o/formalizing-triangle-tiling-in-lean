-- Draft/LaczFormalRG12GExcArrive.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2, Gamma_except, lemma L2 `gexc_arrive_kite_unique` (FABLE_THM21_FINISH blueprint, A.4, F3): at a vertex `Y` of Gamma_kite
-- (an interior (2,2,2) vertex) at most ONE edge of Gamma_except arrives.
-- Route: an edge `X -> Y` of Gamma_except arrives at `Y` as the head of both divisions inside the `gamma`-runs (`run_head_at`: `Y` is a division point of both walks because every tile through `Y` has `Y` as a corner),
-- so a left tile ending at `Y` along `d` and a right tile starting at `Y` along `-d` both have angle `gamma` at `Y`: two ADJACENT `gamma` sectors of the six-sector fan with common ray `-d` (`gexc_arrive_sector`).
-- A (2,2,2) vertex has exactly two `gamma` corners, so the adjacent pair is unique (`gamma_pair_unique`), the arrival direction `d` is determined up to a positive factor, and two edges arriving along the same
-- ray coincide (`align_same`: two walks of parallel direction ending at the same point, both starts with no tile behind them, have the same start).
-- Hypotheses: as `kite_vertex_no_gamma_line` (`CaseC`, `HasFansC`, gamma < pi/2, != pi/3, `AngGen`) and `GKite D idx Y Z` at the target (so that `Y` is an interior (2,2,2) vertex).  The Fig. 5 type (A)/(B) is NOT needed here.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG12GExcStart
import Erdos634.Draft.LaczFormalRG8Align

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

/-- **The head of a `gamma`-run at a corner point.**  A point `Y` of the segment, at parameter `0 < v <= T` along the run prefix `X -> H`, all of whose tiles have `Y` as a corner, is the head of an element of the run. -/
theorem run_head_at (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {b : Bool} {d : V2} (hd : d ≠ 0) {X H Y : Plane}
    {L' : List (Fin N × Plane × Plane)} (W : WalkU D.toRegionDissection b d X H L') (hall : ∀ x ∈ L', GammaHead D idx x) {v T : ℝ}
    (hv : toV2 (Y - X) = (v * d.1, v * d.2)) (hv0 : 0 < v) (hT : toV2 (H - X) = (T * d.1, T * d.2)) (hvT : v ≤ T)
    (hvtx : ∀ i, Y ∈ (D.tile i).carrier → ∃ k, (D.tile i).pts k = Y) :
    ∃ e ∈ L', StepU D.toRegionDissection b d e ∧ e.2.2 = Y ∧ GammaHead D idx e := by
  have hst := walkU_mem_step W
  obtain ⟨e, he, t0, t1, h0, h1, ht0, ht1⟩ := walkU_cover' W hd hT v hv0 hvT
  refine ⟨e, he, hst e he, ?_, hall e he⟩
  rcases ht1.eq_or_lt with h | h
  · rw [← h] at h1; exact pt_eq_of_pos h1 hv
  · exact (not_inner_step D.toRegionDissection hd (hst e he) h0 h1 hv ht0 h (hvtx e.1)).elim

/-- **An edge of Gamma_except arriving at `Y` gives two adjacent `gamma` sectors at `Y`** whose common ray is `-d`, together with the walk from `X` to `Y`. -/
theorem gexc_arrive_sector (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3)) {Y : Plane}
    (F : ExtFan D.toRegionDissection Y Empty) (s : ℕ → AtV D.toRegionDissection Y) (ℓ : ℕ → Fin 3)
    (hpar : ∀ j, Par (F.p (s (j + 1))) (F.q (s j)))
    (hlab : ∀ j, ∃ k, (D.tile (s j).1).pts k = Y ∧ idx (s j).1 k = ℓ j) (hsurj : ∀ x : AtV D.toRegionDissection Y, ∃ j < 6, s j = x)
    {X : Plane} (h : GExc D idx X Y) :
    ∃ (d : V2) (a : ℕ), d ≠ 0 ∧ NoBack D.toRegionDissection d X ∧ ℓ a = 2 ∧ ℓ (a + 1) = 2 ∧ Par (F.p (s (a + 1))) (neg2 d) ∧
      ∃ (b : Bool) (P : List (Fin N × Plane × Plane)), WalkU D.toRegionDissection b d X Y P ∧ P ≠ [] := by
  obtain ⟨d, Z, L1, L2, H1, H2, hd, hnb, W1, W2, hL1, hL2, -, -, hr1, hr2, hY⟩ := h
  have hvtx : ∀ i, Y ∈ (D.tile i).carrier → ∃ k, (D.tile i).pts k = Y := by
    intro i hi
    obtain ⟨j, -, hj⟩ := hsurj ⟨i, hi⟩
    obtain ⟨k, hk, -⟩ := hlab j
    refine ⟨k, ?_⟩
    have : (s j).1 = i := by rw [hj]
    rw [← this]; exact hk
  have finish : ∀ (el er : Fin N × Plane × Plane), StepU D.toRegionDissection true d el → el.2.2 = Y → GammaHead D idx el →
      StepU D.toRegionDissection false d er → er.2.2 = Y → GammaHead D idx er →
      (∃ (b : Bool) (P : List (Fin N × Plane × Plane)), WalkU D.toRegionDissection b d X Y P ∧ P ≠ []) →
      ∃ (d : V2) (a : ℕ), d ≠ 0 ∧ NoBack D.toRegionDissection d X ∧ ℓ a = 2 ∧ ℓ (a + 1) = 2 ∧ Par (F.p (s (a + 1))) (neg2 d) ∧
        ∃ (b : Bool) (P : List (Fin N × Plane × Plane)), WalkU D.toRegionDissection b d X Y P ∧ P ≠ [] := by
    intro el er hl hlY hlg hr hrY hrg hw
    have hl' : TriStep (D.tile el.1) d el.2.1 Y := by
      have : TriStep (D.tile el.1) d el.2.1 el.2.2 := by simpa [StepU] using hl
      rw [hlY] at this; exact this
    have hr' : TriStep (D.tile er.1) (neg2 d) Y er.2.1 := by
      have : TriStep (D.tile er.1) (neg2 d) er.2.2 er.2.1 := by simpa [StepU] using hr
      rw [hrY] at this; exact this
    obtain ⟨x1, hx1i, hx1q⟩ := sec_end F hl'
    obtain ⟨x2, hx2i, hx2p⟩ := sec_start F hr'
    obtain ⟨a, -, hsa⟩ := hsurj x1
    have hx2 : x2 = s (a + 1) := next_sector F s hpar (j := a) (r := neg2 d) (by rw [hsa]; exact hx1q) hx2p
    have hia : (s a).1 = el.1 := by rw [hsa]; exact hx1i
    have hia1 : (s (a + 1)).1 = er.1 := by rw [← hx2]; exact hx2i
    obtain ⟨k, hk, hk2⟩ := hlg
    obtain ⟨k', hk', hk2'⟩ := hrg
    rw [hlY] at hk
    rw [hrY] at hk'
    refine ⟨d, a, hd, hnb, ?_, ?_, by rw [← hx2]; exact hx2p, hw⟩
    · exact (label_eq hlab (j := a) hia hk).symm.trans hk2
    · exact (label_eq hlab (j := a + 1) hia1 hk').symm.trans hk2'
  obtain ⟨P1, Q1, -, hP1, w1, -, hg1⟩ := grun_split D idx (walkU_of_T W1) hr1
  obtain ⟨P2, Q2, -, hP2, w2, -, hg2⟩ := grun_split D idx (walkU_of_R W2) hr2
  obtain ⟨T1, hT1n, hT1, hT1p, -⟩ := walkU_pos w1
  obtain ⟨T2, hT2n, hT2, hT2p, -⟩ := walkU_pos w2
  have hT1pos := hT1p hP1
  have hT2pos := hT2p hP2
  rcases hY with ⟨rfl, hle⟩ | ⟨rfl, hle⟩
  · obtain ⟨el, hel, hlS, hlY, hlg⟩ := run_head_at D idx hd w1 hg1 hT1 hT1pos hT1 le_rfl hvtx
    obtain ⟨er, her, hrS, hrY, hrg⟩ := run_head_at D idx hd w2 hg2 hT1 hT1pos hT2 (pos_le_of_dist_le hd hT1n hT2n hT1 hT2 hle) hvtx
    exact finish el er hlS hlY hlg hrS hrY hrg ⟨true, P1, w1, hP1⟩
  · obtain ⟨el, hel, hlS, hlY, hlg⟩ := run_head_at D idx hd w1 hg1 hT2 hT2pos hT1 (pos_le_of_dist_le hd hT2n hT1n hT2 hT1 hle) hvtx
    obtain ⟨er, her, hrS, hrY, hrg⟩ := run_head_at D idx hd w2 hg2 hT2 hT2pos hT2 le_rfl hvtx
    exact finish el er hlS hlY hlg hrS hrY hrg ⟨false, P2, w2, hP2⟩

set_option maxHeartbeats 3200000 in
/-- **L2: at most one edge of Gamma_except arrives at a vertex of Gamma_kite.** -/
theorem gexc_arrive_kite_unique [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3)
    (G : AngGen (fun l => D.model.angleAt l)) {Y Z X X' : Plane} (hYZ : GKite D idx Y Z) (hX : GExc D idx X Y) (hX' : GExc D idx X' Y) : X = X' := by
  classical
  obtain ⟨-, ⟨hVint, c0, c1, c2⟩⟩ := gkite_vertex_type D P hreg idx hC.hidxA hC.hregc h1 h3 hYZ
  obtain ⟨F, s, ℓ, hF, hlab, hsurj, hperS⟩ := fan222_tile D idx hC.hidxA hVint c0 c1 c2 G
  have hpar : ∀ j, Par (F.p (s (j + 1))) (F.q (s j)) := fun j => hF.hpar j
  have hmodS := per_mod s hperS
  have hperL : ∀ n, ℓ (n + 6) = ℓ n := by
    intro n
    obtain ⟨k, hk, -⟩ := hlab n
    have hk' : (D.tile (s (n + 6)).1).pts k = Y := by rw [hperS n]; exact hk
    have h1' := label_eq hlab (j := n + 6) rfl hk'
    have h2' := label_eq hlab (j := n) rfl hk
    rw [← h1', ← h2', hperS n]
  have hc2 : ((Finset.range 6).filter (fun i => ℓ i = 2)).card = 2 := by
    have := hF.hcnt 0 2; simpa only [zero_add] using this
  obtain ⟨d, a, hd, hnb, ha1, ha2, hpa, b, Pw, hw, hPw⟩ := gexc_arrive_sector D idx F s ℓ hpar hlab hsurj hX
  obtain ⟨d', a', hd', hnb', ha1', ha2', hpa', b', Pw', hw', hPw'⟩ := gexc_arrive_sector D idx F s ℓ hpar hlab hsurj hX'
  have hmod : a % 6 = a' % 6 := gamma_pair_unique ℓ hperL hc2 ⟨ha1, ha2⟩ ⟨ha1', ha2'⟩
  have hs : s (a' + 1) = s (a + 1) := by rw [hmodS (a' + 1), hmodS (a + 1)]; congr 1; omega
  have hdd : Par (neg2 d') (neg2 d) := by
    rw [hs] at hpa'
    exact hpa'.symm.trans hpa
  have hdd' : Par d' d := par_neg2 hdd
  exact (align_same D.toRegionDissection hd hdd' hw hPw hw' hPw' hnb hnb').symm

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.gexc_arrive_sector
#print axioms Erdos634.Draft.LaczFormal.RG.gexc_arrive_kite_unique

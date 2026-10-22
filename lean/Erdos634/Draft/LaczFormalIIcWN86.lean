-- Draft/LaczFormalIIcWN86.lean -- Laczkovich (DCG 48 (2012), Sect. 6.2, Fig. 5), the FAN LEMMA, forward half: at a vertex `Y` of two consecutive Gamma_kite edges `XY`, `YZ`,
-- a straight line of tile sides through `Y` (`StraightAt D Y`, Fig. 5(A)) forces `Z - Y = Y - X`, i.e. the turn of the chain at `Y` is 0.
-- Route: the six sectors form a `Fan6`; the line gives three consecutive distinct labels (`straight_run_labels`), the `beta beta` block of `XY` and the `alpha alpha` block of `YZ` are then 3 apart (`comb_straight`, WN85)
-- so the rays `YX`, `YZ` are opposite (`straight_of_triple`); the sides have equal length (`hC.hidx`).
-- NOTE, UNAUDITED.  Hypotheses: the Case IIc block of `gkite_vertex_type` plus `AngGen`.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2, Fig. 5), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG12GExcFanA
import Erdos634.Draft.LaczFormalIIcWN85
import Erdos634.Draft.LaczFormalIIcWN28

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

theorem gkite_dist_eq (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) {X Y Z : Plane}
    (hXY : GKite D idx X Y) (hYZ : GKite D idx Y Z) : dist X Y = dist Y Z := by
  obtain ⟨i, j, d, kk, f, kk2, f2, hij, hSi, hSj, hk, hf, hik, hif, hk', hf', hjk, hjf⟩ := hXY
  obtain ⟨i', j', d', kk2a, f2a, kk2', f2', hij2, hSi2, hSj2, hk2, hf2, hik2, hif2, hk2', hf2', hjk2, hjf2⟩ := hYZ
  have e1 := hC.hidx i kk f
  have e2 := hC.hidx i' kk2a f2a
  rw [hk, hf, hik, hif] at e1
  rw [hk2, hf2, hik2, hif2] at e2
  rw [e1, e2]

set_option maxHeartbeats 6400000 in
/-- **Fan lemma, forward**: a straight line of tile sides through `Y` makes the Gamma_kite chain go straight: `Z - Y = Y - X`. -/
theorem gkite_straight_fwd [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3)
    (G : AngGen (fun l => D.model.angleAt l)) {X Y Z : Plane} (hXY : GKite D idx X Y) (hYZ : GKite D idx Y Z) (hS : StraightAt D Y) :
    toV2 (Z - Y) = toV2 (Y - X) := by
  classical
  have hdist := gkite_dist_eq D idx hC hXY hYZ
  obtain ⟨⟨hVint, c0, c1, c2⟩, -⟩ := gkite_vertex_type D P hreg idx hC.hidxA hC.hregc h1 h3 hXY
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
  have hcnt : ∀ l, ((Finset.range 6).filter (fun i => ℓ i = l)).card = 2 := by
    intro l; have := hF.hcnt 0 l; simpa only [zero_add] using this
  -- the head kite XY (beta beta)
  obtain ⟨iB, jB, dB, kkB, fB, kkB', fB', -, hSiB, hSjB, hkB, hfB, hikB, hifB, hkB', hfB', hjkB, hjfB⟩ := hXY
  obtain ⟨yB1, hyB1i, hyB1q⟩ := sec_end F hSiB
  obtain ⟨yB2, hyB2i, hyB2p⟩ := sec_start F hSjB
  obtain ⟨b0, hb0, hsb0⟩ := hsurj yB1
  have hyB2 : yB2 = s (b0 + 1) := next_sector F s hpar (j := b0) (by rw [hsb0]; exact hyB1q) hyB2p
  have hiB : (s b0).1 = iB := by rw [hsb0]; exact hyB1i
  have hjB : (s (b0 + 1)).1 = jB := by rw [← hyB2]; exact hyB2i
  have hlb : ℓ b0 = 1 := by rw [← hifB]; exact (label_eq hlab (j := b0) hiB hfB).symm
  have hlb1 : ℓ (b0 + 1) = 1 := by rw [← hjkB]; exact (label_eq hlab (j := b0 + 1) hjB hkB').symm
  -- the tail kite YZ (alpha alpha)
  obtain ⟨iA, jA, dA, kkA, fA, kkA', fA', -, hSiA, hSjA, hkA, hfA, hikA, hifA, hkA', hfA', hjkA, hjfA⟩ := hYZ
  obtain ⟨yA2, hyA2i, hyA2p⟩ := sec_start F hSiA
  obtain ⟨yA1, hyA1i, hyA1q⟩ := sec_end F hSjA
  obtain ⟨c0', hc0', hsc0⟩ := hsurj yA1
  have hyA2 : yA2 = s (c0' + 1) := next_sector F s hpar (j := c0') (r := dA) (by rw [hsc0]; rw [neg2_neg2'] at hyA1q; exact hyA1q) hyA2p
  have hjA : (s c0').1 = jA := by rw [hsc0]; exact hyA1i
  have hiA : (s (c0' + 1)).1 = iA := by rw [← hyA2]; exact hyA2i
  have hlc : ℓ c0' = 0 := by rw [← hjfA]; exact (label_eq hlab (j := c0') hjA hfA').symm
  have hlc1 : ℓ (c0' + 1) = 0 := by rw [← hikA]; exact (label_eq hlab (j := c0' + 1) hiA hkA).symm
  -- the straight line: a distinct triple
  obtain ⟨d0, A0, B0, W1, i0, j0, i2, hi0, hj0, hi2⟩ := hS
  obtain ⟨x1, hx1i, hx1q⟩ := sec_end F hi0
  obtain ⟨x2, hx2i, hx2p⟩ := sec_start F hj0
  obtain ⟨x3, hx3i, hx3p⟩ := sec_start F hi2
  obtain ⟨a1, -, hsa1⟩ := hsurj x1
  have hx2 : x2 = s (a1 + 1) := next_sector F s hpar (j := a1) (r := neg2 d0) (by rw [hsa1]; exact hx1q) hx2p
  obtain ⟨c3, -, hsc3⟩ := hsurj x3
  have hp2 : Par (F.p (s (a1 + 1))) (neg2 d0) := by rw [← hx2]; exact hx2p
  have hp3 : Par (F.p (s c3)) d0 := by rw [hsc3]; exact hx3p
  have hnegp2 : Par (neg2 (F.p (s (a1 + 1)))) d0 := by
    have := par_neg hp2
    have e : ((-(neg2 d0).1, -(neg2 d0).2) : V2) = d0 := by unfold neg2; ext <;> simp
    rw [e] at this
    exact this
  have hopp : Par (F.p (s c3)) (-(F.p (s (a1 + 1))).1, -(F.p (s (a1 + 1))).2) := hp3.trans hnegp2.symm
  have hd0 : F.p (s (a1 + 1)) ≠ 0 := hF.hu (a1 + 1)
  have htriple : ℓ (a1 + 1) ≠ ℓ (a1 + 1 + 1) ∧ ℓ (a1 + 1) ≠ ℓ (a1 + 1 + 2) ∧ ℓ (a1 + 1 + 1) ≠ ℓ (a1 + 1 + 2) := by
    by_cases hn : c3 % 6 = (a1 + 1) % 6
    · exfalso
      have hs : s c3 = s (a1 + 1) := by rw [hmodS c3, hmodS (a1 + 1), hn]
      rw [hs] at hopp
      exact not_par_neg2 hd0 hopp
    · have hm1 : 1 ≤ (c3 + 6 - (a1 + 1) % 6) % 6 := by omega
      have hm5 : (c3 + 6 - (a1 + 1) % 6) % 6 ≤ 5 := by omega
      have hss : s (a1 + 1 + (c3 + 6 - (a1 + 1) % 6) % 6) = s c3 := by
        rw [hmodS (a1 + 1 + (c3 + 6 - (a1 + 1) % 6) % 6), hmodS c3]; congr 1; omega
      have hstr : Par (F.p (s (a1 + 1 + (c3 + 6 - (a1 + 1) % 6) % 6))) (-(F.p (s (a1 + 1))).1, -(F.p (s (a1 + 1))).2) := by rw [hss]; exact hopp
      obtain ⟨-, t1, t2, t3⟩ := straight_run_labels G hF (a1 + 1) _ hm1 hm5 hstr
      exact ⟨t1, t2, t3⟩
  -- the blocks are 3 apart
  obtain ⟨hcb, hdist3⟩ := comb_straight ℓ hperL (hcnt 0) (hcnt 1) (hcnt 2) ⟨hlb, hlb1⟩ ⟨hlc, hlc1⟩ (a1 + 1) htriple
  have hopp2 : Par (F.p (s (b0 + 1 + 3))) (-(F.p (s (b0 + 1))).1, -(F.p (s (b0 + 1))).2) :=
    straight_of_triple G hF (b0 + 1) (by simpa using hdist3.1) (by simpa using hdist3.2.1) (by simpa using hdist3.2.2)
  have hsZ : s (c0' + 1) = s (b0 + 1 + 3) := by
    rw [hmodS (c0' + 1), hmodS (b0 + 1 + 3)]; congr 1; omega
  have hPB : Par (F.p (s (b0 + 1))) (neg2 dB) := by rw [← hyB2]; exact hyB2p
  have hPA : Par (F.p (s (c0' + 1))) dA := by rw [← hyA2]; exact hyA2p
  have hnB : Par (-(F.p (s (b0 + 1))).1, -(F.p (s (b0 + 1))).2) dB := by
    have := par_neg hPB
    have e : ((-(neg2 dB).1, -(neg2 dB).2) : V2) = dB := by unfold neg2; ext <;> simp
    rw [e] at this; exact this
  have hAB : Par dA dB := by
    rw [hsZ] at hPA
    exact (hPA.symm.trans hopp2).trans hnB
  have hZ : Par (toV2 (Z - Y)) dA := by
    obtain ⟨-, -, -, -, -, -, -, -, hp, -⟩ := hSiA; exact hp
  have hYX : Par (toV2 (Y - X)) dB := by
    obtain ⟨-, -, -, -, -, -, -, -, hp, -⟩ := hSiB; exact hp
  have hpp : Par (toV2 (Z - Y)) (toV2 (Y - X)) := (hZ.trans hAB).trans hYX.symm
  apply eq_of_par_nsq hpp
  rw [nsq_toV2, nsq_toV2, dist_comm Z Y, dist_comm Y X]
  exact congrArg (· ^ 2) hdist.symm

#print axioms gkite_straight_fwd

end Erdos634.Draft.LaczFormal.RG

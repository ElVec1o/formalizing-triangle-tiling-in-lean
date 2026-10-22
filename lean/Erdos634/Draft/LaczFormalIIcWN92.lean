-- Draft/LaczFormalIIcWN92.lean -- Laczkovich (DCG 48 (2012), Sect. 6.2/6.3, Fig. 5), R2: the DIRECTION in which an edge of Gamma_except ARRIVES at a vertex of Gamma_kite.
-- `comb_pairs`: three adjacent pairs `beta beta`, `alpha alpha`, `gamma gamma` of a period-6 label sequence (two of each) are in the cyclic order (bb, aa, gg) or (bb, gg, aa).
-- `gexc_arrive_dir`: if an edge `U -> Y` of Gamma_except arrives at `Y`, where `XY`, `YZ` are consecutive Gamma_kite edges, then the ray `Y -> U` is the bisector of the two `gamma` sectors:
--   (case A) `Z - Y = rot (a+b) (X - Y)` and `U - Y` is a positive multiple of `-rot a (X - Y)`; or (case B) `X - Y = rot (a+b) (Z - Y)` and `U - Y` is a positive multiple of `-rot b (Z - Y)`  (`a = alpha`, `b = beta`).
-- NOTE, UNAUDITED.  Hypotheses: the Case IIc block + AngGen.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2, Fig. 5), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN88
import Erdos634.Draft.LaczFormalRG12GExcArrive

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

set_option synthInstance.maxSize 40000 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem comb_pairs_fin : ∀ a0 a1 a2 a3 a4 a5 : Fin 3,
    (((Finset.range 6).filter (fun i => gF a0 a1 a2 a3 a4 a5 i = 0)).card = 2 ∧
    ((Finset.range 6).filter (fun i => gF a0 a1 a2 a3 a4 a5 i = 1)).card = 2 ∧
    ((Finset.range 6).filter (fun i => gF a0 a1 a2 a3 a4 a5 i = 2)).card = 2) →
    ∀ b < 6, ∀ c < 6, ∀ e < 6,
    (gF a0 a1 a2 a3 a4 a5 b = 1 ∧ gF a0 a1 a2 a3 a4 a5 (b + 1) = 1 ∧ gF a0 a1 a2 a3 a4 a5 c = 0 ∧ gF a0 a1 a2 a3 a4 a5 (c + 1) = 0 ∧
    gF a0 a1 a2 a3 a4 a5 e = 2 ∧ gF a0 a1 a2 a3 a4 a5 (e + 1) = 2) →
    (c = (b + 2) % 6 ∧ e = (b + 4) % 6) ∨ (c = (b + 4) % 6 ∧ e = (b + 2) % 6) := by
  decide +kernel

theorem comb_pairs (ℓ : ℕ → Fin 3) (hper : ∀ n, ℓ (n + 6) = ℓ n) (h0 : ((Finset.range 6).filter (fun i => ℓ i = 0)).card = 2)
    (h1 : ((Finset.range 6).filter (fun i => ℓ i = 1)).card = 2) (h2 : ((Finset.range 6).filter (fun i => ℓ i = 2)).card = 2) {b c e : ℕ}
    (hb1 : ℓ b = 1 ∧ ℓ (b + 1) = 1) (hc1 : ℓ c = 0 ∧ ℓ (c + 1) = 0) (he1 : ℓ e = 2 ∧ ℓ (e + 1) = 2) :
    (c % 6 = (b + 2) % 6 ∧ e % 6 = (b + 4) % 6) ∨ (c % 6 = (b + 4) % 6 ∧ e % 6 = (b + 2) % 6) := by
  have hm := per_mod ℓ hper
  have hk : ∀ k (hk : k < 6), (![ℓ 0, ℓ 1, ℓ 2, ℓ 3, ℓ 4, ℓ 5] : Fin 6 → Fin 3) ⟨k, hk⟩ = ℓ k := by
    intro k hk; interval_cases k <;> rfl
  have hg : ∀ n, gF (ℓ 0) (ℓ 1) (ℓ 2) (ℓ 3) (ℓ 4) (ℓ 5) n = ℓ n := by
    intro n
    rw [hm n]
    exact hk (n % 6) (Nat.mod_lt _ (by norm_num))
  have key := comb_pairs_fin (ℓ 0) (ℓ 1) (ℓ 2) (ℓ 3) (ℓ 4) (ℓ 5)
  simp only [hg] at key
  have sh : ∀ n k : ℕ, ℓ (n % 6 + k) = ℓ (n + k) := fun n k => by rw [hm (n % 6 + k), hm (n + k)]; congr 1; omega
  have s0 : ∀ n : ℕ, ℓ (n % 6) = ℓ n := fun n => (hm n).symm
  have := key ⟨h0, h1, h2⟩ (b % 6) (Nat.mod_lt _ (by norm_num)) (c % 6) (Nat.mod_lt _ (by norm_num)) (e % 6) (Nat.mod_lt _ (by norm_num))
    ⟨(by rw [s0]; exact hb1.1), (by rw [sh]; exact hb1.2), (by rw [s0]; exact hc1.1), (by rw [sh]; exact hc1.2),
      (by rw [s0]; exact he1.1), (by rw [sh]; exact he1.2)⟩
  omega

theorem neg2_ne_zero' {v : V2} (hv : v ≠ 0) : neg2 v ≠ 0 := by
  intro h
  apply hv
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [neg2] at h1 h2
  exact Prod.ext (by simpa using h1) (by simpa using h2)

set_option maxHeartbeats 6400000 in
/-- **Direction of arrival of an edge of Gamma_except at a vertex of Gamma_kite.** -/
theorem gexc_arrive_dir [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3)
    (G : AngGen (fun l => D.model.angleAt l)) {X Y Z U : Plane} (hXY : GKite D idx X Y) (hYZ : GKite D idx Y Z) (hU : GExc D idx U Y) :
    (toV2 (Z - Y) = Graph.rot (D.model.angleAt 0 + D.model.angleAt 1) (toV2 (X - Y)) ∧
      Par (toV2 (U - Y)) (neg2 (Graph.rot (D.model.angleAt 0) (toV2 (X - Y))))) ∨
    (toV2 (X - Y) = Graph.rot (D.model.angleAt 0 + D.model.angleAt 1) (toV2 (Z - Y)) ∧
      Par (toV2 (U - Y)) (neg2 (Graph.rot (D.model.angleAt 1) (toV2 (Z - Y))))) := by
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
  have hmodL := per_mod ℓ hperL
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
  -- the arriving edge: two adjacent gamma sectors
  obtain ⟨d, a, hd, hnb, ha1, ha2, hpa, b, Pw, hW, hPne⟩ := gexc_arrive_sector D idx F s ℓ hpar hlab hsurj hU
  obtain ⟨T, hT0, hT, hTpos, -⟩ := walkU_pos hW
  have hTp := hTpos hPne
  have hUY : Par (toV2 (U - Y)) (neg2 d) := by
    have h0 : Y 0 - U 0 = T * d.1 := congrArg Prod.fst hT
    have h1' : Y 1 - U 1 = T * d.2 := congrArg Prod.snd hT
    have e : toV2 (U - Y) = (T * (neg2 d).1, T * (neg2 d).2) := by
      unfold toV2 neg2
      ext <;> simp <;> linarith
    rw [e]
    exact par_smul_pos hTp (par_refl (neg2_ne_zero' hd))
  have hgpar : Par (toV2 (U - Y)) (F.p (s (a + 1))) := hUY.trans hpa.symm
  -- rotations along runs
  have rv : ∀ j m, Par (F.p (s (j + m))) (Graph.rot (∑ i ∈ Finset.range m, wd (F.p (s (j + i))) (F.q (s (j + i)))) (F.p (s j))) := by
    intro j m
    have := run_rotation (fun i => F.p (s (j + i))) (fun i => F.q (s (j + i))) (fun i => hF.hu (j + i)) (fun i => by
      have := hF.hpar (j + i); simpa [add_assoc] using this) m
    simpa using this
  have hwdl : ∀ i, wd (F.p (s i)) (F.q (s i)) = D.model.angleAt (ℓ i) := fun i => hF.hwd i
  have hXu : Par (F.p (s (b0 + 1))) (toV2 (X - Y)) := by
    have e1 : Par (F.p yB2) (neg2 dB) := hyB2p
    rw [hyB2] at e1
    have hYX : Par (toV2 (Y - X)) dB := by obtain ⟨-, -, -, -, -, -, -, -, hp, -⟩ := hSiB; exact hp
    exact e1.trans (par_neg_arm hYX).symm
  have hZu : Par (F.p (s (c0' + 1))) (toV2 (Z - Y)) := by
    have e1 : Par (F.p yA2) dA := hyA2p
    rw [hyA2] at e1
    have hZY : Par (toV2 (Z - Y)) dA := by obtain ⟨-, -, -, -, -, -, -, -, hp, -⟩ := hSiA; exact hp
    exact e1.trans hZY.symm
  have hnorm : nsq (toV2 (Z - Y)) = nsq (toV2 (X - Y)) := by
    rw [nsq_toV2, nsq_toV2, dist_comm Z Y]; exact (congrArg (· ^ 2) hdist).symm
  have hsum : ∀ j, ∑ i ∈ Finset.range 4, wd (F.p (s (j + i))) (F.q (s (j + i))) =
      D.model.angleAt (ℓ j) + D.model.angleAt (ℓ (j + 1)) + D.model.angleAt (ℓ (j + 2)) + D.model.angleAt (ℓ (j + 3)) := by
    intro j
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    simp only [zero_add, add_zero, hwdl]
  have hs := G.sum
  have hpi : D.model.angleAt 0 + D.model.angleAt 1 + D.model.angleAt 2 = Real.pi := G.sum
  rcases comb_pairs ℓ hperL (hcnt 0) (hcnt 1) (hcnt 2) ⟨hlb, hlb1⟩ ⟨hlc, hlc1⟩ ⟨ha1, ha2⟩ with ⟨hc, he⟩ | ⟨hc, he⟩
  · -- case A: alpha block 2 after the beta block, gamma block 4 after
    left
    have hs1 : s (c0' + 1) = s (b0 + 1 + 2) := by rw [hmodS (c0' + 1), hmodS (b0 + 1 + 2)]; congr 1; omega
    have hlc' : ℓ (b0 + 1 + 1) = 0 := by rw [hmodL (b0 + 1 + 1), show (b0 + 1 + 1) % 6 = c0' % 6 by omega, ← hmodL]; exact hlc
    have hlc'' : ℓ (b0 + 1 + 2) = 0 := by rw [hmodL (b0 + 1 + 2), show (b0 + 1 + 2) % 6 = (c0' + 1) % 6 by omega, ← hmodL]; exact hlc1
    have hla : ℓ (b0 + 1 + 3) = 2 := by rw [hmodL (b0 + 1 + 3), show (b0 + 1 + 3) % 6 = a % 6 by omega, ← hmodL]; exact ha1
    have h2 := rv (b0 + 1) 2
    have hsa : s (a + 1) = s (b0 + 1 + 4) := by rw [hmodS (a + 1), hmodS (b0 + 1 + 4)]; congr 1; omega
    have h4 := rv (b0 + 1) 4
    rw [hsum, hlb1, hlc', hlc'', hla, ← hsa] at h4
    have hang : D.model.angleAt 1 + D.model.angleAt 0 + D.model.angleAt 0 + D.model.angleAt 2 = Real.pi + D.model.angleAt 0 := by linarith
    rw [hang] at h4
    refine ⟨?_, ?_⟩
    · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero] at h2
      have hs2 : s (b0 + 1 + 2) = s (c0' + 1) := hs1.symm
      rw [hs2] at h2
      simp only [zero_add, add_zero, hwdl, hlb1, hlc'] at h2
      have h2' : Par (toV2 (Z - Y)) (Graph.rot (D.model.angleAt 1 + D.model.angleAt 0) (toV2 (X - Y))) :=
        hZu.symm.trans (h2.trans (par_rot _ hXu))
      have hrr := eq_of_par_nsq h2' (by rw [nsq_rot]; exact hnorm)
      rw [hrr, add_comm]
    · -- U - Y parallel to -(rot a (X - Y))
      have hg : Par (F.p (s (a + 1))) (Graph.rot (Real.pi + D.model.angleAt 0) (toV2 (X - Y))) := h4.trans (par_rot _ hXu)
      have hneg : Par (Graph.rot (Real.pi + D.model.angleAt 0) (toV2 (X - Y))) (neg2 (Graph.rot (D.model.angleAt 0) (toV2 (X - Y)))) := by
        have hr : Graph.rot (Real.pi + D.model.angleAt 0) (toV2 (X - Y)) = neg2 (Graph.rot (D.model.angleAt 0) (toV2 (X - Y))) := by
          unfold Graph.rot neg2
          rw [Real.cos_add, Real.sin_add, Real.cos_pi, Real.sin_pi]
          ext <;> simp <;> ring
        rw [hr]
        exact par_refl (neg2_ne_zero' (rot_ne_zero (D.model.angleAt 0) hXu.ne_right))
      exact (hgpar.trans hg).trans hneg
  · -- case B
    right
    have hs1 : s (b0 + 1) = s (c0' + 1 + 2) := by rw [hmodS (b0 + 1), hmodS (c0' + 1 + 2)]; congr 1; omega
    have hlb' : ℓ (c0' + 1 + 1) = 1 := by rw [hmodL (c0' + 1 + 1), show (c0' + 1 + 1) % 6 = b0 % 6 by omega, ← hmodL]; exact hlb
    have hlb'' : ℓ (c0' + 1 + 2) = 1 := by rw [hmodL (c0' + 1 + 2), show (c0' + 1 + 2) % 6 = (b0 + 1) % 6 by omega, ← hmodL]; exact hlb1
    have hla : ℓ (c0' + 1 + 3) = 2 := by rw [hmodL (c0' + 1 + 3), show (c0' + 1 + 3) % 6 = a % 6 by omega, ← hmodL]; exact ha1
    have hsa : s (a + 1) = s (c0' + 1 + 4) := by rw [hmodS (a + 1), hmodS (c0' + 1 + 4)]; congr 1; omega
    have h4 := rv (c0' + 1) 4
    rw [hsum, hlc1, hlb', hlb'', hla, ← hsa] at h4
    have hang : D.model.angleAt 0 + D.model.angleAt 1 + D.model.angleAt 1 + D.model.angleAt 2 = Real.pi + D.model.angleAt 1 := by linarith
    rw [hang] at h4
    refine ⟨?_, ?_⟩
    · have h2 := rv (c0' + 1) 2
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero] at h2
      rw [← hs1] at h2
      simp only [zero_add, add_zero, hwdl, hlc1, hlb'] at h2
      have h2' : Par (toV2 (X - Y)) (Graph.rot (D.model.angleAt 0 + D.model.angleAt 1) (toV2 (Z - Y))) :=
        hXu.symm.trans (h2.trans (par_rot _ hZu))
      exact eq_of_par_nsq h2' (by rw [nsq_rot]; exact hnorm.symm)
    · have hg : Par (F.p (s (a + 1))) (Graph.rot (Real.pi + D.model.angleAt 1) (toV2 (Z - Y))) := h4.trans (par_rot _ hZu)
      have hneg : Par (Graph.rot (Real.pi + D.model.angleAt 1) (toV2 (Z - Y))) (neg2 (Graph.rot (D.model.angleAt 1) (toV2 (Z - Y)))) := by
        have hr : Graph.rot (Real.pi + D.model.angleAt 1) (toV2 (Z - Y)) = neg2 (Graph.rot (D.model.angleAt 1) (toV2 (Z - Y))) := by
          unfold Graph.rot neg2
          rw [Real.cos_add, Real.sin_add, Real.cos_pi, Real.sin_pi]
          ext <;> simp <;> ring
        rw [hr]
        exact par_refl (neg2_ne_zero' (rot_ne_zero (D.model.angleAt 1) hZu.ne_right))
      exact (hgpar.trans hg).trans hneg

#print axioms gexc_arrive_dir

end Erdos634.Draft.LaczFormal.RG

-- Draft/LaczFormalIIcG11e.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.3 / Thm 2.1 (v): the printed inequality G11, two exceptional points (`g11_two`).
-- Under the hypotheses of `lemma63_two` (Case IIc block, kiteB = empty, two values of W): with (a, b) the labels of `spokes_angle`, s0 the start of the E-group and r = sin(angle a)/sin(angle b),
--   the sides s0, s0+1, .. are geometric of ratio r (n + 2 < k), and either r^(k-1) side(s0) <= side(s0+k-1)  or  side(s0) <= r side(s0+k-1)    [log spiral `g11_core` + `spokes_disjoint` (L8t)].
-- The second alternative is the printed inequality for the REVERSED reading (ratio 1/r), the first for the forward reading: see G11f for the translation to `Concl5`.
-- NOTE, UNAUDITED.  CONDITIONAL on `kiteB = empty` and on the Case IIc hypothesis block (witnessed by GenWitK (204-tile octagon, genTiling_thm21) and IsoWitM).  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3, Fig. 9), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcL8ab
import Erdos634.Draft.LaczFormalIIcG11c
import Erdos634.Draft.LaczFormalIIcG11d

open scoped Classical Fin.NatCast
open EuclideanGeometry Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

set_option maxHeartbeats 25600000 in
theorem g11_two {k : ℕ} [NeZero (2 * k)] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly (2 * k)) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (G : AngGen (fun l => D.model.angleAt l))
    (hcor : ∀ j : Fin (2 * k), cnt D idx (P.v j) 0 = 1 ∧ cnt D idx (P.v j) 1 = 1 ∧ cnt D idx (P.v j) 2 = 0)
    (hNK : kiteB D idx = ∅) (W : Fin (2 * k) → Plane) (hW : ∀ j, GExc D idx (P.v j) (W j)) (hdiff : ∃ j, W j ≠ W 0) :
    ∃ (a b : Fin 3) (s0 : Fin (2 * k)), ((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0)) ∧
      (∀ n : ℕ, n + 2 < k → P.side (s0 + ((n + 1 : ℕ) : Fin (2 * k))) * Real.sin (D.model.angleAt b) = Real.sin (D.model.angleAt a) * P.side (s0 + ((n : ℕ) : Fin (2 * k)))) ∧
      ((Real.sin (D.model.angleAt a) / Real.sin (D.model.angleAt b)) ^ (k - 1) * P.side s0 ≤ P.side (s0 + ((k - 1 : ℕ) : Fin (2 * k))) ∨
        P.side s0 ≤ (Real.sin (D.model.angleAt a) / Real.sin (D.model.angleAt b)) * P.side (s0 + ((k - 1 : ℕ) : Fin (2 * k)))) := by
  classical
  obtain ⟨E, F, hEF, hI⟩ := index_split D P hreg idx hC hab hac h1 h3 G hcor hNK W hW hdiff
  obtain ⟨hang, hMγ⟩ := corner_angles_gamma D P hreg idx hC h1 h3 hcor
  have hk4 := k_ge_four (model_angle_pos' D 2) h1 h3 hMγ
  have hWex : ∀ j, W j ∈ excVerts2 D idx P := by
    intro j
    rcases gexc_end_cls D P hreg idx hC hab hac h1 h3 G hcor (hW j) with h | h
    · rw [hNK] at h; exact absurd h (Finset.notMem_empty _)
    · exact h
  have hint : ∀ E ∈ excVerts2 D idx P, E ∈ interior D.region := fun E hE =>
    (gexc_exc_interior_exact D P hreg idx hC hab hac h1 h3 G hcor E hE).1
  have hsymm := central_symmetry_two_exc D P hreg idx hC hab hac h1 h3 G hcor hNK W hW hdiff
  obtain ⟨a, b, hab', hsp⟩ := spokes_angle D P hreg idx hC h1 h3 hcor hint W hW
  obtain ⟨s0, hs0⟩ := hI
  have hpi := Real.pi_pos
  have hkγ : (k : ℝ) * D.model.angleAt 2 = Real.pi := by
    have : ((2 * k : ℕ) : ℝ) * D.model.angleAt 2 = 2 * Real.pi := hMγ
    push_cast at this; linarith
  have hγ0 := model_angle_pos' D 2
  have hαβγ : D.model.angleAt a + D.model.angleAt b + D.model.angleAt 2 = Real.pi := by
    have := angleAt_sum D.model
    rcases hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact this
    · linarith
  obtain ⟨m, hm⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  refine ⟨a, b, s0, hab', ?_⟩
  set ι : ℕ → Fin (2 * k) := fun n => (n : Fin (2 * k)) + s0 with hιdef
  have hι : ∀ n, ι (n + 1) = ι n + 1 := by
    intro n; simp only [hιdef]; rw [Nat.cast_succ, add_right_comm]
  have hι2 : ∀ n, ι (n + 2) = ι n + 2 := by
    intro n
    have h := hι (n + 1); rw [hι n] at h
    show ι (n + 1 + 1) = _
    rw [h, add_assoc, one_add_one_eq_two]
  set V : ℕ → Plane := fun n => P.v (ι n) with hV
  have hV1 : ∀ n, V (n + 1) = P.v (ι n + 1) := fun n => by simp only [hV]; rw [hι n]
  have hV2 : ∀ n, V (n + 2) = P.v (ι n + 2) := fun n => by simp only [hV]; rw [hι2 n]
  have hval : ∀ n, n < 2 * k → ((ι n - s0).val = n) := by
    intro n hn
    simp only [hιdef, add_sub_cancel_right]
    rw [Fin.val_natCast]; exact Nat.mod_eq_of_lt hn
  have hWE : ∀ n, n < k → W (ι n) = E := fun n hn => (hs0 (ι n)).1 (by rw [hval n (by omega)]; exact hn)
  have hWF : ∀ n, k ≤ n → n < 2 * k → W (ι n) = F := fun n h1 h2 => (hs0 (ι n)).2 (by rw [hval n h2]; exact h1)
  have hcr : ∀ n, 0 < cross2 (V (n + 1) - V n) (V (n + 2) - V (n + 1)) := by
    intro n
    have hf := ConvPoly.fin_facts P.three_le (ι n)
    have := P.left (ι n) (ι n + 2) hf.2.1 hf.2.2.1
    rw [hV1 n, hV2 n, cross2_shift]
    exact this
  have hang' : ∀ n, ∠ (V n) (V (n + 1)) (V (n + 2)) = Real.pi - D.model.angleAt 2 := by
    intro n
    have := hang (ι n + 1)
    unfold ConvPoly.angle cornerAngle at this
    rw [add_sub_cancel_right] at this
    have hf := ConvPoly.fin_facts P.three_le (ι n)
    rw [hf.2.2.2.2.2] at this
    rw [hV1 n, hV2 n]
    exact this
  have hEa : ∀ n, n < k → ∠ (V (n + 1)) (V n) E = D.model.angleAt a := by
    intro n hn
    have := (hsp (ι n - 1)).1
    rw [sub_add_cancel] at this
    rw [hWE n hn] at this
    rw [hV1 n]
    exact this
  have hEb : ∀ n, n + 1 < k → ∠ (V n) (V (n + 1)) E = D.model.angleAt b := by
    intro n hn
    have := (hsp (ι n)).2
    have hw : W (ι n + 1) = E := by rw [← hι n]; exact hWE (n + 1) hn
    rw [hw] at this
    rw [hV1 n]
    exact this
  have hFa : ∀ n, k ≤ n → n < 2 * k → ∠ (V (n + 1)) (V n) F = D.model.angleAt a := by
    intro n h1 h2
    have := (hsp (ι n - 1)).1
    rw [sub_add_cancel] at this
    rw [hWF n h1 h2] at this
    rw [hV1 n]
    exact this
  have hFb : ∀ n, k ≤ n → n + 1 < 2 * k → ∠ (V n) (V (n + 1)) F = D.model.angleAt b := by
    intro n h1 h2
    have := (hsp (ι n)).2
    have hw : W (ι n + 1) = F := by rw [← hι n]; exact hWF (n + 1) (by omega) h2
    rw [hw] at this
    rw [hV1 n]
    exact this
  -- exceptional points
  have hEmem : E ∈ excVerts2 D idx P := by have := hWex (ι 0); rwa [hWE 0 (by omega)] at this
  have hFmem : F ∈ excVerts2 D idx P := by have := hWex (ι k); rwa [hWF k le_rfl (by omega)] at this
  have hEint : E ∈ interior P.carrier := by have := hint E hEmem; rwa [hreg] at this
  have hFint : F ∈ interior P.carrier := by have := hint F hFmem; rwa [hreg] at this
  have hEl : ∀ n, n + 1 < k → 0 < cross2 (V (n + 1) - V n) (E - V n) := by
    intro n hn
    have := c_pos_of_interior P hEint (ι n)
    unfold ConvPoly.c ConvPoly.e at this
    rw [hV1 n]; exact this
  have hFl : 0 < cross2 (V (k + 1) - V k) (F - V k) := by
    have := c_pos_of_interior P hFint (ι k)
    unfold ConvPoly.c ConvPoly.e at this
    rw [hV1 k]; exact this
  -- sides
  have hne : ∀ n, V n ≠ V (n + 1) := by
    intro n h
    rw [hV1 n] at h
    have := vtx_inj' P h
    exact (ConvPoly.fin_facts P.three_le (ι n)).1 this.symm
  have hside : ∀ j : ℕ, P.side (s0 + (j : Fin (2 * k))) = dist (V j) (V (j + 1)) := by
    intro j
    have : s0 + (j : Fin (2 * k)) = ι j := add_comm _ _
    rw [this]
    unfold ConvPoly.side
    rw [hV1 j]
  have hsa : 0 < Real.sin (D.model.angleAt a) := Real.sin_pos_of_pos_of_lt_pi (model_angle_pos' D a) (by linarith [model_angle_pos' D b])
  refine ⟨?_, ?_⟩
  · intro n hn
    have key := sine_ratio_step (A := V n) (B := V (n + 1)) (C := V (n + 2)) (E := E) (model_angle_pos' D a) (model_angle_pos' D b) (by linarith)
      (hne n) (hne (n + 1)) (hEa n (by omega)) (hEb n (by omega)) (hEa (n + 1) (by omega)) (hEb (n + 1) (by omega))
    rw [hside (n + 1), hside n]
    exact key
  · have h0 : P.side s0 = dist (V 0) (V (0 + 1)) := by simpa using hside 0
    have hsym : dist (V (m + 1)) (V (m + 1 + 1)) = dist (V 0) (V (0 + 1)) := by
      have e : dist (V k) (V (k + 1)) = dist (V 0) (V (0 + 1)) := by
        rw [← hside k, ← h0]; exact (hsymm s0).symm
      have hk : m + 1 = k := hm.symm
      rw [hk]; exact e
    have hk1 : k - 1 = m := by omega
    have core := g11_core (m := m) (by omega) V E F (D.model.angleAt a) (D.model.angleAt b) (D.model.angleAt 2) hcr hang'
      (model_angle_pos' D a) (model_angle_pos' D b) hαβγ hγ0 (by rw [← hm]; exact hkγ)
      (fun n hn => hEa n (by omega)) (fun n hn => hEb n (by omega)) (fun n hn => hEl n (by omega))
      (by have := hFa k le_rfl (by omega); rw [hm] at this; exact this)
      (by have := hFb k le_rfl (by omega); rw [hm] at this; exact this)
      (by have := hFl; rw [hm] at this; exact this) hsym
    rcases core with c1 | c2 | ⟨X, hX1, hX2⟩
    · left
      rw [hk1, h0, hside m]; exact c1
    · right
      rw [hk1, h0, hside m]; exact c2
    · exfalso
      have hi : GExc D idx (P.v (ι m)) E := by
        have := hW (ι m); rwa [hWE m (by omega)] at this
      have hl : GExc D idx (P.v (ι (m + 1))) F := by
        have := hW (ι (m + 1)); rwa [hWF (m + 1) (by omega) (by omega)] at this
      have hil : ι m ≠ ι (m + 1) := by
        rw [hι m]; exact (ConvPoly.fin_facts P.three_le (ι m)).1.symm
      exact spokes_disjoint D P hreg idx hC hab hac h1 h3 G hcor hEmem hFmem hEF hil hi hl X hX1 hX2

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.g11_two

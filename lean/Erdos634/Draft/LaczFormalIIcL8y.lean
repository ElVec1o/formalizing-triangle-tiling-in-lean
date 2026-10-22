-- Draft/LaczFormalIIcL8y.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.3, two exceptional points: the GEOMETRIC SIDES of the E-group (law of sines in the spoke triangles, `sine_ratio_step`):
-- with the index split of `index_split` (first k corners to E), `side (s0 + n + 1) * sin beta_b = sin alpha_a * side (s0 + n)` for `n + 2 < k`, where (a, b) = (0,1) or (1,0) are the labels of `spokes_angle`.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3, (18)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcL8x

open scoped Classical Fin.NatCast
open EuclideanGeometry Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

set_option maxHeartbeats 12800000 in
theorem geometric_sides_of_spokes {k : ℕ} [NeZero (2 * k)] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly (2 * k)) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3)
    (hcor : ∀ j : Fin (2 * k), cnt D idx (P.v j) 0 = 1 ∧ cnt D idx (P.v j) 1 = 1 ∧ cnt D idx (P.v j) 2 = 0) (hk : 3 ≤ k)
    (hint : ∀ E ∈ excVerts2 D idx P, E ∈ interior D.region) (W : Fin (2 * k) → Plane) (hW : ∀ j, GExc D idx (P.v j) (W j)) (E F : Plane)
    (hI : ∃ s0 : Fin (2 * k), ∀ i : Fin (2 * k), ((i - s0).val < k → W i = E) ∧ (k ≤ (i - s0).val → W i = F)) :
    ∃ a b : Fin 3, ((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0)) ∧ ∃ s0 : Fin (2 * k), ∀ n : ℕ, n + 2 < k →
      P.side (s0 + ((n + 1 : ℕ) : Fin (2 * k))) * Real.sin (D.model.angleAt b) = Real.sin (D.model.angleAt a) * P.side (s0 + ((n : ℕ) : Fin (2 * k))) := by
  obtain ⟨a, b, hab, hsp⟩ := spokes_angle D P hreg idx hC h1 h3 hcor hint W hW
  obtain ⟨hang, hMγ⟩ := corner_angles_gamma D P hreg idx hC h1 h3 hcor
  obtain ⟨s0, hs0⟩ := hI
  have hpi := Real.pi_pos
  have hkγ : (k : ℝ) * D.model.angleAt 2 = Real.pi := by
    have : ((2 * k : ℕ) : ℝ) * D.model.angleAt 2 = 2 * Real.pi := hMγ
    push_cast at this; linarith
  have hγ0 := model_angle_pos' D 2
  have hαβγ : D.model.angleAt a + D.model.angleAt b + D.model.angleAt 2 = Real.pi := by
    have := angleAt_sum D.model
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact this
    · linarith
  refine ⟨a, b, hab, s0, fun n hn => ?_⟩
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
  have hne : ∀ n, V n ≠ V (n + 1) := by
    intro n h
    rw [hV1 n] at h
    have := vtx_inj' P h
    exact (ConvPoly.fin_facts P.three_le (ι n)).1 this.symm
  have hsα : 0 < Real.sin (D.model.angleAt a) := Real.sin_pos_of_pos_of_lt_pi (model_angle_pos' D a) (by linarith [model_angle_pos' D b])
  have key := sine_ratio_step (A := V n) (B := V (n + 1)) (C := V (n + 2)) (E := E) (model_angle_pos' D a) (model_angle_pos' D b) (by linarith)
    (hne n) (hne (n + 1)) (hEa n (by omega)) (hEb n (by omega)) (hEa (n + 1) (by omega)) (hEb (n + 1) (by omega))
  have hside : ∀ m : ℕ, P.side (s0 + (m : Fin (2 * k))) = dist (V m) (V (m + 1)) := by
    intro m
    have : s0 + (m : Fin (2 * k)) = ι m := add_comm _ _
    rw [this]
    unfold ConvPoly.side
    rw [hV1 m]
  rw [hside (n + 1), hside n]
  exact key

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.geometric_sides_of_spokes

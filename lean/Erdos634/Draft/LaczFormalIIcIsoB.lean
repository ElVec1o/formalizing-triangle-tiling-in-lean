-- Draft/LaczFormalIIcIsoB.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2, Case IIc with alpha = beta: straight lines through a (2,2,2) vertex.
-- `straight_run_labels_iso` : for the isosceles model (`omega 0 = omega 1`) a straight line through the vertex along tile sides gives `m = 3` and a run of three sectors containing the label 2 (gamma) exactly once.
-- `straight_of_run_iso`     : conversely, three consecutive sectors with exactly one gamma give a straight line (alpha + alpha + gamma = pi).
-- Parallel to `straight_run_labels`/`straight_of_triple` (RG12Fan222), which are NOT edited.  NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcIsoA

open Erdos634.Draft.LaczFormal.Graph

namespace Erdos634.Draft.LaczFormal.RG

theorem fan6_turn_iso {ω : Fin 3 → ℝ} (G : AngGen' ω) {u v : ℕ → V2} {ℓ : ℕ → Fin 3} (F : Fan6 ω u v ℓ) (j : ℕ) :
    ∑ i ∈ Finset.range 6, wd (u (j + i)) (v (j + i)) = 2 * Real.pi := by
  rw [F.run_sum, Fin.sum_univ_three]
  simp only [F.hcnt]
  push_cast
  linarith [G.sum]

/-- **Straight line through a (2,2,2) vertex, isosceles model**: `m = 3` and exactly one of the three corners has label 2. -/
theorem straight_run_labels_iso {ω : Fin 3 → ℝ} (G : AngGen' ω) (h01 : ω 0 = ω 1) {u v : ℕ → V2} {ℓ : ℕ → Fin 3} (F : Fan6 ω u v ℓ) (j m : ℕ)
    (hm1 : 1 ≤ m) (hm5 : m ≤ 5) (hstr : Par (u (j + m)) (-(u j).1, -(u j).2)) :
    m = 3 ∧ ((Finset.range 3).filter (fun i => ℓ (j + i) = 2)).card = 1 := by
  classical
  have hrot := run_rotation (fun i => u (j + i)) (fun i => v (j + i)) (fun i => F.hu _) (fun i => by
    have := F.hpar (j + i); simpa [add_assoc] using this) m
  simp only [add_zero] at hrot
  have hP : Par (rot (∑ i ∈ Finset.range m, wd (u (j + i)) (v (j + i))) (u j)) (-(u j).1, -(u j).2) := (hrot.symm).trans hstr
  obtain ⟨z, hz⟩ := (par_rot_neg_iff _ (F.hu j)).1 hP
  set S := ∑ i ∈ Finset.range m, wd (u (j + i)) (v (j + i)) with hS
  have hpos : ∀ i, 0 < wd (u (j + i)) (v (j + i)) := fun i => by rw [F.hwd]; exact G.pos _
  have hS0 : 0 < S := Finset.sum_pos (fun i _ => hpos i) (Finset.nonempty_range_iff.mpr (by omega))
  have hS6 : S < 2 * Real.pi := by
    rw [← fan6_turn_iso G F j]
    exact Finset.sum_lt_sum_of_subset (Finset.range_subset_range.mpr (by omega : m ≤ 6)) (Finset.mem_range.mpr (show m < 6 by omega))
      (by simp) (hpos m) (fun i _ _ => (hpos i).le)
  have hpi := Real.pi_pos
  have hz0 : z = 0 := by
    have h1 : (-1 : ℝ) < 2 * z := by nlinarith
    have h2 : (2 * z : ℝ) < 1 := by nlinarith
    have h1' : (-1 : ℤ) < 2 * z := by exact_mod_cast h1
    have h2' : 2 * z < (1 : ℤ) := by exact_mod_cast h2
    omega
  have hSpi : S = Real.pi := by rw [hz, hz0]; simp
  rw [hS, F.run_sum, Fin.sum_univ_three] at hSpi
  have hle : ∀ l, ((Finset.range m).filter (fun i => ℓ (j + i) = l)).card ≤ 2 := fun l => by
    rw [← F.hcnt j l]
    exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_subset_range.mpr (by omega)))
  obtain ⟨e2, e01⟩ := straight_run_arith_iso G h01 (hle 0) (hle 1) (hle 2) hSpi
  have hm3 : m = 3 := by
    rw [card_label ℓ j m, Fin.sum_univ_three, e2]
    omega
  subst hm3
  exact ⟨rfl, e2⟩

/-- **Converse**: three consecutive sectors with exactly one corner of label 2 give a straight line (alpha + alpha + gamma = pi). -/
theorem straight_of_run_iso {ω : Fin 3 → ℝ} (G : AngGen' ω) (h01 : ω 0 = ω 1) {u v : ℕ → V2} {ℓ : ℕ → Fin 3} (F : Fan6 ω u v ℓ) (j : ℕ)
    (h : ((Finset.range 3).filter (fun i => ℓ (j + i) = 2)).card = 1) :
    Par (u (j + 3)) (-(u j).1, -(u j).2) := by
  classical
  have hrot := run_rotation (fun i => u (j + i)) (fun i => v (j + i)) (fun i => F.hu _) (fun i => by
    have := F.hpar (j + i); simpa [add_assoc] using this) 3
  simp only [add_zero] at hrot
  have hsum : ∑ i ∈ Finset.range 3, wd (u (j + i)) (v (j + i)) = Real.pi := by
    have := F.run_sum j 3
    rw [this, Fin.sum_univ_three]
    have hc := card_label ℓ j 3
    rw [Fin.sum_univ_three] at hc
    set c0 := ((Finset.range 3).filter (fun i => ℓ (j + i) = 0)).card
    set c1 := ((Finset.range 3).filter (fun i => ℓ (j + i) = 1)).card
    have h2 : ((Finset.range 3).filter (fun i => ℓ (j + i) = (2 : Fin 3))).card = 1 := h
    rw [h2] at hc
    have hc' : (c0 : ℝ) + c1 = 2 := by exact_mod_cast (by omega : c0 + c1 = 2)
    have hs := G.sum
    rw [h2]
    push_cast
    have e : (c0 : ℝ) * ω 0 + c1 * ω 1 = ((c0 : ℝ) + c1) * ω 0 := by rw [← h01]; ring
    rw [hc'] at e
    linarith
  rw [hsum] at hrot
  exact hrot.trans ((par_rot_neg_iff _ (F.hu j)).2 ⟨0, by simp⟩)

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.straight_run_labels_iso
#print axioms Erdos634.Draft.LaczFormal.RG.straight_of_run_iso

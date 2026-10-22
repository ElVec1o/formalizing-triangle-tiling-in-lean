-- Draft/LaczFormalIIcL8g.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.3, index split (G10), step 7: `spokes_interval`.
-- Every vertex of a strictly convex polygon is joined to E or to F (E != F points of the polygon), and a spoke to E never meets a spoke to F.  Then the vertices joined to E form a cyclic interval:
-- there are s and j <= M with  W i = E  iff  (i - s).val < j.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcL8f

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.Draft.LaczFormal.Thm21

namespace Erdos634.Draft.LaczFormal.RG

variable {M : ℕ} [NeZero M]

theorem fin_pred_cast {s : Fin M} (hM : 1 ≤ M) : s + ((M - 1 : ℕ) : Fin M) = s - 1 := by
  have h : ((M - 1 : ℕ) : Fin M) + 1 = 0 := by
    have : ((M - 1 + 1 : ℕ) : Fin M) = 0 := by
      rw [Nat.sub_add_cancel hM]; exact Fin.natCast_self M
    simpa [Nat.cast_succ] using this
  have : ((M - 1 : ℕ) : Fin M) = -1 := eq_neg_of_add_eq_zero_left h
  rw [this]; abel

theorem spokes_interval (P : ConvPoly M) {E F : Plane} (hE : E ∈ P.carrier) (hF : F ∈ P.carrier) (hne : E ≠ F)
    (W : Fin M → Plane) (hW : ∀ j, W j = E ∨ W j = F)
    (hdis : ∀ i l : Fin M, W i = E → W l = F → ∀ X, X ∈ segment ℝ (P.v i) E → X ∈ segment ℝ (P.v l) F → False) :
    ∃ s : Fin M, ∃ j : ℕ, j ≤ M ∧ ∀ i : Fin M, W i = E ↔ (i - s).val < j := by
  have hM := P.three_le
  by_cases hex : ∃ s : Fin M, W s = E ∧ W (s - 1) = F
  · obtain ⟨s, hsE, hsF⟩ := hex
    have hQ : ∃ n : ℕ, 0 < n ∧ n < M ∧ W (s + (n : Fin M)) = F := ⟨M - 1, by omega, by omega, by rw [fin_pred_cast (by omega)]; exact hsF⟩
    set j := Nat.find hQ with hj
    obtain ⟨hj0, hjM, hjF⟩ := Nat.find_spec hQ
    have hjmin : ∀ m, m < j → ¬ (0 < m ∧ m < M ∧ W (s + (m : Fin M)) = F) := fun m hm => Nat.find_min hQ hm
    refine ⟨s, j, by omega, ?_⟩
    have hbefore : ∀ n, n < j → W (s + (n : Fin M)) = E := by
      intro n hn
      by_cases h0 : n = 0
      · subst h0; simpa using hsE
      · have := hjmin n hn
        rcases hW (s + (n : Fin M)) with h | h
        · exact h
        · exact absurd ⟨by omega, by omega, h⟩ this
    have hafter : ∀ n, j ≤ n → n < M → W (s + (n : Fin M)) = F := by
      intro n hn hnM
      rcases hW (s + (n : Fin M)) with h | h
      · exfalso
        have hnj : j < n := by
          rcases Nat.eq_or_lt_of_le hn with h' | h'
          · exfalso; rw [← h'] at h; rw [hjF] at h; exact hne h.symm
          · exact h'
        have hnM1 : n < M - 1 := by
          rcases Nat.eq_or_lt_of_le (Nat.le_pred_of_lt hnM) with h' | h'
          · exfalso
            have : W (s + (n : Fin M)) = F := by
              have hn' : n = M - 1 := by omega
              rw [hn', fin_pred_cast (by omega)]; exact hsF
            rw [this] at h; exact hne h.symm
          · omega
        exact (no_interleave P s (b := j) (c := n) (d := M - 1) hj0 hnj hnM1 (by omega) hE hF
          (by
            intro i l hi hl X hX1 hX2
            have hWi : W i = E := by rcases hi with rfl | rfl; exact hsE; exact h
            have hWl : W l = F := by
              rcases hl with rfl | rfl
              · exact hjF
              · rw [fin_pred_cast (by omega)]; exact hsF
            exact hdis i l hWi hWl X hX1 hX2)).elim
      · exact h
    intro i
    have hn : (i - s).val < M := (i - s).isLt
    have hi : i = s + (((i - s).val : ℕ) : Fin M) := by
      rw [Fin.cast_val_eq_self]; abel
    constructor
    · intro hWi
      by_contra hge
      push_neg at hge
      have := hafter _ hge hn
      rw [← hi] at this
      rw [this] at hWi; exact hne hWi.symm
    · intro hlt
      have := hbefore _ hlt
      rwa [← hi] at this
  · push_neg at hex
    by_cases hall : ∃ i, W i = E
    · obtain ⟨i0, hi0⟩ := hall
      have hprop : ∀ n : ℕ, W (i0 - (n : Fin M)) = E := by
        intro n
        induction n with
        | zero => simpa using hi0
        | succ n ih =>
          have := hex (i0 - (n : Fin M)) ih
          rcases hW (i0 - (n : Fin M) - 1) with h | h
          · rw [Nat.cast_succ, sub_add_eq_sub_sub]; exact h
          · exact absurd h this
      refine ⟨0, M, le_refl _, fun i => ⟨fun _ => by simpa using (i - 0).isLt, fun _ => ?_⟩⟩
      have := hprop ((i0 - i).val)
      rwa [Fin.cast_val_eq_self, sub_sub_cancel] at this
    · push_neg at hall
      exact ⟨0, 0, Nat.zero_le _, fun i => ⟨fun h => absurd h (hall i), fun h => absurd h (Nat.not_lt_zero _)⟩⟩

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.spokes_interval

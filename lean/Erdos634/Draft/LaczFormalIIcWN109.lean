-- Draft/LaczFormalIIcWN109.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3), Lemma 6.2, item (3): the corner polygon keeps the EDGE DIRECTIONS.
-- `IsCornerOfD p q` := `IsCornerOfS p q` and, for each vertex `q j = p k`, the edges of `q` at `q j` are positive multiples of the edges of `p` at `p k`:
-- `q (j+1) - q j = c (p (k+1) - p k)` and `q (j-1) - q j = c' (p (k-1) - p k)` with `c, c' > 0`.  `exists_corner_dir` (same induction as WN73, WN103).
-- (Needed by R4: the side of the corner polygon from a convex end `W_i` towards `W_{i-1}` leaves along the first edge of the cycle.)
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN103

open scoped Classical Fin.NatCast
open Complex

namespace Erdos634.Draft.LaczFormal.WN

def IsCornerOfD {n m : ℕ} [NeZero n] [NeZero m] (p : Fin n → ℂ) (q : Fin m → ℂ) : Prop :=
  IsCornerOfS p q ∧ ∀ j : Fin m, ∃ k : Fin n, q j = p k ∧ (∃ c : ℝ, 0 < c ∧ q (j + 1) - q j = (c : ℂ) * (p (k + 1) - p k)) ∧
    (∃ c : ℝ, 0 < c ∧ q (j - 1) - q j = (c : ℂ) * (p (k - 1) - p k))

theorem exists_corner_dir_aux : ∀ n : ℕ, ∀ p : Fin (n+3) → ℂ, SimplePoly p → Function.Injective p →
    ∃ (m : ℕ) (_ : NeZero m) (q : Fin m → ℂ), IsCornerOfD p q := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro p hs hinj
    by_cases hex : ∃ k, extAng p k = 0
    · obtain ⟨k, hk⟩ := hex
      set p' := rotP p (k + 1) with hp'
      have hs' : SimplePoly p' := rotP_simple hs _
      have hinj' : Function.Injective p' := rotP_inj hinj _
      have hst : extAng p' (Fin.last (n+2)) = 0 := by
        rw [hp', rotP_extAng]
        have : Fin.last (n+2) + (k + 1) = k := by
          have h1 : (Fin.last (n+2) : Fin (n+3)) + 1 = 0 := del_f3 n
          calc Fin.last (n+2) + (k + 1) = (Fin.last (n+2) + 1) + k := by rw [add_comm k 1, ← add_assoc]
            _ = k := by rw [h1, zero_add]
        rw [this]; exact hk
      cases n with
      | zero =>
        exfalso
        exact no_simple_two (delLast p') (delLast_simple hs' hinj' hst) (delLast_inj hinj')
      | succ n' =>
        have hq := ih n' (by omega) (delLast p') (delLast_simple hs' hinj' hst) (delLast_inj hinj')
        obtain ⟨m, hm, q, ⟨⟨⟨h3, hqs, hqi, hqne, hqe, hqv⟩, hqsurj⟩, hqD⟩⟩ := hq
        obtain ⟨lam, hl, hc⟩ := straight_data hinj' hst
        have hS : IsCornerOfS p q := by
          refine ⟨⟨h3, hqs, hqi, hqne, ?_, ?_⟩, ?_⟩
          · rw [hqe, delLast_edgeSet hinj' hst, hp', rotP_edgeSet]
          · intro j
            obtain ⟨k', hk1, hk2⟩ := hqv j
            refine ⟨Fin.castSucc k' + (k + 1), ?_, ?_⟩
            · rw [hk1]; rfl
            · rw [hk2, delLast_extAng hinj' hst, hp', rotP_extAng]
          · intro t ht
            set t' : Fin (n'+1+3) := t - (k + 1) with ht'
            have hpt : p' t' = p t := by
              simp only [hp', rotP, ht', sub_add_cancel]
            have hext : extAng p' t' ≠ 0 := by
              rw [hp', rotP_extAng, ht']
              have : t - (k + 1) + (k + 1) = t := sub_add_cancel t (k + 1)
              rw [this]; exact ht
            have hnl : t' ≠ Fin.last (n'+1+2) := by
              intro e; rw [e] at hext; exact hext hst
            obtain ⟨s, hs'⟩ := Fin.exists_castSucc_eq.2 hnl
            have hext2 : extAng (delLast p') s ≠ 0 := by
              rw [delLast_extAng hinj' hst, hs']; exact hext
            obtain ⟨j, hj⟩ := hqsurj s hext2
            refine ⟨j, ?_⟩
            rw [hj, ← hpt, ← hs']
            rfl
        refine ⟨m, hm, q, hS, ?_⟩
        intro j
        obtain ⟨k'', hqk, ⟨c1, hc1, hf⟩, ⟨c2, hc2, hb⟩⟩ := hqD j
        have hrot : ∀ i : Fin (n'+1+3), p' i = p (i + (k + 1)) := fun i => rfl
        refine ⟨Fin.castSucc k'' + (k + 1), by rw [hqk]; rfl, ?_, ?_⟩
        · -- forward
          have e1 : p (Fin.castSucc k'' + (k + 1) + 1) - p (Fin.castSucc k'' + (k + 1)) =
              p' (Fin.castSucc k'' + 1) - p' (Fin.castSucc k'') := by
            rw [hrot, hrot, add_right_comm]
          rw [e1]
          by_cases hlast : k'' = Fin.last (n'+1+1)
          · subst hlast
            have h2 : (Fin.castSucc (Fin.last (n'+1+1)) : Fin (n'+1+3)) + 1 = Fin.last (n'+1+2) := del_f2 (n'+1)
            rw [h2]
            refine ⟨c1 * (1 + lam), mul_pos hc1 (by linarith), ?_⟩
            rw [hf]
            have h4 : (Fin.last (n'+1+1) : Fin (n'+1+2)) + 1 = 0 := del_f4 (n'+1)
            rw [h4]
            have e2 : delLast p' 0 = p' 0 := rfl
            have e3 : delLast p' (Fin.last (n'+1+1)) = p' (Fin.castSucc (Fin.last (n'+1+1))) := rfl
            rw [e2, e3]
            have : p' 0 - p' (Fin.castSucc (Fin.last (n'+1+1))) = (1 + (lam : ℂ)) * (p' (Fin.last (n'+1+2)) - p' (Fin.castSucc (Fin.last (n'+1+1)))) := by
              linear_combination hc
            rw [this]; push_cast; ring
          · refine ⟨c1, hc1, ?_⟩
            rw [hf, del_f1 (n'+1) k'' hlast]
            rfl
        · -- backward
          have e1 : p (Fin.castSucc k'' + (k + 1) - 1) - p (Fin.castSucc k'' + (k + 1)) =
              p' (Fin.castSucc k'' - 1) - p' (Fin.castSucc k'') := by
            rw [hrot, hrot, sub_add_eq_add_sub]
          rw [e1]
          by_cases hzero : k'' = 0
          · subst hzero
            have h5 : (Fin.castSucc (0 : Fin (n'+1+2)) : Fin (n'+1+3)) = 0 := del_f5 (n'+1)
            rw [h5, del_f6 (n'+1)]
            refine ⟨c2 * (1 + 1 / lam), mul_pos hc2 (by positivity), ?_⟩
            rw [hb, del_f6' (n'+1)]
            have e2 : delLast p' 0 = p' 0 := rfl
            have e3 : delLast p' (Fin.last (n'+1+1)) = p' (Fin.castSucc (Fin.last (n'+1+1))) := rfl
            rw [e2, e3]
            have hlam : (lam : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
            have : p' (Fin.castSucc (Fin.last (n'+1+1))) - p' 0 = (1 + 1 / (lam : ℂ)) * (p' (Fin.last (n'+1+2)) - p' 0) := by
              field_simp
              linear_combination hc
            rw [this]; push_cast; ring
          · refine ⟨c2, hc2, ?_⟩
            rw [hb, del_f8 (n'+1) k'' hzero]
            rfl
    · push Not at hex
      exact ⟨n + 3, inferInstance, p, ⟨⟨⟨by omega, hs, hinj, hex, rfl, fun j => ⟨j, rfl, rfl⟩⟩, fun k _ => ⟨k, rfl⟩⟩,
        fun j => ⟨j, rfl, ⟨1, one_pos, by simp⟩, ⟨1, one_pos, by simp⟩⟩⟩⟩

theorem exists_corner_dir {n : ℕ} [NeZero n] (p : Fin n → ℂ) (hs : SimplePoly p) (hinj : Function.Injective p) (hn : 3 ≤ n) :
    ∃ (m : ℕ) (_ : NeZero m) (q : Fin m → ℂ), IsCornerOfD p q := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 3 := ⟨n - 3, by omega⟩
  exact exists_corner_dir_aux n' p hs hinj

#print axioms exists_corner_dir

end Erdos634.Draft.LaczFormal.WN

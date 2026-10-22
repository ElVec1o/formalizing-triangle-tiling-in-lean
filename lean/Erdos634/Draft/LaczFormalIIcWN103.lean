-- Draft/LaczFormalIIcWN103.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3), Lemma 6.2, item (3): the CORNER POLYGON keeps EVERY non-straight vertex.
-- `IsCornerOfS p q` := `IsCornerOf p q` and every vertex of `p` with `extAng <> 0` is a vertex of `q`.  `exists_corner_surj` (same induction as `exists_corner`, WN73).
-- (Needed by R3: the end of a Gamma_except chord is a non-straight vertex of the cycle, which must be a vertex of the corner polygon.)
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN73

open scoped Classical Fin.NatCast
open Complex

namespace Erdos634.Draft.LaczFormal.WN

def IsCornerOfS {n m : ℕ} [NeZero n] [NeZero m] (p : Fin n → ℂ) (q : Fin m → ℂ) : Prop :=
  IsCornerOf p q ∧ ∀ k : Fin n, extAng p k ≠ 0 → ∃ j : Fin m, q j = p k

theorem exists_corner_surj_aux : ∀ n : ℕ, ∀ p : Fin (n+3) → ℂ, SimplePoly p → Function.Injective p →
    ∃ (m : ℕ) (_ : NeZero m) (q : Fin m → ℂ), IsCornerOfS p q := by
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
        obtain ⟨m, hm, q, ⟨h3, hqs, hqi, hqne, hqe, hqv⟩, hqsurj⟩ := hq
        refine ⟨m, hm, q, ⟨h3, hqs, hqi, hqne, ?_, ?_⟩, ?_⟩
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
    · push Not at hex
      exact ⟨n + 3, inferInstance, p, ⟨by omega, hs, hinj, hex, rfl, fun j => ⟨j, rfl, rfl⟩⟩, fun k _ => ⟨k, rfl⟩⟩

theorem exists_corner_surj {n : ℕ} [NeZero n] (p : Fin n → ℂ) (hs : SimplePoly p) (hinj : Function.Injective p) (hn : 3 ≤ n) :
    ∃ (m : ℕ) (_ : NeZero m) (q : Fin m → ℂ), IsCornerOfS p q := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 3 := ⟨n - 3, by omega⟩
  exact exists_corner_surj_aux n' p hs hinj

#print axioms exists_corner_surj

end Erdos634.Draft.LaczFormal.WN

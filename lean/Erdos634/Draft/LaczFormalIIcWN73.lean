-- Draft/LaczFormalIIcWN73.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3), Lemma 6.2, item (3), step 3: the CORNER POLYGON of a simple polygon.
-- `exists_corner`: every simple injective polygon `p` (>= 3 vertices) has a corner polygon `q`: simple, injective, with `extAng q j <> 0` at EVERY vertex (no straight vertex), the same point set
-- (`edgeSet q = edgeSet p`), >= 3 vertices, and each vertex of `q` is a vertex of `p` with the same turning angle.  It repairs the printed omission of Laczkovich's proof of Lemma 6.2: a Gamma_kite
-- cycle may contain straight (Fig. 5(A)) vertices, which are merged into the sides (repeated `delLast_*` of WN72 after a cyclic shift of WN71).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN72

open scoped Classical Fin.NatCast
open Complex

namespace Erdos634.Draft.LaczFormal.WN

/-- `q` is a corner polygon of `p`. -/
def IsCornerOf {n m : ℕ} [NeZero n] [NeZero m] (p : Fin n → ℂ) (q : Fin m → ℂ) : Prop :=
  3 ≤ m ∧ SimplePoly q ∧ Function.Injective q ∧ (∀ j, extAng q j ≠ 0) ∧ edgeSet q = edgeSet p ∧
    ∀ j, ∃ k, q j = p k ∧ extAng q j = extAng p k

theorem no_simple_two (q : Fin 2 → ℂ) (hs : SimplePoly q) (hinj : Function.Injective q) : False := by
  have h01 : q 0 ≠ q 1 := fun e => absurd (hinj e) (by decide)
  have h10 : (1 : Fin 2) + 1 = 0 := by decide
  have := hs 0 1 (by decide) (midpoint ℝ (q 0) (q 1)) ⟨?_, ?_⟩
  · rcases this with ⟨h | h, -⟩
    · exact h01 ((midpoint_eq_left_iff ℝ).1 h)
    · exact h01 ((midpoint_eq_right_iff ℝ).1 h)
  · simpa using midpoint_mem_segment (q 0) (q 1)
  · rw [h10, segment_symm]
    simpa using midpoint_mem_segment (q 0) (q 1)

theorem exists_corner_aux : ∀ n : ℕ, ∀ p : Fin (n+3) → ℂ, SimplePoly p → Function.Injective p →
    ∃ (m : ℕ) (_ : NeZero m) (q : Fin m → ℂ), IsCornerOf p q := by
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
        obtain ⟨m, hm, q, h3, hqs, hqi, hqne, hqe, hqv⟩ := hq
        refine ⟨m, hm, q, h3, hqs, hqi, hqne, ?_, ?_⟩
        · rw [hqe, delLast_edgeSet hinj' hst, hp', rotP_edgeSet]
        · intro j
          obtain ⟨k', hk1, hk2⟩ := hqv j
          refine ⟨Fin.castSucc k' + (k + 1), ?_, ?_⟩
          · rw [hk1]; rfl
          · rw [hk2, delLast_extAng hinj' hst, hp', rotP_extAng]
    · push Not at hex
      exact ⟨n + 3, inferInstance, p, by omega, hs, hinj, hex, rfl, fun j => ⟨j, rfl, rfl⟩⟩

theorem exists_corner {n : ℕ} [NeZero n] (p : Fin n → ℂ) (hs : SimplePoly p) (hinj : Function.Injective p) (hn : 3 ≤ n) :
    ∃ (m : ℕ) (_ : NeZero m) (q : Fin m → ℂ), IsCornerOf p q := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 3 := ⟨n - 3, by omega⟩
  exact exists_corner_aux n' p hs hinj

#print axioms exists_corner

end Erdos634.Draft.LaczFormal.WN

-- Draft/LaczFormalIIcWN85.lean -- Laczkovich (DCG 48 (2012), Sect. 6.2, Fig. 5), the FAN LEMMA, combinatorial part.
-- Six cyclic labels (two of each), a `beta beta` block at `b, b+1`, an `alpha alpha` block at `c, c+1`, and three consecutive pairwise distinct labels somewhere (a straight line through the vertex, `straight_run_labels`):
-- then the blocks are 3 apart, `c = b + 3 (mod 6)`, and `(b+1, b+2, b+3)` carry three distinct labels (pattern `1,1,2,0,0,2` of Fig. 5(A)).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2, Fig. 5), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG12GExcHelp

open Erdos634.Draft.LaczFormal.Graph

namespace Erdos634.Draft.LaczFormal.RG

set_option synthInstance.maxSize 40000 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem comb_straight_fin : ∀ a0 a1 a2 a3 a4 a5 : Fin 3,
    (((Finset.range 6).filter (fun i => gF a0 a1 a2 a3 a4 a5 i = 0)).card = 2 ∧
    ((Finset.range 6).filter (fun i => gF a0 a1 a2 a3 a4 a5 i = 1)).card = 2 ∧
    ((Finset.range 6).filter (fun i => gF a0 a1 a2 a3 a4 a5 i = 2)).card = 2) →
    ∀ b < 6, ∀ c < 6, ∀ j < 6,
    (gF a0 a1 a2 a3 a4 a5 b = 1 ∧ gF a0 a1 a2 a3 a4 a5 (b + 1) = 1 ∧ gF a0 a1 a2 a3 a4 a5 c = 0 ∧ gF a0 a1 a2 a3 a4 a5 (c + 1) = 0) →
    (gF a0 a1 a2 a3 a4 a5 j ≠ gF a0 a1 a2 a3 a4 a5 (j + 1) ∧ gF a0 a1 a2 a3 a4 a5 j ≠ gF a0 a1 a2 a3 a4 a5 (j + 2) ∧
      gF a0 a1 a2 a3 a4 a5 (j + 1) ≠ gF a0 a1 a2 a3 a4 a5 (j + 2)) →
    c = (b + 3) % 6 ∧ (gF a0 a1 a2 a3 a4 a5 (b + 1) ≠ gF a0 a1 a2 a3 a4 a5 (b + 2) ∧ gF a0 a1 a2 a3 a4 a5 (b + 1) ≠ gF a0 a1 a2 a3 a4 a5 (b + 3) ∧
      gF a0 a1 a2 a3 a4 a5 (b + 2) ≠ gF a0 a1 a2 a3 a4 a5 (b + 3)) := by
  decide +kernel

theorem comb_straight (ℓ : ℕ → Fin 3) (hper : ∀ n, ℓ (n + 6) = ℓ n) (h0 : ((Finset.range 6).filter (fun i => ℓ i = 0)).card = 2)
    (h1 : ((Finset.range 6).filter (fun i => ℓ i = 1)).card = 2) (h2 : ((Finset.range 6).filter (fun i => ℓ i = 2)).card = 2) {b c : ℕ}
    (hb1 : ℓ b = 1 ∧ ℓ (b + 1) = 1) (hc1 : ℓ c = 0 ∧ ℓ (c + 1) = 0) (j : ℕ)
    (hj : ℓ j ≠ ℓ (j + 1) ∧ ℓ j ≠ ℓ (j + 2) ∧ ℓ (j + 1) ≠ ℓ (j + 2)) :
    c % 6 = (b + 3) % 6 ∧ (ℓ (b + 1) ≠ ℓ (b + 2) ∧ ℓ (b + 1) ≠ ℓ (b + 3) ∧ ℓ (b + 2) ≠ ℓ (b + 3)) := by
  have hm := per_mod ℓ hper
  have hk : ∀ k (hk : k < 6), (![ℓ 0, ℓ 1, ℓ 2, ℓ 3, ℓ 4, ℓ 5] : Fin 6 → Fin 3) ⟨k, hk⟩ = ℓ k := by
    intro k hk; interval_cases k <;> rfl
  have hg : ∀ n, gF (ℓ 0) (ℓ 1) (ℓ 2) (ℓ 3) (ℓ 4) (ℓ 5) n = ℓ n := by
    intro n
    rw [hm n]
    exact hk (n % 6) (Nat.mod_lt _ (by norm_num))
  have key := comb_straight_fin (ℓ 0) (ℓ 1) (ℓ 2) (ℓ 3) (ℓ 4) (ℓ 5)
  simp only [hg] at key
  have sh : ∀ n k : ℕ, ℓ (n % 6 + k) = ℓ (n + k) := fun n k => by rw [hm (n % 6 + k), hm (n + k)]; congr 1; omega
  have s0 : ∀ n : ℕ, ℓ (n % 6) = ℓ n := fun n => (hm n).symm
  have := key ⟨h0, h1, h2⟩ (b % 6) (Nat.mod_lt _ (by norm_num)) (c % 6) (Nat.mod_lt _ (by norm_num)) (j % 6) (Nat.mod_lt _ (by norm_num))
    ⟨(by rw [s0]; exact hb1.1), (by rw [sh]; exact hb1.2), (by rw [s0]; exact hc1.1), (by rw [sh]; exact hc1.2)⟩
    (by rw [s0, sh, sh]; exact hj)
  rw [sh, sh, sh] at this
  obtain ⟨hc, hd⟩ := this
  refine ⟨?_, hd⟩
  omega

#print axioms comb_straight

end Erdos634.Draft.LaczFormal.RG

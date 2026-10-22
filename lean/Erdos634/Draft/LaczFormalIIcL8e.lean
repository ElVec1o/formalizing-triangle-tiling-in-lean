-- Draft/LaczFormalIIcL8e.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.3, index split (G10), step 5: the interleaving lemma and the cyclic-interval lemma, PURE CONVEX GEOMETRY.
--  `no_interleave`   : in a strictly convex polygon, vertices s < s+b < s+c < s+d (cyclic order), E, F points of the polygon: the spokes [V_s,E], [V_{s+c},E] and [V_{s+b},F], [V_{s+d},F] cannot be pairwise disjoint.
--  `spokes_interval` : if every vertex is joined to E or to F (E != F points of the polygon) and a spoke to E is disjoint from a spoke to F, the vertices joined to E form a cyclic interval
--                      {s, s+1, ..., s+j-1}  (0 <= j <= M).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3, step "the corners sending to E form a cyclic interval"), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcL8a
import Erdos634.Draft.LaczFormalIIcL8d

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.Draft.LaczFormal.Thm21

namespace Erdos634.Draft.LaczFormal.RG

variable {M : ℕ} [NeZero M]

theorem vtx_mem' (P : ConvPoly M) (j : Fin M) : P.v j ∈ P.carrier := by
  intro i
  show 0 ≤ P.c i (P.v j)
  by_cases h1 : j = i
  · subst h1; exact (P.c_self j).ge
  · by_cases h2 : j = i + 1
    · subst h2; exact (P.c_next i).ge
    · exact (P.c_vertex_pos h1 h2).le

theorem tl_affine (e v A E C X : Plane) :
    cross2 (E - A) (C - A) * cross2 e (X - v) = tlA E C X * cross2 e (A - v) + tlE A C X * cross2 e (E - v) + tlC A E X * cross2 e (C - v) := by
  unfold tlA tlE tlC cross2; simp only [PiLp.sub_apply]; ring

theorem gl_swap (A C X : Plane) : gl C A X = - gl A C X := by
  unfold gl cross2; simp only [PiLp.sub_apply]; ring

theorem cross2_neg_swap (u w : Plane) : cross2 u w = - cross2 w u := by unfold cross2; ring

/-- a vertex `B` of the polygon lying on the `E` side of the chord `AC` and in the triangle `(A, E, C)` (A, C other vertices, E in the polygon) is `E`. -/
theorem vertex_tri_eq (P : ConvPoly M) {a j c : Fin M} (hja : j ≠ a) (hjc : j ≠ c) {E : Plane} (hE : E ∈ P.carrier)
    (hB : gl (P.v a) (P.v c) (P.v j) < 0) (hEg : gl (P.v a) (P.v c) E ≤ 0) :
    (0 ≤ tlA E (P.v c) (P.v j) ∧ 0 ≤ tlE (P.v a) (P.v c) (P.v j) ∧ 0 ≤ tlC (P.v a) E (P.v j)) → P.v j = E := by
  rintro ⟨h1, h2, h3⟩
  have hM := P.three_le
  set A := P.v a; set C := P.v c; set B := P.v j
  have hE2 : 0 < tlE A C B := by rw [tlE_eq]; linarith
  have hsum := tl_sum A E C B
  have hΔ : 0 < cross2 (E - A) (C - A) := by linarith
  -- the two edge functionals at B
  have key : ∀ k : Fin M, P.c k B = 0 → 0 ≤ P.c k A → 0 ≤ P.c k E → 0 ≤ P.c k C →
      tlA E C B * P.c k A = 0 ∧ tlC A E B * P.c k C = 0 := by
    intro k hk0 cA cE cC
    have := tl_affine (P.e k) (P.v k) A E C B
    unfold ConvPoly.c at hk0 cA cE cC
    rw [hk0, mul_zero] at this
    have p1 : 0 ≤ tlA E C B * cross2 (P.e k) (A - P.v k) := mul_nonneg h1 cA
    have p2 : 0 ≤ tlE A C B * cross2 (P.e k) (E - P.v k) := mul_nonneg h2 cE
    have p3 : 0 ≤ tlC A E B * cross2 (P.e k) (C - P.v k) := mul_nonneg h3 cC
    unfold ConvPoly.c
    constructor <;> linarith
  have hcA : ∀ k, 0 ≤ P.c k A := fun k => vtx_mem' P a k
  have hcC : ∀ k, 0 ≤ P.c k C := fun k => vtx_mem' P c k
  have hcE : ∀ k, 0 ≤ P.c k E := fun k => hE k
  have k1 := key j (P.c_self j) (hcA j) (hcE j) (hcC j)
  have k2 := key (j - 1) (P.c_prev_next hM j) (hcA _) (hcE _) (hcC _)
  have hA0 : tlA E C B = 0 := by
    by_contra hne
    have hpos : 0 < tlA E C B := lt_of_le_of_ne h1 (Ne.symm hne)
    have z1 : P.c j A = 0 := by
      rcases mul_eq_zero.mp k1.1 with h | h
      · exact absurd h hne
      · exact h
    have z2 : P.c (j - 1) A = 0 := by
      rcases mul_eq_zero.mp k2.1 with h | h
      · exact absurd h hne
      · exact h
    have := vertex_not_both P hja.symm z1
    linarith
  have hC0 : tlC A E B = 0 := by
    by_contra hne
    have z1 : P.c j C = 0 := by
      rcases mul_eq_zero.mp k1.2 with h | h
      · exact absurd h hne
      · exact h
    have z2 : P.c (j - 1) C = 0 := by
      rcases mul_eq_zero.mp k2.2 with h | h
      · exact absurd h hne
      · exact h
    have := vertex_not_both P hjc.symm z1
    linarith
  have hb := tl_bary A E C B
  rw [hA0, hC0, zero_smul, zero_smul, zero_add, add_zero] at hb
  have hΔe : cross2 (E - A) (C - A) = tlE A C B := by linarith
  rw [hΔe] at hb
  exact smul_right_injective Plane hE2.ne' hb

end Erdos634.Draft.LaczFormal.RG

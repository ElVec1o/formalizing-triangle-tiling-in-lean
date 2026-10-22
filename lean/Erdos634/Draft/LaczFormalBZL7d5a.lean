-- Draft/LaczFormalBZL7d5a.lean -- pure lemmas for the last step of Beeson-Zhang Thm 3.7 / Thm 1.1 (all boundary edges are c-edges => contradiction by the invariant Phi):
--   `sideEdges_all_c`      : a finite family of tile edges, each of length a, b or c, whose lengths add up to m*c, with a, b commensurable and c not commensurable with a: all have length c and there are m of them;
--   `sign_contradiction`   : signs eps_j in {+1,-1} with product 1, positive integers m_j with strict triangle inequalities m_j < m_{j+1} + m_{j+2}: sum eps_j m_j != 0.
-- (The second is the content of BZ Thm 5.2/5.3's last lines, for an arbitrary sign pattern.)  NOTE, UNAUDITED.
-- Credit: Beeson-Zhang (arXiv 2604.01314v1, Lemma 3.4, Thm 5.2, 5.3), Laczkovich (DCG 48 (2012), Sect. 7.3 (d2)), Beeson.
import Erdos634.Draft.LaczFormalIIIcSide

open scoped Classical
open Erdos634.Draft.LaczFormal.IIIc Erdos634.Draft.LaczFormal.Thm21

namespace Erdos634.Draft.LaczFormal.RG

/-- All edges have length `c`, and there are `m` of them. -/
theorem sideEdges_all_c {ι : Type*} (s : Finset ι) (len : ι → ℝ) {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : Comm a b) (hac : ¬ Comm a c)
    (hlen : ∀ e ∈ s, len e = a ∨ len e = b ∨ len e = c) (m : ℕ) (hm : 0 < m) (hsum : ∑ e ∈ s, len e = m * c) :
    (∀ e ∈ s, len e = c) ∧ s.card = m := by
  obtain ⟨nc, S, h1, h2, h3, h4⟩ := iiic_sum_decomp s len ha hb hab hlen
  have hall : ∀ e ∈ s, len e = c := by
    intro e he
    by_contra hne
    obtain ⟨hSpos, hSc⟩ := h4 ⟨e, he, hne⟩
    rw [hsum] at h1
    have hmn : nc < m := by
      by_contra hcon
      push Not at hcon
      have : (m : ℝ) ≤ nc := by exact_mod_cast hcon
      nlinarith
    apply hac
    have hS : S = ((m - nc : ℕ) : ℝ) * c := by
      rw [Nat.cast_sub hmn.le]; linarith
    rw [hS] at hSc
    obtain ⟨p, q, hp, hq, h⟩ := iiic_comm_nsmul (m - nc) (Nat.sub_pos_of_lt hmn) (a := a) hSc
    exact ⟨q, p, hq, hp, h.symm⟩
  refine ⟨hall, ?_⟩
  have : ∑ e ∈ s, len e = s.card * c := by
    rw [Finset.sum_congr rfl hall, Finset.sum_const, nsmul_eq_mul]
  rw [this] at hsum
  have : (s.card : ℝ) = m := by
    have := mul_right_cancel₀ hc.ne' hsum
    exact this
  exact_mod_cast this

/-- Signs with product `1` and a strict triangle inequality: the signed sum cannot vanish. -/
theorem sign_contradiction (e0 e1 e2 : ℝ) (h0 : e0 * e0 = 1) (h1 : e1 * e1 = 1) (h2 : e2 * e2 = 1) (hp : e0 * e1 * e2 = 1)
    (m0 m1 m2 : ℝ) (p0 : 0 < m0) (p1 : 0 < m1) (p2 : 0 < m2)
    (t0 : m0 < m1 + m2) (t1 : m1 < m2 + m0) (t2 : m2 < m0 + m1) : e0 * m0 + e1 * m1 + e2 * m2 ≠ 0 := by
  have s : ∀ x : ℝ, x * x = 1 → x = 1 ∨ x = -1 := by
    intro x hx
    have : (x - 1) * (x + 1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · left; linarith
    · right; linarith
  rcases s e0 h0 with rfl | rfl <;> rcases s e1 h1 with rfl | rfl <;> rcases s e2 h2 with rfl | rfl <;> intro hz <;> norm_num at hp <;> linarith

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.sideEdges_all_c
#print axioms Erdos634.Draft.LaczFormal.RG.sign_contradiction

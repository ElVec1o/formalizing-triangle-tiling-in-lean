-- Draft/LaczFormalIIcWN62.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3), Lemma 6.2 (`IIcNoKites`), step (i), part 6:
-- `claim_X`: for the quadrilateral Q_i = (A i, A (i+1), c (w (i+1)), c (w i)), the vertex c (w k), k not in {i, i+1}, has winding number 0 about it
-- (the chord A k -- c (w k) misses Q_i and A k is outside).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN61

open scoped Classical Fin.NatCast
open Complex Filter Topology

namespace Erdos634.Draft.LaczFormal.WN

variable {N : ℕ} [NeZero N]

section Ring
variable {A c : Fin N → ℂ} {w : Fin N → Fin N} {τA τC : ℝ}

theorem RingSetup.gA_pos (R : RingSetup A c w τA τC) (k m : Fin N) (hm : m ≠ k) :
    0 < τA * (sideFn (A (k - 1)) (A (k - 1 + 1) - A (k - 1)) (A m) + sideFn (A k) (A (k + 1) - A k) (A m)) := by
  rw [mul_add]
  have hn := R.hN
  have hk1 : k - 1 ≠ k := by
    intro h
    have : (1 : Fin N) = 0 := by
      have := congrArg (fun x => k - x) h
      simpa using this
    exact fin_one_ne hn this
  have hk2 : k + 1 ≠ k := by
    intro h
    have : (1 : Fin N) = 0 := by simpa using h
    exact fin_one_ne hn this
  by_cases h1 : m = k - 1
  · subst h1
    have a1 : sideFn (A (k - 1)) (A (k - 1 + 1) - A (k - 1)) (A (k - 1)) = 0 := sideFn_base _ _
    have a2 := R.SA k (k - 1) hk1 (fin_pred_ne_succ hn k)
    rw [a1]; linarith
  · by_cases h2 : m = k + 1
    · subst h2
      have hd : A (k + 1) - A k ≠ 0 := sub_ne_zero.2 (nd R.Ainj hn k)
      have a1 : sideFn (A k) (A (k + 1) - A k) (A (k + 1)) = 0 := by
        have := sideFn_tip (x0 := A k) hd
        rwa [show A k + (A (k + 1) - A k) = A (k + 1) by ring] at this
      have a2 := R.SA (k - 1) (k + 1) (Ne.symm (fin_pred_ne_succ hn k)) (by rw [sub_add_cancel]; exact hk2)
      rw [a1]; linarith
    · have a1 := R.SA (k - 1) m h1 (by rw [sub_add_cancel]; exact hm)
      have a2 := R.SA k m hm h2
      linarith

theorem RingSetup.gc_pos (R : RingSetup A c w τA τC) (k m : Fin N) :
    0 < τA * (sideFn (A (k - 1)) (A (k - 1 + 1) - A (k - 1)) (c m) + sideFn (A k) (A (k + 1) - A k) (c m)) := by
  rw [mul_add]
  have := R.inside (k - 1) m
  have := R.inside k m
  linarith

theorem RingSetup.chord_seg_off (R : RingSetup A c w τA τC) {a b k : Fin N} (hab : a ≠ b) (ha : w k ≠ a) (hb : w k ≠ b)
    {z : ℂ} (hz : z ∈ segment ℝ (A k) (c (w k))) : z ∉ segment ℝ (c a) (c b) := by
  intro hmem
  obtain ⟨s, h0, h1, rfl⟩ := seg_param hz
  rcases h1.lt_or_eq with h1' | h1'
  · obtain ⟨j, hj⟩ := R.out k s h0 h1'
    have := R.seg_in a b hmem j
    linarith
  · rw [h1'] at hmem
    have e : A k + ((1 : ℝ) : ℂ) * (c (w k) - A k) = c (w k) := by push_cast; ring
    rw [e] at hmem
    exact R.vertex_not_seg hab ha hb hmem

theorem RingSetup.claim_X (R : RingSetup A c w τA τC) {i k : Fin N} (hk : k ≠ i) (hk1 : k ≠ i + 1) :
    wind (quad (A i) (A (i + 1)) (c (w (i + 1))) (c (w i))) (c (w k)) = 0 := by
  have hn := R.hN
  have hi1 : i + 1 ≠ i := by
    intro h
    have : (1 : Fin N) = 0 := by simpa using h
    exact fin_one_ne hn this
  have hwk : w k ≠ w i := fun h => hk (R.w_inj h)
  have hwk1 : w k ≠ w (i + 1) := fun h => hk1 (R.w_inj h)
  have hab : w (i + 1) ≠ w i := fun h => hi1 (R.w_inj h)
  have hoff : ∀ z ∈ segment ℝ (A k) (c (w k)), z ∉ edgeSet (quad (A i) (A (i + 1)) (c (w (i + 1))) (c (w i))) := by
    intro z hz hmem
    rw [mem_edgeSet_quad] at hmem
    rcases hmem with h | h | h | h
    · have h0 := R.edge_zero i h
      have h1 := R.chord_pos hk hk1 hz
      linarith
    · exact Set.disjoint_left.1 (R.disj k (i + 1) hk1) hz h
    · exact R.chord_seg_off hab hwk1 hwk hz h
    · rw [segment_symm] at h
      exact Set.disjoint_left.1 (R.disj k i hk) hz h
  have hconst := wind_const_segment (quad (A i) (A (i + 1)) (c (w (i + 1))) (c (w i))) (u := A k) (v := c (w k)) hoff
  rw [← hconst]
  refine wind_zero_outer hn R.Ainj R.SA R.τA1 k _ (fun i' => ?_)
  fin_cases i'
  · simp only [quad]; exact R.gA_pos k i (Ne.symm hk)
  · simp only [quad]; exact R.gA_pos k (i + 1) (Ne.symm hk1)
  · simp only [quad]; exact R.gc_pos k _
  · simp only [quad]; exact R.gc_pos k _

end Ring

#print axioms RingSetup.claim_X

end Erdos634.Draft.LaczFormal.WN

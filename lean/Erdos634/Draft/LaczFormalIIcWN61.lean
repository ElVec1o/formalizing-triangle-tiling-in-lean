-- Draft/LaczFormalIIcWN61.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3), Lemma 6.2 (`IIcNoKites`), step (i), part 5:
-- geometry of a `RingSetup`: chords are disjoint from the other polygon pieces; `claim_X`: for the quadrilateral Q_i = (A i, A (i+1), c (w (i+1)), c (w i)),
-- every vertex c (w k) with k not in {i, i+1} has winding number 0 about it.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN60

open scoped Classical Fin.NatCast
open Complex Filter Topology

namespace Erdos634.Draft.LaczFormal.WN

variable {N : ℕ} [NeZero N]

section Ring
variable {A c : Fin N → ℂ} {w : Fin N → Fin N} {τA τC : ℝ}

theorem seg_param {x y z : ℂ} (hz : z ∈ segment ℝ x y) : ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ z = x + (s : ℂ) * (y - x) := by
  rw [segment_eq_image'] at hz
  obtain ⟨s, ⟨h0, h1⟩, hs⟩ := hz
  exact ⟨s, h0, h1, by rw [← hs]; simp [Complex.real_smul]⟩

theorem RingSetup.w_inj (R : RingSetup A c w τA τC) : Function.Injective w := by
  intro i j h
  by_contra hij
  have := R.disj i j hij
  exact Set.disjoint_left.1 this (right_mem_segment ℝ _ _) (by rw [h]; exact right_mem_segment ℝ _ _)

theorem RingSetup.edge_zero (R : RingSetup A c w τA τC) (i : Fin N) {z : ℂ} (hz : z ∈ segment ℝ (A i) (A (i + 1))) :
    τA * sideFn (A i) (A (i + 1) - A i) z = 0 := by
  obtain ⟨s, -, -, rfl⟩ := seg_param hz
  rw [sideFn_lin]
  have hd : A (i + 1) - A i ≠ 0 := sub_ne_zero.2 (nd R.Ainj R.hN i)
  have h1 := sideFn_tip (x0 := A i) hd
  rw [show A i + (A (i + 1) - A i) = A (i + 1) by ring] at h1
  rw [sideFn_base, h1]; simp

theorem RingSetup.chord_pos (R : RingSetup A c w τA τC) {i k : Fin N} (hk : k ≠ i) (hk1 : k ≠ i + 1) {z : ℂ}
    (hz : z ∈ segment ℝ (A k) (c (w k))) : 0 < τA * sideFn (A i) (A (i + 1) - A i) z := by
  obtain ⟨s, h0, h1, rfl⟩ := seg_param hz
  exact comb_pos h0 h1 (R.SA i k hk hk1) (R.inside i (w k))

theorem RingSetup.seg_in (R : RingSetup A c w τA τC) (a b : Fin N) {z : ℂ} (hz : z ∈ segment ℝ (c a) (c b)) (j : Fin N) :
    0 ≤ τC * sideFn (c j) (c (j + 1) - c j) z := by
  obtain ⟨s, h0, h1, rfl⟩ := seg_param hz
  exact comb_nonneg h0 h1 (R.SCc.vert_nonneg R.cinj R.hN j a) (R.SCc.vert_nonneg R.cinj R.hN j b)

theorem RingSetup.vertex_not_seg (R : RingSetup A c w τA τC) {a b m : Fin N} (hab : a ≠ b) (ha : m ≠ a) (hb : m ≠ b) :
    c m ∉ segment ℝ (c a) (c b) := by
  intro hmem
  obtain ⟨s, h0, h1, hs⟩ := seg_param hmem
  have hf : τC * sideFn (c m) (c (m + 1) - c m) (c a + (s : ℂ) * (c b - c a)) = 0 := by
    rw [← hs, sideFn_base]; simp
  rw [sideFn_lin] at hf
  have hfa : 0 ≤ τC * sideFn (c m) (c (m + 1) - c m) (c a) := R.SCc.vert_nonneg R.cinj R.hN m a
  have hfb : 0 ≤ τC * sideFn (c m) (c (m + 1) - c m) (c b) := R.SCc.vert_nonneg R.cinj R.hN m b
  have hf' : (1 - s) * (τC * sideFn (c m) (c (m + 1) - c m) (c a)) + s * (τC * sideFn (c m) (c (m + 1) - c m) (c b)) = 0 := by
    linarith
  rcases h0.lt_or_eq with h0' | h0'
  · rcases h1.lt_or_eq with h1' | h1'
    · have h1s : 0 < 1 - s := by linarith
      have z1 : τC * sideFn (c m) (c (m + 1) - c m) (c a) = 0 := by
        nlinarith [mul_nonneg h1s.le hfa, mul_nonneg h0'.le hfb]
      have z2 : τC * sideFn (c m) (c (m + 1) - c m) (c b) = 0 := by
        nlinarith [mul_nonneg h1s.le hfa, mul_nonneg h0'.le hfb]
      have ha' : a = m + 1 := by
        by_contra hne
        have := R.SCc m a (Ne.symm ha) hne
        linarith
      have hb' : b = m + 1 := by
        by_contra hne
        have := R.SCc m b (Ne.symm hb) hne
        linarith
      exact hab (ha'.trans hb'.symm)
    · exact hb (R.cinj (by rw [hs, h1']; push_cast; ring))
  · exact ha (R.cinj (by rw [hs, ← h0']; push_cast; ring))

end Ring

end Erdos634.Draft.LaczFormal.WN

-- Draft/LaczFormalIIcWN63.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3), Lemma 6.2 (`IIcNoKites`), step (i), part 7:
-- helper facts for the adjacency argument: the midpoint of two non-adjacent vertices of c is strictly inside c; closed chords contain a point weakly outside c;
-- `no_Q_hit`: a point weakly inside c, strictly inside A on the A-edge i and strictly on one side of the line through c b, c a is off the quadrilateral Q_i.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN62

open scoped Classical Fin.NatCast
open Complex Filter Topology

namespace Erdos634.Draft.LaczFormal.WN

variable {N : ℕ} [NeZero N]

theorem sideFn_mid (x0 d z : ℂ) : sideFn (x0 + ((1 / 2 : ℝ) : ℂ) * d) d z = sideFn x0 d z := by
  unfold sideFn
  by_cases hd : d = 0
  · simp [hd]
  · have : (z - (x0 + ((1 / 2 : ℝ) : ℂ) * d)) / d = (z - x0) / d - ((1 / 2 : ℝ) : ℂ) := by
      push_cast; field_simp; ring
    rw [this]; simp

theorem sideFn_seg_zero {x y z : ℂ} (hxy : y - x ≠ 0) (hz : z ∈ segment ℝ x y) : sideFn x (y - x) z = 0 := by
  obtain ⟨s, -, -, rfl⟩ := seg_param hz
  rw [sideFn_lin, sideFn_base]
  have := sideFn_tip (x0 := x) hxy
  rw [show x + (y - x) = y by ring] at this
  rw [this]; simp

section Ring
variable {A c : Fin N → ℂ} {w : Fin N → Fin N} {τA τC : ℝ}

theorem RingSetup.mid_strict (R : RingSetup A c w τA τC) {a b : Fin N} (hab : a ≠ b) (hb1 : b ≠ a + 1) (hb2 : a ≠ b + 1) (j : Fin N) :
    0 < τC * sideFn (c j) (c (j + 1) - c j) (c b + ((1 / 2 : ℝ) : ℂ) * (c a - c b)) := by
  by_cases ha : a = j ∨ a = j + 1
  · have hb : b ≠ j ∧ b ≠ j + 1 := by
      constructor
      · intro h
        rcases ha with ha | ha
        · exact hab (ha.trans h.symm)
        · apply hb2; rw [ha, h]
      · intro h
        rcases ha with ha | ha
        · apply hb1; rw [h, ha]
        · exact hab (ha.trans h.symm)
    exact comb_pos_left (by norm_num) (by norm_num) (R.SCc j b hb.1 hb.2) (R.SCc.vert_nonneg R.cinj R.hN j a)
  · push Not at ha
    have e : c b + ((1 / 2 : ℝ) : ℂ) * (c a - c b) = c a + ((1 / 2 : ℝ) : ℂ) * (c b - c a) := by push_cast; ring
    rw [e]
    exact comb_pos_left (by norm_num) (by norm_num) (R.SCc j a ha.1 ha.2) (R.SCc.vert_nonneg R.cinj R.hN j b)

theorem RingSetup.chord_cases (R : RingSetup A c w τA τC) (m : Fin N) {z : ℂ} (hz : z ∈ segment ℝ (A m) (c (w m))) :
    (∃ j, τC * sideFn (c j) (c (j + 1) - c j) z < 0) ∨ z = c (w m) := by
  obtain ⟨s, h0, h1, rfl⟩ := seg_param hz
  rcases h1.lt_or_eq with h1' | h1'
  · obtain ⟨j, hj⟩ := R.out m s h0 h1'
    exact Or.inl ⟨j, hj⟩
  · right
    rw [h1']; push_cast; ring

theorem RingSetup.off_three (R : RingSetup A c w τA τC) (i : Fin N) {z : ℂ}
    (hC : ∀ j, 0 ≤ τC * sideFn (c j) (c (j + 1) - c j) z) (hA : 0 < τA * sideFn (A i) (A (i + 1) - A i) z)
    (h1 : z ≠ c (w (i + 1))) (h2 : z ≠ c (w i)) :
    z ∉ segment ℝ (A i) (A (i + 1)) ∧ z ∉ segment ℝ (A (i + 1)) (c (w (i + 1))) ∧ z ∉ segment ℝ (c (w i)) (A i) := by
  have chord : ∀ m : Fin N, z ∈ segment ℝ (A m) (c (w m)) → z ≠ c (w m) → False := by
    intro m hm hne
    rcases R.chord_cases m hm with ⟨j, hj⟩ | hz
    · have := hC j; linarith
    · exact hne hz
  refine ⟨fun h => ?_, fun h => chord (i + 1) h h1, fun h => ?_⟩
  · have := R.edge_zero i h
    linarith
  · rw [segment_symm] at h
    exact chord i h h2

theorem RingSetup.no_Q_hit (R : RingSetup A c w τA τC) (i : Fin N) {z : ℂ}
    (hC : ∀ j, 0 ≤ τC * sideFn (c j) (c (j + 1) - c j) z) (hA : 0 < τA * sideFn (A i) (A (i + 1) - A i) z)
    (hφ : sideFn (c (w (i + 1))) (c (w i) - c (w (i + 1))) z ≠ 0) :
    z ∉ edgeSet (quad (A i) (A (i + 1)) (c (w (i + 1))) (c (w i))) := by
  have hne : c (w i) - c (w (i + 1)) ≠ 0 := by
    intro h
    have := R.cinj (sub_eq_zero.1 h)
    have hw := R.w_inj this
    have : (1 : Fin N) = 0 := by
      have h2 : i + 1 = i := hw.symm
      simpa using h2
    exact fin_one_ne R.hN this
  have e1 : z ≠ c (w (i + 1)) := by
    intro h; apply hφ; rw [h, sideFn_base]
  have e2 : z ≠ c (w i) := by
    intro h; apply hφ; rw [h]
    have := sideFn_tip (x0 := c (w (i + 1))) hne
    rw [show c (w (i + 1)) + (c (w i) - c (w (i + 1))) = c (w i) by ring] at this
    exact this
  obtain ⟨o0, o1, o3⟩ := R.off_three i hC hA e1 e2
  intro hmem
  rw [mem_edgeSet_quad] at hmem
  rcases hmem with h | h | h | h
  · exact o0 h
  · exact o1 h
  · exact hφ (sideFn_seg_zero hne h)
  · exact o3 h

end Ring

end Erdos634.Draft.LaczFormal.WN

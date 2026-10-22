-- Draft/LaczFormalIIcWN53.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3), Lemma 6.2 (`IIcNoKites`), step (h), part 14:
-- `sub_arc`: inside a pocket Q (orientation opposite to p), an exterior chord joining two interior vertices (disjoint from the pocket chord) cuts off a sub-pocket
-- with orientation again opposite to p.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN52

open scoped Classical Fin.NatCast
open Complex Filter Topology

namespace Erdos634.Draft.LaczFormal.WN

variable {n : ℕ} [NeZero n]

theorem chord_pt_mem (x y : ℂ) {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) : x + (s : ℂ) * (y - x) ∈ segment ℝ x y := by
  rw [segment_eq_image']
  exact ⟨s, ⟨h0, h1⟩, by simp [Complex.real_smul]⟩

theorem sub_arc {p : Fin n → ℂ} (hs : SimplePoly p) (hinj : Function.Injective p) (hn : 3 ≤ n) {σ : ℝ} (Op : OrientOK p σ)
    (a : Fin n) {d : ℕ} (hd2 : 2 ≤ d) (hdn : d + 2 ≤ n)
    (hopen : ∀ s : ℝ, 0 < s → s < 1 → p (phi a d) + (s : ℂ) * (p a - p (phi a d)) ∉ edgeSet p)
    {σQ : ℝ} (OQ : OrientOK (arcPoly p a d) σQ) (hσQ : σQ = -σ)
    {x y : ℕ} (hx : 1 ≤ x) (hxy : x < y) (hy : y + 1 ≤ d)
    (hch : ExtChord p (p (phi a x)) (p (phi a y)))
    (hdis : ∀ z ∈ segment ℝ (p (phi a x)) (p (phi a y)), z ∉ segment ℝ (p (phi a d)) (p a)) :
    2 ≤ y - x ∧ ∃ σ' : ℝ, OrientOK (arcPoly p (phi a x) (y - x)) σ' ∧ σ' = -σ := by
  set Q := arcPoly p a d with hQ
  have hσ1 := Op.1.1
  have hc1 := chord_closed_sub hopen
  have hc1' : ∀ z ∈ segment ℝ (p (phi a d)) (p a), z ∈ edgeSet p → z = p a ∨ z = p (phi a d) :=
    fun z hz hE => (hc1 z hz hE).symm
  have SQ : SimplePoly Q := arc_simple hs hinj a hd2 hdn hc1'
  have IQ : Function.Injective Q := arc_inj hinj a (by omega)
  -- the chord is not an edge
  have hnadj : 2 ≤ y - x := by
    by_contra hc
    have h1 : y - x = 1 := by omega
    obtain ⟨-, h2, -⟩ := extChord_ne hch
    apply h2
    have : y = x + 1 := by omega
    rw [this, phi_succ]
  set e := y - x with he
  have hey : x + e = y := by omega
  set u : Fin (d + 1) := ⟨x, by omega⟩ with hu
  have huv : u.val = x := rfl
  have hQu : Q u = p (phi a x) := rfl
  have hvv : (phi u e).val = y := by
    unfold phi
    rw [Fin.val_add, Fin.val_natCast, Nat.mod_eq_of_lt (by omega : e < d + 1)]
    rw [Nat.mod_eq_of_lt (by omega)]
    exact hey
  have hQv : Q (phi u e) = p (phi a y) := by
    simp only [hQ, arcPoly]; rw [hvv]
  -- the chord is off Q
  have hoff : ∀ s : ℝ, 0 < s → s < 1 → p (phi a x) + (s : ℂ) * (p (phi a y) - p (phi a x)) ∉ edgeSet Q := by
    intro s hs0 hs1 hmem
    rcases edgeSet_arc_sub p a d hmem with h | h
    · exact hch.1 s hs0 hs1 h
    · exact hdis _ (chord_pt_mem _ _ hs0.le hs1.le) h
  have hoffQ : ∀ s : ℝ, 0 < s → s < 1 → Q (phi u e) + (s : ℂ) * (Q u - Q (phi u e)) ∉ edgeSet Q := by
    intro s hs0 hs1
    rw [hQu, hQv]
    have := hoff (1 - s) (by linarith) (by linarith)
    have e' : p (phi a y) + (s : ℂ) * (p (phi a x) - p (phi a y)) =
        p (phi a x) + ((1 - s : ℝ) : ℂ) * (p (phi a y) - p (phi a x)) := by push_cast; ring
    rw [e']; exact this
  -- value of the winding number of Q along the chord
  obtain ⟨s0, hs0, hnear⟩ := arc_chord_near hs hinj hn a Op OQ x hx (by omega) hch
  set s1 : ℝ := min (s0 / 2) (1 / 2) with hs1
  have hs1pos : 0 < s1 := lt_min (by linarith) (by norm_num)
  have hs1lt : s1 < s0 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hs1lt1 : s1 < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hw1 : wind Q (p (phi a x) + (s1 : ℂ) * (p (phi a y) - p (phi a x))) = -σ := by
    have := (hnear s1 hs1pos hs1lt hs1lt1).2 hσQ
    rw [this, hσQ]
  have hwmid : wind Q (Q (phi u e) + ((1 / 2 : ℝ) : ℂ) * (Q u - Q (phi u e))) = -σ := by
    rw [hQu, hQv]
    have e' : p (phi a y) + ((1 / 2 : ℝ) : ℂ) * (p (phi a x) - p (phi a y)) =
        p (phi a x) + ((1 / 2 : ℝ) : ℂ) * (p (phi a y) - p (phi a x)) := by push_cast; ring
    rw [e', ← hw1]
    exact (wind_const_on_chord Q hoff (by norm_num) (by norm_num) hs1pos hs1lt1)
  -- split Q along the chord
  obtain ⟨σ1, σ2, O1, O2⟩ := arc_pair_orient SQ IQ u (d := e) hnadj (by omega) hoffQ
  have hsg := chord_signs IQ u (d := e) hnadj (by omega) hoffQ O1.1 O2.1 hwmid
  have hne : (-σ) ≠ 0 := by rcases hσ1 with rfl | rfl <;> norm_num
  have h1 : σ1 = -σ := (hsg.2 hne).1
  refine ⟨hnadj, σ1, ?_, h1⟩
  have := arcPoly_arcPoly p a u (e := e) (by rw [huv]; omega)
  rw [huv] at this
  rw [← this]
  exact O1

end Erdos634.Draft.LaczFormal.WN

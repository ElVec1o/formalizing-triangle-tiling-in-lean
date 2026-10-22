-- Draft/LaczFormalIIcWN64.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3), Lemma 6.2 (`IIcNoKites`), step (i), part 8:
-- `RingSetup.adjacent`: c (w i) and c (w (i+1)) are adjacent vertices of c.  Proof: if not, the neighbours c(a+1), c(a-1) of c a (a = w i) lie on opposite sides of
-- the line c b -- c a, both have winding number 0 about them for the quadrilateral Q_i (claim_X); but across the edge c b -> c a of Q_i the winding number jumps by 1
-- and each side is joined to its vertex inside c, avoiding Q_i.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN63

open scoped Classical Fin.NatCast
open Complex Filter Topology

namespace Erdos634.Draft.LaczFormal.WN

variable {N : ℕ} [NeZero N]

section Ring
variable {A c : Fin N → ℂ} {w : Fin N → Fin N} {τA τC : ℝ}

theorem sideFn_pos_seg {x0 d z1 z2 z : ℂ} (h1 : 0 < sideFn x0 d z1) (h2 : 0 < sideFn x0 d z2) (hz : z ∈ segment ℝ z1 z2) :
    0 < sideFn x0 d z := by
  obtain ⟨s, h0, h1', rfl⟩ := seg_param hz
  have := comb_pos (τ := 1) (x0 := x0) (d := d) (z1 := z1) (z2 := z2) h0 h1' (by simpa using h1) (by simpa using h2)
  simpa using this

theorem sideFn_neg_seg {x0 d z1 z2 z : ℂ} (h1 : sideFn x0 d z1 < 0) (h2 : sideFn x0 d z2 < 0) (hz : z ∈ segment ℝ z1 z2) :
    sideFn x0 d z < 0 := by
  obtain ⟨s, h0, h1', rfl⟩ := seg_param hz
  have := comb_pos (τ := -1) (x0 := x0) (d := d) (z1 := z1) (z2 := z2) h0 h1' (by linarith) (by linarith)
  linarith

theorem RingSetup.adjacent (R : RingSetup A c w τA τC) (i : Fin N) : w (i + 1) = w i + 1 ∨ w i = w (i + 1) + 1 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hb1, hb2⟩ := hcon
  have hn := R.hN
  set a := w i with ha
  set b := w (i + 1) with hb
  have hi1 : i + 1 ≠ i := by
    intro h
    have : (1 : Fin N) = 0 := by simpa using h
    exact fin_one_ne hn this
  have hba : b ≠ a := fun h => hi1 (R.w_inj h)
  have hb3 : b ≠ a - 1 := by
    intro h
    apply hb2
    rw [h]; simp
  have hsurj : Function.Surjective w := Finite.injective_iff_surjective.1 R.w_inj
  obtain ⟨hplus, hminus⟩ := side_opposite R.cinj hn R.SCc a b hba hb1 hb3
  have hne1 : a + 1 ≠ a := by
    intro h
    have : (1 : Fin N) = 0 := by simpa using h
    exact fin_one_ne hn this
  have hne2 : a - 1 ≠ a := by
    intro h
    have : (1 : Fin N) = 0 := by
      have := congrArg (fun x => a - x) h
      simpa using this
    exact fin_one_ne hn this
  -- vertices on the positive / negative side of the directed line c b -> c a
  obtain ⟨mp, mm, hmp, hmm, hp, hm⟩ : ∃ mp mm : Fin N, (mp = a + 1 ∨ mp = a - 1) ∧ (mm = a + 1 ∨ mm = a - 1) ∧
      0 < sideFn (c b) (c a - c b) (c mp) ∧ sideFn (c b) (c a - c b) (c mm) < 0 := by
    rcases R.τC1 with h | h
    · rw [h] at hplus hminus
      exact ⟨a + 1, a - 1, Or.inl rfl, Or.inr rfl, by linarith, by linarith⟩
    · rw [h] at hplus hminus
      exact ⟨a - 1, a + 1, Or.inr rfl, Or.inl rfl, by linarith, by linarith⟩
  have hmp_ne : mp ≠ a ∧ mp ≠ b := by
    rcases hmp with h | h <;> rw [h]
    · exact ⟨hne1, fun h' => hb1 h'.symm⟩
    · exact ⟨hne2, fun h' => hb3 h'.symm⟩
  have hmm_ne : mm ≠ a ∧ mm ≠ b := by
    rcases hmm with h | h <;> rw [h]
    · exact ⟨hne1, fun h' => hb1 h'.symm⟩
    · exact ⟨hne2, fun h' => hb3 h'.symm⟩
  obtain ⟨kp, hkp⟩ := hsurj mp
  obtain ⟨km, hkm⟩ := hsurj mm
  have wp := R.claim_X (i := i) (k := kp) (fun h => hmp_ne.1 (by rw [← hkp, h])) (fun h => hmp_ne.2 (by rw [← hkp, h]))
  have wm := R.claim_X (i := i) (k := km) (fun h => hmm_ne.1 (by rw [← hkm, h])) (fun h => hmm_ne.2 (by rw [← hkm, h]))
  rw [hkp] at wp
  rw [hkm] at wm
  set Q := quad (A i) (A (i + 1)) (c b) (c a) with hQ
  -- jump across the edge c b -> c a of Q
  have hd : Q (2 + 1) - Q 2 ≠ 0 := by
    simp only [hQ, quad]
    exact sub_ne_zero.2 (fun h => hba (R.cinj h).symm)
  have hxs : ∀ j, 0 < τC * sideFn (c j) (c (j + 1) - c j) (c b + ((1 / 2 : ℝ) : ℂ) * (c a - c b)) :=
    fun j => R.mid_strict (fun h => hba (R.cinj (by rw [h])).symm) (fun h => hb1 h) (fun h => hb2 h) j
  have hxA : 0 < τA * sideFn (A i) (A (i + 1) - A i) (c b + ((1 / 2 : ℝ) : ℂ) * (c a - c b)) :=
    comb_pos (by norm_num) (by norm_num) (R.inside i b) (R.inside i a)
  have hQ2 : Q 2 = c b := by simp [hQ, quad]
  have hQ3 : Q (2 + 1) = c a := by simp [hQ, quad]
  have hx0 : sidePt (c b) (c a) (1 / 2) 0 = c b + ((1 / 2 : ℝ) : ℂ) * (c a - c b) := by simp [sidePt]
  have hxne1 : c b + ((1 / 2 : ℝ) : ℂ) * (c a - c b) ≠ c b := by
    intro h
    have := hxs b
    rw [h, sideFn_base] at this
    simp at this
  have hxne2 : c b + ((1 / 2 : ℝ) : ℂ) * (c a - c b) ≠ c a := by
    intro h
    have := hxs a
    rw [h, sideFn_base] at this
    simp at this
  have hother : ∀ j, j ≠ 2 → sidePt (Q 2) (Q (2 + 1)) (1 / 2) 0 ∉ segment ℝ (Q j) (Q (j + 1)) := by
    intro j hj hmem
    rw [hQ2, hQ3, hx0] at hmem
    obtain ⟨o0, o1, o3⟩ := R.off_three i (fun j => (hxs j).le) hxA hxne1 hxne2
    fin_cases j
    · exact o0 (by simpa [hQ, quad] using hmem)
    · exact o1 (by simpa [hQ, quad] using hmem)
    · exact hj rfl
    · exact o3 (by simpa [hQ, quad] using hmem)
  have hjump := wind_jump Q 2 hd (s := 1 / 2) (by norm_num) (by norm_num) hother
  rw [hQ2, hQ3] at hjump
  -- small t
  have hcontC : ∀ j, Continuous (fun t : ℝ => τC * sideFn (c j) (c (j + 1) - c j) (sidePt (c b) (c a) (1 / 2) t)) := by
    intro j; unfold sideFn sidePt; fun_prop
  have hcontA : Continuous (fun t : ℝ => τA * sideFn (A i) (A (i + 1) - A i) (sidePt (c b) (c a) (1 / 2) t)) := by
    unfold sideFn sidePt; fun_prop
  have hevC : ∀ j, ∀ᶠ t in 𝓝 (0 : ℝ), 0 < τC * sideFn (c j) (c (j + 1) - c j) (sidePt (c b) (c a) (1 / 2) t) := fun j =>
    ((hcontC j).continuousAt).eventually (lt_mem_nhds (by simpa only [hx0] using hxs j))
  have hevA : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < τA * sideFn (A i) (A (i + 1) - A i) (sidePt (c b) (c a) (1 / 2) t) :=
    (hcontA.continuousAt).eventually (lt_mem_nhds (by simpa only [hx0] using hxA))
  have hev := (Filter.eventually_all.2 hevC).and hevA
  obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff.1 hev
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Set.Ioo 0 ε := Ioo_mem_nhdsGT hε
  obtain ⟨t, ⟨-, -, hjt⟩, ht⟩ := (hjump.and hsmall).exists
  have ht0 : 0 < t := ht.1
  have hPL := hεP (y := t) (by rw [Real.dist_eq, sub_zero, abs_of_pos ht0]; exact ht.2)
  have hPR := hεP (y := -t) (by rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos ht0]; exact ht.2)
  have hba' : c a - c b ≠ 0 := sub_ne_zero.2 (fun h => hba (R.cinj h).symm)
  have hφmid : ∀ u : ℝ, sideFn (c b) (c a - c b) (sidePt (c b) (c a) (1 / 2) u) = u := by
    intro u
    have := sideFn_sidePt hba' (1 / 2) u
    rw [show c b + ((1 / 2 : ℝ) : ℂ) * (c a - c b) = c b + ((1 / 2 : ℝ) : ℂ) * (c a - c b) from rfl, sideFn_mid] at this
    exact this
  -- the two vertices are joined to the two sides inside c, avoiding Q
  have wL : wind Q (sidePt (c b) (c a) (1 / 2) t) = 0 := by
    rw [← wp]
    apply wind_const_segment
    intro z hz
    apply R.no_Q_hit i
    · intro j
      obtain ⟨s', h0, h1, rfl⟩ := seg_param hz
      exact comb_nonneg h0 h1 (hPL.1 j).le (R.SCc.vert_nonneg R.cinj hn j mp)
    · obtain ⟨s', h0, h1, rfl⟩ := seg_param hz
      exact comb_pos h0 h1 hPL.2 (R.inside i mp)
    · have := sideFn_pos_seg (x0 := c b) (d := c a - c b) (by rw [hφmid]; exact ht0) hp hz
      exact this.ne'
  have wR : wind Q (sidePt (c b) (c a) (1 / 2) (-t)) = 0 := by
    rw [← wm]
    apply wind_const_segment
    intro z hz
    apply R.no_Q_hit i
    · intro j
      obtain ⟨s', h0, h1, rfl⟩ := seg_param hz
      exact comb_nonneg h0 h1 (hPR.1 j).le (R.SCc.vert_nonneg R.cinj hn j mm)
    · obtain ⟨s', h0, h1, rfl⟩ := seg_param hz
      exact comb_pos h0 h1 hPR.2 (R.inside i mm)
    · have := sideFn_neg_seg (x0 := c b) (d := c a - c b) (by rw [hφmid]; linarith) hm hz
      exact this.ne
  rw [wL, wR] at hjt
  norm_num at hjt

end Ring

end Erdos634.Draft.LaczFormal.WN

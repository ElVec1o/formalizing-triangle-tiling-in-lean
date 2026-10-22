-- Draft/LaczFormalIIcWN66.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3), Lemma 6.2 (`IIcNoKites`), step (i): NON-VACUITY witness for `RingSetup` / `ring_order`.
-- Outer triangle A = (4, -2+4i, -2-4i), inner triangle c = (1, -1/2+i, -1/2-i), chords A i -- c i (radial), w = identity: every hypothesis of RingSetup holds.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN65

open scoped Classical Fin.NatCast
open Complex

namespace Erdos634.Draft.LaczFormal.WN

noncomputable def wA : Fin 3 → ℂ := ![(4 : ℂ), ⟨-2, 4⟩, ⟨-2, -4⟩]
noncomputable def wc : Fin 3 → ℂ := ![(1 : ℂ), ⟨-1 / 2, 1⟩, ⟨-1 / 2, -1⟩]

theorem sideFn_ri (x0 d z : ℂ) : sideFn x0 d z = ((z - x0).im * d.re - (z - x0).re * d.im) / Complex.normSq d := by
  unfold sideFn
  rw [Complex.div_im]
  ring

theorem wA_inj : Function.Injective wA := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [wA, Complex.ext_iff] at h ⊢ <;> norm_num at h

theorem wc_inj : Function.Injective wc := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [wc, Complex.ext_iff] at h ⊢ <;> norm_num at h

theorem wA_SC : SC wA 1 := by
  intro j m h1 h2
  fin_cases j <;> fin_cases m <;> simp at h1 h2 ⊢ <;> simp [sideFn_ri, wA, Complex.normSq_apply] <;> norm_num

theorem wc_SC : SC wc 1 := by
  intro j m h1 h2
  fin_cases j <;> fin_cases m <;> simp at h1 h2 ⊢ <;> simp [sideFn_ri, wc, Complex.normSq_apply] <;> norm_num

theorem w_inside : ∀ j m : Fin 3, 0 < (1 : ℝ) * sideFn (wA j) (wA (j + 1) - wA j) (wc m) := by
  intro j m
  fin_cases j <;> fin_cases m <;> simp [sideFn_ri, wA, wc, Complex.normSq_apply] <;> norm_num

theorem w_out : ∀ (i : Fin 3) (s : ℝ), 0 ≤ s → s < 1 →
    ∃ j, (1 : ℝ) * sideFn (wc j) (wc (j + 1) - wc j) (wA i + (s : ℂ) * (wc ((fun x : Fin 3 => x) i) - wA i)) < 0 := by
  intro i s h0 h1
  fin_cases i
  · refine ⟨0, ?_⟩
    simp only [one_mul]
    rw [sideFn_ri]
    apply div_neg_of_neg_of_pos
    · simp [wA, wc]; nlinarith
    · simp [wc, Complex.normSq_apply]; norm_num
  · refine ⟨1, ?_⟩
    simp only [one_mul]
    rw [sideFn_ri]
    apply div_neg_of_neg_of_pos
    · simp [wA, wc]; nlinarith
    · simp [wc, Complex.normSq_apply]; norm_num
  · refine ⟨1, ?_⟩
    simp only [one_mul]
    rw [sideFn_ri]
    apply div_neg_of_neg_of_pos
    · simp [wA, wc]; nlinarith
    · simp [wc, Complex.normSq_apply]; norm_num

theorem w_disj : ∀ i j : Fin 3, i ≠ j → Disjoint (segment ℝ (wA i) (wc ((fun x : Fin 3 => x) i))) (segment ℝ (wA j) (wc ((fun x : Fin 3 => x) j))) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro z h1 h2
  obtain ⟨s, h0, h1', rfl⟩ := seg_param h1
  obtain ⟨s', h0', h1'', heq⟩ := seg_param h2
  have hre := congrArg Complex.re heq
  have him := congrArg Complex.im heq
  fin_cases i <;> fin_cases j <;> simp [wA, wc] at hij hre him <;> nlinarith

theorem ring_witness : ∃ (A c : Fin 3 → ℂ) (w : Fin 3 → Fin 3) (τA τC : ℝ), RingSetup A c w τA τC := by
  refine ⟨wA, wc, fun x => x, 1, 1, ?_⟩
  exact ⟨le_refl 3, Or.inl rfl, Or.inl rfl, wA_inj, wc_inj, wA_SC, wc_SC, w_inside, w_out, w_disj⟩

#print axioms ring_witness

end Erdos634.Draft.LaczFormal.WN

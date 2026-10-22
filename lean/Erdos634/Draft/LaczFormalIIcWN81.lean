-- Draft/LaczFormalIIcWN81.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3), Lemma 6.2: NON-VACUITY witnesses for the pure-geometry hypotheses of WN71-WN77.
-- (1) the triangle `(2, i, 0, 1)` with the straight vertex `1` (the last vertex, between `0` and `2`): `SimplePoly`, injective, `extAng p 3 = 0`, so the hypotheses of `delLast_*` (WN72) and `exists_corner` (WN73) are satisfiable;
-- (2) the square `(1, i, -1, -i)`: injective, `extAng = pi/2 = 2 pi / 4` at every vertex, so the hypotheses of `equiangular_SC` (WN77) are satisfiable, with the conclusion `SC q 1`.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN77
import Erdos634.Draft.LaczFormalIIcWN73

open scoped Classical Fin.NatCast
open Complex

namespace Erdos634.Draft.LaczFormal.WN

theorem mem_seg_iff (a b z : ℂ) : z ∈ segment ℝ a b ↔ ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ z.re = a.re + s * (b.re - a.re) ∧ z.im = a.im + s * (b.im - a.im) := by
  rw [segment_eq_image']
  constructor
  · rintro ⟨s, ⟨h0, h1⟩, rfl⟩
    exact ⟨s, h0, h1, by simp, by simp⟩
  · rintro ⟨s, h0, h1, hre, him⟩
    refine ⟨s, ⟨h0, h1⟩, ?_⟩
    apply Complex.ext <;> simp [hre, him]

/-- The triangle with a straight vertex: vertices `2, i, 0, 1` (the last one lies on the segment `[0, 2]`). -/
noncomputable def pS : Fin 4 → ℂ := ![(2 : ℂ), Complex.I, 0, 1]

theorem pS_inj : Function.Injective pS := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [pS, Complex.ext_iff] at h ⊢ <;> norm_num at h

theorem pS_simple : SimplePoly pS := by
  intro i j hij z hz
  obtain ⟨hz1, hz2⟩ := hz
  rw [mem_seg_iff] at hz1 hz2
  obtain ⟨s, hs0, hs1, hsr, hsi⟩ := hz1
  obtain ⟨t, ht0, ht1, htr, hti⟩ := hz2
  fin_cases i <;> fin_cases j <;> simp [pS, Complex.ext_iff] at hij hsr hsi htr hti ⊢ <;>
    first
    | (refine ⟨?_, ?_⟩ <;> first
        | (left; constructor <;> linarith)
        | (right; constructor <;> linarith)
        | (exfalso; linarith))
    | skip

theorem pS_straight : extAng pS (Fin.last 3) = 0 := by
  unfold extAng
  have e1 : (Fin.last 3 : Fin 4) + 1 = 0 := by decide
  have e2 : (Fin.last 3 : Fin 4) - 1 = 2 := by decide
  rw [e1, e2]
  simp [pS]
  norm_num

/-- The hypotheses of `exists_corner` hold for `pS`, and its corner polygon exists (no new claim: the witness shows the hypotheses are satisfiable). -/
theorem pS_corner : ∃ (m : ℕ) (_ : NeZero m) (q : Fin m → ℂ), IsCornerOf pS q :=
  exists_corner pS pS_simple pS_inj (by norm_num)

/-- The square. -/
noncomputable def sq4 : Fin 4 → ℂ := ![(1 : ℂ), Complex.I, -1, -Complex.I]

theorem sq4_inj : Function.Injective sq4 := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [sq4, Complex.ext_iff] at h ⊢ <;> norm_num at h

theorem sq4_turn (k : Fin 4) : (1 : ℝ) * extAng sq4 k = 2 * Real.pi / (4 : ℕ) := by
  unfold extAng
  have : ∀ k : Fin 4, (sq4 (k + 1) - sq4 k) / (sq4 k - sq4 (k - 1)) = Complex.I := by
    intro k
    have key : ∀ a b : ℂ, b ≠ 0 → a = Complex.I * b → a / b = Complex.I := by
      intro a b hb h; rw [h]; field_simp
    fin_cases k <;> simp only [sq4] <;> apply key <;> simp [Complex.ext_iff] <;> norm_num
  rw [this k, Complex.arg_I]
  push_cast
  ring

theorem sq4_SC : SC sq4 1 := equiangular_SC sq4_inj (by norm_num) (Or.inl rfl) (by push_cast; rfl) sq4_turn

#print axioms pS_simple
#print axioms pS_straight
#print axioms sq4_SC

end Erdos634.Draft.LaczFormal.WN

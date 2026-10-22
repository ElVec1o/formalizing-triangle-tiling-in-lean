-- Draft/LaczFormalIIcWN60.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3), Lemma 6.2 (`IIcNoKites`), step (i), part 4:
-- `RingSetup` (outer strictly convex polygon A, inner strictly convex polygon c strictly inside, disjoint exterior chords A i -- c (w i)), the quadrilateral
-- `quad`, and `wind_zero_outer`: the winding number of a polygon whose vertices all lie strictly on the inner side of the two edge lines at a vertex A k is 0 at A k.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN59

open scoped Classical Fin.NatCast
open Complex Filter Topology

namespace Erdos634.Draft.LaczFormal.WN

variable {N : ℕ} [NeZero N]

structure RingSetup (A c : Fin N → ℂ) (w : Fin N → Fin N) (τA τC : ℝ) : Prop where
  hN : 3 ≤ N
  τA1 : τA = 1 ∨ τA = -1
  τC1 : τC = 1 ∨ τC = -1
  Ainj : Function.Injective A
  cinj : Function.Injective c
  SA : SC A τA
  SCc : SC c τC
  inside : ∀ j m : Fin N, 0 < τA * sideFn (A j) (A (j + 1) - A j) (c m)
  out : ∀ (i : Fin N) (s : ℝ), 0 ≤ s → s < 1 →
    ∃ j, τC * sideFn (c j) (c (j + 1) - c j) (A i + (s : ℂ) * (c (w i) - A i)) < 0
  disj : ∀ i j : Fin N, i ≠ j → Disjoint (segment ℝ (A i) (c (w i))) (segment ℝ (A j) (c (w j)))

def quad (p0 p1 p2 p3 : ℂ) : Fin 4 → ℂ := ![p0, p1, p2, p3]

theorem mem_edgeSet_quad (p0 p1 p2 p3 z : ℂ) :
    z ∈ edgeSet (quad p0 p1 p2 p3) ↔
      z ∈ segment ℝ p0 p1 ∨ z ∈ segment ℝ p1 p2 ∨ z ∈ segment ℝ p2 p3 ∨ z ∈ segment ℝ p3 p0 := by
  unfold edgeSet
  rw [Set.mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i <;> simp [quad] at hi ⊢ <;> tauto
  · rintro (h | h | h | h)
    · exact ⟨0, by simpa [quad] using h⟩
    · exact ⟨1, by simpa [quad] using h⟩
    · exact ⟨2, by simpa [quad] using h⟩
    · exact ⟨3, by simpa [quad] using h⟩

theorem fin_pred_ne_succ (hn : 3 ≤ N) (k : Fin N) : k - 1 ≠ k + 1 := by
  intro h
  apply fin_one_add_one_ne hn
  calc (1 : Fin N) + 1 = (k + 1) - (k - 1) := by abel
    _ = 0 := by rw [← h]; simp

theorem wind_zero_outer {m : ℕ} [NeZero m] {A : Fin N → ℂ} {τA : ℝ} (hn : 3 ≤ N) (hAinj : Function.Injective A) (hSA : SC A τA)
    (hτ : τA = 1 ∨ τA = -1) (k : Fin N) (q : Fin m → ℂ)
    (hq : ∀ i, 0 < τA * (sideFn (A (k - 1)) (A (k - 1 + 1) - A (k - 1)) (q i) + sideFn (A k) (A (k + 1) - A k) (q i))) :
    wind q (A k) = 0 := by
  have he1 : A (k - 1 + 1) - A (k - 1) ≠ 0 := sub_ne_zero.2 (nd hAinj hn (k - 1))
  have he2 : A (k + 1) - A k ≠ 0 := sub_ne_zero.2 (nd hAinj hn k)
  rw [sub_add_cancel] at he1
  simp only [sub_add_cancel] at hq
  set e1 := A k - A (k - 1) with he1def
  set e2 := A (k + 1) - A k with he2def
  set μ : ℂ := (τA : ℂ) * (e1⁻¹ + e2⁻¹) with hμ
  have hform : ∀ z : ℂ, τA * (sideFn (A (k - 1)) e1 z + sideFn (A k) e2 z) = ((z - A k) * μ).im := by
    intro z
    unfold sideFn
    have h1 : (z - A (k - 1)) / e1 = (z - A k) / e1 + 1 := by
      have : z - A (k - 1) = (z - A k) + e1 := by rw [he1def]; ring
      rw [this, add_div, div_self he1]
    rw [h1, hμ]
    have : (z - A k) * ((τA : ℂ) * (e1⁻¹ + e2⁻¹)) = (τA : ℂ) * ((z - A k) / e1 + (z - A k) / e2) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]; ring
    rw [this, Complex.im_ofReal_mul]
    simp [Complex.add_im]
  have hμ0 : μ ≠ 0 := by
    intro h0
    have := hq 0
    rw [hform] at this
    rw [h0] at this
    simp at this
  refine wind_zero_of_affine q hμ0 (fun i => ?_)
  rw [← hform]
  exact hq i

end Erdos634.Draft.LaczFormal.WN

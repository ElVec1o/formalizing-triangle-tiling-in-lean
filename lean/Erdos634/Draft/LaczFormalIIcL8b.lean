-- Draft/LaczFormalIIcL8b.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.3, index split (G10), step 2: PURE PLANE GEOMETRY.
-- `seg_enter`: a segment from a point S outside a closed (nondegenerate, counterclockwise) triangle (A,E,C) -- strictly on the side of E of the line AC and
-- negative in the barycentric coordinate of A or of C -- to a point R of the triangle meets the two sides AE, EC (first-entry argument with explicit roots of the affine
-- barycentric coordinates).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalThm21Area

open Erdos634.Geometry Erdos634.Draft.LaczFormal.Thm21

namespace Erdos634.Draft.LaczFormal.RG

theorem pl_ext {u w : Plane} (h0 : u 0 = w 0) (h1 : u 1 = w 1) : u = w := by
  ext i; fin_cases i <;> simpa

/-- barycentric numerators of `X` in the triangle `(A, E, C)`. -/
def tlA (E C X : Plane) : ℝ := cross2 (E - X) (C - X)
def tlE (A C X : Plane) : ℝ := cross2 (C - X) (A - X)
def tlC (A E X : Plane) : ℝ := cross2 (A - X) (E - X)

theorem tl_sum (A E C X : Plane) : tlA E C X + tlE A C X + tlC A E X = cross2 (E - A) (C - A) := by
  unfold tlA tlE tlC cross2; simp only [PiLp.sub_apply]; ring

theorem tl_bary (A E C X : Plane) : cross2 (E - A) (C - A) • X = tlA E C X • A + tlE A C X • E + tlC A E X • C := by
  apply pl_ext
  · simp only [PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]; unfold tlA tlE tlC cross2; simp only [PiLp.sub_apply]; ring
  · simp only [PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]; unfold tlA tlE tlC cross2; simp only [PiLp.sub_apply]; ring

theorem tlA_comb (E C S R : Plane) (t : ℝ) : tlA E C ((1 - t) • S + t • R) = (1 - t) * tlA E C S + t * tlA E C R := by
  unfold tlA cross2; simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
theorem tlE_comb (A C S R : Plane) (t : ℝ) : tlE A C ((1 - t) • S + t • R) = (1 - t) * tlE A C S + t * tlE A C R := by
  unfold tlE cross2; simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
theorem tlC_comb (A E S R : Plane) (t : ℝ) : tlC A E ((1 - t) • S + t • R) = (1 - t) * tlC A E S + t * tlC A E R := by
  unfold tlC cross2; simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

/-- a point of the triangle with vanishing `A`-coordinate lies on the side `EC`. -/
theorem on_side_EC {A E C X : Plane} (hΔ : 0 < cross2 (E - A) (C - A)) (h0 : tlA E C X = 0) (hE : 0 ≤ tlE A C X) (hC : 0 ≤ tlC A E X) :
    X ∈ segment ℝ E C := by
  have hs := tl_sum A E C X
  have hb := tl_bary A E C X
  rw [h0, zero_smul, zero_add] at hb
  refine ⟨tlE A C X / cross2 (E - A) (C - A), tlC A E X / cross2 (E - A) (C - A), div_nonneg hE hΔ.le, div_nonneg hC hΔ.le, ?_, ?_⟩
  · rw [← add_div, div_eq_one_iff_eq hΔ.ne']; linarith
  · have h := congrArg (fun z => (cross2 (E - A) (C - A))⁻¹ • z) hb
    simp only [smul_smul, inv_mul_cancel₀ hΔ.ne', one_smul, smul_add] at h
    simp only [div_eq_inv_mul]; exact h.symm

/-- a point of the triangle with vanishing `C`-coordinate lies on the side `AE`. -/
theorem on_side_AE {A E C X : Plane} (hΔ : 0 < cross2 (E - A) (C - A)) (h0 : tlC A E X = 0) (hA : 0 ≤ tlA E C X) (hE : 0 ≤ tlE A C X) :
    X ∈ segment ℝ A E := by
  have hs := tl_sum A E C X
  have hb := tl_bary A E C X
  rw [h0, zero_smul, add_zero] at hb
  refine ⟨tlA E C X / cross2 (E - A) (C - A), tlE A C X / cross2 (E - A) (C - A), div_nonneg hA hΔ.le, div_nonneg hE hΔ.le, ?_, ?_⟩
  · rw [← add_div, div_eq_one_iff_eq hΔ.ne']; linarith
  · have h := congrArg (fun z => (cross2 (E - A) (C - A))⁻¹ • z) hb
    simp only [smul_smul, inv_mul_cancel₀ hΔ.ne', one_smul, smul_add] at h
    simp only [div_eq_inv_mul]; exact h.symm

/-- the root of the affine function `s + t (r - s)` with `s < 0 <= r`. -/
noncomputable def aroot (s r : ℝ) : ℝ := s / (s - r)

theorem aroot_facts {s r : ℝ} (hs : s < 0) (hr : 0 ≤ r) :
    0 ≤ aroot s r ∧ aroot s r ≤ 1 ∧ (1 - aroot s r) * s + aroot s r * r = 0 := by
  have hd : s - r < 0 := by linarith
  unfold aroot
  refine ⟨div_nonneg_of_nonpos hs.le hd.le, ?_, ?_⟩
  · rw [div_le_one_of_neg hd]; linarith
  · have h : s / (s - r) * (s - r) = s := div_mul_cancel₀ _ hd.ne
    linear_combination (-1 : ℝ) * h

theorem aroot_mono {s r : ℝ} (hs : s < 0) (hr : 0 ≤ r) {u v : ℝ} (hu : aroot s r ≤ u) (hv : v = (1 - u) * s + u * r) : 0 ≤ v := by
  have hf := aroot_facts hs hr
  have hd : 0 < r - s := by linarith
  have : v = (u - aroot s r) * (r - s) := by
    have e : (1 - aroot s r) * s + aroot s r * r = 0 := hf.2.2
    rw [hv]; linear_combination e
  rw [this]; exact mul_nonneg (by linarith) hd.le

/-- **First entry.**  A segment from `S` (strictly on the `E` side of `AC`, with negative `A`- or `C`-coordinate) to a point `R` of the closed triangle meets `AE ∪ EC`. -/
theorem seg_enter {A E C S R : Plane} (hΔ : 0 < cross2 (E - A) (C - A)) (hSE : 0 < tlE A C S)
    (hS : tlA E C S < 0 ∨ tlC A E S < 0) (hRA : 0 ≤ tlA E C R) (hRE : 0 ≤ tlE A C R) (hRC : 0 ≤ tlC A E R) :
    ∃ X ∈ segment ℝ S R, X ∈ segment ℝ A E ∨ X ∈ segment ℝ E C := by
  have hmem : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (1 - t) • S + t • R ∈ segment ℝ S R := fun t h0 h1 =>
    ⟨1 - t, t, by linarith, h0, by ring, rfl⟩
  have hEt : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → 0 ≤ tlE A C ((1 - t) • S + t • R) := fun t h0 h1 => by
    rw [tlE_comb]; nlinarith
  by_cases hA : tlA E C S < 0
  · by_cases hC : tlC A E S < 0
    · rcases le_total (aroot (tlC A E S) (tlC A E R)) (aroot (tlA E C S) (tlA E C R)) with h | h
      · obtain ⟨a0, a1, a2⟩ := aroot_facts hA hRA
        refine ⟨_, hmem _ a0 a1, Or.inr (on_side_EC hΔ ?_ (hEt _ a0 a1) ?_)⟩
        · rw [tlA_comb]; exact a2
        · rw [tlC_comb]; exact aroot_mono hC hRC h rfl
      · obtain ⟨a0, a1, a2⟩ := aroot_facts hC hRC
        refine ⟨_, hmem _ a0 a1, Or.inl (on_side_AE hΔ ?_ ?_ (hEt _ a0 a1))⟩
        · rw [tlC_comb]; exact a2
        · rw [tlA_comb]; exact aroot_mono hA hRA h rfl
    · obtain ⟨a0, a1, a2⟩ := aroot_facts hA hRA
      refine ⟨_, hmem _ a0 a1, Or.inr (on_side_EC hΔ ?_ (hEt _ a0 a1) ?_)⟩
      · rw [tlA_comb]; exact a2
      · rw [tlC_comb]; push_neg at hC; nlinarith
  · have hC : tlC A E S < 0 := hS.resolve_left hA
    push_neg at hA
    obtain ⟨a0, a1, a2⟩ := aroot_facts hC hRC
    refine ⟨_, hmem _ a0 a1, Or.inl (on_side_AE hΔ ?_ ?_ (hEt _ a0 a1))⟩
    · rw [tlC_comb]; exact a2
    · rw [tlA_comb]; nlinarith

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.seg_enter

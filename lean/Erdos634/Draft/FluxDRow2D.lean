-- Draft/FluxDRow2D.lean — ROW 2, LEMMA D ((private working notes, not included) §5 "Lemma D (the side
-- matrix)", errata 1: six S*-shapes, one survivor) as PURE LINEAR ALGEBRA.  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
--
-- Statement (file): `D ∈ M₃(ℤ≥0)` (rows BC, CA, AB; columns a, b, c) with `D v = μ v`, `v > 0`,
-- `μ ∉ ℚ`, `μ² ∈ ℤ`, every row nonzero, and the corner conditions
--   (A) `(D_cb ≥ 1 ∧ D_bc ≥ 1) ∨ (D_cc ≥ 1 ∧ D_bb ≥ 1)`,  (B) `(D_ca ≥ 1 ∧ D_ac ≥ 1) ∨ (D_cc ≥ 1 ∧ D_aa ≥ 1)`
-- force `D = [[0,0,A],[0,0,B],[D_ca,D_cb,0]]` with `A, B, D_ca, D_cb ≥ 1`.
-- Proof, as the file's: `−μ` is an eigenvalue (the characteristic polynomial has integer coefficients
-- and `μ` is a quadratic irrational: `Row2.neg_eigen_det`); for a `−μ` eigenvector `w` and
-- `t = max |w_j|/v_j`, the sign lemma (`i ∈ S*`, `D_ij > 0` ⇒ `j ∈ S*` with the opposite sign) is
-- `Σ_j D_ij (t v_j ± w_j) = 0` with nonnegative terms; then the shapes: `c ∈ S*` (else `a ∈ S*` and
-- (B) fails), and with `c ∈ S*` the zero diagonal plus (A), (B) give the survivor.  The file's
-- six-shape enumeration is compressed into these two cases (same content).
--
-- NOT formalized here (named): the geometric inputs — S1 (the side matrix of a real tiling:
-- `D_ij` = number of `j`-edges on side `i`; `EdgeWordConversion.side_walk_congruent` gives the words
-- but not the typed count), S2's corner conditions (A), (B) (the corner tile at A is a single
-- α-corner, at B a single β-corner, needing `β ∉ ℤα`), S3 `μ = √N`.  Lemmas K, Q, E, R are not
-- started.  Witness (Draft/FluxDRow2DWitness.lean): the file's survivor `(1, 2, √7)`, `N = 7`,
-- `D = [[0,0,1],[0,0,2],[1,3,0]]` (phantom P2 — an algebraic model, not a tiling).
--
-- Formalization debt; not progress on the three /goal outcomes.
import Erdos634.Draft.FluxDRow12b

open scoped Classical

namespace Erdos634.Geometry

/-- The characteristic polynomial of a real `3 × 3` matrix, written out. -/
theorem Row2.det_sub_smul (A : Matrix (Fin 3) (Fin 3) ℝ) (x : ℝ) :
    (A - x • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det
      = -x ^ 3 + (A 0 0 + A 1 1 + A 2 2) * x ^ 2
        - (A 0 0 * A 1 1 + A 0 0 * A 2 2 + A 1 1 * A 2 2 - A 1 2 * A 2 1 - A 0 1 * A 1 0
            - A 0 2 * A 2 0) * x
        + (A 0 0 * A 1 1 * A 2 2 - A 0 0 * A 1 2 * A 2 1 - A 0 1 * A 1 0 * A 2 2
            + A 0 1 * A 1 2 * A 2 0 + A 0 2 * A 1 0 * A 2 1 - A 0 2 * A 1 1 * A 2 0) := by
  rw [Matrix.det_fin_three]
  simp
  ring

/-- **`−μ` is an eigenvalue.**  If a `3 × 3` matrix with natural entries has the eigenvalue `μ ∉ ℚ`
with `μ² ∈ ℤ`, it also has `−μ`: `det (D + μ·1) = 0`. -/
theorem Row2.neg_eigen_det (D : Fin 3 → Fin 3 → ℕ) {μ : ℝ} (hμ : ¬ ∃ r : ℚ, μ = r) {p : ℤ}
    (hp : μ ^ 2 = p)
    (hdet : (Matrix.of (fun i j => (D i j : ℝ)) - μ • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det = 0) :
    (Matrix.of (fun i j => (D i j : ℝ)) + μ • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det = 0 := by
  set A : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of (fun i j => (D i j : ℝ)) with hAdef
  have hchar := Row2.det_sub_smul A μ
  rw [hdet] at hchar
  simp only [hAdef, Matrix.of_apply] at hchar
  -- `f(μ) = (T p + Δ) − (p + S) μ` with integer `T, S, Δ`
  have e : (((-p - ((D 0 0 : ℤ) * D 1 1 + (D 0 0 : ℤ) * D 2 2 + (D 1 1 : ℤ) * D 2 2
        - (D 1 2 : ℤ) * D 2 1 - (D 0 1 : ℤ) * D 1 0 - (D 0 2 : ℤ) * D 2 0)) : ℤ) : ℝ) * μ
      + ((((D 0 0 : ℤ) + D 1 1 + D 2 2) * p
        + ((D 0 0 : ℤ) * D 1 1 * D 2 2 - (D 0 0 : ℤ) * D 1 2 * D 2 1 - (D 0 1 : ℤ) * D 1 0 * D 2 2
          + (D 0 1 : ℤ) * D 1 2 * D 2 0 + (D 0 2 : ℤ) * D 1 0 * D 2 1
          - (D 0 2 : ℤ) * D 1 1 * D 2 0) : ℤ) : ℝ) = 0 := by
    push_cast
    linear_combination (-1 : ℝ) * hchar
      + (μ - ((D 0 0 : ℝ) + D 1 1 + D 2 2)) * hp
  obtain ⟨hq, hp'⟩ := irr_coord_eq_zero hμ e
  have hq' := congrArg (fun z : ℤ => (z : ℝ)) hq
  have hp'' := congrArg (fun z : ℤ => (z : ℝ)) hp'
  push_cast at hq' hp''
  have h2 := Row2.det_sub_smul A (-μ)
  rw [neg_smul, sub_neg_eq_add] at h2
  rw [h2]
  simp only [hAdef, Matrix.of_apply]
  linear_combination (-μ) * hq' + hp'' + (μ + ((D 0 0 : ℝ) + D 1 1 + D 2 2)) * hp

/-- **LEMMA D (row 2, the side matrix), pure linear algebra.**  Rows `0, 1, 2` = sides BC, CA, AB;
columns `0, 1, 2` = edge types `a, b, c`.  Conclusion: `D = [[0,0,A],[0,0,B],[D_ca,D_cb,0]]`,
`A, B, D_ca, D_cb ≥ 1`. -/
theorem Row2.lemmaD (D : Fin 3 → Fin 3 → ℕ) (v : Fin 3 → ℝ) (hv : ∀ i, 0 < v i) {μ : ℝ}
    (hμ : ¬ ∃ r : ℚ, μ = r) {p : ℤ} (hp : μ ^ 2 = p)
    (hDv : ∀ i, ∑ j, (D i j : ℝ) * v j = μ * v i) (hrow : ∀ i, ∃ j, 0 < D i j)
    (hA : (0 < D 2 1 ∧ 0 < D 1 2) ∨ (0 < D 2 2 ∧ 0 < D 1 1))
    (hB : (0 < D 2 0 ∧ 0 < D 0 2) ∨ (0 < D 2 2 ∧ 0 < D 0 0)) :
    D 0 0 = 0 ∧ D 0 1 = 0 ∧ D 1 0 = 0 ∧ D 1 1 = 0 ∧ D 2 2 = 0 ∧
      0 < D 0 2 ∧ 0 < D 1 2 ∧ 0 < D 2 0 ∧ 0 < D 2 1 := by
  set A : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of (fun i j => (D i j : ℝ)) with hAdef
  -- `μ` is an eigenvalue (eigenvector `v`), hence so is `−μ`
  have hdet1 : (A - μ • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det = 0 := by
    apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨v, fun h => (hv 0).ne' (congrFun h 0), ?_⟩
    ext i
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have : (Matrix.mulVec A v) i = ∑ j, (D i j : ℝ) * v j := by
      simp [hAdef, Matrix.mulVec, dotProduct]
    rw [this, hDv i, sub_self]
  have hdet2 := Row2.neg_eigen_det D hμ hp hdet1
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet2
  have hDw : ∀ i, ∑ j, (D i j : ℝ) * w j = -μ * w i := by
    intro i
    have h := congrFun hw i
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at h
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
    have : (Matrix.mulVec (Matrix.of fun i j => (D i j : ℝ)) w) i = ∑ j, (D i j : ℝ) * w j := by
      simp [Matrix.mulVec, dotProduct]
    rw [this] at h
    linarith
  -- `t = max_j |w_j| / v_j > 0`
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ (fun j => |w j| / v j)
    Finset.univ_nonempty
  set t := |w i₀| / v i₀ with htdef
  have hle : ∀ j, |w j| ≤ t * v j := fun j => by
    have := hi₀ j (Finset.mem_univ _)
    rwa [div_le_iff₀ (hv j)] at this
  have ht : 0 < t := by
    obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
      by_contra hc; push Not at hc; exact hw0 (funext hc)
    have h1 : 0 < |w j| := abs_pos.mpr hj
    have h2 := hle j
    have h3 := hv j
    by_contra ht'; push Not at ht'
    have := mul_nonpos_of_nonpos_of_nonneg ht' h3.le
    linarith
  have htv : ∀ j, 0 < t * v j := fun j => mul_pos ht (hv j)
  have hi₀eq : |w i₀| = t * v i₀ := by rw [htdef, div_mul_cancel₀ _ (hv i₀).ne']
  -- the sign lemma
  have sgn : ∀ i j, (w i = t * v i → 0 < D i j → w j = -(t * v j)) ∧
      (w i = -(t * v i) → 0 < D i j → w j = t * v j) := by
    intro i j
    have e1 := hDw i
    have e2 := hDv i
    constructor
    · intro hi hij
      have hsum : ∑ k, (D i k : ℝ) * (t * v k + w k) = 0 := by
        rw [Fin.sum_univ_three] at e1 e2 ⊢
        rw [hi] at e1
        linear_combination e1 + t * e2
      have hnn : ∀ k ∈ Finset.univ, 0 ≤ (D i k : ℝ) * (t * v k + w k) := fun k _ =>
        mul_nonneg (Nat.cast_nonneg _) (by have := hle k; have := neg_abs_le (w k); linarith)
      have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum j (Finset.mem_univ _)
      have hD : (0 : ℝ) < D i j := by exact_mod_cast hij
      have := (mul_eq_zero.mp h0).resolve_left hD.ne'
      linarith
    · intro hi hij
      have hsum : ∑ k, (D i k : ℝ) * (t * v k - w k) = 0 := by
        rw [Fin.sum_univ_three] at e1 e2 ⊢
        rw [hi] at e1
        linear_combination -e1 + t * e2
      have hnn : ∀ k ∈ Finset.univ, 0 ≤ (D i k : ℝ) * (t * v k - w k) := fun k _ =>
        mul_nonneg (Nat.cast_nonneg _) (by have := hle k; have := le_abs_self (w k); linarith)
      have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum j (Finset.mem_univ _)
      have hD : (0 : ℝ) < D i j := by exact_mod_cast hij
      have := (mul_eq_zero.mp h0).resolve_left hD.ne'
      linarith
  -- zero diagonal on `S*`
  have self0 : ∀ i, (w i = t * v i ∨ w i = -(t * v i)) → D i i = 0 := by
    intro i hi
    by_contra hne
    have hpos : 0 < D i i := Nat.pos_of_ne_zero hne
    have := htv i
    rcases hi with hi | hi
    · have := (sgn i i).1 hi hpos; linarith
    · have := (sgn i i).2 hi hpos; linarith
  have hi₀S : w i₀ = t * v i₀ ∨ w i₀ = -(t * v i₀) := by
    rcases abs_choice (w i₀) with h | h
    · left; rw [← h, hi₀eq]
    · right; rw [← hi₀eq, h, neg_neg]
  -- `c ∈ S*`
  by_cases hcp : w 2 = t * v 2
  · have h22 := self0 2 (Or.inl hcp)
    have hA' : 0 < D 2 1 ∧ 0 < D 1 2 := by
      rcases hA with h | h
      · exact h
      · omega
    have hB' : 0 < D 2 0 ∧ 0 < D 0 2 := by
      rcases hB with h | h
      · exact h
      · omega
    have hw1 := (sgn 2 1).1 hcp hA'.1
    have hw0 := (sgn 2 0).1 hcp hB'.1
    have h00 := self0 0 (Or.inr hw0)
    have h11 := self0 1 (Or.inr hw1)
    have h01 : D 0 1 = 0 := by
      by_contra hne
      have := (sgn 0 1).2 hw0 (Nat.pos_of_ne_zero hne)
      have := htv 1
      linarith
    have h10 : D 1 0 = 0 := by
      by_contra hne
      have := (sgn 1 0).2 hw1 (Nat.pos_of_ne_zero hne)
      have := htv 0
      linarith
    exact ⟨h00, h01, h10, h11, h22, hB'.2, hA'.2, hB'.1, hA'.1⟩
  by_cases hcm : w 2 = -(t * v 2)
  · have h22 := self0 2 (Or.inr hcm)
    have hA' : 0 < D 2 1 ∧ 0 < D 1 2 := by
      rcases hA with h | h
      · exact h
      · omega
    have hB' : 0 < D 2 0 ∧ 0 < D 0 2 := by
      rcases hB with h | h
      · exact h
      · omega
    have hw1 := (sgn 2 1).2 hcm hA'.1
    have hw0 := (sgn 2 0).2 hcm hB'.1
    have h00 := self0 0 (Or.inl hw0)
    have h11 := self0 1 (Or.inl hw1)
    have h01 : D 0 1 = 0 := by
      by_contra hne
      have := (sgn 0 1).1 hw0 (Nat.pos_of_ne_zero hne)
      have := htv 1
      linarith
    have h10 : D 1 0 = 0 := by
      by_contra hne
      have := (sgn 1 0).1 hw1 (Nat.pos_of_ne_zero hne)
      have := htv 0
      linarith
    exact ⟨h00, h01, h10, h11, h22, hB'.2, hA'.2, hB'.1, hA'.1⟩
  -- `c ∉ S*`: then `a ∈ S*`, and (B) fails
  exfalso
  have hno2 : ∀ i, (w i = t * v i ∨ w i = -(t * v i)) → D i 2 = 0 := by
    intro i hi
    by_contra hne
    have hpos := Nat.pos_of_ne_zero hne
    rcases hi with hi | hi
    · exact hcm ((sgn i 2).1 hi hpos)
    · exact hcp ((sgn i 2).2 hi hpos)
  have ha : w 0 = t * v 0 ∨ w 0 = -(t * v 0) := by
    have hcase : i₀ = 0 ∨ i₀ = 1 ∨ i₀ = 2 := by fin_cases i₀ <;> simp
    rcases hcase with h | h | h
    · rw [h] at hi₀S; exact hi₀S
    · rw [h] at hi₀S
      obtain ⟨j, hj⟩ := hrow 1
      have hjcase : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> simp
      rcases hjcase with rfl | rfl | rfl
      · rcases hi₀S with h' | h'
        · right; exact (sgn 1 0).1 h' hj
        · left; exact (sgn 1 0).2 h' hj
      · exact absurd (self0 1 hi₀S) hj.ne'
      · exact absurd (hno2 1 hi₀S) hj.ne'
    · rw [h] at hi₀S
      rcases hi₀S with h' | h'
      · exact absurd h' hcp
      · exact absurd h' hcm
  have h02 := hno2 0 ha
  have h00 := self0 0 ha
  omega

/-- **Lemma D, scale form**: with the survivor shape, `μa = A·c`, `μb = B·c`, `μc = D_ca a + D_cb b`,
so up to scale the tile is `(A, B, μ)`. -/
theorem Row2.lemmaD_scale (D : Fin 3 → Fin 3 → ℕ) (v : Fin 3 → ℝ) (hv : ∀ i, 0 < v i) {μ : ℝ}
    (hμ : ¬ ∃ r : ℚ, μ = r) {p : ℤ} (hp : μ ^ 2 = p)
    (hDv : ∀ i, ∑ j, (D i j : ℝ) * v j = μ * v i) (hrow : ∀ i, ∃ j, 0 < D i j)
    (hA : (0 < D 2 1 ∧ 0 < D 1 2) ∨ (0 < D 2 2 ∧ 0 < D 1 1))
    (hB : (0 < D 2 0 ∧ 0 < D 0 2) ∨ (0 < D 2 2 ∧ 0 < D 0 0)) :
    μ * v 0 = D 0 2 * v 2 ∧ μ * v 1 = D 1 2 * v 2 ∧ μ * v 2 = D 2 0 * v 0 + D 2 1 * v 1 := by
  obtain ⟨h00, h01, h10, h11, h22, -⟩ := Row2.lemmaD D v hv hμ hp hDv hrow hA hB
  have e0 := hDv 0
  have e1 := hDv 1
  have e2 := hDv 2
  rw [Fin.sum_univ_three] at e0 e1 e2
  rw [h00, h01] at e0
  rw [h10, h11] at e1
  rw [h22] at e2
  push_cast at e0 e1 e2
  refine ⟨by linarith, by linarith, by linarith⟩

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Row2.det_sub_smul
#print axioms Erdos634.Geometry.Row2.neg_eigen_det
#print axioms Erdos634.Geometry.Row2.lemmaD
#print axioms Erdos634.Geometry.Row2.lemmaD_scale

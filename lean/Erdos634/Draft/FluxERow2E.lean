-- Draft/FluxERow2E.lean — ROW 2, LEMMA E ((private working notes, not included) §5 "Lemma E (what
-- π ∈ 2Λ forces)") on a REAL `CongruentDissection`, with Lemma K in the file's non-scalene form.
-- Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
--
-- * `CongruentDissection.eType`, `sideCountT`, `sideCountT_sum`: the side matrix with each tile edge
--   given ONE model type of its length (a choice), so `Σ_k D_ik · model_k = target side i` holds for
--   every model, scalene or not.  This is the file's remark under Lemma K ("when lengths coincide,
--   merge their columns"); `Row2.sideCount` (Draft/FluxDRow2S1) needs a scalene model.
-- * `Row2.lemmaK_general`: Lemma K without the scalene hypothesis (cites `Row2.lemmaK`,
--   `Row2.lemmaK_cos`, `Row2.mu_irrational`; the cosine step is `Row2.lemmaK_tiling`'s, re-run).
-- * `Tri.angle_eq_of_oppLen_eq`: equal sides ⇒ equal opposite angles (law of sines, `Tri.lawSin`).
-- * `Row2.lemmaE_abs` (pure angle algebra): angles `θ₀, θ₁, θ₂ > 0` summing to `π`, every rational
--   angle in `{π/3, π/2, 2π/3}` (Lemma Q's conclusion), not equilateral, and `π ∈ 2Λ`,
--   `Λ = ⟨θ₀, θ₁, π⟩`: then `θ_j ≠ k·θ_i` for all `i ≠ j`, `k ∈ ℕ`.  Proof as the file's: such a
--   relation puts `Λ` inside `ℤθ_i + ℤπ`, `π ∈ 2Λ` then forces `θ_i ∈ ℚπ`, so every angle is
--   rational, hence `π/3` by Lemma Q and the angle sum — equilateral.  `k = 1` is the isosceles case.
-- * `Row2.lemmaE`: on a real tile-similar `N`-tiling, `N` prime, `N ≡ 3 (mod 4)`, `N ≥ 7`, with
--   `π ∈ 2Λ`: no model angle is a natural multiple of another, and the model is scalene.
--   (Lemma Q: Draft/FluxERow2Q; "not equilateral": Lemma K's "a/c, b/c not both rational".)
--
-- Witness (Draft/FluxERow2EWitness.lean): `sideCountT_sum` on the real `FluxRow2Witness.D2`;
-- `lemmaE_abs` on the angles `(π/6, π/3, π/2)` of `(1, √3, 2)`... NO: see the witness file for the
-- exact instance used.  `Row2.lemmaE`'s joint hypotheses (prime `N ≡ 3 mod 4`, tile-similar) have no
-- real instance — Theorem S (Draft/FluxERow2S) says there is none.
--
-- Formalization debt; not progress on the three /goal outcomes.
import Erdos634.Draft.FluxERow2Q
import Erdos634.Draft.FluxDRow2S1

open scoped Classical

namespace Erdos634.Geometry

open Real

variable {N : ℕ}

/-! ## The typed side matrix, any model -/

/-- A model type of the edge `e`'s length (a choice when the model has equal sides). -/
noncomputable def CongruentDissection.eType (D : CongruentDissection N) (e : Fin N × Fin 3) :
    Fin 3 :=
  (D.eLen_mem e).choose

theorem CongruentDissection.eLen_eType (D : CongruentDissection N) (e : Fin N × Fin 3) :
    D.eLen e = D.model.oppLen (D.eType e) :=
  (D.eLen_mem e).choose_spec

/-- The side matrix with chosen types: edges on target side `i` of type `k`. -/
noncomputable def CongruentDissection.sideCountT (D : CongruentDissection N) (i k : Fin 3) : ℕ :=
  ((D.sideEdges (i + 1)).filter (fun e => D.eType e = k)).card

/-- **S1, any model**: `Σ_k D_ik · model.oppLen k = target.oppLen i`. -/
theorem CongruentDissection.sideCountT_sum (D : CongruentDissection N) (i : Fin 3) :
    ∑ k, (D.sideCountT i k : ℝ) * D.model.oppLen k = D.target.oppLen i := by
  have hlen := D.toDissection.side_len_sum (i + 1)
  have hopp : D.target.oppLen i = dist (D.target.pts (i + 1)) (D.target.pts (i + 1 + 1)) := by
    unfold Tri.oppLen
    rw [show i + 1 + 1 = i + 2 by fin_cases i <;> rfl]
  rw [hopp, ← hlen]
  have hsplit : ∀ e ∈ D.sideEdges (i + 1), D.eLen e
      = ∑ k, if D.eType e = k then D.model.oppLen k else 0 := by
    intro e _
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true]
    exact D.eLen_eType e
  rw [Finset.sum_congr rfl hsplit, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold CongruentDissection.sideCountT
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

/-- Equation (1), any model: `D v = μ v`. -/
theorem Row2.sideCountT_eigen (D : CongruentDissection N) (μ : ℝ)
    (hside : ∀ k, D.target.oppLen k = μ * D.model.oppLen k) (i : Fin 3) :
    ∑ j, (D.sideCountT i j : ℝ) * D.model.oppLen j = μ * D.model.oppLen i := by
  rw [D.sideCountT_sum i, hside i]

/-- **Lemma K, any model** (the file's merged-column remark): `μ² = N`, `a/c` and `b/c` are not both
rational, and the cosines of the three model angles lie in `ℚ(μ)`. -/
theorem Row2.lemmaK_general (D : CongruentDissection N) (μ : ℝ)
    (hside : ∀ k, D.target.oppLen k = μ * D.model.oppLen k) (hN : ¬ IsSquare N) :
    μ ^ 2 = N ∧
      ¬ ((∃ r : ℚ, D.model.oppLen 0 = r * D.model.oppLen 2) ∧
        (∃ r : ℚ, D.model.oppLen 1 = r * D.model.oppLen 2)) ∧
      ∀ k, Row2.QMu μ (Real.cos (D.model.angleAt k)) := by
  obtain ⟨hμ, hp⟩ := Row2.mu_irrational D μ hside hN
  have hDv := Row2.sideCountT_eigen D μ hside
  obtain ⟨-, -, knot⟩ := Row2.lemmaK D.sideCountT D.model.oppLen D.model.oppLen_pos hμ hp hDv
  obtain ⟨c0, c1, c2⟩ :=
    Row2.lemmaK_cos D.sideCountT D.model.oppLen D.model.oppLen_pos hμ hp hDv
  refine ⟨by exact_mod_cast hp, knot, fun k => ?_⟩
  have hpos := D.model.oppLen_pos
  have hcos : ∀ k, Real.cos (D.model.angleAt k)
      = (D.model.oppLen (k + 1) ^ 2 + D.model.oppLen (k + 2) ^ 2 - D.model.oppLen k ^ 2)
        / (2 * D.model.oppLen (k + 1) * D.model.oppLen (k + 2)) := by
    intro k
    have hl := D.model.lawCos k
    have hne : 2 * D.model.oppLen (k + 1) * D.model.oppLen (k + 2) ≠ 0 :=
      (mul_pos (mul_pos two_pos (hpos _)) (hpos _)).ne'
    rw [eq_div_iff hne]
    linarith
  rw [hcos k]
  fin_cases k
  · exact c0
  · exact c1
  · exact c2

/-! ## Equal sides, equal angles -/

theorem Row2.fin3_pairs : ∀ a b : Fin 3, a ≠ b →
    (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = 2) ∨ (a = 1 ∧ b = 0) ∨ (a = 1 ∧ b = 2) ∨
      (a = 2 ∧ b = 0) ∨ (a = 2 ∧ b = 1) := by decide

theorem Row2.fin3_triples : ∀ a b c : Fin 3, a ≠ b → c ≠ a → c ≠ b →
    (a = 0 ∧ b = 1 ∧ c = 2) ∨ (a = 0 ∧ b = 2 ∧ c = 1) ∨ (a = 1 ∧ b = 0 ∧ c = 2) ∨
      (a = 1 ∧ b = 2 ∧ c = 0) ∨ (a = 2 ∧ b = 0 ∧ c = 1) ∨ (a = 2 ∧ b = 1 ∧ c = 0) := by decide

/-- Two angles of a triangle sum to less than `π`. -/
theorem Tri.angleAt_add_lt (T : Tri) {i j : Fin 3} (hij : i ≠ j) :
    T.angleAt i + T.angleAt j < π := by
  have hsum := T.angleAt_sum
  have h0 := T.angleAt_pos' 0
  have h1 := T.angleAt_pos' 1
  have h2 := T.angleAt_pos' 2
  rcases Row2.fin3_pairs i j hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> linarith

/-- **Equal sides ⇒ equal opposite angles** (law of sines). -/
theorem Tri.angle_eq_of_oppLen_eq (T : Tri) {i j : Fin 3} (hij : i ≠ j)
    (h : T.oppLen i = T.oppLen j) : T.angleAt i = T.angleAt j := by
  have hs := T.lawSin i j
  rw [h] at hs
  have hsin : Real.sin (T.angleAt i) = Real.sin (T.angleAt j) :=
    mul_right_cancel₀ (T.oppLen_pos j).ne' hs
  have hlt := T.angleAt_add_lt hij
  have hi0 := T.angleAt_pos' i
  have hj0 := T.angleAt_pos' j
  by_contra hne
  have hsub := Real.sin_sub_sin (T.angleAt i) (T.angleAt j)
  rw [hsin, sub_self] at hsub
  have hc : 0 < Real.cos ((T.angleAt i + T.angleAt j) / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos]
  have hs0 : Real.sin ((T.angleAt i - T.angleAt j) / 2) ≠ 0 := by
    rcases lt_or_gt_of_ne hne with hlt' | hgt
    · exact (Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)).ne
    · exact (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).ne'
  exact mul_ne_zero (mul_ne_zero two_ne_zero hs0) hc.ne' hsub.symm

/-! ## Lemma E, the angle algebra -/

/-- The third angle. -/
theorem Row2.third_angle (θ : Fin 3 → ℝ) (hsum : θ 0 + θ 1 + θ 2 = π) {i j l : Fin 3}
    (hij : i ≠ j) (hli : l ≠ i) (hlj : l ≠ j) : θ l = π - θ i - θ j := by
  rcases Row2.fin3_triples i j l hij hli hlj with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> linarith

/-- **Lemma E, abstract.**  Positive angles `θ` summing to `π`, whose rational members lie in
`{π/3, π/2, 2π/3}`, not all `π/3`, with `π ∈ 2Λ` for `Λ = ⟨θ₀, θ₁, π⟩`: no angle is a natural
multiple of another. -/
theorem Row2.lemmaE_abs (θ : Fin 3 → ℝ) (hsum : θ 0 + θ 1 + θ 2 = π)
    (hQ : ∀ k, (∃ r : ℚ, θ k = r * π) → θ k = π / 3 ∨ θ k = π / 2 ∨ θ k = π * (2 / 3))
    (hneq : ¬ ∀ k, θ k = π / 3)
    (hπ : ∃ y ∈ AddSubgroup.closure ({θ 0, θ 1, π} : Set ℝ), π = 2 * y)
    {i j : Fin 3} (hij : i ≠ j) (k : ℕ) : θ j ≠ k * θ i := by
  intro hjk
  set H : AddSubgroup ℝ := AddSubgroup.zmultiples (θ i) ⊔ AddSubgroup.zmultiples π with hH
  have mem : ∀ a b : ℤ, (a : ℝ) * θ i + b * π ∈ H := by
    intro a b
    refine AddSubgroup.mem_sup.mpr ⟨a * θ i, ?_, b * π, ?_, rfl⟩
    · exact AddSubgroup.mem_zmultiples_iff.mpr ⟨a, by rw [zsmul_eq_mul]⟩
    · exact AddSubgroup.mem_zmultiples_iff.mpr ⟨b, by rw [zsmul_eq_mul]⟩
  have hall : ∀ l, θ l ∈ H := by
    intro l
    by_cases hli : l = i
    · rw [hli]; simpa using mem 1 0
    by_cases hlj : l = j
    · rw [hlj, hjk]; simpa using mem k 0
    · rw [Row2.third_angle θ hsum hij hli hlj, hjk]
      have := mem (-(k : ℤ) - 1) 1
      convert this using 1
      push_cast; ring
  have hle : AddSubgroup.closure ({θ 0, θ 1, π} : Set ℝ) ≤ H := by
    rw [AddSubgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact hall 0
    · exact hall 1
    · simpa using mem 0 1
  obtain ⟨y, hyΛ, hy⟩ := hπ
  obtain ⟨u, hu, w, hw, huw⟩ := AddSubgroup.mem_sup.mp (hle hyΛ)
  obtain ⟨m, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hu
  obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hw
  rw [zsmul_eq_mul, zsmul_eq_mul] at huw
  rw [← huw] at hy
  have hm : m ≠ 0 := by
    rintro rfl
    have h0 : (1 - 2 * (n : ℝ)) * π = 0 := by push_cast at hy; linear_combination hy
    have h1 : (1 : ℝ) - 2 * n = 0 := (mul_eq_zero.mp h0).resolve_right Real.pi_ne_zero
    have h2 : (1 : ℤ) - 2 * n = 0 := by exact_mod_cast h1
    omega
  have hm' : (2 * (m : ℝ)) ≠ 0 := mul_ne_zero two_ne_zero (by exact_mod_cast hm)
  have hφrat : θ i = (((1 - 2 * n : ℤ) : ℚ) / (2 * m) : ℚ) * π := by
    have e : (2 * (m : ℝ)) * θ i = (1 - 2 * n) * π := by linear_combination (-1 : ℝ) * hy
    push_cast
    rw [div_mul_eq_mul_div, eq_div_iff hm']
    linear_combination e
  have hrat : ∀ l, ∃ r : ℚ, θ l = r * π := by
    intro l
    obtain ⟨u', hu', w', hw', huw'⟩ := AddSubgroup.mem_sup.mp (hall l)
    obtain ⟨a, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hu'
    obtain ⟨b, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hw'
    rw [zsmul_eq_mul, zsmul_eq_mul, hφrat] at huw'
    exact ⟨a * (((1 - 2 * n : ℤ) : ℚ) / (2 * m)) + b, by rw [← huw']; push_cast; ring⟩
  have hge : ∀ l, π / 3 ≤ θ l := by
    intro l
    rcases hQ l (hrat l) with h | h | h <;> rw [h] <;> linarith [Real.pi_pos]
  apply hneq
  have h0 := hge 0
  have h1 := hge 1
  have h2 := hge 2
  intro l
  have e0 : θ 0 = π / 3 := by linarith
  have e1 : θ 1 = π / 3 := by linarith
  have e2 : θ 2 = π / 3 := by linarith
  rcases (show l = 0 ∨ l = 1 ∨ l = 2 by fin_cases l <;> simp) with rfl | rfl | rfl
  · exact e0
  · exact e1
  · exact e2

/-! ## Lemma E on a real tiling -/

/-- **Lemma E (row 2).**  A real `N`-tiling (`N` prime, `N ≡ 3 mod 4`, `N ≥ 7`) of a target
similar to the model with ratio `μ`, with `π ∈ 2Λ`, `Λ = ⟨θ₀, θ₁, π⟩`: no model angle is a natural
multiple of another (in particular the angles are distinct), and the model is scalene. -/
theorem Row2.lemmaE (D : CongruentDissection N) (μ : ℝ)
    (hside : ∀ k, D.target.oppLen k = μ * D.model.oppLen k)
    (hN : N.Prime) (hN4 : N % 4 = 3) (hN7 : 7 ≤ N)
    (hπ : ∃ y ∈ AddSubgroup.closure ({D.model.angleAt 0, D.model.angleAt 1, π} : Set ℝ),
      π = 2 * y) :
    (∀ i j : Fin 3, i ≠ j → ∀ k : ℕ, D.model.angleAt j ≠ k * D.model.angleAt i) ∧
      (∀ i j : Fin 3, i ≠ j → D.model.oppLen i ≠ D.model.oppLen j) := by
  have hsq : ¬ IsSquare N := hN.prime.not_isSquare
  obtain ⟨hμ2, hknot, hcos⟩ := Row2.lemmaK_general D μ hside hsq
  have hsum := D.model.angleAt_sum
  have hQ : ∀ k, (∃ r : ℚ, D.model.angleAt k = r * π) →
      D.model.angleAt k = π / 3 ∨ D.model.angleAt k = π / 2 ∨ D.model.angleAt k = π * (2 / 3) := by
    intro k hr
    have hk0 := D.model.angleAt_pos' k
    have hkπ : D.model.angleAt k < π := by
      have h0 := D.model.angleAt_pos' 0
      have h1 := D.model.angleAt_pos' 1
      have h2 := D.model.angleAt_pos' 2
      rcases (show k = 0 ∨ k = 1 ∨ k = 2 by fin_cases k <;> simp) with rfl | rfl | rfl <;>
        linarith
    exact Row2.lemmaQ hN hN4 hN7 hμ2 hr hk0 hkπ (hcos k)
  have hneq : ¬ ∀ k, D.model.angleAt k = π / 3 := by
    intro hall
    have hsin : Real.sin (π / 3) ≠ 0 :=
      (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])).ne'
    have hs : ∀ i j, D.model.oppLen i = D.model.oppLen j := by
      intro i j
      have h := D.model.lawSin i j
      rw [hall i, hall j] at h
      exact (mul_left_cancel₀ hsin h).symm
    exact hknot ⟨⟨1, by rw [hs 0 2]; simp⟩, ⟨1, by rw [hs 1 2]; simp⟩⟩
  have hE : ∀ i j : Fin 3, i ≠ j → ∀ k : ℕ, D.model.angleAt j ≠ k * D.model.angleAt i :=
    fun i j hij k => Row2.lemmaE_abs D.model.angleAt hsum hQ hneq hπ hij k
  refine ⟨hE, fun i j hij hl => ?_⟩
  have := D.model.angle_eq_of_oppLen_eq hij hl
  exact hE i j hij 1 (by rw [this]; simp)

end Erdos634.Geometry

#print axioms Erdos634.Geometry.CongruentDissection.sideCountT_sum
#print axioms Erdos634.Geometry.Row2.lemmaK_general
#print axioms Erdos634.Geometry.Tri.angle_eq_of_oppLen_eq
#print axioms Erdos634.Geometry.Row2.lemmaE_abs
#print axioms Erdos634.Geometry.Row2.lemmaE

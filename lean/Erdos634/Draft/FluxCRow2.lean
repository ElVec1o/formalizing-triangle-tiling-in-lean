-- Draft/FluxCRow2.lean — consumer layer, item 2: ROW 2 LEMMA W COMPLETE ((private working notes, not included)
-- row2/PROOF.md §Lemma W: "If π ∉ 2Λ, then N is a perfect square").  Adds the AREA HALF
-- (`N·area(tile) = area(target)`, `target = μ·tile` ⇒ `N = μ²`) to `Row2.lemmaW`'s `μ ∈ ℤ`,
-- `μ ≡ N (mod 2)`.  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
--
-- Formalization debt on the prime-case VERIFIED path; not progress on the three /goal outcomes.
-- Row 2's THEOREM still needs Lemmas K, Q, E, D, R and the case split (row2/PROOF.md); only
-- Lemma W is closed here.
--
-- Reuse (cited, not re-derived): `Row2.lemmaW` (Draft/FluxRow2), `CongruentArea.congruentDissection
-- _volume_target` (the area equation, unconditional), `AreaDet.volume_eq_det_mul`,
-- `AreaDet.detTri_eq`, `Tri.volume_pos`, `Tri.volume_ne_top`, `Tri.det_ne_zero`, Mathlib
-- `Prime.not_isSquare` (cf. `InvariantProduct.tile_similar_not_prime`, the ℤ arithmetic shell).
-- Local re-derivation (import weight; named plainly): `dist_sq_coord'` is a verbatim copy of
-- `PlacementCompleteness.dist_sq_coord`.  New: the Cayley–Menger form of `detTri`
-- (`Tri.four_detTri_sq`), `CongruentDissection.abs_detTri_target` (`|det P| = N·|det T|`, the real
-- form of the area equation), `Row2.area_scale` (`N = μ²`).
import Erdos634.Draft.FluxRow2
import Erdos634.AreaDet

open scoped Classical

namespace Erdos634.Geometry

open MeasureTheory

variable {N : ℕ}

/-- Verbatim copy of `PlacementCompleteness.dist_sq_coord` (import weight). -/
theorem dist_sq_coord' (x y : Plane) : dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

/-- **Cayley–Menger (Heron) for a `Tri`**: `4·det² = 4 c² b² − (c² + b² − a²)²` with
`a, b, c` the sides opposite vertices `0, 1, 2`. -/
theorem Tri.four_detTri_sq (T : Tri) :
    4 * Erdos634.AreaDet.detTri T ^ 2
      = 4 * T.oppLen 2 ^ 2 * T.oppLen 1 ^ 2 - (T.oppLen 2 ^ 2 + T.oppLen 1 ^ 2 - T.oppLen 0 ^ 2) ^ 2 := by
  rw [Erdos634.AreaDet.detTri_eq]
  unfold Tri.oppLen
  simp only [show (0:Fin 3) + 1 = 1 from rfl, show (0:Fin 3) + 2 = 2 from rfl,
    show (1:Fin 3) + 1 = 2 from rfl, show (1:Fin 3) + 2 = 0 from rfl,
    show (2:Fin 3) + 1 = 0 from rfl, show (2:Fin 3) + 2 = 1 from rfl]
  rw [dist_sq_coord' (T.pts 0) (T.pts 1), dist_sq_coord' (T.pts 2) (T.pts 0),
    dist_sq_coord' (T.pts 1) (T.pts 2)]
  simp only [PiLp.sub_apply]
  ring

/-- `detTri` is `Tri.det` (the two coordinate formulas agree). -/
theorem Tri.detTri_eq_det (T : Tri) : Erdos634.AreaDet.detTri T = T.det := by
  rw [Erdos634.AreaDet.detTri_eq]
  unfold Tri.det
  ring

/-- **The area equation, real form**: `|det P| = N·|det T|` for any `CongruentDissection`. -/
theorem CongruentDissection.abs_detTri_target (D : CongruentDissection N) :
    |Erdos634.AreaDet.detTri D.target| = N * |Erdos634.AreaDet.detTri D.model| := by
  have h := Erdos634.CongruentArea.congruentDissection_volume_target D
  have hm := D.model.volume_pos
  have hmt := D.model.volume_ne_top
  rw [Erdos634.AreaDet.volume_eq_det_mul, Erdos634.AreaDet.volume_eq_det_mul] at h
  rw [Erdos634.AreaDet.volume_eq_det_mul] at hm hmt
  set V := volume Erdos634.AreaDet.stdCarrier with hVdef
  have hV0 : V ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hm; exact lt_irrefl _ hm
  have hd0 : ENNReal.ofReal |Erdos634.AreaDet.detTri D.model| ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hm; exact lt_irrefl _ hm
  have hVt : V ≠ ⊤ := by
    intro ht; apply hmt; rw [ht, ENNReal.mul_top hd0]
  rw [← mul_assoc, ← ENNReal.ofReal_natCast N, ← ENNReal.ofReal_mul (Nat.cast_nonneg N)] at h
  have h2 := (ENNReal.mul_left_inj hV0 hVt).mp h
  exact (ENNReal.ofReal_eq_ofReal_iff (abs_nonneg _) (by positivity)).mp h2

/-- **The area half of Lemma W: `N = μ²`.**  If the target's sides are `μ` times the model's
(same vertex order), then `N = μ²`. -/
theorem Row2.area_scale (D : CongruentDissection N) (μ : ℝ)
    (hside : ∀ k, D.target.oppLen k = μ * D.model.oppLen k) : (N : ℝ) = μ ^ 2 := by
  have hA := D.abs_detTri_target
  have hT := D.target.four_detTri_sq
  have hM := D.model.four_detTri_sq
  rw [hside 0, hside 1, hside 2] at hT
  have hdm : Erdos634.AreaDet.detTri D.model ≠ 0 := by
    rw [Tri.detTri_eq_det]; exact D.model.det_ne_zero
  have hsq : Erdos634.AreaDet.detTri D.target ^ 2 = (N : ℝ) ^ 2 * Erdos634.AreaDet.detTri D.model ^ 2 := by
    have h := congrArg (fun x : ℝ => x ^ 2) hA
    simp only [mul_pow, sq_abs] at h
    exact h
  -- `det P² = μ⁴ det T²`
  have h4 : Erdos634.AreaDet.detTri D.target ^ 2 = (μ ^ 2) ^ 2 * Erdos634.AreaDet.detTri D.model ^ 2 := by
    linear_combination (1/4 : ℝ) * hT - (μ ^ 4 / 4) * hM
  have hd2 : Erdos634.AreaDet.detTri D.model ^ 2 ≠ 0 := pow_ne_zero 2 hdm
  have hN2 : (N : ℝ) ^ 2 = (μ ^ 2) ^ 2 := by
    have := hsq.symm.trans h4
    exact mul_right_cancel₀ hd2 this
  have hNpos : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hμpos : (0 : ℝ) ≤ μ ^ 2 := sq_nonneg μ
  exact (pow_left_inj₀ hNpos hμpos two_ne_zero).mp hN2

/-- **Row 2, Lemma W, complete** (row2/PROOF.md §Lemma W).  If a `CongruentDissection`'s target is
similar to its model with ratio `μ` (same vertex order; reflections allowed) and `π ∉ 2Λ`,
`Λ = ⟨θ₀, θ₁, π⟩ ⊆ ℝ`, then `N` is a perfect square, `N = m²` with `m = μ` a positive integer. -/
theorem Row2.lemmaW_square (D : CongruentDissection N) (μ : ℝ)
    (hsim : ∀ k, D.target.angleAt k = D.model.angleAt k
      ∧ D.target.oppLen k = μ * D.model.oppLen k)
    (hπ : ∀ y ∈ AddSubgroup.closure ({D.model.angleAt 0, D.model.angleAt 1, Real.pi} : Set ℝ),
      Real.pi ≠ 2 * y) :
    ∃ m : ℕ, N = m ^ 2 ∧ μ = m := by
  obtain ⟨S, hS, -⟩ := Row2.lemmaW D μ hsim hπ
  have hN := Row2.area_scale D μ (fun k => (hsim k).2)
  -- `μ > 0`: a side of the target is positive
  have hμ : 0 < μ := by
    have ht : 0 < D.target.oppLen 0 := by
      unfold Tri.oppLen
      have hne : (0 : Fin 3) + 1 ≠ 0 + 2 := by decide
      exact dist_pos.mpr fun h => hne (D.target.indep.injective h)
    have hmo : 0 < D.model.oppLen 0 := by
      unfold Tri.oppLen
      have hne : (0 : Fin 3) + 1 ≠ 0 + 2 := by decide
      exact dist_pos.mpr fun h => hne (D.model.indep.injective h)
    rw [(hsim 0).2] at ht
    by_contra hc
    push Not at hc
    nlinarith
  have hS0 : 0 ≤ S := by
    have : (0 : ℝ) < S := by rw [← hS]; exact hμ
    exact_mod_cast this.le
  have hcast : ((S.toNat : ℕ) : ℝ) = (S : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hS0]
  refine ⟨S.toNat, ?_, ?_⟩
  · have : (N : ℝ) = ((S.toNat ^ 2 : ℕ) : ℝ) := by
      rw [hN, hS, Nat.cast_pow, hcast]
    exact_mod_cast this
  · rw [hS, hcast]

/-- **Lemma W at a prime: no tile-similar target with `π ∉ 2Λ` has a prime tile count.** -/
theorem Row2.lemmaW_not_prime (D : CongruentDissection N) (μ : ℝ)
    (hsim : ∀ k, D.target.angleAt k = D.model.angleAt k
      ∧ D.target.oppLen k = μ * D.model.oppLen k)
    (hπ : ∀ y ∈ AddSubgroup.closure ({D.model.angleAt 0, D.model.angleAt 1, Real.pi} : Set ℝ),
      Real.pi ≠ 2 * y) :
    ¬ Nat.Prime N := by
  obtain ⟨m, hm, -⟩ := Row2.lemmaW_square D μ hsim hπ
  intro hp
  exact hp.prime.not_isSquare ⟨m, by rw [hm]; ring⟩

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Tri.four_detTri_sq
#print axioms Erdos634.Geometry.CongruentDissection.abs_detTri_target
#print axioms Erdos634.Geometry.Row2.area_scale
#print axioms Erdos634.Geometry.Row2.lemmaW_square
#print axioms Erdos634.Geometry.Row2.lemmaW_not_prime

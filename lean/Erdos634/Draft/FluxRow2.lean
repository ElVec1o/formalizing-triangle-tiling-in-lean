-- Draft/FluxRow2.lean — consumer corollary for row 2: LEMMA W ((private working notes, not included)
-- :182, from row3/PROOF.md §3): a target similar to the tile with ratio `μ`, when `π ∉ 2Λ`
-- (`Λ = ℤθ₀ + ℤθ₁ + ℤπ`, the tile's angle group), has `μ ∈ ℤ` (and `μ ≡ N mod 2`).
-- Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).  Design: (private working notes, not included) §4.2 row 2 (`Row2.lemmaW`).
--
-- What this does NOT give: `N = μ²` (area scaling, a separate named blocker), nor row 2's theorem
-- (Lemmas K, Q, E, D, R and the case split remain).  Formalization debt; not progress on the /goal.
--
-- Reuse (cited): `Tri.flux_grid_pm`, `CongruentDissection.target_flux_signs`, `GridChar.ofHom(_sq)`.
-- Local re-proofs (import weight; named plainly): `Tri.range_pts_eq'`, `Tri.strict_triangle'` are
-- verbatim copies of `TilePlacement.range_pts_eq` / `TilePlacement.strict_triangle` (that module
-- pulls 23 project modules).  `exists_zmod2_char` is new (Mathlib: `QuotientAddGroup.zmodModule`,
-- `Module.Projective.exists_dual_eq_one`).
import Erdos634.Draft.FluxValue
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Convex.StrictConvexBetween

open scoped Classical

namespace Erdos634.Geometry

/-- **A `ZMod 2` character with `χ x = 1` exists iff `x ∉ 2A`** (the "if" direction): `A/2A` is an
`𝔽₂`-vector space in which `x` is nonzero, and a vector space separates points. -/
theorem exists_zmod2_char {A : Type*} [AddCommGroup A] (x : A) (hx : ∀ y : A, x ≠ 2 • y) :
    ∃ χ : A →+ ZMod 2, χ x = 1 := by
  let H : AddSubgroup A := (nsmulAddMonoidHom 2 : A →+ A).range
  have hH : ∀ z : A, 2 • z ∈ H := fun z => AddMonoidHom.mem_range.mpr ⟨z, rfl⟩
  letI : Module (ZMod 2) (A ⧸ H) := QuotientAddGroup.zmodModule hH
  have hq : (QuotientAddGroup.mk x : A ⧸ H) ≠ 0 := by
    intro h
    rw [QuotientAddGroup.eq_zero_iff] at h
    obtain ⟨z, hz⟩ := AddMonoidHom.mem_range.mp h
    exact hx z hz.symm
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) hq
  exact ⟨f.toAddMonoidHom.comp (QuotientAddGroup.mk' H), hf⟩

/-- Verbatim copy of `TilePlacement.range_pts_eq`. -/
theorem Tri.range_pts_eq' (T : Tri) (j : Fin 3) :
    Set.range T.pts = {T.pts (j + 1), T.pts j, T.pts (j + 2)} := by
  have hfin : ∀ a b : Fin 3, a = b ∨ a = b + 1 ∨ a = b + 2 := by decide
  have hfin' : ∀ i : Fin 3, i = j ∨ i = j + 1 ∨ i = j + 2 := fun i => hfin i j
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    rcases hfin' i with rfl | rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact ⟨j + 1, rfl⟩
    · exact ⟨j, rfl⟩
    · exact ⟨j + 2, rfl⟩

/-- Verbatim copy of `TilePlacement.strict_triangle`. -/
theorem Tri.strict_triangle' (T : Tri) (j : Fin 3) :
    dist (T.pts (j + 1)) (T.pts (j + 2))
      < dist (T.pts (j + 1)) (T.pts j) + dist (T.pts j) (T.pts (j + 2)) := by
  rcases lt_or_eq_of_le (dist_triangle (T.pts (j + 1)) (T.pts j) (T.pts (j + 2))) with h | h
  · exact h
  · exfalso
    have hw : Wbtw ℝ (T.pts (j + 1)) (T.pts j) (T.pts (j + 2)) :=
      dist_add_dist_eq_iff.mp h.symm
    have hcol : Collinear ℝ (Set.range T.pts) := by
      rw [T.range_pts_eq' j]; exact hw.collinear
    exact (affineIndependent_iff_not_collinear.mp T.indep) hcol

/-- **`K ≠ 0`.**  A `±1`-weighted sum of the three sides of a nondegenerate triangle is never `0`
(strict triangle inequality). -/
theorem GridChar.tileValue_ne_zero (G : GridChar ℝ) (hsq : ∀ l ∈ G.L, G.chi l * G.chi l = 1)
    (T : Tri) (h : ∀ k, ((T.angleAt k : ℝ) : Real.Angle) ∈ G.L) : G.tileValue T ≠ 0 := by
  unfold GridChar.tileValue Tri.oppLen
  rw [Fin.sum_univ_three]
  simp only [show (0:Fin 3) + 1 = 1 from rfl, show (0:Fin 3) + 2 = 2 from rfl,
    show (1:Fin 3) + 1 = 2 from rfl, show (1:Fin 3) + 2 = 0 from rfl,
    show (2:Fin 3) + 1 = 0 from rfl, show (2:Fin 3) + 2 = 1 from rfl]
  have s0 := T.strict_triangle' 0
  have s1 := T.strict_triangle' 1
  have s2 := T.strict_triangle' 2
  simp only [show (0:Fin 3) + 1 = 1 from rfl, show (0:Fin 3) + 2 = 2 from rfl,
    show (1:Fin 3) + 1 = 2 from rfl, show (1:Fin 3) + 2 = 0 from rfl,
    show (2:Fin 3) + 1 = 0 from rfl, show (2:Fin 3) + 2 = 1 from rfl] at s0 s1 s2
  have c01 := dist_comm (T.pts 0) (T.pts 1)
  have c12 := dist_comm (T.pts 1) (T.pts 2)
  have c20 := dist_comm (T.pts 2) (T.pts 0)
  rcases mul_self_eq_one_iff.mp (hsq _ (T.pi_sub_angleAt_mem G h 0)) with e0 | e0 <;>
  rcases mul_self_eq_one_iff.mp (hsq _ (T.pi_sub_angleAt_mem G h 1)) with e1 | e1 <;>
  rcases mul_self_eq_one_iff.mp (hsq _ (T.pi_sub_angleAt_mem G h 2)) with e2 | e2 <;>
  · rw [e0, e1, e2]
    intro hz
    linarith

/-- **Lemma W (row 2).**  If a `CongruentDissection`'s target is similar to its model with ratio
`μ` (same vertex order; reflections allowed) and `π ∉ 2Λ`, `Λ = ⟨θ₀, θ₁, π⟩ ⊆ ℝ`, then `μ` is an
integer congruent to `N` mod 2. -/
theorem Row2.lemmaW {N : ℕ} (D : CongruentDissection N) (μ : ℝ)
    (hsim : ∀ k, D.target.angleAt k = D.model.angleAt k
      ∧ D.target.oppLen k = μ * D.model.oppLen k)
    (hπ : ∀ y ∈ AddSubgroup.closure ({D.model.angleAt 0, D.model.angleAt 1, Real.pi} : Set ℝ),
      Real.pi ≠ 2 * y) :
    ∃ S : ℤ, μ = S ∧ (2 : ℤ) ∣ S - N := by
  set Λ := AddSubgroup.closure ({D.model.angleAt 0, D.model.angleAt 1, Real.pi} : Set ℝ) with hΛ
  have hπΛ : Real.pi ∈ Λ := AddSubgroup.subset_closure (by simp)
  have h0Λ : D.model.angleAt 0 ∈ Λ := AddSubgroup.subset_closure (by simp)
  have h1Λ : D.model.angleAt 1 ∈ Λ := AddSubgroup.subset_closure (by simp)
  have h2Λ : D.model.angleAt 2 ∈ Λ := by
    have hs := D.model.angleAt_sum
    have e : D.model.angleAt 2 = Real.pi - D.model.angleAt 0 - D.model.angleAt 1 := by linarith
    rw [e]
    exact Λ.sub_mem (Λ.sub_mem hπΛ h0Λ) h1Λ
  let x₀ : Λ := ⟨Real.pi, hπΛ⟩
  have hx : ∀ y : Λ, x₀ ≠ 2 • y := by
    intro y hy
    have h1 : ((x₀ : Λ) : ℝ) = ((2 • y : Λ) : ℝ) := congrArg Subtype.val hy
    have h2 : Real.pi = 2 * (y : ℝ) := by
      rw [show ((x₀ : Λ) : ℝ) = Real.pi from rfl, AddSubgroup.coe_nsmul, nsmul_eq_mul] at h1
      exact_mod_cast h1
    exact hπ y y.2 h2
  obtain ⟨χ, hχ⟩ := exists_zmod2_char x₀ hx
  let φ : Λ →+ Real.Angle := Real.Angle.coeHom.comp Λ.subtype
  have hφ : ∀ a : Λ, φ a = ((a : ℝ) : Real.Angle) := fun a => rfl
  have hker : ∀ a, φ a = 0 → χ a = 0 := by
    intro a ha
    rw [hφ, Real.Angle.coe_eq_zero_iff] at ha
    obtain ⟨m, hm⟩ := ha
    have hsplit : a = 2 • (m • x₀) := by
      apply Subtype.ext
      rw [AddSubgroup.coe_nsmul, AddSubgroup.coe_zsmul, ← hm]
      show m • (2 * Real.pi) = 2 • (m • Real.pi)
      rw [zsmul_eq_mul, zsmul_eq_mul, nsmul_eq_mul]
      push_cast
      ring
    rw [hsplit, map_nsmul, two_nsmul]
    exact CharTwo.add_self_eq_zero _
  let G : GridChar ℝ := GridChar.ofHom φ χ hker x₀ rfl hχ 0
  have hsq : ∀ l ∈ G.L, G.chi l * G.chi l = 1 := GridChar.ofHom_sq φ χ hker x₀ rfl hχ 0
  have hmemL : ∀ θ ∈ Λ, ((θ : ℝ) : Real.Angle) ∈ G.L := fun θ hθ =>
    AddMonoidHom.mem_range.mpr ⟨⟨θ, hθ⟩, rfl⟩
  have hmodel : ∀ k, ((D.model.angleAt k : ℝ) : Real.Angle) ∈ G.L := by
    intro k
    have hk : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
    rcases hk with rfl | rfl | rfl
    · exact hmemL _ h0Λ
    · exact hmemL _ h1Λ
    · exact hmemL _ h2Λ
  have htarget : ∀ k, ((D.target.angleAt k : ℝ) : Real.Angle) ∈ G.L := fun k => by
    rw [(hsim k).1]; exact hmodel k
  obtain ⟨S, hS2, -, hSf⟩ := D.target_flux_signs G hsq hmodel
  have hKt : G.tileValue D.target = μ * G.tileValue D.model := by
    unfold GridChar.tileValue
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [(hsim k).1, (hsim k).2]
    ring
  have hK0 := G.tileValue_ne_zero hsq D.model hmodel
  rcases D.target.flux_grid_pm G hsq htarget with h1 | h1
  · refine ⟨S, ?_, hS2⟩
    rw [hSf, hKt] at h1
    exact (mul_right_cancel₀ hK0 h1).symm
  · refine ⟨-S, ?_, ?_⟩
    · rw [hSf, hKt] at h1
      have h3 : ((S : ℝ) + μ) * G.tileValue D.model = 0 := by linear_combination h1
      have h4 := (mul_eq_zero.mp h3).resolve_right hK0
      push_cast
      linarith
    · rw [show -S - (N : ℤ) = -(S - N) - 2 * N by ring]
      exact dvd_sub (dvd_neg.mpr hS2) (dvd_mul_right 2 _)

end Erdos634.Geometry

#print axioms Erdos634.Geometry.exists_zmod2_char
#print axioms Erdos634.Geometry.GridChar.tileValue_ne_zero
#print axioms Erdos634.Geometry.Row2.lemmaW

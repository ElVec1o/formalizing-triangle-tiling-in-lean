-- Draft/FluxCRow5.lean — consumer layer, item 4: ROW 5, THEOREM E steps E1–E7
-- ((private working notes, not included) §4 and P2): the EQUILATERAL target's two invariants, the
-- area identity `S² = N·ab`, the product `st = 3N` (`m₁m₂ = 3N`), and the prime pinning
-- `{s, t} = {3, N}` (`m₁ = N`, `m₂ = 3`), for both branches `γ = 2π/3` and `γ = π/3`, `α ∉ ℚπ`,
-- reflections allowed, NOT necessarily edge-to-edge.  Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).
--
-- CONDITIONAL, NOT A RESULT YET: the corpus has NO Lean dissection of an equilateral target by a
-- `2π/3` or `π/3` tile with `α ∉ ℚπ` (real ones exist on paper, e.g. Herdt's `N = 1944` by
-- `(3,8,7)`, `EquilateralScaling` header).  Only sub-hypotheses are witnessed
-- (Draft/FluxCRow5Witness.lean).  Theorem E itself still needs E7b (π/3 sign class and "no c-edge
-- on ∂ABC"), E8 (side words `S = pa + qb + rc`) and the two irrationality closings.
--
-- Formalization debt on the prime-case VERIFIED path; not progress on the three /goal outcomes.
-- Row 5 at primes is `thm:main`'s equilateral row, already PROVED at paper level.
--
-- Reuse (cited): `CongruentDissection.triangle_boundary_anchor`, `GridChar.tileValue_eq_paperK`
-- (FluxCBoundary); `GridChar.rankn(_mem/_chi/_sq)`, `Tri.TwoPiThreeData`, `Tri.data_angles_mem`,
-- `data_tileValue_alpha/beta` (FluxPaper); `Tri.lawSin`, `Tri.oppLen_pos` (FluxCRow12);
-- `CongruentDissection.abs_detTri_target`, `Tri.four_detTri_sq` (FluxCRow2); `Tri.strict_triangle'`
-- (FluxRow2); `EqSpecAlgebra.XY_eq`, `EqSpecAlgebra.st_eq` (E6 algebra over ℝ); Mathlib's law of
-- cosines.  `SixtyInvariant.tile_value_sixty` is the π/3 tile value as ℤ arithmetic; `sixty_tileValue`
-- is the geometric statement for a real placement (either orientation).  `(a+b−c)(a+b+c) = 3ab` for
-- the π/3 tile is written inline (no ℝ copy found in the corpus).
import Erdos634.Draft.FluxCBoundary
import Erdos634.Draft.FluxPaper
import Erdos634.Draft.FluxCRow2
import Erdos634.Draft.FluxCRow12
import Erdos634.EqSpecAlgebra

open scoped Classical

namespace Erdos634.Geometry

variable {N : ℕ}

/-! ## Triangle bookkeeping: rotation and permutation sums, strict triangle, law of cosines -/

theorem Tri.oppLen_succ (T : Tri) (v : Fin 3) : T.oppLen (v + 1) = dist (T.pts (v + 2)) (T.pts v) := by
  unfold Tri.oppLen
  rw [show v + 1 + 1 = v + 2 by fin_cases v <;> rfl, show v + 1 + 2 = v by fin_cases v <;> rfl]

theorem Tri.oppLen_succ2 (T : Tri) (v : Fin 3) : T.oppLen (v + 2) = dist (T.pts (v + 1)) (T.pts v) := by
  unfold Tri.oppLen
  rw [show v + 2 + 1 = v by fin_cases v <;> rfl, show v + 2 + 2 = v + 1 by fin_cases v <;> rfl,
    dist_comm]

theorem Tri.sum_rot (T : Tri) (n : ℕ) (v : Fin 3) :
    ∑ k, T.oppLen k ^ n = T.oppLen v ^ n + T.oppLen (v + 1) ^ n + T.oppLen (v + 2) ^ n := by
  rw [Fin.sum_univ_three]
  have hv : v = 0 ∨ v = 1 ∨ v = 2 := by fin_cases v <;> simp
  rcases hv with rfl | rfl | rfl
  · rfl
  · show _ = T.oppLen 1 ^ n + T.oppLen 2 ^ n + T.oppLen 0 ^ n; ring
  · show _ = T.oppLen 2 ^ n + T.oppLen 0 ^ n + T.oppLen 1 ^ n; ring

theorem Tri.sum_perm (T : Tri) (n : ℕ) (σ : Equiv.Perm (Fin 3)) :
    ∑ k, T.oppLen k ^ n = T.oppLen (σ 0) ^ n + T.oppLen (σ 1) ^ n + T.oppLen (σ 2) ^ n := by
  rw [← Equiv.sum_comp σ (fun k => T.oppLen k ^ n), Fin.sum_univ_three]

/-- Strict triangle inequality, opposite-side form. -/
theorem Tri.oppLen_lt (T : Tri) (v : Fin 3) : T.oppLen v < T.oppLen (v + 1) + T.oppLen (v + 2) := by
  have h := T.strict_triangle' v
  rw [T.oppLen_succ, T.oppLen_succ2]
  have e := dist_comm (T.pts v) (T.pts (v + 2))
  show dist (T.pts (v + 1)) (T.pts (v + 2)) < _
  linarith

/-- Strict triangle inequality for the side labelled `σ i`. -/
theorem Tri.oppLen_lt_perm (T : Tri) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    2 * T.oppLen (σ i) < T.oppLen (σ 0) + T.oppLen (σ 1) + T.oppLen (σ 2) := by
  have h := T.oppLen_lt (σ i)
  have s1 := T.sum_rot 1 (σ i)
  have s2 := T.sum_perm 1 σ
  simp only [pow_one] at s1 s2
  linarith

/-- The law of cosines at vertex `v`. -/
theorem Tri.lawCos (T : Tri) (v : Fin 3) :
    T.oppLen v ^ 2 = T.oppLen (v + 1) ^ 2 + T.oppLen (v + 2) ^ 2
      - 2 * T.oppLen (v + 1) * T.oppLen (v + 2) * Real.cos (T.angleAt v) := by
  have hlaw :=
    EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle
      (T.pts (v + 1)) (T.pts v) (T.pts (v + 2))
  rw [T.oppLen_succ, T.oppLen_succ2]
  show dist (T.pts (v + 1)) (T.pts (v + 2)) ^ 2 = _ - _ * Real.cos
    (EuclideanGeometry.angle (T.pts (v + 1)) (T.pts v) (T.pts (v + 2)))
  linear_combination hlaw

/-- **The law of cosines for a labelled triangle**: the side `σ 2` against the angle at `σ 2`
and the other two labelled sides (whatever the orientation of `σ`). -/
theorem Tri.lawCos_perm (T : Tri) (σ : Equiv.Perm (Fin 3)) :
    T.oppLen (σ 2) ^ 2 = T.oppLen (σ 0) ^ 2 + T.oppLen (σ 1) ^ 2
      - 2 * T.oppLen (σ 0) * T.oppLen (σ 1) * Real.cos (T.angleAt (σ 2)) := by
  have hl := T.lawCos (σ 2)
  have r1 := T.sum_rot 1 (σ 2)
  have p1 := T.sum_perm 1 σ
  have r2 := T.sum_rot 2 (σ 2)
  have p2 := T.sum_perm 2 σ
  simp only [pow_one] at r1 p1
  set x := T.oppLen (σ 2 + 1)
  set y := T.oppLen (σ 2 + 2)
  set A := T.oppLen (σ 0)
  set B := T.oppLen (σ 1)
  set C := T.oppLen (σ 2)
  set co := Real.cos (T.angleAt (σ 2))
  have hs1 : x + y = A + B := by linarith
  have hs2 : x ^ 2 + y ^ 2 = A ^ 2 + B ^ 2 := by linarith
  linear_combination hl + (1 + co) * hs2 - co * (x + y + A + B) * hs1

/-- Symmetric Heron: `4·det² = (Σ side²)² − 2 Σ side⁴`. -/
theorem Tri.four_detTri_sq_sym (T : Tri) :
    4 * Erdos634.AreaDet.detTri T ^ 2
      = (∑ k, T.oppLen k ^ 2) ^ 2 - 2 * ∑ k, T.oppLen k ^ 4 := by
  rw [T.four_detTri_sq, Fin.sum_univ_three, Fin.sum_univ_three]
  ring

/-! ## The `ℤ·π/3 + ℤ·α` grid characters, anchored -/

/-- The paper's grid characters `w₁ = (−1)^j` (`b = 0`), `w₂ = (−1)^(j+k)` (`b = 1`) on `jπ/3 + kα`,
anchored at `anc`. -/
noncomputable def wAt (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (b : ZMod 2)
    (anc : Real.Angle) : GridChar ℝ :=
  GridChar.rankn 3 (by norm_num) (by decide) α hα b anc

theorem wAt_sq (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (b : ZMod 2) (anc : Real.Angle) :
    ∀ l ∈ (wAt α hα b anc).L, (wAt α hα b anc).chi l * (wAt α hα b anc).chi l = 1 :=
  GridChar.rankn_sq _ _ _ _ _ _ _

theorem wAt_form (α : ℝ) (j k : ℤ) :
    ((j : ℝ) * (Real.pi / 3) + (k : ℝ) * α) = ((j : ℝ) * (Real.pi / ((3 : ℕ) : ℝ)) + (k : ℝ) * α) := by
  push_cast; ring

theorem wAt_mem (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (b : ZMod 2) (anc : Real.Angle)
    (j k : ℤ) : (((j : ℝ) * (Real.pi / 3) + (k : ℝ) * α : ℝ) : Real.Angle) ∈ (wAt α hα b anc).L := by
  rw [wAt_form]
  exact GridChar.rankn_mem _ _ _ _ _ _ _ _ _

theorem wAt_chi (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (b : ZMod 2) (anc : Real.Angle)
    (j k : ℤ) :
    (wAt α hα b anc).chi (((j : ℝ) * (Real.pi / 3) + (k : ℝ) * α : ℝ) : Real.Angle)
      = if (j : ZMod 2) + b * (k : ZMod 2) = 0 then 1 else -1 := by
  rw [wAt_form]
  exact GridChar.rankn_chi _ _ _ _ _ _ _ _ _

theorem wAt_tileValue (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (b : ZMod 2)
    (anc : Real.Angle) (T : Tri) : (wAt α hα b anc).tileValue T = (wAt α hα b 0).tileValue T := rfl

/-! ## The `π/3` tile -/

/-- **A placement of the `π/3` tile**: angles `(α, 2π/3 − α, π/3)`, opposite sides `(a, b, c)`. -/
def Tri.SixtyData (T : Tri) (α a b c : ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3),
    T.angleAt (σ 0) = α ∧ T.oppLen (σ 0) = a ∧
    T.angleAt (σ 1) = 2 * Real.pi / 3 - α ∧ T.oppLen (σ 1) = b ∧
    T.angleAt (σ 2) = Real.pi / 3 ∧ T.oppLen (σ 2) = c

theorem Tri.sixty_angles_mem {T : Tri} {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : T.SixtyData α a b c) (b' : ZMod 2) (anc : Real.Angle) :
    ∀ j, ((T.angleAt j : ℝ) : Real.Angle) ∈ (wAt α hα b' anc).L := by
  obtain ⟨σ, h0, -, h1, -, h2, -⟩ := h
  intro j
  obtain ⟨k, rfl⟩ := σ.surjective j
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
  rcases hk with rfl | rfl | rfl
  · rw [h0, show ((α : ℝ) : Real.Angle)
        = ((((0 : ℤ) : ℝ) * (Real.pi / 3) + ((1 : ℤ) : ℝ) * α : ℝ) : Real.Angle) by
          congr 1; push_cast; ring]
    exact wAt_mem _ _ _ _ _ _
  · rw [h1, show 2 * Real.pi / 3 - α = ((2 : ℤ) : ℝ) * (Real.pi / 3) + ((-1 : ℤ) : ℝ) * α by
      push_cast; ring]
    exact wAt_mem _ _ _ _ _ _
  · rw [h2, show Real.pi / 3 = ((1 : ℤ) : ℝ) * (Real.pi / 3) + ((0 : ℤ) : ℝ) * α by push_cast; ring]
    exact wAt_mem _ _ _ _ _ _

/-- Tile values of the `π/3` tile: exterior angles `π − α = (3,−1)`, `π − β = (1,1)`,
`π − π/3 = (2,0)`. -/
theorem sixty_tileValue (T : Tri) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : T.SixtyData α a b c) (b' : ZMod 2) :
    (wAt α hα b' 0).tileValue T
      = (if ((3 : ℤ) : ZMod 2) + b' * ((-1 : ℤ) : ZMod 2) = 0 then 1 else -1) * a
        + (if ((1 : ℤ) : ZMod 2) + b' * ((1 : ℤ) : ZMod 2) = 0 then 1 else -1) * b
        + (if ((2 : ℤ) : ZMod 2) + b' * ((0 : ℤ) : ZMod 2) = 0 then 1 else -1) * c := by
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  unfold GridChar.tileValue
  rw [← Equiv.sum_comp σ (fun j => (wAt α hα b' 0).chi
      ((Real.pi - T.angleAt j : ℝ) : Real.Angle) * T.oppLen j), Fin.sum_univ_three]
  rw [h0, o0, h1, o1, h2, o2,
    show Real.pi - α = ((3 : ℤ) : ℝ) * (Real.pi / 3) + ((-1 : ℤ) : ℝ) * α by push_cast; ring,
    show Real.pi - (2 * Real.pi / 3 - α) = ((1 : ℤ) : ℝ) * (Real.pi / 3) + ((1 : ℤ) : ℝ) * α by
      push_cast; ring,
    show Real.pi - Real.pi / 3 = ((2 : ℤ) : ℝ) * (Real.pi / 3) + ((0 : ℤ) : ℝ) * α by
      push_cast; ring,
    wAt_chi, wAt_chi, wAt_chi]

theorem sixty_tileValue_one (T : Tri) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : T.SixtyData α a b c) : (wAt α hα 0 0).tileValue T = -(a + b - c) := by
  rw [sixty_tileValue T hα h 0, if_neg (by decide), if_neg (by decide), if_pos (by decide)]
  ring

theorem sixty_tileValue_two (T : Tri) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : T.SixtyData α a b c) : (wAt α hα 1 0).tileValue T = a + b + c := by
  rw [sixty_tileValue T hα h 1, if_pos (by decide), if_pos (by decide), if_pos (by decide)]
  ring

/-! ## E4: the equilateral boundary -/

/-- **E4.**  On an equilateral target (all angles `π/3`), anchored at side `01`, for either grid
character: the sides are equal, and `S·K(model) = 3·side` with `S` a sum of `N` signs. -/
theorem Row5.equilateral_boundary (D : CongruentDissection N) {α : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (b' : ZMod 2)
    (hmodel : ∀ k, ((D.model.angleAt k : ℝ) : Real.Angle)
      ∈ (wAt α hα b' (D.target.leftUnit 0).angle).L)
    (hP : ∀ k, D.target.angleAt k = Real.pi / 3) :
    D.target.oppLen 1 = D.target.oppLen 0 ∧ D.target.oppLen 2 = D.target.oppLen 0 ∧
    ∃ S : ℤ, (2 : ℤ) ∣ S - N ∧ |S| ≤ N ∧
      (S : ℝ) * (wAt α hα b' 0).tileValue D.model = 3 * D.target.oppLen 0 := by
  set anc := (D.target.leftUnit 0).angle with hancdef
  have e3 : Real.pi / 3 = ((1 : ℤ) : ℝ) * (Real.pi / 3) + ((0 : ℤ) : ℝ) * α := by push_cast; ring
  have htarget : ∀ k, ((D.target.angleAt k : ℝ) : Real.Angle) ∈ (wAt α hα b' anc).L := by
    intro k; rw [hP k, e3]; exact wAt_mem _ _ _ _ _ _
  have hchi : (wAt α hα b' anc).chi ((Real.pi / 3 : ℝ) : Real.Angle) = -1 := by
    rw [e3, wAt_chi, if_neg]
    have h1 : ((1 : ℤ) : ZMod 2) = 1 := by decide
    have h0 : ((0 : ℤ) : ZMod 2) = 0 := by decide
    rw [h1, h0, mul_zero, add_zero]
    decide
  -- equal sides (law of sines, `sin(π/3) > 0`)
  have hsin : 0 < Real.sin (Real.pi / 3) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  have l01 := D.target.lawSin 0 1
  have l02 := D.target.lawSin 0 2
  rw [hP 0, hP 1] at l01
  rw [hP 0, hP 2] at l02
  have e1 : D.target.oppLen 1 = D.target.oppLen 0 := mul_left_cancel₀ hsin.ne' l01
  have e2 : D.target.oppLen 2 = D.target.oppLen 0 := mul_left_cancel₀ hsin.ne' l02
  refine ⟨e1, e2, ?_⟩
  have hPK : (wAt α hα b' anc).paperK D.target = 3 * D.target.oppLen 0 := by
    unfold GridChar.paperK
    rw [Fin.sum_univ_three, hP 0, hP 1, hP 2, hchi, e1, e2]
    ring
  obtain ⟨S, hS2, hSN, hSe⟩ := D.triangle_boundary_anchor (wAt α hα b' anc) (wAt_sq _ _ _ _)
    hmodel htarget 0 rfl
  rw [show (0 : Fin 3) + 2 = 2 from rfl, hP 2, hchi, hPK,
    ← GridChar.tileValue_eq_paperK _ (wAt_sq _ _ _ _) _ hmodel, wAt_tileValue] at hSe
  exact ⟨S, hS2, hSN, by linear_combination hSe⟩

/-! ## E5: the area identity -/

/-- **E5.**  If the model's labelled sides satisfy `c² = a² + b² + κab`, `κ = ±1`, and the target is
equilateral with side `S`, then `S² = N·ab`. -/
theorem Row5.area (D : CongruentDissection N) (σ : Equiv.Perm (Fin 3)) {a b c κ : ℝ}
    (ha : D.model.oppLen (σ 0) = a) (hb : D.model.oppLen (σ 1) = b) (hc : D.model.oppLen (σ 2) = c)
    (hκ : κ ^ 2 = 1) (hcos : c ^ 2 = a ^ 2 + b ^ 2 + κ * a * b)
    (hP1 : D.target.oppLen 1 = D.target.oppLen 0) (hP2 : D.target.oppLen 2 = D.target.oppLen 0) :
    D.target.oppLen 0 ^ 2 = N * a * b := by
  have hA := D.abs_detTri_target
  have hT := D.target.four_detTri_sq_sym
  have hM := D.model.four_detTri_sq_sym
  rw [Fin.sum_univ_three, Fin.sum_univ_three, hP1, hP2] at hT
  rw [D.model.sum_perm 2 σ, D.model.sum_perm 4 σ, ha, hb, hc] at hM
  have hsq : Erdos634.AreaDet.detTri D.target ^ 2
      = (N : ℝ) ^ 2 * Erdos634.AreaDet.detTri D.model ^ 2 := by
    have h := congrArg (fun x : ℝ => x ^ 2) hA
    simp only [mul_pow, sq_abs] at h
    exact h
  have ha0 : 0 < a := ha ▸ D.model.oppLen_pos (σ 0)
  have hb0 : 0 < b := hb ▸ D.model.oppLen_pos (σ 1)
  have hS0 : 0 < D.target.oppLen 0 := D.target.oppLen_pos 0
  set S := D.target.oppLen 0
  -- `S⁴ = N² a² b²`
  have h4 : (S ^ 2) ^ 2 = ((N : ℝ) * a * b) ^ 2 := by
    have eT : 4 * Erdos634.AreaDet.detTri D.target ^ 2 = 3 * S ^ 4 := by rw [hT]; ring
    have eM : 4 * Erdos634.AreaDet.detTri D.model ^ 2 = 3 * a ^ 2 * b ^ 2 := by
      rw [hM]
      linear_combination (-(a ^ 2 * b ^ 2)) * hκ - (c ^ 2 - a ^ 2 - b ^ 2 + κ * a * b) * hcos
    linear_combination (-1 / 3 : ℝ) * eT + ((N : ℝ) ^ 2 / 3) * eM + (4 / 3 : ℝ) * hsq
  have hN0 : (0 : ℝ) ≤ N * a * b := mul_nonneg (mul_nonneg (Nat.cast_nonneg N) ha0.le) hb0.le
  exact (pow_left_inj₀ (sq_nonneg S) hN0 two_ne_zero).mp h4

/-! ## E7: the prime pinning (arithmetic) -/

/-- **E7, arithmetic.**  `s·t = 3N` with `1 ≤ s, t ≤ N` and `N` prime forces `{s, t} = {3, N}`. -/
theorem Row5.prime_pin (hN : N.Prime) (s t : ℤ) (hs1 : 1 ≤ s) (hsN : s ≤ N) (ht1 : 1 ≤ t)
    (htN : t ≤ N) (hst : s * t = 3 * N) : (s = 3 ∧ t = N) ∨ (s = N ∧ t = 3) := by
  lift s to ℕ using (by omega)
  lift t to ℕ using (by omega)
  have hst' : s * t = 3 * N := by exact_mod_cast hst
  have hsN' : s ≤ N := by exact_mod_cast hsN
  have htN' : t ≤ N := by exact_mod_cast htN
  have hs1' : 1 ≤ s := by exact_mod_cast hs1
  have ht1' : 1 ≤ t := by exact_mod_cast ht1
  have hNpos := hN.pos
  have hdvd : N ∣ s * t := ⟨3, by rw [hst']; ring⟩
  rcases (Nat.Prime.dvd_mul hN).mp hdvd with h | h
  · have hs : s = N := le_antisymm hsN' (Nat.le_of_dvd (by omega) h)
    subst hs
    have : t = 3 := by
      have h' : s * t = s * 3 := by rw [hst']; ring
      exact Nat.eq_of_mul_eq_mul_left hNpos h'
    right; exact ⟨rfl, by exact_mod_cast this⟩
  · have ht : t = N := le_antisymm htN' (Nat.le_of_dvd (by omega) h)
    subst ht
    have : s = 3 := by
      have h' : t * s = t * 3 := by rw [mul_comm, hst']; ring
      exact Nat.eq_of_mul_eq_mul_left hNpos h'
    left; exact ⟨by exact_mod_cast this, rfl⟩

/-! ## Theorem E, steps E1–E7, both branches -/

/-- **Theorem E, E1–E7, `2π/3` branch** (row5/AUDIT.md §4).  For an `N`-tiling of an equilateral
target of side `S` by a `2π/3` tile `(α, π/3 − α, 2π/3)` with sides `(a, b, c)`, `α ∉ ℚπ`: the two
invariants `s(c+a−b) = 3S`, `t(c+b−a) = 3S` with `s, t ∈ [1, N]`, `s ≡ t ≡ N (mod 2)` (E4); the
area identity `S² = N·ab` (E5); `st = 3N` (E6); and at prime `N`, `{s, t} = {3, N}` (E7). -/
theorem Row5.theoremE_twoPiThree (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoPiThreeData α a b c)
    (hP : ∀ k, D.target.angleAt k = Real.pi / 3) :
    ∃ s t : ℤ, (2 : ℤ) ∣ s - N ∧ (2 : ℤ) ∣ t - N ∧ 1 ≤ s ∧ s ≤ N ∧ 1 ≤ t ∧ t ≤ N ∧
      (s : ℝ) * (c + a - b) = 3 * D.target.oppLen 0 ∧
      (t : ℝ) * (c + b - a) = 3 * D.target.oppLen 0 ∧
      D.target.oppLen 0 ^ 2 = N * a * b ∧ s * t = 3 * N ∧
      (N.Prime → (s = 3 ∧ t = N) ∨ (s = N ∧ t = 3)) := by
  have hmodel : ∀ b' : ZMod 2, ∀ k, ((D.model.angleAt k : ℝ) : Real.Angle)
      ∈ (wAt α hα b' (D.target.leftUnit 0).angle).L :=
    fun b' => D.model.data_angles_mem hα h b'
  obtain ⟨e1, e2, S₁, h1, hN1, hS1⟩ := Row5.equilateral_boundary D hα 0 (hmodel 0) hP
  obtain ⟨-, -, S₂, h2, hN2, hS2⟩ := Row5.equilateral_boundary D hα 1 (hmodel 1) hP
  have tv1 : (wAt α hα 0 0).tileValue D.model = -(c + a - b) := data_tileValue_alpha D.model hα h
  have tv2 : (wAt α hα 1 0).tileValue D.model = -(c + b - a) := data_tileValue_beta D.model hα h
  rw [tv1] at hS1
  rw [tv2] at hS2
  obtain ⟨σ, -, oa, -, ob, hγ, oc⟩ := h
  -- positivity of the linear forms (strict triangle inequality)
  have tb := D.model.oppLen_lt_perm σ 1
  have ta := D.model.oppLen_lt_perm σ 0
  rw [oa, ob, oc] at tb ta
  have hS0 : 0 < D.target.oppLen 0 := D.target.oppLen_pos 0
  have ha0 : 0 < a := oa ▸ D.model.oppLen_pos (σ 0)
  have hb0 : 0 < b := ob ▸ D.model.oppLen_pos (σ 1)
  -- the law of cosines at the `2π/3` corner
  have hcos : c ^ 2 = a ^ 2 + b ^ 2 + 1 * a * b := by
    have hl := D.model.lawCos_perm σ
    rw [oa, ob, oc, hγ, show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
      Real.cos_pi_div_three] at hl
    linear_combination hl
  have harea := Row5.area D σ oa ob oc (by norm_num) hcos e1 e2
  set S := D.target.oppLen 0
  have hs_pos : (0 : ℝ) < -S₁ := by
    by_contra hc; push Not at hc
    have : (-(S₁ : ℝ)) * (c + a - b) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc (by linarith)
    linarith
  have ht_pos : (0 : ℝ) < -S₂ := by
    by_contra hc; push Not at hc
    have : (-(S₂ : ℝ)) * (c + b - a) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc (by linarith)
    linarith
  have hs1 : 1 ≤ -S₁ := by
    have : (0 : ℤ) < -S₁ := by exact_mod_cast hs_pos
    omega
  have ht1 : 1 ≤ -S₂ := by
    have : (0 : ℤ) < -S₂ := by exact_mod_cast ht_pos
    omega
  have hsN : -S₁ ≤ N := by have := (abs_le.mp hN1).1; linarith
  have htN : -S₂ ≤ N := by have := (abs_le.mp hN2).1; linarith
  -- E6: `st = 3N`
  have hprod : (-S₁) * (-S₂) = 3 * (N : ℤ) := by
    have hab : a * b ≠ 0 := (mul_pos ha0 hb0).ne'
    have hXY := Erdos634.EqSpecAlgebra.XY_eq (a := a) (b := b) (c := c)
      (by linear_combination hcos)
    have h := Erdos634.EqSpecAlgebra.st_eq (S := S) (c + a - b) (c + b - a) (-(S₁ : ℝ))
      (-(S₂ : ℝ)) (N : ℝ) (by linear_combination hS1) (by linear_combination hS2) hXY
      (by linear_combination (-1 : ℝ) * harea) hab
    have h2 : (-(S₁ : ℝ)) * (-(S₂ : ℝ)) = 3 * (N : ℝ) := mul_right_cancel₀ hab h
    exact_mod_cast h2
  refine ⟨-S₁, -S₂, ?_, ?_, hs1, hsN, ht1, htN, ?_, ?_, harea, hprod,
    fun hN => Row5.prime_pin hN _ _ hs1 hsN ht1 htN hprod⟩
  · rw [show -S₁ - (N : ℤ) = -(S₁ - N) - 2 * N by ring]
    exact dvd_sub (dvd_neg.mpr h1) (dvd_mul_right 2 _)
  · rw [show -S₂ - (N : ℤ) = -(S₂ - N) - 2 * N by ring]
    exact dvd_sub (dvd_neg.mpr h2) (dvd_mul_right 2 _)
  · push_cast; linear_combination hS1
  · push_cast; linear_combination hS2

/-- **Theorem E, E1–E7, `π/3` branch.**  Same setting with a `π/3` tile `(α, 2π/3 − α, π/3)`:
`m₁(a+b−c) = 3S`, `m₂(a+b+c) = 3S` with `m₁, m₂ ∈ [1, N]`, `≡ N (mod 2)` (E4); `S² = N·ab` (E5);
`m₁m₂ = 3N` (E6); `m₁ > m₂`; and at prime `N > 3`, `m₁ = N`, `m₂ = 3` (E7). -/
theorem Row5.theoremE_sixty (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.SixtyData α a b c)
    (hP : ∀ k, D.target.angleAt k = Real.pi / 3) :
    ∃ m₁ m₂ : ℤ, (2 : ℤ) ∣ m₁ - N ∧ (2 : ℤ) ∣ m₂ - N ∧ 1 ≤ m₁ ∧ m₁ ≤ N ∧ 1 ≤ m₂ ∧ m₂ ≤ N ∧
      (m₁ : ℝ) * (a + b - c) = 3 * D.target.oppLen 0 ∧
      (m₂ : ℝ) * (a + b + c) = 3 * D.target.oppLen 0 ∧
      D.target.oppLen 0 ^ 2 = N * a * b ∧ m₁ * m₂ = 3 * N ∧ m₂ < m₁ ∧
      (N.Prime → 3 < N → m₁ = N ∧ m₂ = 3) := by
  have hmodel : ∀ b' : ZMod 2, ∀ k, ((D.model.angleAt k : ℝ) : Real.Angle)
      ∈ (wAt α hα b' (D.target.leftUnit 0).angle).L :=
    fun b' => D.model.sixty_angles_mem hα h b' _
  obtain ⟨e1, e2, S₁, h1, hN1, hS1⟩ := Row5.equilateral_boundary D hα 0 (hmodel 0) hP
  obtain ⟨-, -, S₂, h2, hN2, hS2⟩ := Row5.equilateral_boundary D hα 1 (hmodel 1) hP
  rw [sixty_tileValue_one D.model hα h] at hS1
  rw [sixty_tileValue_two D.model hα h] at hS2
  obtain ⟨σ, -, oa, -, ob, hγ, oc⟩ := h
  have tc := D.model.oppLen_lt_perm σ 2
  rw [oa, ob, oc] at tc
  have hS0 : 0 < D.target.oppLen 0 := D.target.oppLen_pos 0
  have ha0 : 0 < a := oa ▸ D.model.oppLen_pos (σ 0)
  have hb0 : 0 < b := ob ▸ D.model.oppLen_pos (σ 1)
  have hc0 : 0 < c := oc ▸ D.model.oppLen_pos (σ 2)
  have hcos : c ^ 2 = a ^ 2 + b ^ 2 + (-1) * a * b := by
    have hl := D.model.lawCos_perm σ
    rw [oa, ob, oc, hγ, Real.cos_pi_div_three] at hl
    linear_combination hl
  have harea := Row5.area D σ oa ob oc (by norm_num) hcos e1 e2
  set S := D.target.oppLen 0
  have hm1_pos : (0 : ℝ) < -S₁ := by
    by_contra hc; push Not at hc
    have : (-(S₁ : ℝ)) * (a + b - c) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc (by linarith)
    linarith
  have hm2_pos : (0 : ℝ) < S₂ := by
    by_contra hc; push Not at hc
    have : (S₂ : ℝ) * (a + b + c) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc (by linarith)
    linarith
  have hm1 : 1 ≤ -S₁ := by
    have : (0 : ℤ) < -S₁ := by exact_mod_cast hm1_pos
    omega
  have hm2 : 1 ≤ S₂ := by
    have : (0 : ℤ) < S₂ := by exact_mod_cast hm2_pos
    omega
  have hm1N : -S₁ ≤ N := by have := (abs_le.mp hN1).1; linarith
  have hm2N : S₂ ≤ N := by have := (abs_le.mp hN2).2; linarith
  have eq1 : (-(S₁ : ℝ)) * (a + b - c) = 3 * S := by linear_combination hS1
  -- E6: `m₁ m₂ = 3N`
  have hprod : (-S₁) * S₂ = 3 * (N : ℤ) := by
    have hab : a * b ≠ 0 := (mul_pos ha0 hb0).ne'
    have hXY : (a + b - c) * (a + b + c) = 3 * (a * b) := by linear_combination (-1 : ℝ) * hcos
    have h := Erdos634.EqSpecAlgebra.st_eq (S := S) (a + b - c) (a + b + c) (-(S₁ : ℝ))
      (S₂ : ℝ) (N : ℝ) eq1 hS2 hXY (by linear_combination (-1 : ℝ) * harea) hab
    have h2 : (-(S₁ : ℝ)) * (S₂ : ℝ) = 3 * (N : ℝ) := mul_right_cancel₀ hab h
    exact_mod_cast h2
  -- `m₁ > m₂` (from `c > 0`)
  have hlt : S₂ < -S₁ := by
    have : (S₂ : ℝ) < -S₁ := by
      by_contra hc; push Not at hc
      have h3 : (-(S₁ : ℝ)) * (a + b - c) < (S₂ : ℝ) * (a + b + c) := by
        calc (-(S₁ : ℝ)) * (a + b - c) ≤ (S₂ : ℝ) * (a + b - c) :=
              mul_le_mul_of_nonneg_right hc (by linarith)
          _ < (S₂ : ℝ) * (a + b + c) := mul_lt_mul_of_pos_left (by linarith) hm2_pos
      linarith
    exact_mod_cast this
  refine ⟨-S₁, S₂, ?_, h2, hm1, hm1N, hm2, hm2N, ?_, hS2, harea, hprod, hlt, fun hN h3 => ?_⟩
  · rw [show -S₁ - (N : ℤ) = -(S₁ - N) - 2 * N by ring]
    exact dvd_sub (dvd_neg.mpr h1) (dvd_mul_right 2 _)
  · push_cast; linear_combination hS1
  · rcases Row5.prime_pin hN _ _ hm1 hm1N hm2 hm2N hprod with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exfalso
      have : (N : ℤ) < 3 := by rw [← hb, ← ha]; exact hlt
      omega
    · exact ⟨ha, hb⟩

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Tri.lawCos_perm
#print axioms Erdos634.Geometry.Row5.equilateral_boundary
#print axioms Erdos634.Geometry.Row5.area
#print axioms Erdos634.Geometry.Row5.prime_pin
#print axioms Erdos634.Geometry.Row5.theoremE_twoPiThree
#print axioms Erdos634.Geometry.Row5.theoremE_sixty

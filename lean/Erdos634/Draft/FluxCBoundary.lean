-- Draft/FluxCBoundary.lean — consumer layer, item 1: the TRIANGLE-TARGET BOUNDARY LEMMA shared by
-- every row: `PROOF_invariants.md` I3(i) (sign constancy), I3(ii) (value), I3(iv) (the target) and
-- I4's triangle clause `s(P)·K_χ(P) = S·K_χ(T)`.  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
--
-- Formalization debt on the prime-case VERIFIED path; not progress on the three /goal outcomes.
--
-- Reuse (cited, not re-derived): `Tri.flux_grid_of_pos/neg`, `Tri.flux_grid_pm`, `Tri.chi_prod`,
-- `Tri.pi_sub_angleAt_mem`, `CongruentDissection.target_flux_signs`, `GridChar.val_add`,
-- `GridChar.val_sq`, `GridChar.val_anchor`, `Tri.leftUnit_turn_of_pos/neg` (the turn lemma).
-- New here: the paper's `K_χ = −Σ_V χ(φ_V)|opp V|` (`GridChar.paperK`) and its identification with
-- `tileValue`; the per-edge sign `s_k = χ(π − φ_{k+2})·F(e_k)` and the chirality-free identity
-- `C_F(t) = s_k·K` for EVERY edge `k` (I3(i)+(ii); `flux_grid_pm` only gave `±K`); the boundary
-- lemma with the explicit target sign, and its anchored form.
import Erdos634.Draft.FluxValue

open scoped Classical

namespace Erdos634.Geometry

variable {N : ℕ}

namespace GridChar

variable (G : GridChar ℝ)

/-- For a `±1`-valued character, `χ(π − θ) = −χ(θ)` on `L`. -/
theorem chi_pi_sub (hsq : ∀ l ∈ G.L, G.chi l * G.chi l = 1) {θ : ℝ}
    (h : ((θ : ℝ) : Real.Angle) ∈ G.L) :
    G.chi ((Real.pi - θ : ℝ) : Real.Angle) = - G.chi ((θ : ℝ) : Real.Angle) := by
  have hneg : ((-θ : ℝ) : Real.Angle) ∈ G.L := by
    rw [Real.Angle.coe_neg]; exact G.L.neg_mem h
  have e : ((Real.pi - θ : ℝ) : Real.Angle)
      = ((Real.pi : ℝ) : Real.Angle) + ((-θ : ℝ) : Real.Angle) := by
    rw [← Real.Angle.coe_add, sub_eq_add_neg]
  have h0 : G.chi ((θ : ℝ) : Real.Angle) * G.chi ((-θ : ℝ) : Real.Angle) = 1 := by
    rw [← G.chi_add h hneg, ← Real.Angle.coe_add, add_neg_cancel, Real.Angle.coe_zero, G.chi_zero]
  have hs := hsq _ h
  have hsym : G.chi ((-θ : ℝ) : Real.Angle) = G.chi ((θ : ℝ) : Real.Angle) := by
    linear_combination (G.chi ((θ : ℝ) : Real.Angle)) * h0
      - (G.chi ((-θ : ℝ) : Real.Angle)) * hs
  rw [e, G.chi_add G.pi_mem hneg, G.chi_pi, hsym]
  ring

/-- **The paper's triangle value** `K_χ(t) = −Σ_V χ(φ_V)·|side opposite V|`
(`PROOF_invariants.md` I3). -/
noncomputable def paperK (T : Tri) : ℝ :=
  - ∑ k : Fin 3, G.chi ((T.angleAt k : ℝ) : Real.Angle) * T.oppLen k

/-- `tileValue` (the exterior-angle form of `FluxValue`) IS the paper's `K_χ`. -/
theorem tileValue_eq_paperK (hsq : ∀ l ∈ G.L, G.chi l * G.chi l = 1) (T : Tri)
    (h : ∀ k, ((T.angleAt k : ℝ) : Real.Angle) ∈ G.L) : G.tileValue T = G.paperK T := by
  unfold tileValue paperK
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [G.chi_pi_sub hsq (h k)]
  ring

/-- **The sign of edge `k`** of `T`: edge `k` joins vertices `k`, `k+1` and is opposite vertex
`k+2`; `s_k = χ(π − φ_{k+2})·F(e_k)`, i.e. the paper's `s_V = −χ(φ_V)·F(e_V)` at `V = k+2`. -/
noncomputable def edgeSign (T : Tri) (k : Fin 3) : ℝ :=
  G.chi ((Real.pi - T.angleAt (k + 2) : ℝ) : Real.Angle) * G.weight (T.leftUnit k)

theorem edgeSign_eq_paper (hsq : ∀ l ∈ G.L, G.chi l * G.chi l = 1) (T : Tri)
    (h : ∀ k, ((T.angleAt k : ℝ) : Real.Angle) ∈ G.L) (k : Fin 3) :
    G.edgeSign T k = - G.chi ((T.angleAt (k + 2) : ℝ) : Real.Angle) * G.weight (T.leftUnit k) := by
  unfold edgeSign
  rw [G.chi_pi_sub hsq (h (k + 2))]

/-- The edge sign is `±1`. -/
theorem edgeSign_sq (hsq : ∀ l ∈ G.L, G.chi l * G.chi l = 1) (T : Tri)
    (h : ∀ k, ((T.angleAt k : ℝ) : Real.Angle) ∈ G.L) (k : Fin 3) :
    G.edgeSign T k * G.edgeSign T k = 1 := by
  unfold edgeSign
  have h1 := hsq _ (T.pi_sub_angleAt_mem G h (k + 2))
  have h2 := G.val_sq hsq (T.leftUnit k).angle
  unfold weight
  linear_combination (G.val (T.leftUnit k).angle * G.val (T.leftUnit k).angle) * h1 + h2

end GridChar

/-- Consecutive weights of a ccw tile: `F(e_{k+1}) = χ(π − φ_{k+1})·F(e_k)` (the turn lemma). -/
theorem Tri.weight_succ_of_pos (G : GridChar ℝ) (T : Tri) (hT : 0 < T.det)
    (h : ∀ k, ((T.angleAt k : ℝ) : Real.Angle) ∈ G.L) (k : Fin 3) :
    G.weight (T.leftUnit (k + 1))
      = G.chi ((Real.pi - T.angleAt (k + 1) : ℝ) : Real.Angle) * G.weight (T.leftUnit k) := by
  unfold GridChar.weight
  rw [T.leftUnit_turn_of_pos hT k, G.val_add _ (T.pi_sub_angleAt_mem G h (k + 1))]

/-- Consecutive weights of a cw tile: `F(e_k) = χ(π − φ_{k+1})·F(e_{k+1})`. -/
theorem Tri.weight_succ_of_neg (G : GridChar ℝ) (T : Tri) (hT : T.det < 0)
    (h : ∀ k, ((T.angleAt k : ℝ) : Real.Angle) ∈ G.L) (k : Fin 3) :
    G.weight (T.leftUnit k)
      = G.chi ((Real.pi - T.angleAt (k + 1) : ℝ) : Real.Angle) * G.weight (T.leftUnit (k + 1)) := by
  unfold GridChar.weight
  rw [T.leftUnit_turn_of_neg hT k, G.val_add _ (T.pi_sub_angleAt_mem G h (k + 1))]

/-- **I3(i) + I3(ii), chirality-free, every edge.**  For a `±1` character and a triangle whose
angles lie in `L`, in either orientation, `C_F(T) = s_k·K_χ(T)` for EACH of the three edges `k`
(so in particular the three edge signs agree). -/
theorem Tri.flux_eq_edgeSign (G : GridChar ℝ) (hsq : ∀ l ∈ G.L, G.chi l * G.chi l = 1) (T : Tri)
    (h : ∀ k, ((T.angleAt k : ℝ) : Real.Angle) ∈ G.L) (k : Fin 3) :
    T.flux G.weight = G.edgeSign T k * G.tileValue T := by
  have hc0 := hsq _ (T.pi_sub_angleAt_mem G h 0)
  have hc1 := hsq _ (T.pi_sub_angleAt_mem G h 1)
  have hc2 := hsq _ (T.pi_sub_angleAt_mem G h 2)
  have hprod := T.chi_prod G h
  have hK : G.tileValue T
      = G.chi ((Real.pi - T.angleAt 0 : ℝ) : Real.Angle) * T.oppLen 0
        + G.chi ((Real.pi - T.angleAt 1 : ℝ) : Real.Angle) * T.oppLen 1
        + G.chi ((Real.pi - T.angleAt 2 : ℝ) : Real.Angle) * T.oppLen 2 := by
    unfold GridChar.tileValue
    rw [Fin.sum_univ_three]
  unfold GridChar.edgeSign
  set c0 := G.chi ((Real.pi - T.angleAt 0 : ℝ) : Real.Angle) with hc0def
  set c1 := G.chi ((Real.pi - T.angleAt 1 : ℝ) : Real.Angle) with hc1def
  set c2 := G.chi ((Real.pi - T.angleAt 2 : ℝ) : Real.Angle) with hc2def
  have e02 : c0 * c2 = c1 := by linear_combination c1 * hprod - (c0 * c2) * hc1
  have e01 : c0 * c1 = c2 := by linear_combination c2 * hprod - (c0 * c1) * hc2
  rcases T.det_pos_or_neg with hT | hT
  · have hF := T.flux_grid_of_pos G hT h
    have w1 := T.weight_succ_of_pos G hT h 0
    have w2 := T.weight_succ_of_pos G hT h 1
    simp only [show (0:Fin 3) + 1 = 1 from rfl, show (1:Fin 3) + 1 = 2 from rfl] at w1 w2
    rw [← hc1def] at w1
    rw [← hc2def] at w2
    rw [← hc1def, ← hc2def] at hF
    set w0 := G.weight (T.leftUnit 0)
    -- the flux is `c2·w0·K`
    have key : T.flux G.weight = (c2 * w0) * G.tileValue T := by
      rw [hF, hK]
      linear_combination (-(w0 * T.oppLen 0)) * e02 - (w0 * T.oppLen 2) * hc2
    rw [key]
    fin_cases k
    · show (c2 * w0) * _ = (G.chi ((Real.pi - T.angleAt ((0 : Fin 3) + 2) : ℝ) : Real.Angle)
        * w0) * _
      rfl
    · show (c2 * w0) * _ = (G.chi ((Real.pi - T.angleAt ((1 : Fin 3) + 2) : ℝ) : Real.Angle)
        * G.weight (T.leftUnit 1)) * _
      rw [show (1 : Fin 3) + 2 = 0 from rfl, ← hc0def, w1]
      congr 1
      linear_combination (-w0) * e01
    · show (c2 * w0) * _ = (G.chi ((Real.pi - T.angleAt ((2 : Fin 3) + 2) : ℝ) : Real.Angle)
        * G.weight (T.leftUnit 2)) * _
      rw [show (2 : Fin 3) + 2 = 1 from rfl, ← hc1def, w2, w1]
      congr 1
      linear_combination (-(c2 * w0)) * hc1
  · have hF := T.flux_grid_of_neg G hT h
    have w0 := T.weight_succ_of_neg G hT h 0
    have w1 := T.weight_succ_of_neg G hT h 1
    simp only [show (0:Fin 3) + 1 = 1 from rfl, show (1:Fin 3) + 1 = 2 from rfl] at w0 w1
    rw [← hc1def] at w0
    rw [← hc2def] at w1
    rw [← hc1def, ← hc2def] at hF
    set w2 := G.weight (T.leftUnit 2)
    have key : T.flux G.weight = (c1 * w2) * G.tileValue T := by
      rw [hF, hK]
      linear_combination (-(w2 * T.oppLen 0)) * e01 - (w2 * T.oppLen 1) * hc1
    rw [key]
    fin_cases k
    · show (c1 * w2) * _ = (G.chi ((Real.pi - T.angleAt ((0 : Fin 3) + 2) : ℝ) : Real.Angle)
        * G.weight (T.leftUnit 0)) * _
      rw [show (0 : Fin 3) + 2 = 2 from rfl, ← hc2def, w0, w1]
      congr 1
      linear_combination (-(c1 * w2)) * hc2
    · show (c1 * w2) * _ = (G.chi ((Real.pi - T.angleAt ((1 : Fin 3) + 2) : ℝ) : Real.Angle)
        * G.weight (T.leftUnit 1)) * _
      rw [show (1 : Fin 3) + 2 = 0 from rfl, ← hc0def, w1]
      congr 1
      linear_combination (-w2) * e02
    · show (c1 * w2) * _ = (G.chi ((Real.pi - T.angleAt ((2 : Fin 3) + 2) : ℝ) : Real.Angle)
        * w2) * _
      rfl

/-- **Anchored edge.**  If the grid is anchored at the direction of `T`'s edge `k`, that edge's
weight is `1` and `C_F(T) = χ(π − φ_{k+2})·K_χ(T) = −χ(φ_{k+2})·K_χ(T)`. -/
theorem Tri.flux_eq_of_anchor (G : GridChar ℝ) (hsq : ∀ l ∈ G.L, G.chi l * G.chi l = 1) (T : Tri)
    (h : ∀ k, ((T.angleAt k : ℝ) : Real.Angle) ∈ G.L) (k : Fin 3)
    (hanc : G.anchor = (T.leftUnit k).angle) :
    T.flux G.weight = - G.chi ((T.angleAt (k + 2) : ℝ) : Real.Angle) * G.paperK T := by
  rw [T.flux_eq_edgeSign G hsq h k, G.edgeSign_eq_paper hsq T h k, G.tileValue_eq_paperK hsq T h]
  have hw : G.weight (T.leftUnit k) = 1 := by
    unfold GridChar.weight; rw [← hanc]; exact G.val_anchor
  rw [hw, mul_one]

/-- **THE TRIANGLE-TARGET BOUNDARY LEMMA** (I3(iv) + I4's triangle clause).  For a
`CongruentDissection` whose model and target both have their angles in `L`, and a `±1` character:
there is a sum `S` of `N` signs (`S ≡ N mod 2`, `|S| ≤ N`) with, for every target edge `k`,
`S·K_χ(model) = s_k(P)·K_χ(P)`, where `s_k(P) = −χ(φ_{k+2})·F(e_k)` is `±1`. -/
theorem CongruentDissection.triangle_boundary (D : CongruentDissection N) (G : GridChar ℝ)
    (hsq : ∀ l ∈ G.L, G.chi l * G.chi l = 1)
    (hmodel : ∀ k, ((D.model.angleAt k : ℝ) : Real.Angle) ∈ G.L)
    (htarget : ∀ k, ((D.target.angleAt k : ℝ) : Real.Angle) ∈ G.L) :
    ∃ S : ℤ, (2 : ℤ) ∣ S - N ∧ |S| ≤ N ∧
      ∀ k : Fin 3, (S : ℝ) * G.paperK D.model = G.edgeSign D.target k * G.paperK D.target := by
  obtain ⟨S, hS2, hSN, hSf⟩ := D.target_flux_signs G hsq hmodel
  refine ⟨S, hS2, hSN, fun k => ?_⟩
  rw [← G.tileValue_eq_paperK hsq _ hmodel, ← G.tileValue_eq_paperK hsq _ htarget, ← hSf]
  exact D.target.flux_eq_edgeSign G hsq htarget k

/-- The boundary lemma, `±` form: `S·K_χ(model) = ±K_χ(target)`. -/
theorem CongruentDissection.triangle_boundary_pm (D : CongruentDissection N) (G : GridChar ℝ)
    (hsq : ∀ l ∈ G.L, G.chi l * G.chi l = 1)
    (hmodel : ∀ k, ((D.model.angleAt k : ℝ) : Real.Angle) ∈ G.L)
    (htarget : ∀ k, ((D.target.angleAt k : ℝ) : Real.Angle) ∈ G.L) :
    ∃ S : ℤ, (2 : ℤ) ∣ S - N ∧ |S| ≤ N ∧
      ((S : ℝ) * G.paperK D.model = G.paperK D.target
        ∨ (S : ℝ) * G.paperK D.model = - G.paperK D.target) := by
  obtain ⟨S, hS2, hSN, hk⟩ := D.triangle_boundary G hsq hmodel htarget
  refine ⟨S, hS2, hSN, ?_⟩
  have h0 := hk 0
  rcases mul_self_eq_one_iff.mp (G.edgeSign_sq hsq D.target htarget 0) with e | e
  · left; rw [h0, e, one_mul]
  · right; rw [h0, e, neg_one_mul]

/-- **The boundary lemma, anchored at a target side.**  If the grid's anchor is the direction of
target edge `k` (traversed ccw), then `S·K_χ(model) = −χ(φ_{k+2})·K_χ(P)` with no unknown sign:
the target's value is read off its corner angles and side lengths alone. -/
theorem CongruentDissection.triangle_boundary_anchor (D : CongruentDissection N)
    (G : GridChar ℝ) (hsq : ∀ l ∈ G.L, G.chi l * G.chi l = 1)
    (hmodel : ∀ k, ((D.model.angleAt k : ℝ) : Real.Angle) ∈ G.L)
    (htarget : ∀ k, ((D.target.angleAt k : ℝ) : Real.Angle) ∈ G.L) (k : Fin 3)
    (hanc : G.anchor = (D.target.leftUnit k).angle) :
    ∃ S : ℤ, (2 : ℤ) ∣ S - N ∧ |S| ≤ N ∧
      (S : ℝ) * G.paperK D.model
        = - G.chi ((D.target.angleAt (k + 2) : ℝ) : Real.Angle) * G.paperK D.target := by
  obtain ⟨S, hS2, hSN, hSf⟩ := D.target_flux_signs G hsq hmodel
  refine ⟨S, hS2, hSN, ?_⟩
  rw [← G.tileValue_eq_paperK hsq _ hmodel, ← hSf]
  exact D.target.flux_eq_of_anchor G hsq htarget k hanc

/-- I3(iii) in the paper's form: `K_χ` is a congruence invariant (reflections included). -/
theorem GridChar.paperK_congr (G : GridChar ℝ) (hsq : ∀ l ∈ G.L, G.chi l * G.chi l = 1)
    {T U : Tri} (hTU : T.Congruent U) (hT : ∀ k, ((T.angleAt k : ℝ) : Real.Angle) ∈ G.L)
    (hU : ∀ k, ((U.angleAt k : ℝ) : Real.Angle) ∈ G.L) : G.paperK T = G.paperK U := by
  rw [← G.tileValue_eq_paperK hsq T hT, ← G.tileValue_eq_paperK hsq U hU,
    G.tileValue_congr hTU]

end Erdos634.Geometry

#print axioms Erdos634.Geometry.GridChar.chi_pi_sub
#print axioms Erdos634.Geometry.GridChar.tileValue_eq_paperK
#print axioms Erdos634.Geometry.GridChar.edgeSign_sq
#print axioms Erdos634.Geometry.Tri.flux_eq_edgeSign
#print axioms Erdos634.Geometry.Tri.flux_eq_of_anchor
#print axioms Erdos634.Geometry.CongruentDissection.triangle_boundary
#print axioms Erdos634.Geometry.CongruentDissection.triangle_boundary_pm
#print axioms Erdos634.Geometry.CongruentDissection.triangle_boundary_anchor

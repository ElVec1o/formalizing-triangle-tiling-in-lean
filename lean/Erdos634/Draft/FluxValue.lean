-- Draft/FluxValue.lean — layer 2, part 3: the tile value (`lem:value` for a general grid: every
-- tile contributes `±K`) and `cor:int` (the boundary flux is `K` times a sum of `N` signs).
-- Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).  Design: (private working notes, not included) §3.6 (`FluxValue.lean`).
--
-- Formalization debt (`lem:value`, `cor:int`); not progress on the three /goal outcomes.
--
-- Reuse (cited): `Tri.Congruent.dist_eq`, `Tri.det_pos_or_neg` (Congruence), `angle_of_sss`,
-- `fin3_cases` (CongruentAngles), `InvariantCore.integrality_parity`, and this room's
-- `Dissection.flux_cancel`, `Tri.leftUnit_turn_of_pos/neg`, `GridChar.val_add/weight_odd`.
import Erdos634.Draft.FluxWeight
import Erdos634.Draft.FluxCancel
import Erdos634.CongruentAngles
import Erdos634.InvariantCore

open scoped Classical

namespace Erdos634.Geometry

variable {N : ℕ}

/-- Exterior angles of a tile whose angles lie in `L` lie in `L`. -/
theorem Tri.pi_sub_angleAt_mem (G : GridChar ℝ) (T : Tri)
    (h : ∀ k, ((T.angleAt k : ℝ) : Real.Angle) ∈ G.L) (k : Fin 3) :
    ((Real.pi - T.angleAt k : ℝ) : Real.Angle) ∈ G.L := by
  rw [Real.Angle.coe_sub]
  exact G.L.sub_mem G.pi_mem (h k)

/-- **Tile flux, ccw tile**: `C = w₀ · (|e₀| + χ(π−θ₁)|e₁| + χ(π−θ₁)χ(π−θ₂)|e₂|)`. -/
theorem Tri.flux_grid_of_pos (G : GridChar ℝ) (T : Tri) (hT : 0 < T.det)
    (h : ∀ k, ((T.angleAt k : ℝ) : Real.Angle) ∈ G.L) :
    T.flux G.weight = G.weight (T.leftUnit 0) *
      (T.oppLen 2 + G.chi ((Real.pi - T.angleAt 1 : ℝ) : Real.Angle) * T.oppLen 0
        + G.chi ((Real.pi - T.angleAt 1 : ℝ) : Real.Angle)
          * G.chi ((Real.pi - T.angleAt 2 : ℝ) : Real.Angle) * T.oppLen 1) := by
  have t1 := T.leftUnit_turn_of_pos hT 0
  have t2 := T.leftUnit_turn_of_pos hT 1
  simp only [show (0:Fin 3) + 1 = 1 from rfl, show (1:Fin 3) + 1 = 2 from rfl] at t1 t2
  have w1 : G.weight (T.leftUnit 1)
      = G.chi ((Real.pi - T.angleAt 1 : ℝ) : Real.Angle) * G.weight (T.leftUnit 0) := by
    unfold GridChar.weight
    rw [t1, G.val_add _ (T.pi_sub_angleAt_mem G h 1)]
  have w2 : G.weight (T.leftUnit 2)
      = G.chi ((Real.pi - T.angleAt 2 : ℝ) : Real.Angle) * G.weight (T.leftUnit 1) := by
    unfold GridChar.weight
    rw [t2, G.val_add _ (T.pi_sub_angleAt_mem G h 2)]
  unfold Tri.flux Tri.oppLen
  rw [Fin.sum_univ_three]
  simp only [show (0:Fin 3) + 1 = 1 from rfl, show (1:Fin 3) + 1 = 2 from rfl,
    show (2:Fin 3) + 1 = 0 from rfl, show (0:Fin 3) + 2 = 2 from rfl,
    show (1:Fin 3) + 2 = 0 from rfl, show (2:Fin 3) + 2 = 1 from rfl, smul_eq_mul]
  rw [w2, w1]
  ring

/-- **Tile flux, cw tile** (the ccw traversal runs `2 → 1 → 0`). -/
theorem Tri.flux_grid_of_neg (G : GridChar ℝ) (T : Tri) (hT : T.det < 0)
    (h : ∀ k, ((T.angleAt k : ℝ) : Real.Angle) ∈ G.L) :
    T.flux G.weight = G.weight (T.leftUnit 2) *
      (T.oppLen 1 + G.chi ((Real.pi - T.angleAt 2 : ℝ) : Real.Angle) * T.oppLen 0
        + G.chi ((Real.pi - T.angleAt 2 : ℝ) : Real.Angle)
          * G.chi ((Real.pi - T.angleAt 1 : ℝ) : Real.Angle) * T.oppLen 2) := by
  have t0 := T.leftUnit_turn_of_neg hT 0
  have t1 := T.leftUnit_turn_of_neg hT 1
  simp only [show (0:Fin 3) + 1 = 1 from rfl, show (1:Fin 3) + 1 = 2 from rfl] at t0 t1
  have w1 : G.weight (T.leftUnit 1)
      = G.chi ((Real.pi - T.angleAt 2 : ℝ) : Real.Angle) * G.weight (T.leftUnit 2) := by
    unfold GridChar.weight
    rw [t1, G.val_add _ (T.pi_sub_angleAt_mem G h 2)]
  have w0 : G.weight (T.leftUnit 0)
      = G.chi ((Real.pi - T.angleAt 1 : ℝ) : Real.Angle) * G.weight (T.leftUnit 1) := by
    unfold GridChar.weight
    rw [t0, G.val_add _ (T.pi_sub_angleAt_mem G h 1)]
  unfold Tri.flux Tri.oppLen
  rw [Fin.sum_univ_three]
  simp only [show (0:Fin 3) + 1 = 1 from rfl, show (1:Fin 3) + 1 = 2 from rfl,
    show (2:Fin 3) + 1 = 0 from rfl, show (0:Fin 3) + 2 = 2 from rfl,
    show (1:Fin 3) + 2 = 0 from rfl, show (2:Fin 3) + 2 = 1 from rfl, smul_eq_mul]
  rw [w0, w1]
  ring

/-- **The chirality-free tile value** `K_G(T) = Σ_k χ(π − θ_k)·(side opposite k)`. -/
noncomputable def GridChar.tileValue (G : GridChar ℝ) (T : Tri) : ℝ :=
  ∑ k : Fin 3, G.chi ((Real.pi - T.angleAt k : ℝ) : Real.Angle) * T.oppLen k

/-- The three exterior characters multiply to `χ(2π) = 1`. -/
theorem Tri.chi_prod (G : GridChar ℝ) (T : Tri)
    (h : ∀ k, ((T.angleAt k : ℝ) : Real.Angle) ∈ G.L) :
    G.chi ((Real.pi - T.angleAt 0 : ℝ) : Real.Angle)
      * G.chi ((Real.pi - T.angleAt 1 : ℝ) : Real.Angle)
      * G.chi ((Real.pi - T.angleAt 2 : ℝ) : Real.Angle) = 1 := by
  have m0 := T.pi_sub_angleAt_mem G h 0
  have m1 := T.pi_sub_angleAt_mem G h 1
  have m2 := T.pi_sub_angleAt_mem G h 2
  rw [← G.chi_add m0 m1, ← G.chi_add (G.L.add_mem m0 m1) m2, ← Real.Angle.coe_add,
    ← Real.Angle.coe_add]
  have hs : (Real.pi - T.angleAt 0) + (Real.pi - T.angleAt 1) + (Real.pi - T.angleAt 2)
      = 2 * Real.pi := by linarith [T.angleAt_sum]
  rw [hs, Real.Angle.coe_two_pi, G.chi_zero]

/-- **`lem:value` for a general grid.**  For a `±1`-valued character, every placement of a tile
whose angles lie in `L` — either orientation — has flux `±K_G(T)`. -/
theorem Tri.flux_grid_pm (G : GridChar ℝ) (hsq : ∀ l ∈ G.L, G.chi l * G.chi l = 1) (T : Tri)
    (h : ∀ k, ((T.angleAt k : ℝ) : Real.Angle) ∈ G.L) :
    T.flux G.weight = G.tileValue T ∨ T.flux G.weight = - G.tileValue T := by
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
  set c0 := G.chi ((Real.pi - T.angleAt 0 : ℝ) : Real.Angle) with hc0def
  set c1 := G.chi ((Real.pi - T.angleAt 1 : ℝ) : Real.Angle) with hc1def
  set c2 := G.chi ((Real.pi - T.angleAt 2 : ℝ) : Real.Angle) with hc2def
  rcases T.det_pos_or_neg with hT | hT
  · rw [T.flux_grid_of_pos G hT h, hK]
    set w := G.weight (T.leftUnit 0) with hwdef
    have hw : w * w = 1 := G.val_sq hsq _
    have e1 : c0 * c2 = c1 := by linear_combination c1 * hprod - (c0 * c2) * hc1
    have key : w * (T.oppLen 2 + c1 * T.oppLen 0 + c1 * c2 * T.oppLen 1)
        = (w * c2) * (c0 * T.oppLen 0 + c1 * T.oppLen 1 + c2 * T.oppLen 2) := by
      linear_combination (-(w * T.oppLen 0)) * e1 - (w * T.oppLen 2) * hc2
    have hs : (w * c2) * (w * c2) = 1 := by linear_combination c2 * c2 * hw + hc2
    rw [key]
    rcases mul_self_eq_one_iff.mp hs with h1 | h1
    · left; rw [h1, one_mul]
    · right; rw [h1, neg_one_mul]
  · rw [T.flux_grid_of_neg G hT h, hK]
    set w := G.weight (T.leftUnit 2) with hwdef
    have hw : w * w = 1 := G.val_sq hsq _
    have e2 : c0 * c1 = c2 := by linear_combination c2 * hprod - (c0 * c1) * hc2
    have key : w * (T.oppLen 1 + c2 * T.oppLen 0 + c2 * c1 * T.oppLen 2)
        = (w * c1) * (c0 * T.oppLen 0 + c1 * T.oppLen 1 + c2 * T.oppLen 2) := by
      linear_combination (-(w * T.oppLen 0)) * e2 - (w * T.oppLen 1) * hc1
    have hs : (w * c1) * (w * c1) = 1 := by linear_combination c1 * c1 * hw + hc1
    rw [key]
    rcases mul_self_eq_one_iff.mp hs with h1 | h1
    · left; rw [h1, one_mul]
    · right; rw [h1, neg_one_mul]

/-- **Congruent triangles: one permutation matches angles and opposite sides.** -/
theorem Tri.Congruent.exists_perm {T U : Tri} (h : T.Congruent U) :
    ∃ σ : Equiv.Perm (Fin 3), ∀ k, T.angleAt k = U.angleAt (σ k) ∧ T.oppLen k = U.oppLen (σ k) := by
  obtain ⟨σ, hd⟩ := h.dist_eq
  refine ⟨σ, fun k => ?_⟩
  have hne1 : k + 1 ≠ k := by fin_cases k <;> decide
  have hne2 : k + 2 ≠ k := by fin_cases k <;> decide
  have hne12 : k + 1 ≠ k + 2 := by fin_cases k <;> decide
  have hT1 : T.pts (k + 1) ≠ T.pts k := fun hh => hne1 (T.indep.injective hh)
  have hT2 : T.pts (k + 2) ≠ T.pts k := fun hh => hne2 (T.indep.injective hh)
  have hs1 : σ (k + 1) ≠ σ k := fun hh => hne1 (σ.injective hh)
  have hs2 : σ (k + 2) ≠ σ k := fun hh => hne2 (σ.injective hh)
  have hs12 : σ (k + 1) ≠ σ (k + 2) := fun hh => hne12 (σ.injective hh)
  have hang : T.angleAt k = cornerAngle (U.pts (σ (k + 1))) (U.pts (σ k)) (U.pts (σ (k + 2))) := by
    unfold Tri.angleAt cornerAngle
    exact angle_of_sss (hd (k + 1) k) (hd k (k + 2)) (hd (k + 1) (k + 2)) hT1 hT2
  have hopp : T.oppLen k = dist (U.pts (σ (k + 1))) (U.pts (σ (k + 2))) := hd (k + 1) (k + 2)
  have hsum : σ k + 1 ≠ σ k + 2 := by
    intro hh
    have := add_left_cancel hh
    exact absurd this (by decide)
  rcases fin3_cases _ _ hs1 with ha | ha
  · rcases fin3_cases _ _ hs2 with hb | hb
    · exact absurd (ha.trans hb.symm) hs12
    · refine ⟨?_, ?_⟩
      · rw [hang, ha, hb]; rfl
      · rw [hopp, ha, hb]; rfl
  · rcases fin3_cases _ _ hs2 with hb | hb
    · refine ⟨?_, ?_⟩
      · rw [hang, ha, hb]
        unfold Tri.angleAt cornerAngle
        exact EuclideanGeometry.angle_comm _ _ _
      · rw [hopp, ha, hb, dist_comm]; rfl
    · exact absurd (ha.trans hb.symm) hs12

/-- The tile value is a congruence invariant (reflections included). -/
theorem GridChar.tileValue_congr (G : GridChar ℝ) {T U : Tri} (h : T.Congruent U) :
    G.tileValue T = G.tileValue U := by
  obtain ⟨σ, hσ⟩ := h.exists_perm
  unfold GridChar.tileValue
  rw [← Equiv.sum_comp σ
    (fun j => G.chi ((Real.pi - U.angleAt j : ℝ) : Real.Angle) * U.oppLen j)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [(hσ k).1, (hσ k).2]

/-- **`cor:int`, any grid.**  In a dissection into congruent copies of a tile whose angles lie in
`L`, the target's flux is `K_G(model)` times a sum `S` of `N` signs: `S ≡ N (mod 2)`, `|S| ≤ N`. -/
theorem CongruentDissection.target_flux_signs (D : CongruentDissection N) (G : GridChar ℝ)
    (hsq : ∀ l ∈ G.L, G.chi l * G.chi l = 1)
    (h : ∀ k, ((D.model.angleAt k : ℝ) : Real.Angle) ∈ G.L) :
    ∃ S : ℤ, (2 : ℤ) ∣ S - N ∧ |S| ≤ N ∧
      D.target.flux G.weight = (S : ℝ) * G.tileValue D.model := by
  set K := G.tileValue D.model with hKdef
  have htile : ∀ i, (D.tile i).flux G.weight = K ∨ (D.tile i).flux G.weight = -K := by
    intro i
    obtain ⟨σ, hσ⟩ := (D.tiles_congruent i).exists_perm
    have hi : ∀ k, (((D.tile i).angleAt k : ℝ) : Real.Angle) ∈ G.L := fun k => by
      rw [(hσ k).1]; exact h _
    rw [hKdef, ← G.tileValue_congr (D.tiles_congruent i)]
    exact (D.tile i).flux_grid_pm G hsq hi
  let ε : Fin N → ℤ := fun i => if (D.tile i).flux G.weight = K then 1 else -1
  have hε : ∀ i, ε i = 1 ∨ ε i = -1 := by
    intro i
    by_cases hi : (D.tile i).flux G.weight = K
    · left; exact if_pos hi
    · right; exact if_neg hi
  have hεval : ∀ i, (D.tile i).flux G.weight = (ε i : ℝ) * K := by
    intro i
    by_cases hi : (D.tile i).flux G.weight = K
    · rw [show ε i = 1 from if_pos hi]; push_cast; rw [one_mul, hi]
    · rw [show ε i = -1 from if_neg hi]; push_cast
      rcases htile i with h1 | h1
      · exact absurd h1 hi
      · rw [h1, neg_one_mul]
  refine ⟨∑ i, ε i, InvariantCore.integrality_parity N ε hε, ?_, ?_⟩
  · calc |∑ i, ε i| ≤ ∑ i, |ε i| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ _i : Fin N, (1 : ℤ) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rcases hε i with h1 | h1 <;> rw [h1] <;> rfl
      _ = N := by simp
  · rw [← D.flux_cancel G.weight G.weight_odd]
    rw [Finset.sum_congr rfl fun i _ => hεval i, ← Finset.sum_mul]
    push_cast
    rfl

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Tri.flux_grid_pm
#print axioms Erdos634.Geometry.GridChar.tileValue_congr
#print axioms Erdos634.Geometry.CongruentDissection.target_flux_signs

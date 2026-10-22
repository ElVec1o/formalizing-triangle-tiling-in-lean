import Erdos634.BADAngles
import Erdos634.NormalPosition

/-!
# BAD layer L2, final statement: Theorem A at the dissection level (`BAD.theoremA_L2`)

Written 2026-10-03.  UNAUDITED.  Statement: a `CongruentDissection` (isometries incl. reflections,
`N` free, not necessarily edge-to-edge) whose model has side lengths `(ef, f²-e², f²)` with
`gcd(e,f)=1`, `0<e<f`, and whose target is a triangle with side lengths `f²w, f²w, (2f²-e²)w`
(in any vertex labelling) forces `(f²-e²) ∣ w`.  No real dissection witness is known (see notes).
-/

open LaurentPolynomial

namespace Erdos634.BADL2
open Erdos634.Geometry Erdos634.NormalPosition

noncomputable section

theorem relabel_opp (T : Tri) (τ : Equiv.Perm (Fin 3)) (k : Fin 3) :
    (relabelTri T τ).oppLen k = T.oppLen (τ k) := by
  have d1 : τ k ≠ τ (k + 1) := fun h => by
    have := τ.injective h; fin_cases k <;> simp at this
  have d2 : τ k ≠ τ (k + 2) := fun h => by
    have := τ.injective h; fin_cases k <;> simp at this
  have d3 : τ (k + 1) ≠ τ (k + 2) := fun h => by
    have := τ.injective h; fin_cases k <;> simp at this
  unfold Tri.oppLen
  simp only [relabelTri_pts]
  rcases perm3 _ _ _ d1 d2 d3 with ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ |
    ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ <;>
  · rw [hx, hy, hz]
    first | rfl | (rw [dist_comm]; rfl)

theorem relabel_ang (T : Tri) (τ : Equiv.Perm (Fin 3)) (k : Fin 3) :
    (relabelTri T τ).angleAt k = T.angleAt (τ k) := by
  have d1 : τ k ≠ τ (k + 1) := fun h => by
    have := τ.injective h; fin_cases k <;> simp at this
  have d2 : τ k ≠ τ (k + 2) := fun h => by
    have := τ.injective h; fin_cases k <;> simp at this
  have d3 : τ (k + 1) ≠ τ (k + 2) := fun h => by
    have := τ.injective h; fin_cases k <;> simp at this
  unfold Tri.angleAt cornerAngle
  simp only [relabelTri_pts]
  rcases perm3 _ _ _ d1 d2 d3 with ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ |
    ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ <;>
  · rw [hx, hy, hz]
    first | rfl | (exact EuclideanGeometry.angle_comm _ _ _)

/-- the dissection with its target relabelled. -/
def relabelCD {N : ℕ} (D : CongruentDissection N) (τ : Equiv.Perm (Fin 3)) :
    CongruentDissection N where
  toDissection := relabelTarget D.toDissection τ
  model := D.model
  tiles_congruent := D.tiles_congruent

theorem cop_e_b {e f : ℤ} (h : IsCoprime e f) : IsCoprime e (f ^ 2 - e ^ 2) := by
  obtain ⟨u, v, huv⟩ := h.pow_right (n := 2)
  exact ⟨u + v * e, v, by linear_combination huv⟩

theorem cop_f_b {e f : ℤ} (h : IsCoprime e f) : IsCoprime f (f ^ 2 - e ^ 2) := by
  obtain ⟨u, v, huv⟩ := h.symm.pow_right (n := 2)
  exact ⟨u + v * f, -v, by linear_combination huv⟩

theorem cos_iso (c f2 Q w : ℝ) (hw : 0 < w) (hY : 0 < Q * w) (hX : 0 < f2 * w) (hf2 : 0 < f2)
    (h : c * (2 * (f2 * w)) * (Q * w) = (Q * w) ^ 2) : c = Q / (2 * f2) := by
  have e1 : (c * (2 * (f2 * w)) - Q * w) * (Q * w) = 0 := by linear_combination h
  have e2 : c * (2 * (f2 * w)) = Q * w := by
    rcases mul_eq_zero.mp e1 with h1 | h1
    · linarith
    · exact absurd h1 hY.ne'
  rw [eq_div_iff (by positivity)]
  apply mul_right_cancel₀ hw.ne'
  linear_combination e2

theorem theoremA_L2 {N : ℕ} (D : CongruentDissection N) (e f w : ℤ) (h0 : 0 < e) (hef : e < f)
    (hcop : IsCoprime e f)
    (hmodel : ∃ σ : Equiv.Perm (Fin 3),
      D.model.oppLen (σ 0) = (e : ℝ) * f ∧ D.model.oppLen (σ 1) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∧
      D.model.oppLen (σ 2) = (f : ℝ) ^ 2)
    (htgt : ∃ τ : Equiv.Perm (Fin 3),
      D.target.oppLen (τ 0) = (f : ℝ) ^ 2 * w ∧ D.target.oppLen (τ 1) = (f : ℝ) ^ 2 * w ∧
      D.target.oppLen (τ 2) = (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) * w) :
    (f ^ 2 - e ^ 2) ∣ w := by
  obtain ⟨σ, l0, l1, l2⟩ := hmodel
  obtain ⟨τ, m0, m1, m2⟩ := htgt
  obtain ⟨hcα, h3, hγ, hirr⟩ := tile_angles D.model σ e f h0 hef l0 l1 l2
  generalize hαg : D.model.angleAt (σ 0) = α at hcα h3 hγ hirr
  generalize hβg : D.model.angleAt (σ 1) = β at h3 hγ
  obtain ⟨D', hM, hO⟩ : ∃ D' : CongruentDissection N, D'.model = D.model ∧
      ∀ k, D'.target.oppLen k = D.target.oppLen (τ k) :=
    ⟨relabelCD D τ, rfl, fun k => relabel_opp _ _ _⟩
  have hαb : α ∈ Set.Icc 0 Real.pi := by
    rw [← hαg]; exact ⟨(ang_bounds _ _).1, (ang_bounds _ _).2⟩
  have hf : (0 : ℝ) < f := by exact_mod_cast lt_trans h0 hef
  have o0 : D'.target.oppLen 0 = (f : ℝ) ^ 2 * w := by
    rw [hO]; exact m0
  have o1 : D'.target.oppLen 1 = (f : ℝ) ^ 2 * w := by
    rw [hO]; exact m1
  have o2 : D'.target.oppLen 2 = (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) * w := by
    rw [hO]; exact m2
  have hX : 0 < (f : ℝ) ^ 2 * w := by rw [← o0]; exact opp_pos _ 0
  have hY : 0 < (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) * w := by rw [← o2]; exact opp_pos _ 2
  have hw : 0 < (w : ℝ) := by
    by_contra hneg
    push Not at hneg
    nlinarith [sq_nonneg (f : ℝ), pow_pos hf 2]
  obtain ⟨c0, c1, c2⟩ := cos_laws D'.target
  rw [o0, o1, o2] at c0 c1
  have hang : ∀ k : Fin 3, ∀ (hc : Real.cos (D'.target.angleAt k) = Real.cos α),
      D'.target.angleAt k = α := by
    intro k hc
    refine Real.injOn_cos ?_ ?_ hc
    · exact ⟨(ang_bounds _ k).1, (ang_bounds _ k).2⟩
    · exact hαb
  have hf2 : (0 : ℝ) < (f : ℝ) ^ 2 := by positivity
  have hT0 : D'.target.angleAt 0 = α := by
    apply hang
    rw [hcα]
    exact cos_iso _ _ _ _ hw hY hX hf2 (by linarith [c0])
  have hT1 : D'.target.angleAt 1 = α := by
    apply hang
    rw [hcα]
    exact cos_iso _ _ _ _ hw hY hX hf2 (by linarith [c1])
  have hm : ∃ σ : Equiv.Perm (Fin 3),
      D'.model.angleAt (σ 0) = α ∧ D'.model.oppLen (σ 0) = (e : ℝ) * f ∧
      D'.model.angleAt (σ 1) = β ∧ D'.model.oppLen (σ 1) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∧
      D'.model.angleAt (σ 2) = Real.pi - α - β ∧ D'.model.oppLen (σ 2) = (f : ℝ) ^ 2 := by
    rw [hM]; exact ⟨σ, hαg, l0, hβg, l1, hγ, l2⟩
  have ht : D'.target.angleAt 0 = α ∧ D'.target.angleAt 1 = α ∧
      D'.target.oppLen 0 = (f : ℝ) ^ 2 * w ∧ D'.target.oppLen 1 = (f : ℝ) ^ 2 * w ∧
      D'.target.oppLen 2 = (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) * w := ⟨hT0, hT1, o0, o1, o2⟩
  obtain ⟨X', Y', l, hX', hY', hBd⟩ := L2 D' e f α β hirr h3 hm _ _ ht
  have hXi : f ^ 2 * w = X' := by exact_mod_cast hX'
  have hYi : (2 * f ^ 2 - e ^ 2) * w = Y' := by exact_mod_cast hY'
  exact BAD.basealpha_div_of_poly e f w h0 hef (cop_e_b hcop) (cop_f_b hcop) l
    (by rw [Bdry_eq_Bd, hXi, hYi]; exact hBd)

end

end Erdos634.BADL2

#print axioms Erdos634.BADL2.theoremA_L2

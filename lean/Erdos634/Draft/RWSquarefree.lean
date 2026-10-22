-- Draft/RWSquarefree.lean — R-W with `Squarefree N` in place of `N.Prime` (room ALLN, Erdős F2).
-- Copy of RWStatementProof with the hypothesis replaced; new arithmetic core `w_arith_sqfree`.  UNAUDITED.
-- Route: relabel target → Row14.setup → N e² = S²(2f²−e²) → `w_arith` (k = 1) → sides of the target
-- (law of cosines) → scale by f²/c → SSS to `W₁(e,f)` → `rw_tiled`.
-- Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).
import Erdos634.Draft.RWAssemble
import Erdos634.Draft.RWArith
import Erdos634.Draft.ScaleBaseBetaFull

open scoped Classical
open Erdos634.Geometry Erdos634.TilePlacement Erdos634.BaseBetaTargetCoord Erdos634.Realizable
  Erdos634.Draft.TheoremPConditional Erdos634.Draft.RWPieces Erdos634.Draft.RWAssemble Erdos634.CertCoord

namespace Erdos634.Draft.RWSquarefree

/-- **Law of cosines at a tile corner, in `oppLen` form.** -/
theorem cos_angleAt_mul (T : Tri) (k : Fin 3) :
    2 * T.oppLen (k + 1) * T.oppLen (k + 2) * Real.cos (T.angleAt k)
      = T.oppLen (k + 1) ^ 2 + T.oppLen (k + 2) ^ 2 - T.oppLen k ^ 2 := by
  have h := EuclideanGeometry.law_cos (T.pts (k + 1)) (T.pts k) (T.pts (k + 2))
  have e1 : dist (T.pts (k + 1)) (T.pts k) = T.oppLen (k + 2) := by
    unfold Tri.oppLen
    rw [show k + 2 + 1 = k by
      have : ∀ x : Fin 3, x + 2 + 1 = x := by decide
      exact this k, show k + 2 + 2 = k + 1 by
      have : ∀ x : Fin 3, x + 2 + 2 = x + 1 := by decide
      exact this k, dist_comm]
  have e2 : dist (T.pts (k + 2)) (T.pts k) = T.oppLen (k + 1) := by
    unfold Tri.oppLen
    rw [show k + 1 + 1 = k + 2 by
      have : ∀ x : Fin 3, x + 1 + 1 = x + 2 := by decide
      exact this k, show k + 1 + 2 = k by
      have : ∀ x : Fin 3, x + 1 + 2 = x := by decide
      exact this k]
  have e3 : dist (T.pts (k + 1)) (T.pts (k + 2)) = T.oppLen k := rfl
  unfold Tri.angleAt cornerAngle
  rw [e1, e2, e3] at h
  nlinarith [h]

/-- Symmetric form: adjacent sides in either order. -/
theorem cos_angleAt_sym (T : Tri) (k : Fin 3) (i j : Fin 3)
    (hij : (i = k + 1 ∧ j = k + 2) ∨ (i = k + 2 ∧ j = k + 1)) :
    2 * T.oppLen i * T.oppLen j * Real.cos (T.angleAt k)
      = T.oppLen i ^ 2 + T.oppLen j ^ 2 - T.oppLen k ^ 2 := by
  rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact cos_angleAt_mul T k
  · have := cos_angleAt_mul T k
    nlinarith [this]

theorem perm_adj (σ : Equiv.Perm (Fin 3)) :
    (σ 1 = σ 0 + 1 ∧ σ 2 = σ 0 + 2) ∨ (σ 1 = σ 0 + 2 ∧ σ 2 = σ 0 + 1) := by
  revert σ; decide


theorem w_arith_sqfree {N : ℕ} {e f S : ℤ} (hN : Squarefree N) (hN0' : 0 < N)
    (he : 0 < e) (hef : e < f) (hcop : IsCoprime e f) (hS : 0 < S)
    (hEq : (N : ℤ) * e ^ 2 = S ^ 2 * (2 * f ^ 2 - e ^ 2)) :
    (N : ℤ) = 2 * f ^ 2 - e ^ 2 ∧ S = e := by
  have hNsq : Squarefree (N : ℤ) := Int.squarefree_natCast.mpr hN
  have hN0 : (0 : ℤ) < N := by exact_mod_cast hN0'
  have hgcd : 0 < Int.gcd S e := Int.gcd_pos_of_ne_zero_left _ hS.ne'
  obtain ⟨d, S', e', hd, hg1, hS', he'⟩ := Int.exists_gcd_one' hgcd
  have hdZ : (0 : ℤ) < d := by exact_mod_cast hd
  have hS'pos : 0 < S' := by
    by_contra h; push Not at h; nlinarith
  have he'pos : 0 < e' := by
    by_contra h; push Not at h; nlinarith
  set g : ℤ := 2 * f ^ 2 - e ^ 2 with hg
  have h1 : (N : ℤ) * e' ^ 2 = S' ^ 2 * g := by
    have : (d : ℤ) ^ 2 * ((N : ℤ) * e' ^ 2) = (d : ℤ) ^ 2 * (S' ^ 2 * g) := by
      have := hEq; rw [hS', he'] at this
      linear_combination this
    exact mul_left_cancel₀ (pow_pos hdZ 2).ne' this
  have hcop' : IsCoprime S' e' := Int.isCoprime_iff_gcd_eq_one.mpr hg1
  have hdvd : S' ^ 2 ∣ (N : ℤ) * e' ^ 2 := ⟨g, h1⟩
  have hdvd2 : S' ^ 2 ∣ (N : ℤ) := (hcop'.pow.dvd_of_dvd_mul_right hdvd)
  have hunit : IsUnit S' := hNsq S' (by rw [← sq]; exact hdvd2)
  have hS1 : S' = 1 := by
    rcases Int.isUnit_iff.mp hunit with h | h
    · exact h
    · omega
  subst hS1
  have hgd : g = N * e' ^ 2 := by rw [h1]; ring
  have hcope : IsCoprime e' f := hcop.of_isCoprime_of_dvd_left ⟨d, by rw [he']⟩
  have h2f : 2 * f ^ 2 = ((N : ℤ) + (d : ℤ) ^ 2) * e' ^ 2 := by
    have : 2 * f ^ 2 = g + e ^ 2 := by rw [hg]; ring
    rw [this, hgd, he']; ring
  have hdiv : e' ^ 2 ∣ 2 * f ^ 2 := ⟨(N : ℤ) + (d : ℤ) ^ 2, by rw [h2f]; ring⟩
  have hdiv2 : e' ^ 2 ∣ 2 := hcope.pow.dvd_of_dvd_mul_right hdiv
  have he1 : e' = 1 := by
    have : e' ^ 2 ≤ 2 := Int.le_of_dvd (by norm_num) hdiv2
    nlinarith
  subst he1
  refine ⟨?_, ?_⟩
  · rw [hg] at hgd; linarith
  · rw [hS', he']

def RWStatementSqfree : Prop :=
  ∀ (N : ℕ) (D : CongruentDissection N), Squarefree N →
    ∀ (α β a b c : ℝ) (r : ℚ), IrrPi α → 3 * α + 2 * β = Real.pi →
      D.model.ThreeAlphaData α β a b c → a = (r : ℝ) * c → b = (1 - (r : ℝ) ^ 2) * c →
      TgtAngles D (2 * α) β (α + β) → BaseBetaTiled

set_option maxHeartbeats 4000000 in
theorem rwStatement_sqfree : RWStatementSqfree := by
  intro N D hN α β a b c r hα hrel hmod har hbr htgt
  -- Step 0: relabel the target so its angles are (2α, β, α+β) at vertices 0, 1, 2
  obtain ⟨σ_t, ht0, ht1, ht2⟩ := htgt
  set D' := D.relabelTarget' σ_t
  have hD'_tgt_pts : ∀ k, D'.target.pts k = D.target.pts (σ_t k) := fun _ => rfl
  have hP0 : D'.target.angleAt 0 = 2 * α :=
    (Row14AnyLabel.angleAt_of_pts σ_t hD'_tgt_pts 0).trans ht0
  have hP1 : D'.target.angleAt 1 = β :=
    (Row14AnyLabel.angleAt_of_pts σ_t hD'_tgt_pts 1).trans ht1
  have hP2 : D'.target.angleAt 2 = α + β :=
    (Row14AnyLabel.angleAt_of_pts σ_t hD'_tgt_pts 2).trans ht2
  -- Step 1: Row 14
  obtain ⟨s, S, hs0, hs1, hc, ha_sc, hb_sc, hO1, hSc, hquad⟩ :=
    Row14.setup D' hα hrel hmod hP0 hP1 hP2
  have hsr : s = (r : ℝ) := mul_right_cancel₀ hc.ne' (by rw [← ha_sc, ← har])
  set p_i := r.num
  set q_i : ℤ := (r.den : ℤ)
  have hq_pos : (0 : ℤ) < q_i := by show (0 : ℤ) < (r.den : ℤ); exact_mod_cast r.pos
  have hcop_pq : IsCoprime p_i q_i := by
    rw [Int.isCoprime_iff_gcd_eq_one]; exact_mod_cast r.reduced
  have hq_r : (q_i : ℝ) ≠ 0 := by exact_mod_cast hq_pos.ne'
  have hr_pq : (r : ℝ) = (p_i : ℝ) / (q_i : ℝ) := by
    have h1 : (r : ℝ) = (r.num : ℝ) / (r.den : ℝ) := Rat.cast_def r
    simpa [p_i, q_i, Int.cast_natCast] using h1
  have hqR : (0 : ℝ) < (q_i : ℝ) := by exact_mod_cast hq_pos
  have hp_pos : (0 : ℤ) < p_i := by
    have hpR : (0 : ℝ) < (p_i : ℝ) := by
      have := hs0; rw [hsr, hr_pq] at this
      rcases div_pos_iff.mp this with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact h1
      · linarith
    exact_mod_cast hpR
  have hp_lt_q : p_i < q_i := by
    have := hs1; rw [hsr, hr_pq] at this
    exact_mod_cast (div_lt_one hqR).mp this
  -- Step 2: the integer equation
  have hEq : (N : ℤ) * p_i ^ 2 = S ^ 2 * (2 * q_i ^ 2 - p_i ^ 2) := by
    have hq2 : (q_i : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hq_r
    have h1 := hquad; rw [hsr, hr_pq] at h1
    have h2 : (N : ℝ) * (p_i : ℝ) ^ 2 = (S : ℝ) ^ 2 * (2 * (q_i : ℝ) ^ 2 - (p_i : ℝ) ^ 2) := by
      field_simp at h1; linarith
    exact_mod_cast h2
  -- Step 3: S > 0
  have hO2pos : 0 < D'.target.oppLen 2 := Row3.RP.oppLen_pos D'.target 2
  have hSpos : 0 < S := by
    have : (0 : ℝ) < (S : ℝ) * c := by rw [hSc]; exact mul_pos hs0 hO2pos
    have : (0 : ℝ) < (S : ℝ) := by
      by_contra hle; push Not at hle; nlinarith
    exact_mod_cast this
  -- Step 4: k = 1
  obtain ⟨hNeq, hSeq⟩ := w_arith_sqfree hN (by have := D.pos; omega) hp_pos hp_lt_q hcop_pq hSpos hEq
  have hSR : (S : ℝ) = (p_i : ℝ) := by exact_mod_cast hSeq
  have hpR : (0 : ℝ) < (p_i : ℝ) := by exact_mod_cast hp_pos
  -- Step 5: the target's sides
  have hO2 : D'.target.oppLen 2 = (q_i : ℝ) * c := by
    have h1 := hSc; rw [hSR, hsr, hr_pq] at h1
    field_simp at h1
    linarith
  have hO1 : D'.target.oppLen 1 = ((q_i : ℝ) ^ 2 - (p_i : ℝ) ^ 2) * c / q_i := by
    rw [hO1, hO2, hsr, hr_pq]; field_simp
  -- cos α from the model
  obtain ⟨σm, hα0m, ham, hβ1m, hbm, hγ2m, hcm⟩ := hmod
  have hcosA : 2 * b * c * Real.cos α = b ^ 2 + c ^ 2 - a ^ 2 := by
    have := cos_angleAt_sym D.model (σm 0) (σm 1) (σm 2) (perm_adj σm)
    rw [hα0m, ham, hbm, hcm] at this
    exact this
  have hcosα : Real.cos α = (2 * (q_i : ℝ) ^ 2 - (p_i : ℝ) ^ 2) / (2 * (q_i : ℝ) ^ 2) := by
    have hb' : b = (1 - s ^ 2) * c := hb_sc
    have ha' : a = s * c := ha_sc
    have hs' : s = (p_i : ℝ) / q_i := by rw [hsr, hr_pq]
    have h1 : (1 - s ^ 2) ≠ 0 := by nlinarith
    rw [hb', ha'] at hcosA
    have h2 : c ^ 2 * (1 - s ^ 2) * (2 * Real.cos α - (2 - s ^ 2)) = 0 := by nlinarith [hcosA]
    have h3 : Real.cos α = (2 - s ^ 2) / 2 := by
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd h (mul_ne_zero (pow_ne_zero 2 hc.ne') h1)
      · linarith
    rw [h3, hs']; field_simp
  -- O0 by the law of cosines at target vertex 0
  have hO0 : D'.target.oppLen 0 = (p_i : ℝ) * (2 * (q_i : ℝ) ^ 2 - (p_i : ℝ) ^ 2) * c / (q_i : ℝ) ^ 2 := by
    have hcl := cos_angleAt_mul D'.target 0
    rw [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl, hP0,
      Real.cos_two_mul, hcosα, hO1, hO2] at hcl
    have hO0pos : 0 < D'.target.oppLen 0 := Row3.RP.oppLen_pos D'.target 0
    have hsq : D'.target.oppLen 0 ^ 2
        = ((p_i : ℝ) * (2 * (q_i : ℝ) ^ 2 - (p_i : ℝ) ^ 2) * c / (q_i : ℝ) ^ 2) ^ 2 := by
      field_simp at hcl ⊢
      nlinarith [hcl]
    have hrhs : 0 ≤ (p_i : ℝ) * (2 * (q_i : ℝ) ^ 2 - (p_i : ℝ) ^ 2) * c / (q_i : ℝ) ^ 2 := by
      have : (0 : ℝ) < 2 * (q_i : ℝ) ^ 2 - (p_i : ℝ) ^ 2 := by
        have : (p_i : ℝ) < q_i := by exact_mod_cast hp_lt_q
        nlinarith
      positivity
    exact RWPieces.eq_of_sq_eq hO0pos.le hrhs hsq
  -- Step 6: natural-number parameters
  set e_n : ℕ := p_i.natAbs
  set f_n : ℕ := q_i.natAbs
  have he_pos : 0 < e_n := Int.natAbs_pos.mpr (Int.ne_of_gt hp_pos)
  have he_int : (e_n : ℤ) = p_i := Int.natAbs_of_nonneg hp_pos.le
  have hf_int : (f_n : ℤ) = q_i := Int.natAbs_of_nonneg hq_pos.le
  have hef_lt : e_n < f_n := by
    have : (e_n : ℤ) < (f_n : ℤ) := by rw [he_int, hf_int]; exact hp_lt_q
    exact_mod_cast this
  have hcop_nat : Nat.Coprime e_n f_n := by
    show Nat.Coprime p_i.natAbs q_i.natAbs
    rw [Nat.Coprime]; exact_mod_cast r.reduced
  have he_cast : (e_n : ℝ) = (p_i : ℝ) := by exact_mod_cast he_int
  have hf_cast : (f_n : ℝ) = (q_i : ℝ) := by exact_mod_cast hf_int
  -- Step 7: scale by f²/c and relabel the model
  set scale_r := (f_n : ℝ) ^ 2 / c with hscale
  have hscale_pos : 0 < scale_r := div_pos (by positivity) hc
  let D_sc := scaleDissection (D'.model.pts 0) scale_r hscale_pos.ne' D'
  let D'' := D_sc.relabelModel σm
  have hoppLen : ∀ k : Fin 3, D''.model.oppLen k = scale_r * D'.model.oppLen (σm k) := fun k => by
    have heq : D''.model.oppLen k = D_sc.model.oppLen (σm k) :=
      Row14AnyLabel.oppLen_of_pts σm (fun _ => rfl) k
    rw [heq]
    unfold Tri.oppLen
    rw [scaleDissection_model_pts, scaleDissection_model_pts, homothetyEquiv_dist,
      abs_of_nonneg (le_of_lt hscale_pos)]
  have hso : ∀ (T : Tri) (k : Fin 3), sideOpp T k = T.oppLen k := fun _ _ => rfl
  have hm0 : sideOpp D''.model 0 = (e_n : ℝ) * f_n := by
    rw [hso, hoppLen 0]
    show scale_r * D.model.oppLen (σm 0) = _
    rw [ham, ha_sc, hscale, hsr, hr_pq, hf_cast, he_cast]; field_simp
  have hm1 : sideOpp D''.model 1 = (f_n : ℝ) ^ 2 - (e_n : ℝ) ^ 2 := by
    rw [hso, hoppLen 1]
    show scale_r * D.model.oppLen (σm 1) = _
    rw [hbm, hb_sc, hscale, hsr, hr_pq, hf_cast, he_cast]; field_simp
  have hm2 : sideOpp D''.model 2 = (f_n : ℝ) ^ 2 := by
    rw [hso, hoppLen 2]
    show scale_r * D.model.oppLen (σm 2) = _
    rw [hcm, hscale, hf_cast]; field_simp
  -- Step 8: target congruent to the west piece W₁
  have hhe : (0 : ℝ) < (e_n : ℝ) := by exact_mod_cast he_pos
  have hhef : (e_n : ℝ) < (f_n : ℝ) := by exact_mod_cast hef_lt
  have hD''_tpts : ∀ k, D''.target.pts k =
      homothetyEquiv (D'.model.pts 0) scale_r hscale_pos.ne' (D'.target.pts k) := fun _ => rfl
  have hd01 : dist (D''.target.pts 0) (D''.target.pts 1) = (f_n : ℝ) ^ 3 := by
    rw [hD''_tpts 0, hD''_tpts 1, homothetyEquiv_dist, abs_of_pos hscale_pos,
      show dist (D'.target.pts 0) (D'.target.pts 1) = D'.target.oppLen 2 from rfl, hO2, hscale,
      hf_cast]
    field_simp
  have hd12 : dist (D''.target.pts 1) (D''.target.pts 2)
      = (e_n : ℝ) * (2 * (f_n : ℝ) ^ 2 - (e_n : ℝ) ^ 2) := by
    rw [hD''_tpts 1, hD''_tpts 2, homothetyEquiv_dist, abs_of_pos hscale_pos,
      show dist (D'.target.pts 1) (D'.target.pts 2) = D'.target.oppLen 0 from rfl, hO0, hscale,
      hf_cast, he_cast]
    field_simp
  have hd20 : dist (D''.target.pts 2) (D''.target.pts 0)
      = (f_n : ℝ) * ((f_n : ℝ) ^ 2 - (e_n : ℝ) ^ 2) := by
    rw [hD''_tpts 2, hD''_tpts 0, homothetyEquiv_dist, abs_of_pos hscale_pos,
      show dist (D'.target.pts 2) (D'.target.pts 0) = D'.target.oppLen 1 from rfl, hO1, hscale,
      hf_cast, he_cast]
    field_simp
  have hcong : D''.target.Congruent (wTri (e := (e_n : ℝ)) (f := (f_n : ℝ)) hhe hhef) := by
    refine SssCongruent.congruent_of_dist_three ?_ ?_ ?_
    · rw [hd01]
      show (f_n : ℝ) ^ 3 = dist (mkPt (baseLen (e_n : ℝ) f_n / 2) (height (e_n : ℝ) f_n)) (mkPt 0 0)
      rw [d_AW hhe hhef]
    · rw [hd12]
      show (e_n : ℝ) * (2 * (f_n : ℝ) ^ 2 - (e_n : ℝ) ^ 2)
        = dist (mkPt 0 0) (mkPt (xP (e_n : ℝ) f_n) 0)
      rw [d_WP hhe hhef]
    · rw [hd20]
      show (f_n : ℝ) * ((f_n : ℝ) ^ 2 - (e_n : ℝ) ^ 2)
        = dist (mkPt (xP (e_n : ℝ) f_n) 0) (mkPt (baseLen (e_n : ℝ) f_n / 2) (height (e_n : ℝ) f_n))
      rw [dist_comm, d_AP hhe hhef]
  obtain ⟨N', D3, h3c, h30, h31, h32⟩ := rw_tiled e_n f_n he_pos hef_lt D'' hcong hm0 hm1 hm2
  exact ⟨e_n, f_n, he_pos, hef_lt, hcop_nat, N', D3, h3c, h30, h31, h32⟩

end Erdos634.Draft.RWSquarefree

#print axioms Erdos634.Draft.RWSquarefree.rwStatement_sqfree

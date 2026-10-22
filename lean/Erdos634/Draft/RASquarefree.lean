-- Draft/RASquarefree.lean — R-A with `Squarefree N` in place of `N.Prime` (room ALLN, Erdős F1):
-- the only primality use in RAStatementProof is `ra_arith`.  Generalised here.  UNAUDITED.
-- (copy of RAStatementProof with the hypothesis replaced)
-- Route: relabel target → Row13.setup → N(q+p) = K²(q−p) → `ra_arith` (f²−e² = Nσ²) → target sides →
-- scale by f²/c → ladder at ratio σ gives the atom → West ⊔ A₁ ⊔ East → `ra_tiled`.
-- Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).
import Erdos634.Draft.RAAssemble
import Erdos634.Draft.RAArith
import Erdos634.Draft.RASetup
import Erdos634.Draft.ScaleBaseBetaFull

open scoped Classical
open Erdos634.Geometry Erdos634.TilePlacement Erdos634.BaseBetaTargetCoord Erdos634.Realizable
  Erdos634.Draft.TheoremPConditional Erdos634.Draft.RAAssemble Erdos634.CertCoord

namespace Erdos634.Draft.RASquarefree


/-- Squarefree version of `RAArith.ra_arith`: `N (f+e) = K² (f−e)`, `N` squarefree. -/
theorem ra_arith_sqfree {N : ℕ} {e f K : ℤ} (hN : Squarefree N) (hN0' : 0 < N) (he : 0 < e) (hef : e < f)
    (hK : 0 < K) (hEq : (N : ℤ) * (f + e) = K ^ 2 * (f - e)) :
    ∃ σ : ℤ, 0 < σ ∧ f ^ 2 - e ^ 2 = N * σ ^ 2 ∧ (f - e) * K = N * σ := by
  have hNsq : Squarefree (N : ℤ) := Int.squarefree_natCast.mpr hN
  have hN0 : (0 : ℤ) < N := by exact_mod_cast hN0'
  have hk2 : ((f - e) * K) ^ 2 = N * (f ^ 2 - e ^ 2) := by
    have : ((f - e) * K) ^ 2 = (f - e) * (K ^ 2 * (f - e)) := by ring
    rw [this, ← hEq]; ring
  have hdvd : (N : ℤ) ∣ ((f - e) * K) ^ 2 := ⟨f ^ 2 - e ^ 2, hk2⟩
  obtain ⟨σ, hσ⟩ := (hNsq.dvd_pow_iff_dvd (by norm_num : 2 ≠ 0)).mp hdvd
  have hkpos : 0 < (f - e) * K := mul_pos (by linarith) hK
  have hσpos : 0 < σ := by
    by_contra hle; push Not at hle; nlinarith
  refine ⟨σ, hσpos, ?_, hσ⟩
  have : (N : ℤ) * ((N : ℤ) * σ ^ 2) = N * (f ^ 2 - e ^ 2) := by
    rw [← hk2, hσ]; ring
  exact (mul_left_cancel₀ hN0.ne' this).symm

def RAStatementSqfree : Prop :=
  ∀ (N : ℕ) (D : CongruentDissection N), Squarefree N →
    ∀ (α β a b c : ℝ) (r : ℚ), IrrPi α → 3 * α + 2 * β = Real.pi →
      D.model.ThreeAlphaData α β a b c → a = (r : ℝ) * c → b = (1 - (r : ℝ) ^ 2) * c →
      TgtAngles D (α + β) (α + β) α → BaseBetaTiled

set_option maxHeartbeats 4000000 in
theorem raStatement_sqfree : RAStatementSqfree := by
  intro N D hN α β a b c r hα hrel hmod har hbr htgt
  -- Step 0: relabel the target so its angles are (α+β, α+β, α) at vertices 0, 1, 2
  obtain ⟨σ_t, ht0, ht1, ht2⟩ := htgt
  set D' := D.relabelTarget' σ_t
  have hD'_tgt_pts : ∀ k, D'.target.pts k = D.target.pts (σ_t k) := fun _ => rfl
  have hP0 : D'.target.angleAt 0 = α + β :=
    (Row14AnyLabel.angleAt_of_pts σ_t hD'_tgt_pts 0).trans ht0
  have hP1 : D'.target.angleAt 1 = α + β :=
    (Row14AnyLabel.angleAt_of_pts σ_t hD'_tgt_pts 1).trans ht1
  -- Step 1: Row 13 with area
  obtain ⟨s, K, hs0, hs1, hc, ha_sc, hb_sc, hO1, hO2, hKc, hNK⟩ :=
    Row13.setup D' hα hrel hmod hP0 hP1
  have hsr : s = (r : ℝ) := mul_right_cancel₀ hc.ne' (by rw [← ha_sc, ← har])
  set p_i := r.num
  set q_i : ℤ := (r.den : ℤ)
  have hq_pos : (0 : ℤ) < q_i := by show (0 : ℤ) < (r.den : ℤ); exact_mod_cast r.pos
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
  have hpR : (0 : ℝ) < (p_i : ℝ) := by exact_mod_cast hp_pos
  -- Step 2: K > 0, and the integer equation
  have hX0pos : 0 < D'.target.oppLen 0 := Row3.RP.oppLen_pos D'.target 0
  have hKpos : 0 < K := by
    have h1 : (0 : ℝ) < (K : ℝ) * c * (1 - s) := by rw [hKc]; exact hX0pos
    have h2 : (0 : ℝ) < (K : ℝ) := by
      by_contra hle; push Not at hle
      have := mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hle hc.le)
        (by linarith : (0 : ℝ) ≤ 1 - s)
      linarith
    exact_mod_cast h2
  have hEq : (N : ℤ) * (q_i + p_i) = K ^ 2 * (q_i - p_i) := by
    have h1 := hNK; rw [hsr, hr_pq] at h1
    have h2 : (N : ℝ) * ((q_i : ℝ) + p_i) = (K : ℝ) ^ 2 * ((q_i : ℝ) - p_i) := by
      field_simp at h1; linarith
    exact_mod_cast h2
  -- Step 3: k = Nσ
  obtain ⟨σz, hσpos, hσb, hσk⟩ := ra_arith_sqfree hN (by have := D.pos; omega) hp_pos hp_lt_q hKpos hEq
  set σn : ℕ := σz.toNat
  have hσn : (σn : ℤ) = σz := Int.toNat_of_nonneg hσpos.le
  have hσn_pos : 0 < σn := by omega
  have hσR : (σn : ℝ) = (σz : ℝ) := by exact_mod_cast hσn
  have hσb_R : (q_i : ℝ) ^ 2 - (p_i : ℝ) ^ 2 = (N : ℝ) * (σz : ℝ) ^ 2 := by exact_mod_cast hσb
  have hσk_R : ((q_i : ℝ) - p_i) * (K : ℝ) = (N : ℝ) * (σz : ℝ) := by exact_mod_cast hσk
  -- Step 4: the target's sides
  have hO0 : D'.target.oppLen 0 = (N : ℝ) * (σz : ℝ) * c / (q_i : ℝ) := by
    rw [← hKc, hsr, hr_pq]
    have : (K : ℝ) * c * (1 - (p_i : ℝ) / q_i) = ((q_i : ℝ) - p_i) * (K : ℝ) * c / q_i := by
      field_simp
    rw [this, hσk_R]
  have hO1' : D'.target.oppLen 1 = (N : ℝ) * (σz : ℝ) * c / (q_i : ℝ) := by rw [hO1, hO0]
  have hO2' : D'.target.oppLen 2 = (p_i : ℝ) * (N : ℝ) * (σz : ℝ) * c / (q_i : ℝ) ^ 2 := by
    rw [hO2, hO0, hsr, hr_pq]; field_simp
  -- Step 5: natural-number parameters
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
  -- Step 6: scale by f²/c, relabel the model
  obtain ⟨σm, hα0m, ham, hβ1m, hbm, hγ2m, hcm⟩ := hmod
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
  -- Step 7: rotate the target so the apex is vertex 0, then the ladder distances
  let D3 := D''.relabelTarget' (finRotate 3).symm
  have hD''_tpts : ∀ k, D''.target.pts k =
      homothetyEquiv (D'.model.pts 0) scale_r hscale_pos.ne' (D'.target.pts k) := fun _ => rfl
  have hD3p0 : D3.target.pts 0 = D''.target.pts 2 := rfl
  have hD3p1 : D3.target.pts 1 = D''.target.pts 0 := rfl
  have hD3p2 : D3.target.pts 2 = D''.target.pts 1 := rfl
  have hdist : ∀ i j : Fin 3, dist (D''.target.pts i) (D''.target.pts j) = scale_r * dist (D'.target.pts i) (D'.target.pts j) := by
    intro i j
    rw [hD''_tpts i, hD''_tpts j, homothetyEquiv_dist, abs_of_pos hscale_pos]
  have hσf : (σn : ℝ) * dist (D3.target.pts 0) (D3.target.pts 1)
      = (f_n : ℝ) * ((f_n : ℝ) ^ 2 - (e_n : ℝ) ^ 2) := by
    rw [hD3p0, hD3p1, hdist, show dist (D'.target.pts 2) (D'.target.pts 0) = D'.target.oppLen 1 from rfl,
      hO1', hscale, hσR, hf_cast, he_cast, hσb_R]
    field_simp
  have hσe : (σn : ℝ) * dist (D3.target.pts 1) (D3.target.pts 2)
      = (e_n : ℝ) * ((f_n : ℝ) ^ 2 - (e_n : ℝ) ^ 2) := by
    rw [hD3p1, hD3p2, hdist, show dist (D'.target.pts 0) (D'.target.pts 1) = D'.target.oppLen 2 from rfl,
      hO2', hscale, hσR, hf_cast, he_cast, hσb_R]
    field_simp
  have hσf' : (σn : ℝ) * dist (D3.target.pts 2) (D3.target.pts 0)
      = (f_n : ℝ) * ((f_n : ℝ) ^ 2 - (e_n : ℝ) ^ 2) := by
    rw [hD3p2, hD3p0, hdist, show dist (D'.target.pts 1) (D'.target.pts 2) = D'.target.oppLen 0 from rfl,
      hO0, hscale, hσR, hf_cast, he_cast, hσb_R]
    field_simp
  obtain ⟨N', D4, h4c, h40, h41, h42⟩ := ra_tiled e_n f_n σn he_pos hef_lt hσn_pos D3 hσf hσe hσf'
    hm0 hm1 hm2
  exact ⟨e_n, f_n, he_pos, hef_lt, hcop_nat, N', D4, h4c, h40, h41, h42⟩

end Erdos634.Draft.RASquarefree

#print axioms Erdos634.Draft.RASquarefree.raStatement_sqfree

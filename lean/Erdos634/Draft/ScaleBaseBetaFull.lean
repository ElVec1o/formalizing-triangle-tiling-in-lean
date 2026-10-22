-- Draft/ScaleBaseBetaFull.lean
-- Proves `scaleBaseBeta : ScaleBaseBetaStatement`.
--
-- Route: relabel target → Row12.setup → N*(p+q)²=M²*(3q²-p²) → IsCoprime, split_of_raw,
-- parity (v=1) → scale by f²/c, relabel model → SSS → BaseBetaTiled.
--
-- Axioms (2026-09-30): standard three only; `#print axioms scaleBaseBeta` is clean. Older note said sorryAx; this file adds
-- no new sorry beyond those already present in imports.
import Erdos634.Draft.FluxDRow12b
import Erdos634.Draft.TheoremPConditional
import Erdos634.Draft.FluxFRow14AnyLabel
import Erdos634.FCStep2
import Erdos634.Realizable
import Erdos634.SssCongruent
import Erdos634.BaseBetaTargetCoord
import Erdos634.Congruence
import Erdos634.Draft.FluxCRow12

open scoped Classical

namespace Erdos634.Draft.ScaleBaseBetaFull

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.BaseBetaTargetCoord
open Erdos634.Realizable Erdos634.Draft.TheoremPConditional

/-! ### Arithmetic lemmas -/

private lemma isCoprime_sum_left {p q : ℤ} (hcop : IsCoprime p q) : IsCoprime (p + q) p := by
  obtain ⟨u, v, huv⟩ := hcop; exact ⟨v, u - v, by linarith⟩

private lemma isCoprime_sum_sq {p q : ℤ} (hcop : IsCoprime p q) (hodd : ¬ (2 : ℤ) ∣ p + q) :
    IsCoprime (p + q) (3 * q ^ 2 - p ^ 2) := by
  have hcp : IsCoprime (p + q) p := isCoprime_sum_left hcop
  have hcp2 : IsCoprime (p + q) 2 := by
    obtain ⟨k, hk⟩ : ∃ k : ℤ, p + q = 2 * k + 1 := ⟨(p + q - 1) / 2, by omega⟩
    exact ⟨1, -k, by rw [hk]; ring⟩
  have hcp2p2 : IsCoprime (p + q) (2 * p ^ 2) := hcp2.mul_right hcp.pow_right
  rw [show 3 * q ^ 2 - p ^ 2 = 2 * p ^ 2 + (p + q) * (3 * (q - p)) by ring]
  exact hcp2p2.add_mul_left_right _

private lemma sq_inj_pos' {x y : ℤ} (hx : 0 < x) (hy : 0 < y) (h : x ^ 2 = y ^ 2) : x = y :=
  le_antisymm (by nlinarith) (by nlinarith)

private lemma sum_odd_of_quadratic {N : ℕ} {p q M : ℤ}
    (hN4 : N % 4 = 3) (hq : 0 < q) (hp : 0 < p)
    (hcop : IsCoprime p q) (hM2 : (2 : ℤ) ∣ M - N)
    (hquad : (N : ℤ) * (p + q) ^ 2 = M ^ 2 * (3 * q ^ 2 - p ^ 2)) :
    ¬ (2 : ℤ) ∣ p + q := by
  have hNodd : ¬ (2 : ℤ) ∣ (N : ℤ) := by
    intro hdvd
    have : (2 : ℕ) ∣ N := by exact_mod_cast hdvd
    have hmod2 : N % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp this
    omega
  have hModd : ¬ (2 : ℤ) ∣ M := by
    intro hM
    apply hNodd
    have h1 : (2 : ℤ) ∣ M := hM
    have h2 : (2 : ℤ) ∣ M - (N : ℤ) := hM2
    exact ⟨M / 2 - (M - (N : ℤ)) / 2, by
      obtain ⟨a, ha⟩ := h1; obtain ⟨b, hb⟩ := h2; omega⟩
  intro hpq
  obtain ⟨k, hk⟩ := hpq
  have hp_odd : ¬ (2 : ℤ) ∣ p := by
    intro hp2
    have hq2 : (2 : ℤ) ∣ q := by
      obtain ⟨a, ha⟩ := hp2; exact ⟨k - a, by omega⟩
    obtain ⟨u, v, huv⟩ := hcop
    have : (2 : ℤ) ∣ 1 := by
      obtain ⟨a, ha⟩ := hp2; obtain ⟨b, hb⟩ := hq2
      exact ⟨u * a + v * b, by rw [ha, hb] at huv; nlinarith⟩
    norm_num at this
  obtain ⟨a, ha⟩ : ∃ a : ℤ, p = 2 * a + 1 := ⟨(p - 1) / 2, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b : ℤ, q = 2 * b + 1 := by
    refine ⟨(q - 1) / 2, ?_⟩
    have : ¬ (2 : ℤ) ∣ q := by
      intro hq2
      exact hp_odd (by obtain ⟨c, hc⟩ := hq2; exact ⟨k - c, by omega⟩)
    omega
  obtain ⟨m, hm⟩ : ∃ m : ℤ, M = 2 * m + 1 := ⟨(M - 1) / 2, by omega⟩
  have hLHS : (4 : ℤ) ∣ (N : ℤ) * (p + q) ^ 2 := ⟨(N : ℤ) * k ^ 2, by rw [hk]; ring⟩
  obtain ⟨l, hl⟩ : ∃ l : ℤ, M ^ 2 * (3 * q ^ 2 - p ^ 2) = 4 * l + 2 := by
    rw [hm, ha, hb]
    exact ⟨2*(3*b^2+3*b-a^2-a)*(2*m^2+2*m) + (3*b^2+3*b-a^2-a) + (2*m^2+2*m), by ring⟩
  rw [hquad, hl] at hLHS; obtain ⟨d, hd⟩ := hLHS; omega

/-! ### Main theorem -/

theorem scaleBaseBeta : ScaleBaseBetaStatement := by
  intro N D hN h4 h3 α β a b c r hα hrel hmod har hbr htgt
  -- Step 0: relabel target so β at positions 0, 1
  obtain ⟨σ_t, ht0, ht1, _⟩ := htgt
  set D' := D.relabelTarget' σ_t
  have hD'_tgt_pts : ∀ k, D'.target.pts k = D.target.pts (σ_t k) := fun _ => rfl
  have hD'_tgt0 : D'.target.angleAt 0 = β :=
    (Row14AnyLabel.angleAt_of_pts σ_t hD'_tgt_pts 0).trans ht0
  have hD'_tgt1 : D'.target.angleAt 1 = β :=
    (Row14AnyLabel.angleAt_of_pts σ_t hD'_tgt_pts 1).trans ht1
  -- Step 1: Row12.setup (D'.model = D.model definitionally)
  obtain ⟨s, M, hs0, hs1, hc, ha_sc, hb_sc, hM2, _, hM0, _, hMleg, hYs, hquad⟩ :=
    Row12.setup D' hα hrel hmod hD'_tgt0 hD'_tgt1
  -- Step 2: s = r
  have hsr : s = (r : ℝ) := mul_right_cancel₀ hc.ne' (by rw [← ha_sc, ← har])
  -- p = r.num, q = r.den (as integers)
  set p_i := r.num
  set q_i : ℤ := (r.den : ℤ)
  have hq_pos : (0 : ℤ) < q_i := by
    show (0 : ℤ) < (r.den : ℤ); exact_mod_cast r.pos
  have hcop_pq : IsCoprime p_i q_i := by
    rw [Int.isCoprime_iff_gcd_eq_one]; exact_mod_cast r.reduced
  have hq_r : (q_i : ℝ) ≠ 0 := by exact_mod_cast hq_pos.ne'
  have hr_pq : (r : ℝ) = (p_i : ℝ) / (q_i : ℝ) := by
    have h1 : (r : ℝ) = (r.num : ℝ) / (r.den : ℝ) := Rat.cast_def r
    simpa [p_i, q_i, Int.cast_natCast] using h1
  have hp_pos : (0 : ℤ) < p_i := by
    have hpR : (0 : ℝ) < (p_i : ℝ) := by
      have := hs0; rw [hsr, hr_pq] at this
      have hqR : (0 : ℝ) < (q_i : ℝ) := by exact_mod_cast hq_pos
      rcases div_pos_iff.mp this with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact h1
      · linarith
    exact_mod_cast hpR
  have hp_lt_q : p_i < q_i := by
    have := hs1; rw [hsr, hr_pq] at this
    exact_mod_cast (div_lt_one (by exact_mod_cast hq_pos)).mp this
  -- Step 3: quadratic as integers
  have hquad_int : (N : ℤ) * (p_i + q_i) ^ 2 = M ^ 2 * (3 * q_i ^ 2 - p_i ^ 2) := by
    have hkey := hquad; rw [hsr, hr_pq] at hkey
    have hkey2 : (q_i : ℝ) ^ 2 * (((N : ℝ) + (M : ℝ) ^ 2) * ((p_i : ℝ) / q_i) ^ 2 +
        2 * N * ((p_i : ℝ) / q_i) + ((N : ℝ) - 3 * (M : ℝ) ^ 2)) = 0 := by
      rw [hkey]; ring
    have hkey3 : (N : ℝ) * (p_i + q_i) ^ 2 = (M : ℝ) ^ 2 * (3 * q_i ^ 2 - p_i ^ 2) := by
      have hq2 : (q_i : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hq_r
      field_simp at hkey2 ⊢
      nlinarith [hkey2, sq_nonneg (p_i : ℝ), sq_nonneg (q_i : ℝ)]
    exact_mod_cast hkey3
  -- Step 4: split_of_raw with A=1, B=3q²-p²
  have hB_pos : (0 : ℤ) < 3 * q_i ^ 2 - p_i ^ 2 := by nlinarith [sq_nonneg p_i, sq_nonneg q_i]
  rcases FCStep2.split_of_raw hN isCoprime_one_left one_pos hB_pos (Int.ne_of_gt hM0)
      (show (N : ℤ) * (p_i + q_i) ^ 2 = M ^ 2 * 1 * (3 * q_i ^ 2 - p_i ^ 2) by
        rw [mul_one]; exact hquad_int) with ⟨u, _, hu, _⟩ | ⟨_, v, _, hBN⟩
  · -- Case 1: 1 = N*u² → impossible since N ≥ 2
    exfalso
    have hN2 : (2 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN.two_le
    have hu2 := sq_nonneg u
    rcases eq_or_lt_of_le hu2 with h | h
    · have : u = 0 := by nlinarith [sq_nonneg u]
      simp [this] at hu
    · nlinarith
  · -- Case 2: 3q²-p² = N*v²
    have hpq_pos : (0 : ℤ) < p_i + q_i := by linarith [hp_pos, hq_pos]
    have hpq_sq : (p_i + q_i) ^ 2 = M ^ 2 * v ^ 2 := by
      have hN_ne0 : (N : ℤ) ≠ 0 := (show (0 : ℤ) < N from by exact_mod_cast hN.pos).ne'
      exact mul_left_cancel₀ hN_ne0 (by rw [hquad_int, hBN]; ring)
    -- parity argument
    have hpq_odd : ¬ (2 : ℤ) ∣ p_i + q_i :=
      sum_odd_of_quadratic h4 hq_pos hp_pos hcop_pq hM2 hquad_int
    -- IsCoprime(p+q, 3q²-p²)
    have hcop_pq_B : IsCoprime (p_i + q_i) (3 * q_i ^ 2 - p_i ^ 2) :=
      isCoprime_sum_sq hcop_pq hpq_odd
    -- IsCoprime(p+q, v²) from IsCoprime(p+q, 3q²-p²) and v² | 3q²-p²
    have hcop_pq_v2 : IsCoprime (p_i + q_i) (v ^ 2) :=
      hcop_pq_B.of_isCoprime_of_dvd_right ⟨(N : ℤ), by rw [hBN]; ring⟩
    -- v² | (p+q): by Bezout / hpq_sq
    have hv2_dvd_pq : (v ^ 2) ∣ (p_i + q_i) := by
      obtain ⟨u, w, huw⟩ := hcop_pq_v2
      refine ⟨u * M ^ 2 + w * (p_i + q_i), ?_⟩
      have step : v ^ 2 * (u * M ^ 2 + w * (p_i + q_i))
          = (p_i + q_i) * (u * (p_i + q_i) + w * v ^ 2) := by
        linear_combination -u * hpq_sq
      linarith [show (p_i + q_i) * (u * (p_i + q_i) + w * v ^ 2) = p_i + q_i by
        rw [huw]; ring]
    -- v² = 1: v² | (p+q) and IsCoprime(p+q, v²) → v² | 1
    have hv2_one : v ^ 2 = 1 := by
      have hdvd : v ^ 2 ∣ 1 := by
        obtain ⟨k, hk⟩ := hv2_dvd_pq
        obtain ⟨u, w, huw⟩ := hcop_pq_v2
        exact ⟨u * k + w, by
          have : v ^ 2 * (u * k + w) = u * (p_i + q_i) + w * v ^ 2 := by
            rw [hk]; ring
          linarith [huw]⟩
      have hnn : 0 ≤ v ^ 2 := sq_nonneg v
      have hne : v ^ 2 ≠ 0 := by
        intro h; simp only [h, mul_zero] at hBN; linarith [hB_pos]
      have hle : v ^ 2 ≤ 1 := Int.le_of_dvd one_pos hdvd
      omega
    -- M = p+q
    have hMeq : M = p_i + q_i := by
      have hpq_sq_M : (p_i + q_i) ^ 2 = M ^ 2 := by rw [hpq_sq, hv2_one, mul_one]
      exact (sq_inj_pos' hpq_pos hM0 hpq_sq_M).symm
    -- Step 5: e = p, f = q (natural numbers)
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
    -- Step 6: scale and relabel model
    -- D'.model = D.model definitionally (relabelTarget' only changes target)
    have hmod' : D'.model.ThreeAlphaData α β a b c := hmod
    obtain ⟨σ_mdl, _, ho_a0, _, ho_b1, _, ho_c2⟩ := hmod'
    set scale_r := (f_n : ℝ) ^ 2 / c
    have hscale_pos : 0 < scale_r := div_pos (by positivity) hc
    let D_sc := scaleDissection (D'.model.pts 0) scale_r hscale_pos.ne' D'
    let D'' := D_sc.relabelModel σ_mdl
    have hoppLen : ∀ k : Fin 3, D''.model.oppLen k =
        scale_r * D'.model.oppLen (σ_mdl k) := fun k => by
      have heq : D''.model.oppLen k = D_sc.model.oppLen (σ_mdl k) :=
        Row14AnyLabel.oppLen_of_pts σ_mdl (fun _ => rfl) k
      rw [heq]
      unfold Tri.oppLen
      rw [scaleDissection_model_pts, scaleDissection_model_pts, homothetyEquiv_dist,
          abs_of_nonneg (le_of_lt hscale_pos)]
    have hso : ∀ (T : Tri) (k : Fin 3), sideOpp T k = T.oppLen k := fun _ _ => rfl
    have hm0 : sideOpp D''.model 0 = (e_n : ℝ) * f_n := by
      rw [hso, hoppLen 0, ho_a0, ha_sc,
          show scale_r = (f_n : ℝ) ^ 2 / c from rfl, hsr, hr_pq, hf_cast, he_cast]
      field_simp
    have hm1 : sideOpp D''.model 1 = (f_n : ℝ) ^ 2 - (e_n : ℝ) ^ 2 := by
      rw [hso, hoppLen 1, ho_b1, hb_sc,
          show scale_r = (f_n : ℝ) ^ 2 / c from rfl, hsr, hr_pq, hf_cast, he_cast]
      field_simp
    have hm2 : sideOpp D''.model 2 = (f_n : ℝ) ^ 2 := by
      rw [hso, hoppLen 2, ho_c2, show scale_r = (f_n : ℝ) ^ 2 / c from rfl, hf_cast]
      field_simp
    -- Step 7: target congruence
    -- D''.target = D_sc.target (relabelModel does not change target)
    have hD''_tpts : ∀ k, D''.target.pts k =
        homothetyEquiv (D'.model.pts 0) scale_r hscale_pos.ne' (D'.target.pts k) :=
      fun _ => rfl
    set X := D'.target.oppLen 0
    have hX1 : D'.target.oppLen 1 = X := by
      have hlaw := Tri.lawSin D'.target 0 1
      rw [hD'_tgt0, hD'_tgt1] at hlaw
      have hβ_pos : 0 < β := by
        have := Tri.angleAt_pos' D'.target 0; rwa [hD'_tgt0] at this
      have hβ_lt_pi : β < Real.pi := by
        have hsum := D'.target.angleAt_sum; rw [hD'_tgt0, hD'_tgt1] at hsum
        linarith [Tri.angleAt_pos' D'.target 2]
      have hs_pos : 0 < Real.sin β :=
        Real.sin_pos_of_pos_of_lt_pi hβ_pos hβ_lt_pi
      exact mul_left_cancel₀ hs_pos.ne' hlaw
    have hX_cq : X = c * (q_i : ℝ) := by
      have hMeq_r : (M : ℝ) = (p_i : ℝ) + q_i := by exact_mod_cast hMeq
      have hpq_ne : (p_i : ℝ) + (q_i : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hpq_pos)
      have h1 : ((p_i : ℝ) + q_i) * c = X * (1 + (p_i : ℝ) / q_i) := by
        have := hMleg; rw [hMeq_r, hsr, hr_pq] at this; exact this
      have h2 : ((p_i : ℝ) + q_i) * (X - c * q_i) = 0 := by
        field_simp at h1; linarith
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd h hpq_ne
      · linarith
    have hX_eq : scale_r * X = (f_n : ℝ) ^ 3 := by
      rw [show scale_r = (f_n : ℝ) ^ 2 / c from rfl, hX_cq, hf_cast]
      field_simp
    have hhe : (0 : ℝ) < (e_n : ℝ) := by exact_mod_cast he_pos
    have hhef : (e_n : ℝ) < (f_n : ℝ) := by exact_mod_cast hef_lt
    have hbaseLen : baseLen (e_n : ℝ) f_n = (e_n : ℝ) * (3 * (f_n : ℝ) ^ 2 - (e_n : ℝ) ^ 2) := by
      unfold baseLen Nq; ring
    -- Distances in D''.target (scaled by scale_r from D'.target)
    -- oppLen 2 T = dist (T.pts 0) (T.pts 1), oppLen 0 T = dist (T.pts 1) (T.pts 2),
    -- oppLen 1 T = dist (T.pts 2) (T.pts 0) — all rfl in Fin 3
    have hd01 : dist (D''.target.pts 0) (D''.target.pts 1) = baseLen (e_n : ℝ) f_n := by
      rw [hD''_tpts 0, hD''_tpts 1, homothetyEquiv_dist, abs_of_pos hscale_pos,
          show dist (D'.target.pts 0) (D'.target.pts 1) = D'.target.oppLen 2 from rfl]
      rw [hYs, hX_cq, show scale_r = (f_n : ℝ) ^ 2 / c from rfl, hsr, hr_pq, he_cast, hf_cast]
      unfold baseLen Nq; field_simp
    have hd12 : dist (D''.target.pts 1) (D''.target.pts 2) = (f_n : ℝ) ^ 3 := by
      have : dist (D''.target.pts 1) (D''.target.pts 2) = scale_r * X := by
        rw [hD''_tpts 1, hD''_tpts 2, homothetyEquiv_dist, abs_of_pos hscale_pos,
            show dist (D'.target.pts 1) (D'.target.pts 2) = X from rfl]
      rw [this, hX_eq]
    have hd20 : dist (D''.target.pts 2) (D''.target.pts 0) = (f_n : ℝ) ^ 3 := by
      have : dist (D''.target.pts 2) (D''.target.pts 0) = scale_r * X := by
        rw [hD''_tpts 2, hD''_tpts 0, homothetyEquiv_dist, abs_of_pos hscale_pos,
            show dist (D'.target.pts 2) (D'.target.pts 0) = D'.target.oppLen 1 from rfl,
            hX1]
      rw [this, hX_eq]
    have htgt_cong : D''.target.Congruent
        (baseBetaTarget (e_n : ℝ) f_n (by exact_mod_cast he_pos) (by exact_mod_cast hef_lt)) :=
      SssCongruent.congruent_of_dist_three
        (by rw [hd01, baseBetaTarget_dist_base hhe hhef]; exact hbaseLen)
        (by rw [hd12, baseBetaTarget_dist_leg₁ hhe hhef])
        (by rw [hd20, dist_comm, baseBetaTarget_dist_leg₀ hhe hhef])
    exact ⟨e_n, f_n, he_pos, hef_lt, hcop_nat, N, D'', htgt_cong, hm0, hm1, hm2⟩

end Erdos634.Draft.ScaleBaseBetaFull

#print axioms Erdos634.Draft.ScaleBaseBetaFull.scaleBaseBeta

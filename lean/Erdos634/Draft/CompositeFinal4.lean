/-
Draft/CompositeFinal4.lean — atoms for N = 66 and N = 70 beyond CompositeFinal3 / ChainCompositeR8b.
UNAUDITED.  Formalization debt, NOT /goal progress.  No sorry, no native_decide.

(1) `S1Closed 66` PROVED.  `S1Arith 66` is false ((p,q,M) = (3,5,8)); the genuine solution is the base-β
    instance (e,f) = (3,5) (3·25−9 = 66), so the S1 shape at N = 66 yields `BaseBetaTiled` (front end of
    `s1Closed_of_arith` + back end of `ScaleBaseBetaFull.scaleBaseBeta`, joined by an arithmetic hypothesis
    `M = p+q`), and `not_baseBetaTiled` (= `basebeta_full_unc`) closes it.
(2) `GapR8Rest70` PROVED (all five shapes of `GapR8 70`, via `R8Gen2.gapR8_of_arith2` with NoF2/NoF3/NoF4z at 70).
(3) `S3Closed 70`: NOT proved; see the report (the arithmetic solution (e,d,m) = (2,1,1) is the tile (6,5,9),
    target (45,45,70); excluded in the registry only by a 134M-node search, not by a proof).
-/
import Erdos634.Draft.CompositeFinal3
import Erdos634.Draft.ChainCompositeR8b
import Erdos634.Draft.BaseBetaFullUnc

set_option synthInstance.maxSize 1000
set_option synthInstance.maxHeartbeats 400000

namespace Erdos634.Draft.CompositeFinal4

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.BaseBetaTargetCoord
open Erdos634.Realizable Erdos634.Draft.TheoremPConditional Erdos634.Draft.CompositeS1Arith

open Erdos634.Draft.ScaleBaseBetaFull in
set_option maxHeartbeats 4000000 in
/-- S1 shape (β,β,3α) with `(p,q,M)` forced to `M = p+q` by arithmetic ⇒ `BaseBetaTiled` (some member's base-β
target is tiled by its tile). -/
theorem s1_baseBetaTiled_of_arith (N : ℕ)
    (hA : ∀ p q M : ℤ, 0 < p → p < q → IsCoprime p q → 0 < M →
      (N : ℤ) * (p + q) ^ 2 = M ^ 2 * (3 * q ^ 2 - p ^ 2) → M = p + q)
    (D : CongruentDissection N) (α β a b c : ℝ) (r : ℚ) (hα : IrrPi α) (hrel : 3 * α + 2 * β = Real.pi)
    (hmod : D.model.ThreeAlphaData α β a b c) (har : a = (r : ℝ) * c)
    (hbr : b = (1 - (r : ℝ) ^ 2) * c) (htgt : TgtAngles D β β (3 * α)) : BaseBetaTiled := by
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
  have hB_pos : (0 : ℤ) < 3 * q_i ^ 2 - p_i ^ 2 := by nlinarith [sq_nonneg p_i, sq_nonneg q_i]
  have hpq_pos : (0 : ℤ) < p_i + q_i := by linarith [hp_pos, hq_pos]
  have hMeq : M = p_i + q_i := hA p_i q_i M hp_pos hp_lt_q hcop_pq hM0 hquad_int
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



open Erdos634.Draft.ScaleBaseBetaFull in
/-- helper: `p+q` coprime to `p`. -/
theorem isCoprime_sum_left' {p q : ℤ} (hcop : IsCoprime p q) : IsCoprime (p + q) p := by
  obtain ⟨u, v, huv⟩ := hcop; exact ⟨v, u - v, by linarith⟩

/-- The arithmetic of S1 at N = 66: every coprime solution has `M = p + q` (indeed `(p,q) = (3,5)`, `M = 8`). -/
theorem s1_arith_66 : ∀ p q M : ℤ, 0 < p → p < q → IsCoprime p q → 0 < M →
    (66 : ℕ) * (p + q) ^ 2 = M ^ 2 * (3 * q ^ 2 - p ^ 2) → M = p + q := by
  intro p q M hp hpq hcop hM heq
  push_cast at heq
  have hq0 : 0 < q := by omega
  have hY : 0 < 3 * q ^ 2 - p ^ 2 := by nlinarith
  have hs : 0 < p + q := by omega
  have h1 : (66 : ℤ) * (3 * q ^ 2 - p ^ 2) * (p + q) ^ 2 = (M * (3 * q ^ 2 - p ^ 2)) ^ 2 := by
    have : (66 : ℤ) * (3 * q ^ 2 - p ^ 2) * (p + q) ^ 2 = (3 * q ^ 2 - p ^ 2) * (66 * (p + q) ^ 2) := by ring
    rw [this, heq]; ring
  have hdvd : (p + q) ^ 2 ∣ (M * (3 * q ^ 2 - p ^ 2)) ^ 2 :=
    ⟨66 * (3 * q ^ 2 - p ^ 2), by rw [← h1]; ring⟩
  obtain ⟨w, hw⟩ := (Int.pow_dvd_pow_iff (two_ne_zero)).mp hdvd
  have hw2 : w ^ 2 = 66 * (3 * q ^ 2 - p ^ 2) := by
    have : (p + q) ^ 2 * w ^ 2 = (p + q) ^ 2 * (66 * (3 * q ^ 2 - p ^ 2)) := by
      calc (p + q) ^ 2 * w ^ 2 = ((p + q) * w) ^ 2 := by ring
        _ = (M * (3 * q ^ 2 - p ^ 2)) ^ 2 := by rw [← hw]
        _ = (p + q) ^ 2 * (66 * (3 * q ^ 2 - p ^ 2)) := by rw [← h1]; ring
    exact mul_left_cancel₀ (pow_ne_zero 2 hs.ne') this
  have h2 : (2 : ℤ) ∣ w := Int.prime_two.dvd_of_dvd_pow (n := 2) ⟨33 * (3 * q ^ 2 - p ^ 2), by rw [hw2]; ring⟩
  have h3 : (3 : ℤ) ∣ w := Int.prime_three.dvd_of_dvd_pow (n := 2) ⟨22 * (3 * q ^ 2 - p ^ 2), by rw [hw2]; ring⟩
  have h11 : (11 : ℤ) ∣ w := (Int.prime_iff_natAbs_prime.mpr (by norm_num : Nat.Prime (Int.natAbs 11))).dvd_of_dvd_pow (n := 2)
    ⟨6 * (3 * q ^ 2 - p ^ 2), by rw [hw2]; ring⟩
  have h66 : (66 : ℤ) ∣ w := by omega
  obtain ⟨u, hu⟩ := h66
  have hYu : 3 * q ^ 2 - p ^ 2 = 66 * u ^ 2 := by
    have : (66 : ℤ) * (3 * q ^ 2 - p ^ 2) = 66 * (66 * u ^ 2) := by rw [← hw2, hu]; ring
    exact mul_left_cancel₀ (by norm_num) this
  have hu0 : u ≠ 0 := by
    rintro rfl; nlinarith
  have hMu : M * u = p + q := by
    have h4 : (66 * u) * (M * u) = (66 * u) * (p + q) := by
      have : M * (3 * q ^ 2 - p ^ 2) = (p + q) * w := hw
      rw [hYu, hu] at this; linear_combination this
    exact mul_left_cancel₀ (by intro h; apply hu0; omega) h4
  have hupos : 0 < u := by
    by_contra hc
    nlinarith
  have hcop_s : IsCoprime (p + q) p := isCoprime_sum_left' hcop
  have hcop_up : IsCoprime u p := hcop_s.of_isCoprime_of_dvd_left ⟨M, by rw [← hMu]; ring⟩
  have hu_dvd : u ∣ 2 * p ^ 2 := ⟨66 * u - 3 * (q - p) * M, by linear_combination hYu + 3 * (q - p) * hMu⟩
  have hu2 : u ∣ 2 := (hcop_up.pow_right (n := 2)).dvd_of_dvd_mul_right hu_dvd
  have hule : u ≤ 2 := Int.le_of_dvd (by norm_num) hu2
  have hu12 : u = 1 ∨ u = 2 := by omega
  rcases hu12 with rfl | rfl
  · linarith
  · exfalso
    have hq11 : q ≤ 11 := by nlinarith
    have hg := Int.isCoprime_iff_gcd_eq_one.mp hcop
    have hp10 : p ≤ 10 := by omega
    interval_cases q <;> interval_cases p <;> first | omega | (norm_num at hg)

theorem s1Closed_66 : S1Closed 66 := by
  intro D α β a b c r hα hrel hmod har hbr htgt
  exact not_baseBetaTiled
    (s1_baseBetaTiled_of_arith 66 s1_arith_66 D α β a b c r hα hrel hmod har hbr htgt)

/-! ## N = 70 : GapR8 -/

open Erdos634.Draft.R8Gen2 in
theorem noF3_70 : NoF3 70 := by
  intro s j hj hjs h
  push_cast at h
  have h1 : j ≤ 4 := by nlinarith
  have h2 : s ≤ 12 := by nlinarith
  interval_cases j <;> interval_cases s <;> omega

open Erdos634.Draft.R8Gen2 in
theorem noF2_70 : NoF2 70 := by
  apply noF2_of_int
  · intro z hz
    push_cast at hz
    have h1 : z ≤ 6 := by nlinarith
    have h2 : -6 ≤ z := by nlinarith
    interval_cases z <;> omega
  · intro x r hx hr h z hz
    push_cast at hz
    have hx7 : x ≤ 6 := by nlinarith
    have hr9 : r ≤ 9 := by nlinarith
    interval_cases x <;> interval_cases r <;> omega

open Erdos634.Draft.R8Gen2 in
theorem noF4z_70 : NoF4z 70 := by
  apply noF4z_of_int
  intro x r hx hr h z hz
  have hx7 : x ≤ 6 := by nlinarith
  have hr9 : r ≤ 9 := by nlinarith
  interval_cases x <;> interval_cases r <;>
    first
    | omega
    | (norm_num at hz
       have h1 : z ≤ 7 := by nlinarith
       have h2 : -7 ≤ z := by nlinarith
       interval_cases z <;> omega)

/-- **`GapR8 70` PROVED** (all five shapes). -/
theorem gapR8_70 : Chain15.GapR8 70 :=
  Erdos634.Draft.R8Gen2.gapR8_of_arith2 70 noF2_70 noF3_70 noF4z_70

open Erdos634.Draft.CompositeFinal2 in
/-- `GapR8Rest70` PROVED. -/
theorem gapR8Rest70 : GapR8Rest70 := by
  intro D α a b c hirr hm h
  apply gapR8_70 D α a b c hirr hm
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))


/-- Non-vacuity of the arithmetic hypothesis: (3,5,8) satisfies the equation, so `s1_arith_66` is not vacuous and
`S1Arith 66` is genuinely false; the conclusion `M = p+q` holds there (8 = 3+5). -/
theorem s1_arith_66_witness : ((66 : ℕ) : ℤ) * (3 + 5) ^ 2 = 8 ^ 2 * (3 * 5 ^ 2 - 3 ^ 2) ∧ (8 : ℤ) = 3 + 5 := by
  norm_num

open Erdos634.Draft.CompositeFinal2 Erdos634.Draft.CompositeFinal3 Erdos634.Draft.ChainComposite in
/-- **N = 66, modulo `H1Right 66` only.** -/
theorem chain_66_H1only (gR : H1Right 66) (D : CongruentDissection 66) : False :=
  chain_66_final gR s1Closed_66 Erdos634.Draft.R8Gen2.gapR8_66 D

open Erdos634.Draft.CompositeFinal2 Erdos634.Draft.CompositeFinal3 Erdos634.Draft.ChainComposite in
/-- **N = 70, modulo `H1Right 70` and `S3Closed 70` only.** -/
theorem chain_70_H1S3 (gR : H1Right 70) (gS3 : Erdos634.Draft.CompositeGen2.S3Closed 70)
    (D : CongruentDissection 70) : False :=
  chain_70_final gR gS3 gapR8Rest70 D

end Erdos634.Draft.CompositeFinal4

#print axioms Erdos634.Draft.CompositeFinal4.s1_baseBetaTiled_of_arith
#print axioms Erdos634.Draft.CompositeFinal4.s1Closed_66
#print axioms Erdos634.Draft.CompositeFinal4.gapR8_70
#print axioms Erdos634.Draft.CompositeFinal4.gapR8Rest70
#print axioms Erdos634.Draft.CompositeFinal4.chain_66_H1only
#print axioms Erdos634.Draft.CompositeFinal4.chain_70_H1S3

/-
Draft/RWInst.lean -- the S4 leaf `RWStatementNsq N` from its finitely many scaled instances.

`NSQRW.rwStatement_nsq` proves `RWStatementNsq N` when no `S' ≥ 2`, coprime `e < f` have `N = S'²(2f² − e²)` (`RWFree N`).
Here each such triple is carried as a leaf `S4Inst S' e f`: "no dissection of the triangle with sides
`S' e (2f²−e²)`, `S' f (f²−e²)`, `S' f³` by the tile `(e f, f²−e², f²)`".  The proof is `rwStatement_nsq` verbatim except
for the step `S' = 1`, which is now obtained by refuting `S' ≥ 2` with the instance (target sides recomputed with the
factor `S'`, then scaling by `f²/c`).  `s4inst_of_cert` discharges an instance from a search certificate by SSS.

Composite-N leaves; not prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.NSQRW
import Erdos634.Draft.GapE120Dis

open scoped Classical
open Erdos634.Geometry Erdos634.TilePlacement Erdos634.BaseBetaTargetCoord Erdos634.Realizable
  Erdos634.Draft.TheoremPConditional Erdos634.Draft.RWPieces Erdos634.Draft.RWAssemble Erdos634.CertCoord

namespace Erdos634.Draft.NSQRW

/-- **The S4 instance `(S', e, f)`**: no dissection (any number of tiles) of the triangle with
`oppLen = (S' e (2f²−e²), S' f (f²−e²), S' f³)` by the tile with sides `(e f, f² − e², f²)`. -/
def S4Inst (S' e f : ℤ) : Prop :=
  ∀ {N : ℕ} (D : CongruentDissection N),
    D.target.oppLen 0 = (S' : ℝ) * e * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) →
    D.target.oppLen 1 = (S' : ℝ) * f * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) →
    D.target.oppLen 2 = (S' : ℝ) * (f : ℝ) ^ 3 →
    (∃ σ : Equiv.Perm (Fin 3), D.model.oppLen (σ 0) = (e : ℝ) * f ∧
      D.model.oppLen (σ 1) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∧ D.model.oppLen (σ 2) = (f : ℝ) ^ 2) → False

open Erdos634.Geometry.GapE120Dis in
/-- an S4 instance from a certificate: `TGT` has sides `(S' f (f²−e²), S' e (2f²−e²), S' f³)` and `MODEL` sides
`(e f, f²−e², f²)`, both in the vertex order `01, 12, 02` -/
theorem s4inst_of_cert (S' e f : ℤ) (TGT MODEL : Erdos634.Geometry.Tri)
    (hT : dist (TGT.pts 0) (TGT.pts 1) = (S' : ℝ) * f * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ∧
      dist (TGT.pts 1) (TGT.pts 2) = (S' : ℝ) * e * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ∧
      dist (TGT.pts 0) (TGT.pts 2) = (S' : ℝ) * (f : ℝ) ^ 3)
    (hM : dist (MODEL.pts 0) (MODEL.pts 1) = (e : ℝ) * f ∧
      dist (MODEL.pts 1) (MODEL.pts 2) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∧ dist (MODEL.pts 0) (MODEL.pts 2) = (f : ℝ) ^ 2)
    (hno : ∀ {N : ℕ} (D : CongruentDissection N), D.target.Congruent TGT → D.model.Congruent MODEL → False) :
    S4Inst S' e f := by
  intro N D h0 h1 h2 ⟨σ, m0, m1, m2⟩
  obtain ⟨g1, g2, g3⟩ := hT
  obtain ⟨k1, k2, k3⟩ := hM
  have hTc : D.target.Congruent TGT := by
    set ρ : Equiv.Perm (Fin 3) := Equiv.swap (1 : Fin 3) 2 with hρ
    have r0 : ρ 0 = 0 := by simp [hρ, sw0]
    have r1 : ρ 1 = 2 := by simp [hρ, sw1]
    have r2 : ρ 2 = 1 := by simp [hρ, sw2]
    have hc := Tri.congruent_of_dist (D.target.relabel ρ) TGT
      (by simp only [Tri.relabel_pts, Function.comp]; rw [r0, r1, g1, ← h1, dist_comm]; rfl)
      (by simp only [Tri.relabel_pts, Function.comp]; rw [r1, r2, g2, ← h0, dist_comm]; rfl)
      (by simp only [Tri.relabel_pts, Function.comp]; rw [r0, r2, g3, ← h2]; rfl)
    exact (D.target.congruent_relabel ρ).trans hc
  obtain ⟨s1, s2, s3⟩ := sides_of_perm D.model σ
  rw [m0] at s1; rw [m1] at s2; rw [m2] at s3
  have hMc : D.model.Congruent MODEL := by
    set τ : Equiv.Perm (Fin 3) := (finRotate 3).trans σ with hτ
    have h0' : τ 0 = σ 1 := by simp [hτ, fr0]
    have h1' : τ 1 = σ 2 := by simp [hτ, fr1]
    have h2' : τ 2 = σ 0 := by simp [hτ, fr2]
    have hc := Tri.congruent_of_dist (D.model.relabel τ) MODEL
      (by simp only [Tri.relabel_pts, Function.comp]; rw [h0', h1', s1, k1])
      (by simp only [Tri.relabel_pts, Function.comp]; rw [h1', h2', dist_comm, s2, k2])
      (by simp only [Tri.relabel_pts, Function.comp]; rw [h0', h2', dist_comm, s3, k3])
    exact (D.model.congruent_relabel τ).trans hc
  exact hno D hTc hMc

set_option maxHeartbeats 4000000 in
theorem rwStatement_of_inst (N : ℕ)
    (hinst : ∀ S' e f : ℤ, 2 ≤ S' → 0 < e → e < f → IsCoprime e f → (N : ℤ) = S' ^ 2 * (2 * f ^ 2 - e ^ 2) →
      S4Inst S' e f) : RWStatementNsq N := by
  intro D α β a b c r hα hrel hmod har hbr htgt
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
  obtain ⟨S', hS'pos, hNS', hSS'⟩ := w_arith_nsq (by have := D.pos; omega) hp_pos hp_lt_q hcop_pq hSpos hEq
  have hS'1 : S' = 1 := by
    by_contra hne
    exfalso
    have hS2 : 2 ≤ S' := by omega
    have hSRg : (S : ℝ) = (S' : ℝ) * p_i := by exact_mod_cast hSS'
    have hpRg : (0 : ℝ) < (p_i : ℝ) := by exact_mod_cast hp_pos
    have hS'R : (0 : ℝ) < (S' : ℝ) := by exact_mod_cast hS'pos
    have hpq : (p_i : ℝ) < q_i := by exact_mod_cast hp_lt_q
    -- the target's sides, with the scale `S'`
    have hO2g : D'.target.oppLen 2 = (S' : ℝ) * q_i * c := by
      have h1 := hSc; rw [hSRg, hsr, hr_pq] at h1
      have h2 : (p_i : ℝ) / q_i * D'.target.oppLen 2 * q_i = (p_i : ℝ) * D'.target.oppLen 2 := by field_simp
      have h3 : (p_i : ℝ) * D'.target.oppLen 2 = (p_i : ℝ) * ((S' : ℝ) * q_i * c) := by
        rw [← h2, ← h1]; ring
      exact mul_left_cancel₀ hpRg.ne' h3
    have hO1g : D'.target.oppLen 1 = (S' : ℝ) * ((q_i : ℝ) ^ 2 - (p_i : ℝ) ^ 2) * c / q_i := by
      rw [hO1, hO2g, hsr, hr_pq]; first | (field_simp; ring) | field_simp
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
    have hO0g : D'.target.oppLen 0
        = (S' : ℝ) * p_i * (2 * (q_i : ℝ) ^ 2 - (p_i : ℝ) ^ 2) * c / (q_i : ℝ) ^ 2 := by
      have hcl := cos_angleAt_mul D'.target 0
      rw [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl, hP0, Real.cos_two_mul] at hcl
      have hO0pos : 0 < D'.target.oppLen 0 := Row3.RP.oppLen_pos D'.target 0
      have hsq0 : D'.target.oppLen 0 ^ 2 = D'.target.oppLen 1 ^ 2 + D'.target.oppLen 2 ^ 2
          - 2 * D'.target.oppLen 1 * D'.target.oppLen 2 * (2 * Real.cos α ^ 2 - 1) := by linarith [hcl]
      have hsq : D'.target.oppLen 0 ^ 2
          = ((S' : ℝ) * p_i * (2 * (q_i : ℝ) ^ 2 - (p_i : ℝ) ^ 2) * c / (q_i : ℝ) ^ 2) ^ 2 := by
        rw [hsq0, hO1g, hO2g, hcosα]; first | (field_simp; ring) | field_simp
      have hrhs : 0 ≤ (S' : ℝ) * p_i * (2 * (q_i : ℝ) ^ 2 - (p_i : ℝ) ^ 2) * c / (q_i : ℝ) ^ 2 := by
        have : (0 : ℝ) < 2 * (q_i : ℝ) ^ 2 - (p_i : ℝ) ^ 2 := by nlinarith
        positivity
      exact RWPieces.eq_of_sq_eq hO0pos.le hrhs hsq
    -- scale by `f²/c`
    set sc : ℝ := (q_i : ℝ) ^ 2 / c with hsc
    have hscpos : 0 < sc := div_pos (by positivity) hc
    set Ds := scaleDissection (D'.model.pts 0) sc hscpos.ne' D' with hDs
    have htd : ∀ i j : Fin 3, dist (Ds.target.pts i) (Ds.target.pts j) = sc * dist (D'.target.pts i) (D'.target.pts j) := by
      intro i j
      rw [hDs, scaleDissection_target_pts, scaleDissection_target_pts, homothetyEquiv_dist, abs_of_pos hscpos]
    have hmd : ∀ i j : Fin 3, dist (Ds.model.pts i) (Ds.model.pts j) = sc * dist (D'.model.pts i) (D'.model.pts j) := by
      intro i j
      rw [hDs, scaleDissection_model_pts, scaleDissection_model_pts, homothetyEquiv_dist, abs_of_pos hscpos]
    have hto : ∀ k : Fin 3, Ds.target.oppLen k = sc * D'.target.oppLen k := fun k => by
      unfold Tri.oppLen; exact htd _ _
    have hmo : ∀ k : Fin 3, Ds.model.oppLen k = sc * D.model.oppLen k := fun k => by
      unfold Tri.oppLen; exact hmd _ _
    refine hinst S' p_i q_i hS2 hp_pos hp_lt_q hcop_pq hNS' Ds ?_ ?_ ?_ ⟨σm, ?_, ?_, ?_⟩
    · rw [hto, hO0g, hsc]; first | (field_simp; ring) | field_simp
    · rw [hto, hO1g, hsc]; first | (field_simp; ring) | field_simp
    · rw [hto, hO2g, hsc]; first | (field_simp; ring) | field_simp
    · rw [hmo, ham, ha_sc, hsr, hr_pq, hsc]; first | (field_simp; ring) | field_simp
    · rw [hmo, hbm, hb_sc, hsr, hr_pq, hsc]; first | (field_simp; ring) | field_simp
    · rw [hmo, hcm, hsc]; first | (field_simp; ring) | field_simp
  have hSeq : S = p_i := by rw [hSS', hS'1]; ring
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
  have hso : ∀ (T : Erdos634.Geometry.Tri) (k : Fin 3), sideOpp T k = T.oppLen k := fun _ _ => rfl
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

end Erdos634.Draft.NSQRW

#print axioms Erdos634.Draft.NSQRW.rwStatement_of_inst

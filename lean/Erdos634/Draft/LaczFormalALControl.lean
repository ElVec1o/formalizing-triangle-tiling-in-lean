import Erdos634.Draft.LaczFormalALFinal
import Erdos634.Draft.LaczFormalMJControl

/-!
# Non-vacuity control for Lemma A(j): the hypothesis package on GENUINE dissections

Erdős #634, base-`β` row.  Credit: AI assistant (Lemma A(k) proposal), Beeson–Roșu, Beeson, Laczkovich, Paliy.  UNAUDITED.
Axiom-clean; no `sorry`.  This file proves NOTHING new about #634: it exercises the hypothesis package of `walk_noA`,
`walk_noAm` (band setting `S`, exchanged lattice frame `AF`, base walk with its step data, lattice points
of the frame in the target) on every genuine tiling of `T_M(e,f)` (`betaTilable_self`, e.g. the kernel-checked 207-tiling
of `T_3(2,3)`), as `LaczFormalMJControl` does for `M(j)`.
-/

namespace Erdos634.LaczAL

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Walk
  Erdos634.LaczJunction.Grammar Erdos634.Draft.UniformThreshold Erdos634.Draft.LaczFormal.Graph
  Erdos634.BaseBetaTargetCoord Erdos634.Draft.FDBBaseBetaE1 Erdos634.LaczMJ

variable {N : ℕ}

/-- **The frame norm identity `|v − e0| = b` for the exchanged frame** (`v` of length `c` along the left leg, `e0` of length
`a` along the base): the law of cosines is symmetric in `a, c`. -/
theorem canon_hb_A {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r)
    (hori : 0 < cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p)) :
    ‖((tc e f : ℝ) / dist (D.target.pts p) (D.target.pts r)) • (D.target.pts r - D.target.pts p) -
      ((ta e f : ℝ) / dist (D.target.pts p) (D.target.pts q)) • (D.target.pts q - D.target.pts p)‖ = (tb e f : ℝ) := by
  set P := D.target.pts p with hP
  set Q := D.target.pts q with hQ
  set R := D.target.pts r with hR
  have hPQ : P ≠ Q := by
    intro h
    have : cross (Q - P) (R - P) = 0 := by rw [← h]; simp [cross]
    linarith
  have hPR : P ≠ R := by
    intro h
    have : cross (Q - P) (R - P) = 0 := by rw [← h]; simp [cross]
    linarith
  have hpq : 0 < dist P Q := dist_pos.mpr hPQ
  have hpr : 0 < dist P R := dist_pos.mpr hPR
  have hna : ‖Q - P‖ = dist P Q := by rw [dist_comm, dist_eq_norm]
  have hnr : ‖R - P‖ = dist P R := by rw [dist_comm, dist_eq_norm]
  have ha : (0 : ℝ) < ta e f := by exact_mod_cast a_pos e f S.he S.hef
  have hc : (0 : ℝ) < tc e f := LFrame.tc_pos S
  have hb : (0 : ℝ) < tb e f := by exact_mod_cast b_pos e f S.he S.hef
  -- the model: b² = a² + c² - 2ac cos β
  have hmod := EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle
    (V := Plane) (D.model.pts 2) (D.model.pts 1) (D.model.pts 0)
  have d21 : dist (D.model.pts 2) (D.model.pts 1) = ta e f := by
    rw [dist_comm]; exact (by simpa [sideOpp] using S.hsa)
  have d01 : dist (D.model.pts 0) (D.model.pts 1) = tc e f := by
    simpa [sideOpp] using S.hsc
  have d20 : dist (D.model.pts 2) (D.model.pts 0) = tb e f := by
    simpa [sideOpp] using S.hsb
  have hcosβ : Real.cos β = ((ta e f : ℝ) ^ 2 + (tc e f : ℝ) ^ 2 - (tb e f : ℝ) ^ 2) / (2 * ta e f * tc e f) := by
    have h1 : EuclideanGeometry.angle (V := Plane) (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β := S.hβ'
    rw [h1, d20, d21, d01] at hmod
    field_simp
    nlinarith [hmod]
  -- the target inner product
  have hcos := InnerProductGeometry.cos_angle_mul_norm_mul_norm (Q - P) (R - P)
  have hang : InnerProductGeometry.angle (Q - P) (R - P) = β := by
    have := S.cornerP
    unfold cornerAngle EuclideanGeometry.angle at this
    simpa [vsub_eq_sub] using this
  rw [hang, hna, hnr] at hcos
  have hinner : inner ℝ (Q - P) (R - P) = Real.cos β * (dist P Q * dist P R) := hcos.symm
  -- the norm of the difference
  have hsq : ‖((tc e f : ℝ) / dist P R) • (R - P) - ((ta e f : ℝ) / dist P Q) • (Q - P)‖ ^ 2 = (tb e f : ℝ) ^ 2 := by
    rw [norm_sub_sq_real, norm_smul, norm_smul, inner_smul_left, inner_smul_right, hna, hnr,
      Real.norm_of_nonneg (div_nonneg hc.le hpr.le), Real.norm_of_nonneg (div_nonneg ha.le hpq.le)]
    simp only [conj_trivial]
    rw [real_inner_comm, hinner, hcosβ]
    field_simp
    ring
  have h0 : 0 ≤ ‖((tc e f : ℝ) / dist P R) • (R - P) - ((ta e f : ℝ) / dist P Q) • (Q - P)‖ := norm_nonneg _
  nlinarith [hsq, h0, hb]


/-- The conclusion of `a_control_of_dims`: band setting, exchanged lattice frame, base walk with its step data, lattice points
of the frame in the target, and Lemma A(j) for the walk (`1 ≤ j ≤ f − 1`). -/
def APackage (D : CongruentDissection N) (e f : ℕ) (p q r : Fin 3) : Prop :=
    ∃ (S : BandSetup D e f (modelAlpha (e : ℝ) f) (modelBeta (e : ℝ) f)
        (2 * modelAlpha (e : ℝ) f + modelBeta (e : ℝ) f) p q r)
      (F : AF D e f (modelAlpha (e : ℝ) f) (modelBeta (e : ℝ) f)
        (2 * modelAlpha (e : ℝ) f + modelBeta (e : ℝ) f) p q r)
      (L : List (Fin N × Plane × Plane)),
      F.S = S ∧
      F.pt 1 0 ∈ openSegment ℝ (D.target.pts p) (D.target.pts q) ∧
      F.pt 0 1 ∈ openSegment ℝ (D.target.pts p) (D.target.pts r) ∧
      F.pt 1 1 ∈ interior D.target.carrier ∧
      WalkT D.toDissection (toV2 (D.target.pts q - D.target.pts p)) (D.target.pts p) (D.target.pts q) L ∧
      (∀ x ∈ L, StepData D e f (modelAlpha (e : ℝ) f) (modelBeta (e : ℝ) f)
        (2 * modelAlpha (e : ℝ) f + modelBeta (e : ℝ) f) p q x) ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ f - 1 →
        ¬ winA j (L.map (elemTok D (modelAlpha (e : ℝ) f) (modelBeta (e : ℝ) f))) ∧
        ¬ winAm j (L.map (elemTok D (modelAlpha (e : ℝ) f) (modelBeta (e : ℝ) f)))

/-- **The hypothesis package of `walk_noA` / `al_holds` is satisfiable on a genuine dissection.** -/
theorem a_control_of_dims (D : CongruentDissection N) (e f M : ℕ) (he : 2 ≤ e) (hef : e < f)
    (hcop : Nat.Coprime e f) (hM2 : 2 ≤ M)
    (hsa : sideOpp D.model 0 = (ta e f : ℝ)) (hsb : sideOpp D.model 1 = (tb e f : ℝ))
    (hsc : sideOpp D.model 2 = (tc e f : ℝ))
    {p q r : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hbase : dist (D.target.pts p) (D.target.pts q) = ((M * e * (3 * f ^ 2 - e ^ 2) : ℕ) : ℝ))
    (hlegL : dist (D.target.pts p) (D.target.pts r) = ((M * f ^ 3 : ℕ) : ℝ))
    (hlegR : dist (D.target.pts q) (D.target.pts r) = ((M * f ^ 3 : ℕ) : ℝ))
    (hori : 0 < cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p)) :
    APackage D e f p q r := by
  classical
  unfold APackage
  have S := BandSetup.of_dims D e f M (by omega) hef hcop (by omega) hsa hsb hsc hpq hpr hqr hbase hlegL hlegR
  have hori' : 0 < crs (toV2 (D.target.pts q - D.target.pts p)) (toV2 (D.target.pts r - D.target.pts p)) := by
    rw [crs_toV2]; exact hori
  obtain ⟨L, hL, hpar, hnd, hstep⟩ := base_walk S hori'
  set α := modelAlpha (e : ℝ) f
  set β := modelBeta (e : ℝ) f
  set γ := 2 * α + β
  let F := AF.canon S hori (canon_hb_A S hori)
  have hf3 : 3 ≤ f := by omega
  have hlamR : (2 : ℝ) < F.lam := by
    show (2 : ℝ) < dist (D.target.pts p) (D.target.pts q) / (ta e f : ℝ)
    rw [lt_div_iff₀ (AF.ta_pos S), hbase]
    have := base_gt_ja e f M 2 (by omega) hef (by omega) (by omega)
    rw [← hbase] at this
    simpa [hbase] using this
  have hmuR : (2 : ℝ) < F.mu := by
    show (2 : ℝ) < dist (D.target.pts p) (D.target.pts r) / (tc e f : ℝ)
    rw [lt_div_iff₀ (LFrame.tc_pos S), hlegL]
    have := leg_gt_jc e f M 2 (by omega) (by omega) (by omega)
    simpa using this
  have hbase' : ∀ m : ℕ, m + 1 ≤ f - 1 → ((m + 1 : ℕ) : ℝ) * ta e f < dist (D.target.pts p) (D.target.pts q) := by
    intro m hm
    rw [hbase]
    exact base_gt_ja e f M (m + 1) (by omega) hef (by omega) hm
  have hlegs : ∀ m : ℕ, m + 1 ≤ f - 1 → ((m + 1 : ℕ) : ℝ) * tc e f < dist (D.target.pts p) (D.target.pts r) ∧
      ((m + 1 : ℕ) : ℝ) * tc e f < dist (D.target.pts q) (D.target.pts r) := by
    intro m hm
    have hr : ((m + 1 : ℕ) : ℝ) * tc e f < ((M * f ^ 3 : ℕ) : ℝ) := leg_gt_jc e f M (m + 1) (by omega) hm (by omega)
    exact ⟨by rw [hlegL]; exact hr, by rw [hlegR]; exact hr⟩
  refine ⟨S, F, L, rfl, F.pt_base_mem one_pos (by linarith), F.pt_leg_mem one_pos (by linarith),
    F.pt_interior one_pos one_pos ?_, hL, hstep, ?_⟩
  · have h1 : 1 / F.lam < 1 / 2 := one_div_lt_one_div_of_lt (by norm_num) hlamR
    have h2 : 1 / F.mu < 1 / 2 := one_div_lt_one_div_of_lt (by norm_num) hmuR
    show 1 / F.lam + 1 / F.mu < 1
    linarith
  · intro j hj1 hjf
    obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    exact ⟨walk_noA S hjf (hbase' m hjf) (hlegs m hjf).1 hL hstep,
      walk_noAm S hjf (hbase' m hjf) (hlegs m hjf).2 hL hstep⟩

#print axioms a_control_of_dims

/-- **The package on every genuine tiling of `T_M(e,f)` with `M ≥ 2`, `e ≥ 2`.** -/
theorem a_control_beta_tilable (e f M : ℕ) (he : 2 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f) (hM2 : 2 ≤ M)
    (hT : BetaTilable e f M) :
    ∃ (N : ℕ) (D : CongruentDissection N) (p q r : Fin 3), p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
      sideOpp D.model 0 = (ta e f : ℝ) ∧ sideOpp D.model 1 = (tb e f : ℝ) ∧ sideOpp D.model 2 = (tc e f : ℝ) ∧
      dist (D.target.pts p) (D.target.pts q) = ((M * e * (3 * f ^ 2 - e ^ 2) : ℕ) : ℝ) ∧
      dist (D.target.pts p) (D.target.pts r) = ((M * f ^ 3 : ℕ) : ℝ) ∧
      dist (D.target.pts q) (D.target.pts r) = ((M * f ^ 3 : ℕ) : ℝ) ∧
      0 < cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p) ∧
      APackage D e f p q r := by
  obtain ⟨N, D, ⟨τ, t0, t1, t2⟩, hm⟩ := hT
  obtain ⟨σ, s0, s1, s2⟩ := Erdos634.Draft.ThmDRun.sideOpp_relabel_of_hasSidesT (M := D.model) hm
  let D' : CongruentDissection N :=
    { toDissection := D.toDissection, model := D.model.relabel σ,
      tiles_congruent := fun i => (D.tiles_congruent i).trans (Tri.congruent_relabel _ σ) }
  have hs0 : sideOpp D'.model 0 = (ta e f : ℝ) := by
    show sideOpp (D.model.relabel σ) 0 = _; rw [s0]; simp [ta]
  have hs1 : sideOpp D'.model 1 = (tb e f : ℝ) := by
    show sideOpp (D.model.relabel σ) 1 = _; rw [s1]; rw [tb_real e f hef]
  have hs2 : sideOpp D'.model 2 = (tc e f : ℝ) := by
    show sideOpp (D.model.relabel σ) 2 = _; rw [s2]; simp [tc]
  have h01 : τ 0 ≠ τ 1 := fun h => by have := τ.injective h; simp at this
  have h02 : τ 0 ≠ τ 2 := fun h => by have := τ.injective h; simp at this
  have h12 : τ 1 ≠ τ 2 := fun h => by have := τ.injective h; simp at this
  have hsub : e ^ 2 ≤ 3 * f ^ 2 := by nlinarith
  have hb : dist (D'.target.pts (τ 0)) (D'.target.pts (τ 1)) = ((M * e * (3 * f ^ 2 - e ^ 2) : ℕ) : ℝ) := by
    show dist (D.target.pts (τ 0)) (D.target.pts (τ 1)) = _
    rw [t2]; push_cast [Nat.cast_sub hsub]; ring
  have hl : dist (D'.target.pts (τ 0)) (D'.target.pts (τ 2)) = ((M * f ^ 3 : ℕ) : ℝ) := by
    show dist (D.target.pts (τ 0)) (D.target.pts (τ 2)) = _
    rw [dist_comm, t1]; push_cast; ring
  have hr : dist (D'.target.pts (τ 1)) (D'.target.pts (τ 2)) = ((M * f ^ 3 : ℕ) : ℝ) := by
    show dist (D.target.pts (τ 1)) (D.target.pts (τ 2)) = _
    rw [t0]; push_cast; ring
  obtain ⟨p, q, r, hpq, hpr, hqr, hb', hl', hr', hori⟩ :=
    orient_dims D' e f M he hef (by omega) h01 h02 h12 hb hl hr
  exact ⟨N, D', p, q, r, hpq, hpr, hqr, hs0, hs1, hs2, hb', hl', hr', hori,
    a_control_of_dims D' e f M he hef hcop hM2 hs0 hs1 hs2 hpq hpr hqr hb' hl' hr' hori⟩

/-- **The 207-tiling.**  `(e,f,M) = (2,3,3)`: the whole package. -/
theorem a_control_207 :
    ∃ (N : ℕ) (D : CongruentDissection N) (p q r : Fin 3), p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
      0 < cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p) ∧
      APackage D 2 3 p q r :=
  let ⟨N, D, p, q, r, a, b, c, _, _, _, _, _, _, h, hP⟩ :=
    a_control_beta_tilable 2 3 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) betaTilable_2_3_three
  ⟨N, D, p, q, r, a, b, c, h, hP⟩

#print axioms a_control_207

/-- **Every seed tiling** (`M = f`, every coprime `2 ≤ e < f`, `betaTilable_self`). -/
theorem a_control_seed (e f : ℕ) (he : 2 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f) :
    ∃ (N : ℕ) (D : CongruentDissection N) (p q r : Fin 3), p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
      0 < cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p) ∧
      APackage D e f p q r :=
  let ⟨N, D, p, q, r, a, b, c, _, _, _, _, _, _, h, hP⟩ :=
    a_control_beta_tilable e f f he hef hcop (by omega) (betaTilable_self (by omega) hef)
  ⟨N, D, p, q, r, a, b, c, h, hP⟩

#print axioms a_control_seed

/-- **H4 at the maximal run length is satisfiable.**  In every genuine target `T_M(e,f)` (`M ≥ 1`), the exchanged frame
`AF.canon` has `Bnd (f − 1)`: every lattice point `(x, y)` with `x + y ≤ f − 1` lies in the target (so the chord triangle
`L J D_j` of the hand proof lies in the target for all `j ≤ f − 1`).  This is the hypothesis `hB` of `AL_main`.
Remark (diff audit): the `∃ α β γ S` quantifies over the `BandSetup` that `BandSetup.of_dims` constructs from the dimensions;
this lemma is a satisfiability control only and is not used by `AARule_holds`, whose `Bnd` hypotheses are discharged directly
by `base_gt_ja` and `leg_gt_jc` in `LaczFormalALFinal`. -/
theorem a_canon_bnd (D : CongruentDissection N) (e f M : ℕ) (he : 1 ≤ e) (hef : e < f)
    (hcop : Nat.Coprime e f) (hM : 1 ≤ M)
    (hsa : sideOpp D.model 0 = (ta e f : ℝ)) (hsb : sideOpp D.model 1 = (tb e f : ℝ))
    (hsc : sideOpp D.model 2 = (tc e f : ℝ))
    {p q r : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hbase : dist (D.target.pts p) (D.target.pts q) = ((M * e * (3 * f ^ 2 - e ^ 2) : ℕ) : ℝ))
    (hlegL : dist (D.target.pts p) (D.target.pts r) = ((M * f ^ 3 : ℕ) : ℝ))
    (hlegR : dist (D.target.pts q) (D.target.pts r) = ((M * f ^ 3 : ℕ) : ℝ))
    (hori : 0 < cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p)) :
    ∃ (α β γ : ℝ) (S : BandSetup D e f α β γ p q r), (AF.canon S hori (canon_hb_A S hori)).Bnd (f - 1) := by
  have S := BandSetup.of_dims D e f M he hef hcop hM hsa hsb hsc hpq hpr hqr hbase hlegL hlegR
  refine ⟨_, _, _, S, ?_, ?_⟩
  · show ((f - 1 : ℕ) : ℝ) < dist (D.target.pts p) (D.target.pts q) / (ta e f : ℝ)
    rw [lt_div_iff₀ (AF.ta_pos S), hbase]
    exact_mod_cast (by
      have := base_gt_ja e f M (f - 1) he hef hM le_rfl
      rw [← Nat.cast_mul] at this
      exact_mod_cast this)
  · show ((f - 1 : ℕ) : ℝ) < dist (D.target.pts p) (D.target.pts r) / (tc e f : ℝ)
    rw [lt_div_iff₀ (LFrame.tc_pos S), hlegL]
    exact leg_gt_jc e f M (f - 1) hM le_rfl (by omega)

#print axioms a_canon_bnd

end Erdos634.LaczAL

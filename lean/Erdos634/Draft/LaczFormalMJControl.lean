import Erdos634.Draft.LaczFormalMJFinal
import Erdos634.Draft.UniformThreshold
import Erdos634.Draft.ThmDRunSetup
import Erdos634.Draft.LaczFormalUDims

/-!
# Non-vacuity control for the rule `M(j)` (audit room `band_gaps_2026-10-21`)

Erdős #634, base-`β` band.  This file proves NOTHING new about #634; it exercises the hypothesis package of
`mj_oriented`, `walk_noMJ`, `walk_noMJm`, `MRule_holds` on GENUINE dissections (the seed tilings
`betaTilable_self`, e.g. the kernel-checked 207-tiling of `T_3(2,3)`), to show the hypotheses are satisfiable.
Credit: AI assistant (items of the band program), Beeson–Roșu, Beeson, Laczkovich, Paliy, Zhang.  Axiom-clean; no `sorry`.
-/

namespace Erdos634.LaczMJ

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Walk
  Erdos634.LaczJunction.Grammar Erdos634.Draft.UniformThreshold Erdos634.Draft.LaczFormal.Graph
  Erdos634.BaseBetaTargetCoord Erdos634.Draft.FDBBaseBetaE1

variable {N : ℕ}

/-- **The lattice-frame norm identity `|v − e0| = b` follows from the geometry of the target alone.**  In a band
setting (angle `β` at `A_p` between the base and the left leg, model tile with `β` between its sides `a` and `c`),
the points at distance `a` along the left leg and `c` along the base are at distance `b` (law of cosines in the
model and in the target).  So `LFrame.canon` needs no token data. -/
theorem canon_hb {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r)
    (hori : 0 < cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p)) :
    ‖((ta e f : ℝ) / dist (D.target.pts p) (D.target.pts r)) • (D.target.pts r - D.target.pts p) -
      ((tc e f : ℝ) / dist (D.target.pts p) (D.target.pts q)) • (D.target.pts q - D.target.pts p)‖ = (tb e f : ℝ) := by
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
  have hsq : ‖((ta e f : ℝ) / dist P R) • (R - P) - ((tc e f : ℝ) / dist P Q) • (Q - P)‖ ^ 2 = (tb e f : ℝ) ^ 2 := by
    rw [norm_sub_sq_real, norm_smul, norm_smul, inner_smul_left, inner_smul_right, hna, hnr,
      Real.norm_of_nonneg (div_nonneg ha.le hpr.le), Real.norm_of_nonneg (div_nonneg hc.le hpq.le)]
    simp only [conj_trivial]
    rw [real_inner_comm, hinner, hcosβ]
    field_simp
    ring
  have h0 : 0 ≤ ‖((ta e f : ℝ) / dist P R) • (R - P) - ((tc e f : ℝ) / dist P Q) • (Q - P)‖ := norm_nonneg _
  nlinarith [hsq, h0, hb]

#print axioms canon_hb

/-- Legs and base are long enough for the rule `M(j)`, `j ≤ e`, in any target `T_M(e,f)` with `M ≥ 2`. -/
theorem legs_long (e f M : ℕ) (he : 1 ≤ e) (hef : e < f) (hM : 1 ≤ M) (j : ℕ) (hje : j ≤ e) :
    j * ta e f < M * f ^ 3 := by
  unfold ta
  have h1 : j * (e * f) ≤ e * (e * f) := Nat.mul_le_mul_right _ hje
  have h2 : e * (e * f) < f ^ 3 := by
    have h0 : e * e < f * f := Nat.mul_self_lt_mul_self hef
    have hf : 0 < f := by omega
    calc e * (e * f) = (e * e) * f := by ring
      _ < (f * f) * f := Nat.mul_lt_mul_of_pos_right h0 hf
      _ = f ^ 3 := by ring
  have h3 : f ^ 3 ≤ M * f ^ 3 := Nat.le_mul_of_pos_left _ (by omega)
  omega

/-- The conclusion of `control_of_dims`, as a named `Prop`: band setting, lattice frame, base walk with its step data,
lattice points of the frame in the target, and the rule `M(j)` for the walk (`1 ≤ j ≤ e`). -/
def MJPackage (D : CongruentDissection N) (e f : ℕ) (p q r : Fin 3) : Prop :=
    ∃ (S : BandSetup D e f (modelAlpha (e : ℝ) f) (modelBeta (e : ℝ) f)
        (2 * modelAlpha (e : ℝ) f + modelBeta (e : ℝ) f) p q r)
      (F : LFrame D e f (modelAlpha (e : ℝ) f) (modelBeta (e : ℝ) f)
        (2 * modelAlpha (e : ℝ) f + modelBeta (e : ℝ) f) p q r)
      (L : List (Fin N × Plane × Plane)),
      F.S = S ∧
      F.pt 1 0 ∈ openSegment ℝ (D.target.pts p) (D.target.pts q) ∧
      F.pt 0 1 ∈ openSegment ℝ (D.target.pts p) (D.target.pts r) ∧
      F.pt 1 1 ∈ interior D.target.carrier ∧
      WalkT D.toDissection (toV2 (D.target.pts q - D.target.pts p)) (D.target.pts p) (D.target.pts q) L ∧
      (∀ x ∈ L, StepData D e f (modelAlpha (e : ℝ) f) (modelBeta (e : ℝ) f)
        (2 * modelAlpha (e : ℝ) f + modelBeta (e : ℝ) f) p q x) ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ e →
        ¬ winM j (L.map (elemTok D (modelAlpha (e : ℝ) f) (modelBeta (e : ℝ) f))) ∧
        ¬ winMm j (L.map (elemTok D (modelAlpha (e : ℝ) f) (modelBeta (e : ℝ) f)))

/-- **The hypothesis package of `walk_noMJ` / `mj_holds` is satisfiable on a genuine dissection.**  Given any
`CongruentDissection` with the dimensions of `T_M(e,f)`, `e ≥ 2`, `M ≥ 2`, oriented counterclockwise: the band setting `S`,
a lattice frame `F` (LFrame, built by `LFrame.canon` from `canon_hb`), the base walk `L` with its `StepData` for every
entry, and the conclusion of the rule `M(j)` for `1 ≤ j ≤ e`.  NOTE: no band inequality and no `a`-token hypothesis is used. -/
theorem control_of_dims (D : CongruentDissection N) (e f M : ℕ) (he : 2 ≤ e) (hef : e < f)
    (hcop : Nat.Coprime e f) (hM2 : 2 ≤ M)
    (hsa : sideOpp D.model 0 = (ta e f : ℝ)) (hsb : sideOpp D.model 1 = (tb e f : ℝ))
    (hsc : sideOpp D.model 2 = (tc e f : ℝ))
    {p q r : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hbase : dist (D.target.pts p) (D.target.pts q) = ((M * e * (3 * f ^ 2 - e ^ 2) : ℕ) : ℝ))
    (hlegL : dist (D.target.pts p) (D.target.pts r) = ((M * f ^ 3 : ℕ) : ℝ))
    (hlegR : dist (D.target.pts q) (D.target.pts r) = ((M * f ^ 3 : ℕ) : ℝ))
    (hori : 0 < cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p)) :
    MJPackage D e f p q r := by
  classical
  unfold MJPackage
  have S := BandSetup.of_dims D e f M (by omega) hef hcop (by omega) hsa hsb hsc hpq hpr hqr hbase hlegL hlegR
  have hori' : 0 < crs (toV2 (D.target.pts q - D.target.pts p)) (toV2 (D.target.pts r - D.target.pts p)) := by
    rw [crs_toV2]; exact hori
  obtain ⟨L, hL, hpar, hnd, hstep⟩ := base_walk S hori'
  set α := modelAlpha (e : ℝ) f
  set β := modelBeta (e : ℝ) f
  set γ := 2 * α + β
  let F := LFrame.canon S hori (canon_hb S hori)
  have hlamR : (2 : ℝ) < F.lam := by
    show (2 : ℝ) < dist (D.target.pts p) (D.target.pts q) / (tc e f : ℝ)
    rw [lt_div_iff₀ (LFrame.tc_pos S), hbase]
    have h1 : 2 * tc e f < M * e * (3 * f ^ 2 - e ^ 2) := by
      unfold tc
      have : e ^ 2 < f ^ 2 := Nat.pow_lt_pow_left hef (by norm_num)
      have h2 : f ^ 2 < 3 * f ^ 2 - e ^ 2 := by omega
      calc 2 * f ^ 2 < 2 * (3 * f ^ 2 - e ^ 2) := by omega
        _ ≤ M * e * (3 * f ^ 2 - e ^ 2) := by
          apply Nat.mul_le_mul_right; nlinarith
    exact_mod_cast h1
  have hmuR : (2 : ℝ) < F.mu := by
    show (2 : ℝ) < dist (D.target.pts p) (D.target.pts r) / (ta e f : ℝ)
    have ha : (0 : ℝ) < ta e f := by exact_mod_cast a_pos e f S.he S.hef
    rw [lt_div_iff₀ ha, hlegL]
    have h1 : 2 * ta e f < M * f ^ 3 := by
      unfold ta
      have : e * f < f ^ 3 := by
        have : e < f ^ 2 := by nlinarith
        calc e * f < f ^ 2 * f := Nat.mul_lt_mul_of_pos_right this (by omega)
          _ = f ^ 3 := by ring
      have h4 : 2 * f ^ 3 ≤ M * f ^ 3 := Nat.mul_le_mul_right _ hM2
      omega
    exact_mod_cast h1
  have hbase' : ∀ m : ℕ, m + 1 ≤ e → ((m + 1 : ℕ) : ℝ) * tc e f < dist (D.target.pts p) (D.target.pts q) := by
    intro m hm
    rw [hbase]
    exact base_gt_jc e f M (m + 1) (by omega) hef hM2 hm
  have hlegs : ∀ m : ℕ, m + 1 ≤ e → ((m + 1 : ℕ) : ℝ) * ta e f < dist (D.target.pts p) (D.target.pts r) ∧
      ((m + 1 : ℕ) : ℝ) * ta e f < dist (D.target.pts q) (D.target.pts r) := by
    intro m hm
    have hr : ((m + 1 : ℕ) : ℝ) * ta e f < ((M * f ^ 3 : ℕ) : ℝ) := by
      exact_mod_cast legs_long e f M (by omega) hef (by omega) (m + 1) hm
    exact ⟨by rw [hlegL]; exact hr, by rw [hlegR]; exact hr⟩
  refine ⟨S, F, L, rfl, F.pt_base_mem one_pos (by linarith), F.pt_leg_mem one_pos (by linarith),
    F.pt_interior one_pos one_pos ?_, hL, hstep, ?_⟩
  · have h1 : 1 / F.lam < 1 / 2 := one_div_lt_one_div_of_lt (by norm_num) hlamR
    have h2 : 1 / F.mu < 1 / 2 := one_div_lt_one_div_of_lt (by norm_num) hmuR
    show 1 / F.lam + 1 / F.mu < 1
    linarith
  · intro j hj1 hje
    obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    exact ⟨walk_noMJ S hje (hbase' m hje) (hlegs m hje).1 hL hstep,
      walk_noMJm S hje (hbase' m hje) (hlegs m hje).2 hL hstep⟩

#print axioms control_of_dims

/-- **Any dissection with the dimensions of `T_M(e,f)` can be oriented counterclockwise** by swapping `p, q`. -/
theorem orient_dims (D : CongruentDissection N) (e f M : ℕ) (he : 2 ≤ e) (hef : e < f) (hM : 1 ≤ M)
    {p q r : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hbase : dist (D.target.pts p) (D.target.pts q) = ((M * e * (3 * f ^ 2 - e ^ 2) : ℕ) : ℝ))
    (hlegL : dist (D.target.pts p) (D.target.pts r) = ((M * f ^ 3 : ℕ) : ℝ))
    (hlegR : dist (D.target.pts q) (D.target.pts r) = ((M * f ^ 3 : ℕ) : ℝ)) :
    ∃ p' q' r' : Fin 3, p' ≠ q' ∧ p' ≠ r' ∧ q' ≠ r' ∧
      dist (D.target.pts p') (D.target.pts q') = ((M * e * (3 * f ^ 2 - e ^ 2) : ℕ) : ℝ) ∧
      dist (D.target.pts p') (D.target.pts r') = ((M * f ^ 3 : ℕ) : ℝ) ∧
      dist (D.target.pts q') (D.target.pts r') = ((M * f ^ 3 : ℕ) : ℝ) ∧
      0 < cross (D.target.pts q' - D.target.pts p') (D.target.pts r' - D.target.pts p') := by
  have hne0 := dims_cross_ne D e f M he hef hM hbase hlegL hlegR
  rcases lt_or_gt_of_ne hne0 with hneg | hpos
  · refine ⟨q, p, r, hpq.symm, hqr, hpr, by rw [dist_comm]; exact hbase, hlegR, hlegL, ?_⟩
    have : cross (D.target.pts p - D.target.pts q) (D.target.pts r - D.target.pts q) =
        - cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p) := by
      simp only [cross, PiLp.sub_apply]; ring
    rw [this]; linarith
  · exact ⟨p, q, r, hpq, hpr, hqr, hbase, hlegL, hlegR, hpos⟩

/-- **The package on every genuine tiling of `T_M(e,f)` with `M ≥ 2`, `e ≥ 2`.**  `BetaTilable e f M` is the existence
of a `CongruentDissection` of the base-`β` target by the tile; by `betaTilable_self` it holds at `M = f` for every
coprime `e < f` (the seed tilings; `M = 3, (e,f) = (2,3)` is the kernel-checked 207-tiling,
`betaTilable_2_3_three`).  Conclusion: after relabelling the model, `D` has the right sides, and every
hypothesis of `walk_noMJ` is satisfied, with the rule `M(j)` as output. -/
theorem control_beta_tilable (e f M : ℕ) (he : 2 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f) (hM2 : 2 ≤ M)
    (hT : BetaTilable e f M) :
    ∃ (N : ℕ) (D : CongruentDissection N) (p q r : Fin 3), p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
      sideOpp D.model 0 = (ta e f : ℝ) ∧ sideOpp D.model 1 = (tb e f : ℝ) ∧ sideOpp D.model 2 = (tc e f : ℝ) ∧
      dist (D.target.pts p) (D.target.pts q) = ((M * e * (3 * f ^ 2 - e ^ 2) : ℕ) : ℝ) ∧
      dist (D.target.pts p) (D.target.pts r) = ((M * f ^ 3 : ℕ) : ℝ) ∧
      dist (D.target.pts q) (D.target.pts r) = ((M * f ^ 3 : ℕ) : ℝ) ∧
      0 < cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p) ∧
      MJPackage D e f p q r := by
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
    control_of_dims D' e f M he hef hcop hM2 hs0 hs1 hs2 hpq hpr hqr hb' hl' hr' hori⟩

#print axioms control_beta_tilable

/-- **The 207-tiling.**  `(e,f,M) = (2,3,3)`: the whole package. -/
theorem control_207 :
    ∃ (N : ℕ) (D : CongruentDissection N) (p q r : Fin 3), p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
      sideOpp D.model 0 = (ta 2 3 : ℝ) ∧ sideOpp D.model 1 = (tb 2 3 : ℝ) ∧ sideOpp D.model 2 = (tc 2 3 : ℝ) ∧
      dist (D.target.pts p) (D.target.pts q) = ((3 * 2 * (3 * 3 ^ 2 - 2 ^ 2) : ℕ) : ℝ) ∧
      dist (D.target.pts p) (D.target.pts r) = ((3 * 3 ^ 3 : ℕ) : ℝ) ∧
      dist (D.target.pts q) (D.target.pts r) = ((3 * 3 ^ 3 : ℕ) : ℝ) ∧
      0 < cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p) ∧
      MJPackage D 2 3 p q r :=
  control_beta_tilable 2 3 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) betaTilable_2_3_three

#print axioms control_207

/-- **Every seed tiling** (`M = f`, every coprime `2 ≤ e < f`, `betaTilable_self`). -/
theorem control_seed (e f : ℕ) (he : 2 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f) :
    ∃ (N : ℕ) (D : CongruentDissection N) (p q r : Fin 3), p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
      0 < cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p) ∧
      MJPackage D e f p q r :=
  let ⟨N, D, p, q, r, a, b, c, _, _, _, _, _, _, h, hP⟩ :=
    control_beta_tilable e f f he hef hcop (by omega) (betaTilable_self (by omega) hef)
  ⟨N, D, p, q, r, a, b, c, h, hP⟩

#print axioms control_seed

/-- **Where the genuine tilings leave the band.**  The hypotheses of `MRule e f` that these tilings do NOT satisfy:
`hhi : 2 M e < f + e` fails for every `M ≥ f` (the tilings exist exactly outside the band, `M ≥ f`), while
`hlo : f ≤ 2 M e` holds.  Nothing else about the dimensions fails. -/
theorem seed_outside_band (e f M : ℕ) (he : 1 ≤ e) (hef : e < f) (hMf : f ≤ M) :
    f ≤ 2 * M * e ∧ ¬ (2 * M * e < f + e) := by
  constructor <;> nlinarith

/-- The `207`-tiling: `a < b` fails too (`a = 6`, `b = 5`), another hypothesis of `MRule` it does not meet. -/
theorem control_207_not_a_lt_b : ¬ (ta 2 3 < tb 2 3) := by
  unfold ta tb; norm_num


/-! ## G2: the default branch of `tokOf` is never used -/

section G2
open Erdos634.LaczJunction.Walk

/-- **`tokOf`'s default (`(a,A)`, `(b,B)`, `(c,G) ↦ cBA`) is never reached by a genuine step.**  For a step `(i, U, U')`
as in `elem_baseTok`, the pair (side read from the length, corner read from the angle at `U`) is one of the six
legitimate pairs.  Proof: if it were a default pair, `elemTok = cBA`; but `elem_baseTok` gives `|UU'| = c` and
`angle at U = β`, contradicting `|UU'| ∈ {a, b}` resp. `angle ∉ {α, β}`. -/
theorem elemTok_default_unused {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r) (i : Fin N) (kk fi g : Fin 3) (hfk : fi ≠ kk) (hgk : g ≠ kk)
    (hgf : g ≠ fi) {U U' Z : Plane} (hU : (D.tile i).pts kk = U) (hU' : (D.tile i).pts fi = U')
    (hZ : (D.tile i).pts g = Z)
    (hm1 : U ∈ segment ℝ (D.target.pts p) (D.target.pts q))
    (hm2 : U' ∈ segment ℝ (D.target.pts p) (D.target.pts q))
    (hord : dist (D.target.pts p) U < dist (D.target.pts p) U') :
    ¬ ((sideOfLen (sideOpp D.model 0) (sideOpp D.model 1) (dist U U') = .a ∧
          cornerOfAng α β ((D.tile i).localAngle U) = .A) ∨
       (sideOfLen (sideOpp D.model 0) (sideOpp D.model 1) (dist U U') = .b ∧
          cornerOfAng α β ((D.tile i).localAngle U) = .B) ∨
       (sideOfLen (sideOpp D.model 0) (sideOpp D.model 1) (dist U U') = .c ∧
          cornerOfAng α β ((D.tile i).localAngle U) = .G)) := by
  classical
  obtain ⟨hαβ, hβγ, hαγ, -, -, -⟩ := BandSetup.distinct S
  obtain ⟨hab, hbc, hac⟩ := BandSetup.dist3 S
  have B := elem_baseTok S i kk fi g hfk hgk hgf hU hU' hZ hm1 hm2 hord
  have htok : elemTok D α β (i, U, U') =
      tokOf (sideOfLen (sideOpp D.model 0) (sideOpp D.model 1) (dist U U'))
        (cornerOfAng α β ((D.tile i).localAngle U)) := rfl
  intro h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- (a, A) : tokOf = cBA, so |UU'| = c, but sideOfLen = a forces |UU'| = a
    rw [h1, h2] at htok
    have htok' : elemTok D α β (i, U, U') = Tok.cBA := htok
    have hl := B.length
    rw [htok'] at hl
    simp only [Tok.side, lenOf] at hl
    have hxa : dist U U' = sideOpp D.model 0 := by
      unfold sideOfLen at h1
      by_contra hne; rw [if_neg hne] at h1; split_ifs at h1
    rw [S.hsa] at hxa
    exact hac (hxa.symm.trans hl)
  · rw [h1, h2] at htok
    have htok' : elemTok D α β (i, U, U') = Tok.cBA := htok
    have hl := B.length
    rw [htok'] at hl
    simp only [Tok.side, lenOf] at hl
    have hxb : dist U U' = sideOpp D.model 1 := by
      unfold sideOfLen at h1
      by_cases hA : dist U U' = sideOpp D.model 0
      · rw [if_pos hA] at h1; exact absurd h1 (by decide)
      · rw [if_neg hA] at h1
        by_contra hne; rw [if_neg hne] at h1; exact absurd h1 (by decide)
    rw [S.hsb] at hxb
    exact hbc (hxb.symm.trans hl)
  · rw [h1, h2] at htok
    have htok' : elemTok D α β (i, U, U') = Tok.cBA := htok
    have hang := B.left_angle
    rw [htok'] at hang
    simp only [Tok.left, angOf] at hang
    have := cornerOfAng_B (α := α) (β := β) (θ := (D.tile i).localAngle U) (by rw [hang]; exact hαβ.symm) hang
    rw [this] at h2
    exact absurd h2 (by decide)

#print axioms elemTok_default_unused

end G2

end Erdos634.LaczMJ

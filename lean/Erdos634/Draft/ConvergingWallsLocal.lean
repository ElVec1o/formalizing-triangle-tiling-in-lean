-- Draft/ConvergingWallsLocal.lean — the LOCAL steps of CW(ℓ_j, m_k), the converging walls
-- ((private working notes, not included) §§0–4, review record R1–R3; proof_H_empty.md §5.9), for REAL
-- `m = 1` dissections in the apex frame, on the `Λ₂` lattice `iV + tP′`.  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
--
-- Build (scratch oleans; never .lake): LemmaGCornerReal olean in $S, then
--   lake env bash -c 'LEAN_PATH=$S:$LEAN_PATH lean Erdos634/Draft/ConvergingWallsLocal.lean'
--
-- LAYOUT.  §1 the `Λ₂` points `Q2 i t = iV + tP′` (in the `Λ₃` coordinates `Lam` of
-- Draft/RowWallReal.lean: `Q2 i t = Λ(i(1 + c/b) + t, −i)`), the cells `U(i,t) = T₂ + iV + tP′ = T2c`
-- and `D(i,t) = K + iV + tP′ = Kc` (Draft/LemmaGADReal.lean) and the swap `Sw`; interior points and
-- `O2`.  §2 the three line families: `ℓ_t` (functional `ellF`, band side = away from `r`), `m_i`
-- (`rho`, r-side = away from `A`), `AD_n` (`adF`, far side).  §3 two generic trace-covering lemmas
-- (`wall_lattice`, `start_gen`).  §4 **(B1)** the band straddle on `ℓ_j` (`band_str`, Lemma A,
-- **m = 1**).  §5 **(B2)** the r-side straddle on `m_k` (`r_str`, A2, **m = 1**).  §6 **Step A**, the
-- slot dichotomy (`slot2`: the residual `α` at `X_i^N` is `U` or the swap; no `m = 1` input).
-- §7 counting (`no_two_straight`).  The far word, the half-turn march and the induction are in
-- Draft/ConvergingWallsReal.lean.
import Erdos634.Draft.LemmaGCornerReal

namespace Erdos634.Draft.RowWallReal

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.HalfTurnR3R4
open Erdos634.Draft.HalfTurnR3R4Glue Erdos634.Draft.CornerAdjacency
open Erdos634.Draft.HalfTurnR3R4Order Erdos634.Draft.MirrorStripR2Real
open Erdos634.Draft.HalfTurnR4Real

variable {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ}
variable (F : HFrame D e f α β γ)

/-! ## §1 The `Λ₂` lattice -/

/-- The `Λ₂` point `iV + tP′ = A + i·(V − A) + t·(P′ − A)` (`V − A = vec (1 + c/b) (−1)`,
`P′ − A = vec 1 0`); real `i, t` parametrize the lines `ℓ_t` (fixed `t`), `m_i` (fixed `i`) and
`AD_n` (`i + t = n`). -/
noncomputable def Q2 (F : HFrame D e f α β γ) (i t : ℝ) : Plane :=
  Lam F (i * (1 + cb e f) + t) (-i)

/-- `b/c`. -/
noncomputable def bcr (e f : ℕ) : ℝ := ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2

include F in
theorem bcr_facts : 0 < bcr e f ∧ bcr e f < 1 ∧ bcr e f * cb e f = 1 := by
  obtain ⟨-, hb0, hc0, hbc, -⟩ := consts F
  exact ⟨div_pos hb0 hc0, (div_lt_one hc0).mpr hbc, bc_cb F⟩

theorem Q2_add_eq {i t di dt p q : ℝ} (hp : di * (1 + cb e f) + dt = p) (hq : -di = q) :
    Q2 F i t + vec F p q = Q2 F (i + di) (t + dt) := by
  simp only [Q2]; apply Lam_add_eq F
  · rw [← hp]; ring
  · rw [← hq]; ring

theorem Q2_sub_eq {i t i' t' p q : ℝ} (hp : (i - i') * (1 + cb e f) + (t - t') = p)
    (hq : -(i - i') = q) : Q2 F i t - Q2 F i' t' = vec F p q := by
  simp only [Q2]; apply Lam_sub_eq F
  · rw [← hp]; ring
  · rw [← hq]; ring

theorem Q2_inj (FC : ApexPlacement.FrameCoords F) {i t i' t' : ℝ} (h : Q2 F i t = Q2 F i' t') :
    i = i' ∧ t = t' := by
  obtain ⟨h1, h2⟩ := Lam_inj F FC h
  have hi : i = i' := by linarith
  subst hi
  exact ⟨rfl, by linarith⟩

theorem Q2_ne (FC : ApexPlacement.FrameCoords F) {i t i' t' : ℝ} (h : i ≠ i' ∨ t ≠ t') :
    Q2 F i t ≠ Q2 F i' t' := by
  intro h'
  obtain ⟨h1, h2⟩ := Q2_inj F FC h'
  rcases h with h | h
  · exact h h1
  · exact h h2

/-- `U(i,t) = T₂ + iV + tP′ = (iV+tP′[α], (i+1)V+tP′[β], iV+(t+1)P′[γ])`. -/
theorem U_eq (FC : ApexPlacement.FrameCoords F) (i t : ℕ) :
    T2c F i t = {Q2 F i t, Q2 F ((i : ℝ) + 1) t, Q2 F i ((t : ℝ) + 1)} := by
  have h3 : Lam F ((i : ℝ) * (1 + cb e f) + t + 1) (-(i : ℝ)) = Q2 F i ((t : ℝ) + 1) := by
    simp only [Q2]; congr 1; ring
  rw [T2c_eq F FC, h3]; rfl

/-- `D(i,t) = K + iV + tP′ = ((i+1)V+tP′[γ], iV+(t+1)P′[β], (i+1)V+(t+1)P′[α])`. -/
theorem D_eq (FC : ApexPlacement.FrameCoords F) (i t : ℕ) :
    Kc F i t = {Q2 F ((i : ℝ) + 1) t, Q2 F i ((t : ℝ) + 1), Q2 F ((i : ℝ) + 1) ((t : ℝ) + 1)} := by
  have h2 : Lam F ((i : ℝ) * (1 + cb e f) + t + 1) (-(i : ℝ)) = Q2 F i ((t : ℝ) + 1) := by
    simp only [Q2]; congr 1; ring
  have h3 : Lam F (((i : ℝ) + 1) * (1 + cb e f) + t + 1) (-((i : ℝ) + 1))
      = Q2 F ((i : ℝ) + 1) ((t : ℝ) + 1) := by
    simp only [Q2]; congr 1; ring
  rw [Kc_eq F FC, h2, h3]; rfl

theorem dQ_a (i t : ℝ) : dist (Q2 F (i + 1) t) (Q2 F i (t + 1)) = (e : ℝ) * f := by
  rw [dist_eq_norm, Q2_sub_eq F (p := cb e f) (q := -1) (by ring) (by ring), norm_VP]

theorem dQ_b (i t : ℝ) : dist (Q2 F i (t + 1)) (Q2 F i t) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
  rw [dist_eq_norm, Q2_sub_eq F (p := 1) (q := 0) (by ring) (by ring), norm_vec_10]

theorem dQ_c (i t : ℝ) : dist (Q2 F i t) (Q2 F (i + 1) t) = (f : ℝ) ^ 2 := by
  rw [dist_eq_norm, Q2_sub_eq F (p := -(1 + cb e f)) (q := 1) (by ring) (by ring),
    show vec F (-(1 + cb e f)) 1 = - vec F (1 + cb e f) (-1) by rw [vec_neg]; norm_num,
    norm_neg, norm_V]

/-- Angles of `U(i,t)`: `α` at `iV+tP′`, `β` at `(i+1)V+tP′`, `γ` at `iV+(t+1)P′`. -/
theorem U_angles (FC : ApexPlacement.FrameCoords F) {i t : ℕ} {z : Fin N}
    (hz : Set.range (D.tile z).pts = T2c F i t) :
    (D.tile z).localAngle (Q2 F i t) = α ∧ (D.tile z).localAngle (Q2 F ((i : ℝ) + 1) t) = β ∧
      (D.tile z).localAngle (Q2 F i ((t : ℝ) + 1)) = γ := by
  rw [U_eq F FC] at hz
  have r2 : Set.range (D.tile z).pts = {Q2 F ((i : ℝ) + 1) t, Q2 F i ((t : ℝ) + 1), Q2 F i t} := by
    rw [hz]; ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have r3 : Set.range (D.tile z).pts = {Q2 F i ((t : ℝ) + 1), Q2 F i t, Q2 F ((i : ℝ) + 1) t} := by
    rw [hz]; ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  exact ⟨(angle_of_range F hz).1 (dQ_a F (i : ℝ) (t : ℝ)),
    (angle_of_range F r2).2.1 (dQ_b F (i : ℝ) (t : ℝ)),
    (angle_of_range F r3).2.2 (dQ_c F (i : ℝ) (t : ℝ))⟩

/-- Angles of `D(i,t)`: `γ` at `(i+1)V+tP′`, `β` at `iV+(t+1)P′`, `α` at `(i+1)V+(t+1)P′`. -/
theorem D_angles (FC : ApexPlacement.FrameCoords F) {i t : ℕ} {z : Fin N}
    (hz : Set.range (D.tile z).pts = Kc F i t) :
    (D.tile z).localAngle (Q2 F ((i : ℝ) + 1) t) = γ ∧
      (D.tile z).localAngle (Q2 F i ((t : ℝ) + 1)) = β ∧
      (D.tile z).localAngle (Q2 F ((i : ℝ) + 1) ((t : ℝ) + 1)) = α := by
  rw [D_eq F FC] at hz
  have r2 : Set.range (D.tile z).pts = {Q2 F i ((t : ℝ) + 1), Q2 F ((i : ℝ) + 1) ((t : ℝ) + 1),
      Q2 F ((i : ℝ) + 1) t} := by
    rw [hz]; ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have r3 : Set.range (D.tile z).pts = {Q2 F ((i : ℝ) + 1) ((t : ℝ) + 1), Q2 F ((i : ℝ) + 1) t,
      Q2 F i ((t : ℝ) + 1)} := by
    rw [hz]; ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  exact ⟨(angle_of_range F hz).2.2 (dQ_c F (i : ℝ) ((t : ℝ) + 1)),
    (angle_of_range F r2).2.1 (dQ_b F ((i : ℝ) + 1) (t : ℝ)),
    (angle_of_range F r3).1 (dQ_a F (i : ℝ) (t : ℝ))⟩

/-- Lattice points `iV + tP′` with `i, t ≥ 0`, `i + t > 0` and depth `tb + ic < fb` are interior. -/
theorem Q2_interior (FC : ApexPlacement.FrameCoords F) {i t : ℝ} (hi : 0 ≤ i) (ht : 0 ≤ t)
    (hit : 0 < i + t) (hlt : t + i * cb e f < f) : Q2 F i t ∈ interior D.target.carrier := by
  obtain ⟨hcb0, -⟩ := cb_pos F
  have hpoly := cb_poly F
  obtain ⟨-, hb0, -, -, -⟩ := consts F
  have heR : (2 : ℝ) ≤ e := by exact_mod_cast F.he
  have hefR : (e : ℝ) + 2 ≤ f := by exact_mod_cast F.hef
  have h2 : 0 < 2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have hq : 0 < (f : ℝ) ^ 4 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) := div_pos (pow_pos (f_pos' F) 4) hb0
  apply Lam_interior2 F FC
  · nlinarith
  · have : (i * (1 + cb e f) + t) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
        + (-i) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
        = i * ((f : ℝ) ^ 4 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) + t * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by
      rw [← hpoly]; ring
    rw [this]
    have hm := lt_min hq h2
    nlinarith [mul_le_mul_of_nonneg_left (min_le_left ((f : ℝ) ^ 4 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))
      (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)) hi, mul_le_mul_of_nonneg_left (min_le_right
      ((f : ℝ) ^ 4 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)) ht,
      mul_pos hit hm]
  · have : i * (1 + cb e f) + t + -i = t + i * cb e f := by ring
    linarith

/-- A lattice point of the target has depth `tb + ic ≤ fb`. -/
theorem Q2_le (FC : ApexPlacement.FrameCoords F) {i t : ℝ} (h : Q2 F i t ∈ D.target.carrier) :
    t + i * cb e f ≤ f := by
  by_contra hc
  push Not at hc
  exact Lam_out F FC (by have : i * (1 + cb e f) + t + -i = t + i * cb e f := by ring
                         linarith) h

include F in
/-- **O2**: `tb + ic ≠ fb` for `i ≥ 1` (mod `f`: `f ∣ t e²`, so `f ∣ t`; then `t = 0` and
`i f = f² − e²`, so `f ∣ e²`, against `gcd(e, f) = 1`). -/
theorem O2 (i t : ℕ) (hi : 1 ≤ i) : (t : ℝ) + (i : ℝ) * cb e f ≠ f := by
  intro h
  obtain ⟨-, hb0, hc0, -, -⟩ := consts F
  have hf4 : 4 ≤ f := by have := F.he; have := F.hef; omega
  have h' : (t : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) + (i : ℝ) * (f : ℝ) ^ 2
      = (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by
    rw [cb] at h
    have hb0' := hb0.ne'
    field_simp at h
    linarith
  have hZ : (t : ℤ) * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) + (i : ℤ) * (f : ℤ) ^ 2
      = (f : ℤ) * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) := by exact_mod_cast h'
  have hcop : IsCoprime (f : ℤ) ((e : ℤ) ^ 2) :=
    (Nat.isCoprime_iff_coprime.mpr F.hco.symm).pow_right
  have hdvd : (f : ℤ) ∣ (t : ℤ) * (e : ℤ) ^ 2 :=
    ⟨(t : ℤ) * f + i * f - ((f : ℤ) ^ 2 - (e : ℤ) ^ 2), by linear_combination (-1 : ℤ) * hZ⟩
  obtain ⟨s, hs⟩ := hcop.dvd_of_dvd_mul_right hdvd
  have hf0 : (0 : ℤ) < f := by exact_mod_cast (show 0 < f by omega)
  have hbZ : (0 : ℤ) < (f : ℤ) ^ 2 - (e : ℤ) ^ 2 := by
    have : (e : ℤ) + 2 ≤ f := by exact_mod_cast F.hef
    have : (2 : ℤ) ≤ e := by exact_mod_cast F.he
    nlinarith
  have hi' : (1 : ℤ) ≤ i := by exact_mod_cast hi
  have ht0 : (0 : ℤ) ≤ t := by positivity
  rw [hs] at hZ ht0
  have hs0 : 0 ≤ s := by
    by_contra hneg; push Not at hneg; nlinarith
  have hs1 : s < 1 := by
    by_contra hge; push Not at hge
    have h1 : (f : ℤ) * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) * 1 ≤ (f : ℤ) * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) * s :=
      mul_le_mul_of_nonneg_left hge (le_of_lt (mul_pos hf0 hbZ))
    have h2 : (0 : ℤ) < (i : ℤ) * (f : ℤ) ^ 2 := by positivity
    nlinarith
  have hs00 : s = 0 := by omega
  subst hs00
  have h3 : (f : ℤ) * ((i : ℤ) * f - ((f : ℤ) ^ 2 - (e : ℤ) ^ 2)) = 0 := by linear_combination hZ
  rcases mul_eq_zero.mp h3 with h4 | h4
  · omega
  · have hfe : (f : ℤ) ∣ (e : ℤ) ^ 2 * 1 := ⟨(f : ℤ) - i, by linear_combination h4⟩
    have := hcop.dvd_of_dvd_mul_left hfe
    have : (f : ℤ) ≤ 1 := Int.le_of_dvd one_pos this
    omega

/-- A lattice point `iV + tP′` (`i ≥ 1`) of the target is interior (`Q2_le`, `O2`). -/
theorem Q2_int_of_mem (FC : ApexPlacement.FrameCoords F) (i t : ℕ) (hi : 1 ≤ i)
    (h : Q2 F i t ∈ D.target.carrier) : Q2 F i t ∈ interior D.target.carrier := by
  have h1 := Q2_le F FC h
  have h2 := O2 F i t hi
  have hiR : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  exact Q2_interior F FC (by linarith) ht0 (by linarith) (lt_of_le_of_ne h1 h2)

/-- The band swap at `iV + tP′`: `α` there, `b` along `V − A` (on `ℓ_t`), `c` along `w` (on `m_i`). -/
noncomputable def Sw (F : HFrame D e f α β γ) (i t : ℝ) : Set Plane :=
  {Q2 F i t, Q2 F (i + bcr e f) t, Q2 F i (t + cb e f)}

/-! ## §2 The three line families -/

/-- `ellF = col + (1 + c/b)·rho`: constant on the lines `ℓ_t = {ellF = ellF A + t}` (direction
`V − A`). -/
noncomputable def ellF (F : HFrame D e f α β γ) : Plane →ₗ[ℝ] ℝ := col F + (1 + cb e f) • rho F

theorem ellF_vec (FC : ApexPlacement.FrameCoords F) (p q : ℝ) :
    ellF F (vec F p q) = p + (1 + cb e f) * q := by
  simp only [ellF, LinearMap.add_apply, LinearMap.smul_apply, col_vec F FC, rho_vec F FC,
    smul_eq_mul]

theorem ellF_Q2 (FC : ApexPlacement.FrameCoords F) (i t : ℝ) :
    ellF F (Q2 F i t) = ellF F F.A + t := by
  rw [Q2, Lam, map_add, ellF_vec F FC]; ring

theorem ellF_ne (FC : ApexPlacement.FrameCoords F) : ellF F ≠ 0 := by
  intro h; have := ellF_vec F FC 1 0; rw [h, LinearMap.zero_apply] at this; norm_num at this

theorem rho_Q2 (FC : ApexPlacement.FrameCoords F) (i t : ℝ) :
    rho F (Q2 F i t) = rho F F.A - i := by
  rw [Q2, rho_Lam F FC]; ring

theorem adF_Q2 (FC : ApexPlacement.FrameCoords F) (i t : ℝ) :
    adF F (Q2 F i t) = adF F F.A + (i + t) := by
  rw [Q2, adF_Lam F FC]; ring

/-- The band side of `ℓ_t` (away from `r` and `A`): edges on `ℓ_t` whose tile lies in
`{ellF ≥ ellF A + t}`. -/
noncomputable def bandChain (F : HFrame D e f α β γ) (t : ℝ) : Finset (Fin N × Fin 3) :=
  D.toDissection.lineChain (-(ellF F)) (-(ellF F F.A + t))

/-- `y` is straddled from the band side of `ℓ_t`. -/
def BStr (F : HFrame D e f α β γ) (t : ℝ) (y : Plane) : Prop :=
  TraceCovering.Straddled D.toDissection (-(ellF F)) (-(ellF F F.A + t)) y

/-- The r-side of `m_i` (away from `A`): edges on `m_i` whose tile lies in `{rho ≤ rho A − i}`. -/
noncomputable def rsChain (F : HFrame D e f α β γ) (i : ℝ) : Finset (Fin N × Fin 3) :=
  D.toDissection.lineChain (rho F) (rho F F.A - i)

/-- `y` is straddled from the r-side of `m_i`. -/
def MStr (F : HFrame D e f α β γ) (i : ℝ) (y : Plane) : Prop :=
  TraceCovering.Straddled D.toDissection (rho F) (rho F F.A - i) y

/-- `y` is straddled from the far side of `AD_n`. -/
def AStr (F : HFrame D e f α β γ) (n : ℝ) (y : Plane) : Prop :=
  TraceCovering.Straddled D.toDissection (-(adF F)) (-(adF F F.A + n)) y

/-- Unit vectors along `ℓ` (`V − A`), `m` (`w`) and `AD` (`V − P′`). -/
noncomputable def uE (F : HFrame D e f α β γ) : Plane := (1 / (f : ℝ) ^ 2) • vec F (1 + cb e f) (-1)
noncomputable def uM (F : HFrame D e f α β γ) : Plane :=
  (1 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) • vec F 1 0
noncomputable def uA (F : HFrame D e f α β γ) : Plane := (1 / ((e : ℝ) * f)) • vec F (cb e f) (-1)

theorem uE_norm : ‖uE F‖ = 1 := by
  obtain ⟨-, -, hc0, -, -⟩ := consts F
  rw [uE, norm_smul, norm_V, Real.norm_of_nonneg (by positivity), one_div_mul_cancel hc0.ne']

theorem uM_norm : ‖uM F‖ = 1 := by
  obtain ⟨-, hb0, -, -, -⟩ := consts F
  rw [uM, norm_smul, norm_vec_10, Real.norm_of_nonneg (by positivity), one_div_mul_cancel hb0.ne']

theorem uA_norm : ‖uA F‖ = 1 := by
  obtain ⟨ha0, -, -, -, -⟩ := consts F
  rw [uA, norm_smul, norm_VP, Real.norm_of_nonneg (by positivity), one_div_mul_cancel ha0.ne']

theorem ellF_uE (FC : ApexPlacement.FrameCoords F) : ellF F (uE F) = 0 := by
  rw [uE, map_smul, ellF_vec F FC]; simp

theorem rho_uM (FC : ApexPlacement.FrameCoords F) : rho F (uM F) = 0 := by
  rw [uM, map_smul, rho_vec F FC]; simp

theorem adF_uA (FC : ApexPlacement.FrameCoords F) : adF F (uA F) = 0 := by
  rw [uA, map_smul, adF_vec F FC]; simp

theorem Q2_uE (i t x : ℝ) : Q2 F i t + x • uE F = Q2 F (i + x / (f : ℝ) ^ 2) t := by
  rw [uE, smul_smul, vec_smul]; simp only [Q2]; apply Lam_add_eq F <;> ring

theorem Q2_uM (i t y : ℝ) :
    Q2 F i t + y • uM F = Q2 F i (t + y / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) := by
  rw [uM, smul_smul, vec_smul]; simp only [Q2]; apply Lam_add_eq F <;> ring

theorem Q2_uA (i t s : ℝ) :
    Q2 F i t + s • uA F = Q2 F (i + s / ((e : ℝ) * f)) (t - s / ((e : ℝ) * f)) := by
  rw [uA, smul_smul, vec_smul]; simp only [Q2]; apply Lam_add_eq F
  · rw [cb]; ring
  · ring

/-! ## §3 Two generic trace-covering lemmas -/

/-- **A lattice wall.**  If for each `k < q` some tile has the two points `X + kL·u`, `X + (k+1)L·u`
among its vertices, the open stretch `(X, X + qL·u)` meets no tile interior (each of its points lies
on an edge: `Dissection.edge_point_not_interior`). -/
theorem wall_lattice {X u : Plane} (hu0 : u ≠ 0) {Lg : ℝ} (hL : 0 < Lg) (q : ℕ)
    (hcells : ∀ k : ℕ, k < q → ∃ iz : Fin N, X + ((k : ℝ) * Lg) • u ∈ Set.range (D.tile iz).pts ∧
      X + (((k : ℝ) + 1) * Lg) • u ∈ Set.range (D.tile iz).pts) :
    ∀ x ∈ Set.Ioo 0 ((q : ℝ) * Lg), ∀ i, X + x • u ∉ interior (D.tile i).carrier := by
  intro x hx i
  have hq0 : 0 ≤ x / Lg := div_nonneg hx.1.le hL.le
  have hk1 : ((⌊x / Lg⌋₊ : ℕ) : ℝ) ≤ x / Lg := Nat.floor_le hq0
  have hk2 : x / Lg < ((⌊x / Lg⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  set k := ⌊x / Lg⌋₊ with hk
  have hkx : (k : ℝ) * Lg ≤ x := by rwa [le_div_iff₀ hL] at hk1
  have hxk : x < ((k : ℝ) + 1) * Lg := by rwa [div_lt_iff₀ hL] at hk2
  have hkT : k < q := by
    have h1 : (k : ℝ) * Lg < (q : ℝ) * Lg := lt_of_le_of_lt hkx hx.2
    exact_mod_cast lt_of_mul_lt_mul_right h1 hL.le
  obtain ⟨iz, hP, hQ⟩ := hcells k hkT
  have hPQ : X + ((k : ℝ) * Lg) • u ≠ X + (((k : ℝ) + 1) * Lg) • u := by
    intro h
    have := TraceCovering.lm_injective hu0 h
    simp only at this
    linarith
  obtain ⟨m, hm⟩ := edge_idx hP hQ hPQ
  have hseg : X + x • u ∈ segment ℝ (X + ((k : ℝ) * Lg) • u) (X + (((k : ℝ) + 1) * Lg) • u) := by
    rw [TraceCovering.segment_param]
    exact ⟨x, ⟨le_trans (min_le_left _ _) hkx, le_trans hxk.le (le_max_right _ _)⟩, rfl⟩
  have hmem : X + x • u ∈ (D.tile iz).edge m := by
    rw [Tri.edge]
    rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact hseg
    · rw [h1, h2, segment_symm]; exact hseg
  exact D.toDissection.edge_point_not_interior hmem i

/-- **The start of a side covering** (generic `start_of_edge`): an edge of the side `lineChain g d`
running from `X` along `u` means no edge of that side has `X` in its relative interior
(`TraceCovering.meet`: two same-side edges share at most a point). -/
theorem start_gen {g f' : Plane →ₗ[ℝ] ℝ} {d c0 : ℝ} {X u : Plane} (hg : g ≠ 0)
    (hgd : ∀ y, g y = d ↔ f' y = c0) (hf : f' ≠ 0) (hX : f' X = c0) (hu : f' u = 0)
    (hu0 : u ≠ 0) {ε : Fin N × Fin 3} (hε : ε ∈ D.toDissection.lineChain g d) {ℓ : ℝ}
    (hℓ : 0 < ℓ) (hedge : (D.tile ε.1).edge ε.2 = segment ℝ (X + (0 : ℝ) • u) (X + ℓ • u)) :
    ¬ TraceCovering.Straddled D.toDissection g d (X + (0 : ℝ) • u) := by
  classical
  have hin := fun y => TraceCovering.mem_edge_iff hgd hf hX hu hu0 hε y
  have hX1 := (hin 0).mp (by rw [hedge]; exact left_mem_segment ℝ _ _)
  have hX2 := (hin ℓ).mp (by rw [hedge]; exact right_mem_segment ℝ _ _)
  intro hstr
  obtain ⟨ε', hε', hlo, hhi⟩ := (TraceCovering.str_iff hgd hf hX hu hu0 0).mp hstr
  by_cases hεe : ε' = ε
  · subst hεe
    have hlo' := (hin (TraceCovering.lo D.toDissection X u ε')).mpr ⟨le_rfl, by linarith⟩
    rw [hedge, TraceCovering.segment_param] at hlo'
    obtain ⟨x', hx', hxe⟩ := hlo'
    have := TraceCovering.lm_injective hu0 hxe
    rw [min_eq_left hℓ.le] at hx'
    linarith [hx'.1]
  · have hsub := TraceCovering.meet hg hgd hf hX hu hu0 ε' hε' ε hε hεe
    set δ := min (TraceCovering.hi D.toDissection X u ε') ℓ / 2 with hδ
    have hδ0 : 0 < δ := by rw [hδ]; exact half_pos (lt_min hhi hℓ)
    have hδ1 : δ < TraceCovering.hi D.toDissection X u ε' := by
      have := min_le_left (TraceCovering.hi D.toDissection X u ε') ℓ
      rw [hδ]; linarith
    have hδ2 : δ ≤ ℓ := by
      have := min_le_right (TraceCovering.hi D.toDissection X u ε') ℓ
      rw [hδ]; linarith
    have := hsub ⟨⟨hlo.le, hhi.le⟩, hX1⟩ ⟨⟨by linarith, hδ1.le⟩, ⟨by linarith [hX1.1], by
      linarith [hX2.2]⟩⟩
    linarith

/-! ## §4 (B1) The band straddle on `ℓ_j` — Lemma A -/

set_option maxHeartbeats 1000000 in
/-- **(B1) — Lemma A on `ℓ_j`** (proof_CW_P2.md §4.3 (B1), §4.5 (T1); the P2 band end).  Let
`j = j' + 1`.  If the strip side of `ℓ_j` from `X = i₀V + jP′` to `Y = (i₀+q)V + jP′` is lined by the
`c`-edges of `D(i₀+s, j−1)`, `s < q`, the band covering of `ℓ_j` starts at `X` with a `b`-edge (the
seed), and `Y` is strictly inside the target, then `Y` is straddled from the band side: otherwise the
band side of `[X, Y]` is a whole-edge word of value `q·c` (`TraceCovering.wall_sum`) containing `b`.
**m = 1 enters here**: `Inflation.c_side_no_b` needs `q < f` (at N = 44, `2c = a + 2b`). -/
theorem band_str (L : LFrame F) (j' i0 q : ℕ) (hq : 1 ≤ q) (hqf : q + 1 ≤ f)
    (hY : ((j' : ℝ) + 1) + ((i0 : ℝ) + q) * cb e f < f)
    (hcells : ∀ s < q, Present D (Kc F (i0 + s) j'))
    (hseed : ∃ ε ∈ bandChain F ((j' : ℝ) + 1),
      EdgeIs D ε (Q2 F i0 ((j' : ℝ) + 1)) (Q2 F ((i0 : ℝ) + bcr e f) ((j' : ℝ) + 1))) :
    BStr F ((j' : ℝ) + 1) (Q2 F ((i0 : ℝ) + q) ((j' : ℝ) + 1)) := by
  classical
  by_contra hn
  have FC := L.FC
  obtain ⟨ha0, hb0, hc0, hbc, hac⟩ := consts F
  obtain ⟨hcb0, hcb1⟩ := cb_pos F
  have hu1 : ‖uE F‖ = 1 := uE_norm F
  have hu0 : uE F ≠ 0 := TraceCovering.ne_zero_of_norm hu1
  have hg : ellF F ≠ 0 := ellF_ne F FC
  have hg' : (-(ellF F) : Plane →ₗ[ℝ] ℝ) ≠ 0 := fun h => hg (neg_eq_zero.mp h)
  have hgd : ∀ y, (-(ellF F)) y = -(ellF F F.A + ((j' : ℝ) + 1)) ↔
      ellF F y = ellF F F.A + ((j' : ℝ) + 1) := TraceCovering.neg_iff
  have hgu : ellF F (uE F) = 0 := ellF_uE F FC
  have hXg : ellF F (Q2 F i0 ((j' : ℝ) + 1)) = ellF F F.A + ((j' : ℝ) + 1) := ellF_Q2 F FC _ _
  have hpt : ∀ x : ℝ, Q2 F i0 ((j' : ℝ) + 1) + x • uE F
      = Q2 F ((i0 : ℝ) + x / (f : ℝ) ^ 2) ((j' : ℝ) + 1) := fun x => Q2_uE F _ _ x
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqc : (0 : ℝ) ≤ (q : ℝ) * (f : ℝ) ^ 2 := by positivity
  have hint : ∀ x ∈ Set.Ioo 0 ((q : ℝ) * (f : ℝ) ^ 2),
      Q2 F i0 ((j' : ℝ) + 1) + x • uE F ∈ interior D.target.carrier := by
    intro x hx
    rw [hpt]
    have h1 : x / (f : ℝ) ^ 2 < q := by rw [div_lt_iff₀ hc0]; exact hx.2
    have h0 : 0 ≤ x / (f : ℝ) ^ 2 := div_nonneg hx.1.le hc0.le
    apply Q2_interior F FC (by positivity) (by positivity) (by positivity)
    nlinarith [mul_lt_mul_of_pos_right h1 hcb0]
  have hwall := wall_lattice (D := D) hu0 hc0 q (X := Q2 F i0 ((j' : ℝ) + 1)) (fun k hk => by
    obtain ⟨iz, hiz⟩ := hcells k hk
    refine ⟨iz, ?_, ?_⟩ <;> rw [hiz, D_eq F FC, hpt]
    · have : Q2 F ((i0 : ℝ) + (k : ℝ) * (f : ℝ) ^ 2 / (f : ℝ) ^ 2) ((j' : ℝ) + 1)
          = Q2 F ((i0 + k : ℕ) : ℝ) ((j' : ℝ) + 1) := by
        rw [mul_div_cancel_right₀ _ hc0.ne']; push_cast; rfl
      rw [this]; exact mem3_2
    · have : Q2 F ((i0 : ℝ) + ((k : ℝ) + 1) * (f : ℝ) ^ 2 / (f : ℝ) ^ 2) ((j' : ℝ) + 1)
          = Q2 F (((i0 + k : ℕ) : ℝ) + 1) ((j' : ℝ) + 1) := by
        rw [mul_div_cancel_right₀ _ hc0.ne']; push_cast; ring_nf
      rw [this]; exact mem3_3)
  -- the seed: the start of the band covering
  obtain ⟨ε0, hε0, hE0⟩ := hseed
  have hpq0 := pts_ne (D.tile ε0.1) (TraceCovering.fin3_succ_ne ε0.2)
  have hbpt : Q2 F i0 ((j' : ℝ) + 1) + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • uE F
      = Q2 F ((i0 : ℝ) + bcr e f) ((j' : ℝ) + 1) := by rw [hpt]; rfl
  have hedge0 : (D.tile ε0.1).edge ε0.2 = segment ℝ (Q2 F i0 ((j' : ℝ) + 1) + (0 : ℝ) • uE F)
      (Q2 F i0 ((j' : ℝ) + 1) + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • uE F) := by
    rw [zero_smul, add_zero, hbpt, Tri.edge]
    rcases pair_cases hE0 hpq0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, segment_symm]
  have hs := start_gen hg' hgd hg hXg hgu hu0 hε0 hb0 hedge0
  have ht : ¬ TraceCovering.Straddled D.toDissection (-(ellF F)) (-(ellF F F.A + ((j' : ℝ) + 1)))
      (Q2 F i0 ((j' : ℝ) + 1) + ((q : ℝ) * (f : ℝ) ^ 2) • uE F) := by
    rw [hpt, mul_div_cancel_right₀ _ hc0.ne']; exact hn
  have hsum := TraceCovering.wall_sum (D := D.toDissection) hg' hgd hg hXg hgu hu1 hqc hint hwall
    hs ht
  have hin0 : (D.tile ε0.1).edge ε0.2 ⊆ segment ℝ (Q2 F i0 ((j' : ℝ) + 1) + (0 : ℝ) • uE F)
      (Q2 F i0 ((j' : ℝ) + 1) + ((q : ℝ) * (f : ℝ) ^ 2) • uE F) := by
    rw [hedge0]
    apply (convex_segment _ _).segment_subset (left_mem_segment ℝ _ _)
    rw [TraceCovering.segment_param, min_eq_left hqc, max_eq_right hqc]
    exact ⟨_, ⟨hb0.le, by nlinarith⟩, rfl⟩
  have hdM : dist ((D.tile ε0.1).pts ε0.2) ((D.tile ε0.1).pts (ε0.2 + 1))
      = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    have hd : dist (Q2 F i0 ((j' : ℝ) + 1)) (Q2 F ((i0 : ℝ) + bcr e f) ((j' : ℝ) + 1))
        = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
      rw [← hbpt]; exact dist_self_add_unit hu1 hb0.le
    rcases pair_cases hE0 hpq0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact hd
    · rw [h1, h2, dist_comm]; exact hd
  set sF := (D.toDissection.lineChain (-(ellF F)) (-(ellF F F.A + ((j' : ℝ) + 1)))).filter
    (fun ε => (D.tile ε.1).edge ε.2 ⊆ segment ℝ (Q2 F i0 ((j' : ℝ) + 1) + (0 : ℝ) • uE F)
      (Q2 F i0 ((j' : ℝ) + 1) + ((q : ℝ) * (f : ℝ) ^ 2) • uE F)) with hsF
  have hmemS : ε0 ∈ sF := Finset.mem_filter.mpr ⟨hε0, hin0⟩
  rw [← Finset.add_sum_erase sF _ hmemS] at hsum
  obtain ⟨P', Q', R', hPQR, -⟩ := Erdos634.Geometry.sum_three_values (sF.erase ε0)
    (fun ε => dist ((D.tile ε.1).pts ε.2) ((D.tile ε.1).pts (ε.2 + 1)))
    ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)
    (fun ε _ => edge_len_mem D F.hM.hs0 F.hM.hs1 F.hM.hs2 ε.1 ε.2)
  have hee : e ^ 2 ≤ f ^ 2 := Nat.pow_le_pow_left (by have := F.hef; omega) 2
  have hreal : ((P' * (e * f) + (Q' + 1) * (f ^ 2 - e ^ 2) + R' * f ^ 2 : ℕ) : ℝ)
      = ((q * f ^ 2 : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub hee]
    simp only at hsum hdM
    rw [hdM] at hsum
    linarith
  have hnat : P' * (e * f) + (Q' + 1) * (f ^ 2 - e ^ 2) + R' * f ^ 2 = q * f ^ 2 := by
    exact_mod_cast hreal
  have := Inflation.c_side_no_b e f (f ^ 2 - e ^ 2) q P' (Q' + 1) R' (by have := F.he; omega)
    (by have := F.hef; omega) F.hco (Nat.sub_add_cancel hee) (by omega) hnat
  omega

/-! ## §5 (B2) The r-side straddle on `m_k` — A2 -/

set_option maxHeartbeats 1000000 in
/-- **(B2) — A2 on `m_k`** (proof_CW_P2.md §4.3 (B2), §4.5 (T1)).  Let `k = k' + 1`.  If the A-side
of `m_k` from `kV` to `W = kV + qP′` is lined by the `b`-edges of `D(k−1, s)`, `s < q`, the r-side
covering of `m_k` starts at `kV` with a `c`-edge (the c-seed, `B_k`'s), and `W` is strictly inside
the target, then `W` is straddled from the r-side: either the seed itself passes `W` (`qb < c`), or the
r-side of `[kV, W]` is a whole-edge word of value `q·b` containing `c`.  **m = 1 enters here**:
`Inflation.b_side_rigid` needs `q < f` (at N = 44, `2b = a + c`). -/
theorem r_str (L : LFrame F) (k' q : ℕ) (hq : 1 ≤ q) (hqf : q + 1 ≤ f)
    (hW : (q : ℝ) + ((k' : ℝ) + 1) * cb e f < f)
    (hcells : ∀ s < q, Present D (Kc F k' s))
    (hseed : ∃ ε ∈ rsChain F ((k' : ℝ) + 1),
      EdgeIs D ε (Q2 F ((k' : ℝ) + 1) 0) (Q2 F ((k' : ℝ) + 1) (cb e f))) :
    MStr F ((k' : ℝ) + 1) (Q2 F ((k' : ℝ) + 1) q) := by
  classical
  have FC := L.FC
  obtain ⟨ha0, hb0, hc0, hbc, hac⟩ := consts F
  obtain ⟨hcb0, hcb1⟩ := cb_pos F
  have hu1 : ‖uM F‖ = 1 := uM_norm F
  have hu0 : uM F ≠ 0 := TraceCovering.ne_zero_of_norm hu1
  have hg : rho F ≠ 0 := rho_ne F FC
  have hgd : ∀ y, rho F y = rho F F.A - ((k' : ℝ) + 1) ↔ rho F y = rho F F.A - ((k' : ℝ) + 1) :=
    fun y => Iff.rfl
  have hgu : rho F (uM F) = 0 := rho_uM F FC
  have hXg : rho F (Q2 F ((k' : ℝ) + 1) 0) = rho F F.A - ((k' : ℝ) + 1) := rho_Q2 F FC _ _
  have hpt : ∀ y : ℝ, Q2 F ((k' : ℝ) + 1) 0 + y • uM F
      = Q2 F ((k' : ℝ) + 1) (y / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) := by
    intro y; rw [Q2_uM, zero_add]
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqb : (0 : ℝ) ≤ (q : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by positivity
  have hcbb : cb e f * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) = (f : ℝ) ^ 2 := by
    rw [cb]; field_simp
  obtain ⟨ε0, hε0, hE0⟩ := hseed
  have hpq0 := pts_ne (D.tile ε0.1) (TraceCovering.fin3_succ_ne ε0.2)
  have hcpt : Q2 F ((k' : ℝ) + 1) 0 + ((f : ℝ) ^ 2) • uM F = Q2 F ((k' : ℝ) + 1) (cb e f) := by
    rw [hpt, cb]
  have hedge0 : (D.tile ε0.1).edge ε0.2 = segment ℝ (Q2 F ((k' : ℝ) + 1) 0 + (0 : ℝ) • uM F)
      (Q2 F ((k' : ℝ) + 1) 0 + ((f : ℝ) ^ 2) • uM F) := by
    rw [zero_smul, add_zero, hcpt, Tri.edge]
    rcases pair_cases hE0 hpq0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, segment_symm]
  have hWpt : Q2 F ((k' : ℝ) + 1) 0 + ((q : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) • uM F
      = Q2 F ((k' : ℝ) + 1) q := by
    rw [hpt, mul_div_cancel_right₀ _ hb0.ne']
  rcases lt_or_ge ((q : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) ((f : ℝ) ^ 2) with hlt | hge
  · -- the seed passes `W`
    refine ⟨ε0, hε0, ?_⟩
    have hopen : Q2 F ((k' : ℝ) + 1) q ∈ openSegment ℝ (Q2 F ((k' : ℝ) + 1) 0 + (0 : ℝ) • uM F)
        (Q2 F ((k' : ℝ) + 1) 0 + ((f : ℝ) ^ 2) • uM F) := by
      rw [← hWpt, TraceCovering.openSegment_param (by linarith), min_eq_left hc0.le,
        max_eq_right hc0.le]
      exact ⟨_, ⟨by positivity, hlt⟩, rfl⟩
    rw [zero_smul, add_zero, hcpt] at hopen
    rcases pair_cases hE0 hpq0 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    · exact hopen
    · rw [openSegment_symm]; exact hopen
  · by_contra hn
    have hint : ∀ x ∈ Set.Ioo 0 ((q : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)),
        Q2 F ((k' : ℝ) + 1) 0 + x • uM F ∈ interior D.target.carrier := by
      intro x hx
      rw [hpt]
      have h1 : x / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) < q := by rw [div_lt_iff₀ hb0]; exact hx.2
      have h0 : 0 ≤ x / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) := div_nonneg hx.1.le hb0.le
      apply Q2_interior F FC (by positivity) h0 (by positivity)
      linarith
    have hwall := wall_lattice (D := D) hu0 hb0 q (X := Q2 F ((k' : ℝ) + 1) 0) (fun s hs => by
      obtain ⟨iz, hiz⟩ := hcells s hs
      refine ⟨iz, ?_, ?_⟩ <;> rw [hiz, D_eq F FC, hpt]
      · rw [mul_div_cancel_right₀ _ hb0.ne']; exact mem3_1
      · rw [mul_div_cancel_right₀ _ hb0.ne']; exact mem3_3)
    have hs := start_gen hg hgd hg hXg hgu hu0 hε0 hc0 hedge0
    have ht : ¬ TraceCovering.Straddled D.toDissection (rho F) (rho F F.A - ((k' : ℝ) + 1))
        (Q2 F ((k' : ℝ) + 1) 0 + ((q : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) • uM F) := by
      rw [hWpt]; exact hn
    have hsum := TraceCovering.wall_sum (D := D.toDissection) hg hgd hg hXg hgu hu1 hqb hint hwall
      hs ht
    have hin0 : (D.tile ε0.1).edge ε0.2 ⊆ segment ℝ (Q2 F ((k' : ℝ) + 1) 0 + (0 : ℝ) • uM F)
        (Q2 F ((k' : ℝ) + 1) 0 + ((q : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) • uM F) := by
      rw [hedge0]
      apply (convex_segment _ _).segment_subset (left_mem_segment ℝ _ _)
      rw [TraceCovering.segment_param, min_eq_left hqb, max_eq_right hqb]
      exact ⟨_, ⟨hc0.le, hge⟩, rfl⟩
    have hdM : dist ((D.tile ε0.1).pts ε0.2) ((D.tile ε0.1).pts (ε0.2 + 1)) = (f : ℝ) ^ 2 := by
      have hd : dist (Q2 F ((k' : ℝ) + 1) 0) (Q2 F ((k' : ℝ) + 1) (cb e f)) = (f : ℝ) ^ 2 := by
        rw [← hcpt]; exact dist_self_add_unit hu1 hc0.le
      rcases pair_cases hE0 hpq0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact hd
      · rw [h1, h2, dist_comm]; exact hd
    set sF := (D.toDissection.lineChain (rho F) (rho F F.A - ((k' : ℝ) + 1))).filter
      (fun ε => (D.tile ε.1).edge ε.2 ⊆ segment ℝ (Q2 F ((k' : ℝ) + 1) 0 + (0 : ℝ) • uM F)
        (Q2 F ((k' : ℝ) + 1) 0 + ((q : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) • uM F)) with hsF
    have hmemS : ε0 ∈ sF := Finset.mem_filter.mpr ⟨hε0, hin0⟩
    rw [← Finset.add_sum_erase sF _ hmemS] at hsum
    obtain ⟨P', Q', R', hPQR, -⟩ := Erdos634.Geometry.sum_three_values (sF.erase ε0)
      (fun ε => dist ((D.tile ε.1).pts ε.2) ((D.tile ε.1).pts (ε.2 + 1)))
      ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)
      (fun ε _ => edge_len_mem D F.hM.hs0 F.hM.hs1 F.hM.hs2 ε.1 ε.2)
    have hee : e ^ 2 ≤ f ^ 2 := Nat.pow_le_pow_left (by have := F.hef; omega) 2
    have hreal : ((P' * (e * f) + Q' * (f ^ 2 - e ^ 2) + (R' + 1) * f ^ 2 : ℕ) : ℝ)
        = ((q * (f ^ 2 - e ^ 2) : ℕ) : ℝ) := by
      push_cast [Nat.cast_sub hee]
      simp only at hsum hdM
      rw [hdM] at hsum
      linarith
    have hnat : P' * (e * f) + Q' * (f ^ 2 - e ^ 2) + (R' + 1) * f ^ 2 = q * (f ^ 2 - e ^ 2) := by
      exact_mod_cast hreal
    have := Inflation.b_side_rigid e f (f ^ 2 - e ^ 2) q P' Q' (R' + 1) (by have := F.he; omega)
      (by have := F.hef; omega) F.hco (Nat.sub_add_cancel hee) (by omega) hnat
    omega

/-! ## §6 Step A: the slot dichotomy -/

/-- `z ≠ iT` from flank directions, `Λ₂` form. -/
theorem ne_of_flank_Q2 (FC : ApexPlacement.FrameCoords F) {z iT : Fin N} {mz : Fin 3}
    {i t i1 t1 i2 t2 p q d1 e1 d2 e2 : ℝ} {U W : Plane} {S : ℝ}
    (hmz : (D.tile z).pts mz = Q2 F i t) (hUW : IsFlankPair (D.tile z) mz (Q2 F i t) U W)
    (hS : 0 < S) (hU0 : vec F p q = S • U)
    (hr : Set.range (D.tile iT).pts = {Q2 F i t, Q2 F i1 t1, Q2 F i2 t2})
    (hd1 : (i1 - i) * (1 + cb e f) + (t1 - t) = d1) (he1 : -(i1 - i) = e1)
    (hd2 : (i2 - i) * (1 + cb e f) + (t2 - t) = d2) (he2 : -(i2 - i) = e2)
    (h1 : ∀ S' : ℝ, 0 < S' → p = S' * d1 → q = S' * e1 → False)
    (h2 : ∀ S' : ℝ, 0 < S' → p = S' * d2 → q = S' * e2 → False) : z ≠ iT := by
  refine ne_of_flank hmz hUW hS hU0 hr ?_ ?_
  · rw [Q2_sub_eq F hd1 he1]; exact vec_ne_smul F FC h1
  · rw [Q2_sub_eq F hd2 he2]; exact vec_ne_smul F FC h2

/-- **An `α`-tile across a flank along `V − A`** at any `Λ₂` point (generalizes
`alpha_at_R`, stated there at `Λ(x, 0)`): it is `U(i,t)` (`c` along `V − A`, `b` along `w`) or the
swap `Sw i t` (`b` along `V − A`, `c` along `w`).  No `m = 1` input. -/
theorem alpha_at_R2 (FC : ApexPlacement.FrameCoords F) {z : Fin N} {mz : Fin 3} {i t : ℝ}
    {U W : Plane} {S : ℝ} (hmz : (D.tile z).pts mz = Q2 F i t)
    (hUW : IsFlankPair (D.tile z) mz (Q2 F i t) U W) (hS : 0 < S)
    (hU0 : vec F (1 + cb e f) (-1) = S • U)
    (hside : cross (vec F (1 + cb e f) (-1)) W * cross (vec F (1 + cb e f) (-1)) (vec F (cb e f) (-1))
      < 0)
    (hα : (D.tile z).localAngle (Q2 F i t) = α) :
    Set.range (D.tile z).pts = {Q2 F i t, Q2 F (i + 1) t, Q2 F i (t + 1)} ∨
      Set.range (D.tile z).pts = Sw F i t := by
  obtain ⟨ha0, hb0, hc0, hbc, hac⟩ := consts F
  have hK := K_ne F FC
  have hK2 : 0 < ((f : ℝ) ^ 2 * cross (w F) F.uL) * ((f : ℝ) ^ 2 * cross (w F) F.uL) :=
    mul_self_pos.mpr hK
  obtain ⟨hn, hopp⟩ := (corner_dataH F hmz hUW).2 hα
  have hL0 := norm_V F
  obtain ⟨hcb0, -⟩ := cb_pos F
  have hbc1 := bc_cb F
  have hq : (0 : ℝ) < ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2 := by positivity
  rcases hn with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- `b` along `V − A`: the swap
    right
    have hU : U = vec F (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2 * (1 + cb e f))
        (-(((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2)) := by
      rw [flank_eq hS hU0 h1 hL0 hc0, vec_smul]; congr 1; ring
    have hs2 : cross (vec F (1 + cb e f) (-1)) (vec F (cb e f) 0) *
        cross (vec F (1 + cb e f) (-1)) (vec F (cb e f) (-1)) < 0 := by
      rw [cross_vec, cross_vec]; nlinarith
    have hUne : vec F (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2 * (1 + cb e f))
        (-(((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2)) ≠ 0 := by
      intro h; rw [← vec_zero F] at h; have := (vec_inj F FC h).2; linarith
    have hr := ident hmz hUW hU hUne
      (by have := side_of_across hS hU0 hside hs2; rwa [hU] at this)
      (by rw [h2, norm_vec_p0 F hcb0.le, cb, div_mul_cancel₀ _ hb0.ne'])
      (by
        rw [hopp, dist_add_vec]
        apply (norm_of_sq ha0.le _ (norm_nonneg _)).symm
        rw [norm_vec_sq, cb]
        have hf0 : (f : ℝ) ≠ 0 := (f_pos' F).ne'
        field_simp; ring)
    rw [hr, Sw, Q2_add_eq F (di := bcr e f) (dt := 0) (by rw [bcr]; ring) (by rw [bcr]),
      Q2_add_eq F (di := 0) (dt := cb e f) (by ring) (by ring), add_zero, add_zero]
  · -- `c` along `V − A`: the lattice cell
    left
    have hU : U = vec F (1 + cb e f) (-1) := by
      rw [flank_eq hS hU0 h1 hL0 hc0, div_self hc0.ne', one_smul]
    have hs2 : cross (vec F (1 + cb e f) (-1)) (vec F 1 0) *
        cross (vec F (1 + cb e f) (-1)) (vec F (cb e f) (-1)) < 0 := by
      rw [cross_vec, cross_vec]; nlinarith
    have hr := ident hmz hUW hU (by intro h; rw [h, norm_zero] at hL0; linarith)
      (by have := side_of_across hS hU0 hside hs2; rwa [hU] at this)
      (by rw [h2, norm_vec_10]) (by rw [hopp, dist_add_vec,
        show 1 + cb e f - 1 = cb e f by ring, show (-1 : ℝ) - 0 = -1 by ring, norm_VP])
    rw [hr, Q2_add_eq F (di := 1) (dt := 0) (by ring) (by ring),
      Q2_add_eq F (di := 0) (dt := 1) (by ring) (by ring), add_zero, add_zero]

set_option maxHeartbeats 1000000 in
/-- **Step A (proof_CW_P2.md §4.2): the slot at `X = (i+1)V + (t+1)P′`.**  Around it: `D(i,t)` (`α`),
`U(i,t+1)`, `D(i+1,t)` (`β`, `β`), `U(i+1,t)`, `D(i,t+1)` (`γ`, `γ`); the figure is
`{2α, 2β, 2γ}` (`interior_card_eqs`), so the tile across `D(i+1,t)`'s flank along `V − A` is the
residual `α`-tile: the lattice cell `U(i+1,t+1)` or the swap `Sw` (`alpha_at_R2`; C2 = α
indecomposable).  No `m = 1` input. -/
theorem slot2 (L : LFrame F) (i t : ℕ)
    (hXint : Q2 F ((i : ℝ) + 1) ((t : ℝ) + 1) ∈ interior D.target.carrier)
    (hA : Present D (Kc F i t)) (hB1 : Present D (T2c F i (t + 1)))
    (hB2 : Present D (Kc F (i + 1) t)) (hG1 : Present D (T2c F (i + 1) t))
    (hG2 : Present D (Kc F i (t + 1))) :
    Present D (T2c F (i + 1) (t + 1)) ∨ Present D (Sw F ((i : ℝ) + 1) ((t : ℝ) + 1)) := by
  classical
  have FC := L.FC
  obtain ⟨iA, hrA⟩ := hA
  obtain ⟨iB1, hrB1⟩ := hB1
  obtain ⟨iB2, hrB2⟩ := hB2
  obtain ⟨iG1, hrG1⟩ := hG1
  obtain ⟨iG2, hrG2⟩ := hG2
  have gA : (D.tile iA).localAngle (Q2 F ((i : ℝ) + 1) ((t : ℝ) + 1)) = α := (D_angles F FC hrA).2.2
  have gB1 : (D.tile iB1).localAngle (Q2 F ((i : ℝ) + 1) ((t : ℝ) + 1)) = β := by
    have := (U_angles F FC hrB1).2.1; push_cast at this; exact this
  have gB2 : (D.tile iB2).localAngle (Q2 F ((i : ℝ) + 1) ((t : ℝ) + 1)) = β := by
    have := (D_angles F FC hrB2).2.1; push_cast at this; exact this
  have gG1 : (D.tile iG1).localAngle (Q2 F ((i : ℝ) + 1) ((t : ℝ) + 1)) = γ := by
    have := (U_angles F FC hrG1).2.2; push_cast at this; exact this
  have gG2 : (D.tile iG2).localAngle (Q2 F ((i : ℝ) + 1) ((t : ℝ) + 1)) = γ := by
    have := (D_angles F FC hrG2).1; push_cast at this; exact this
  rw [U_eq F FC] at hrB1 hrG1
  rw [D_eq F FC] at hrB2 hrG2
  push_cast at hrB1 hrB2 hrG1 hrG2
  have rB1 : Set.range (D.tile iB1).pts = {Q2 F ((i : ℝ) + 1) ((t : ℝ) + 1),
      Q2 F i ((t : ℝ) + 1), Q2 F i ((t : ℝ) + 1 + 1)} := by
    rw [hrB1]; ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have rB2 : Set.range (D.tile iB2).pts = {Q2 F ((i : ℝ) + 1) ((t : ℝ) + 1),
      Q2 F ((i : ℝ) + 1 + 1) ((t : ℝ) + 1), Q2 F ((i : ℝ) + 1 + 1) t} := by
    rw [hrB2]; ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have rG1 : Set.range (D.tile iG1).pts = {Q2 F ((i : ℝ) + 1) ((t : ℝ) + 1),
      Q2 F ((i : ℝ) + 1) t, Q2 F ((i : ℝ) + 1 + 1) t} := by
    rw [hrG1]; ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have rG2 : Set.range (D.tile iG2).pts = {Q2 F ((i : ℝ) + 1) ((t : ℝ) + 1),
      Q2 F i ((t : ℝ) + 1 + 1), Q2 F ((i : ℝ) + 1) ((t : ℝ) + 1 + 1)} := by
    rw [hrG2]
  have hG12 : iG1 ≠ iG2 := ne_of_range rG1 rG2 (p := Q2 F ((i : ℝ) + 1) t) mem3_2 (by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    refine ⟨Q2_ne F FC (Or.inr (by intro h; linarith)), Q2_ne F FC (Or.inl (by intro h; linarith)),
      Q2_ne F FC (Or.inr (by intro h; linarith))⟩)
  have hB12 : iB1 ≠ iB2 := ne_of_range rB1 rB2 (p := Q2 F i ((t : ℝ) + 1)) mem3_2 (by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    refine ⟨Q2_ne F FC (Or.inl (by intro h; linarith)), Q2_ne F FC (Or.inl (by intro h; linarith)),
      Q2_ne F FC (Or.inl (by intro h; linarith))⟩)
  obtain ⟨mB, hmB, hflB⟩ := flank_of_range rB2
  rw [Q2_sub_eq F (p := 1 + cb e f) (q := -1) (by ring) (by ring),
    Q2_sub_eq F (p := cb e f) (q := -1) (by ring) (by ring)] at hflB
  obtain ⟨z, hzB, hXz, hcase⟩ := flank_neighbour_dissection D.toDissection hXint hmB hflB
  obtain ⟨E1, E2⟩ := interior_card_eqs D F.hAng F.hM.hα' F.hM.hβ' F.hM.hγ' hXint
  have cA := card_one gA
  have cB := card_two hB12 gB1 gB2
  have cG := card_two hG12 gG1 gG2
  rcases hcase with ⟨mz, hmz, U, W, hUW, S, hS, hU0, hside⟩ | ⟨m', -, hmpos, -, -⟩
  swap
  · exfalso
    have hznv : ∀ q, (D.tile z).pts q ≠ Q2 F ((i : ℝ) + 1) ((t : ℝ) + 1) := fun q hq =>
      NearBaseVertex.vertex_not_edge _ q hq m' hmpos
    rcases localAngle_mem_pi_of_mem (D.tile z) hXz hznv with h | h
    · have := card_one h; omega
    · have := card_one h; omega
  have hang := localAngle_at_own_vertex_mem D α β γ F.hM.hα' F.hM.hβ' F.hM.hγ' z mz
  rw [hmz] at hang
  rcases hang with hz | hz | hz
  · rcases alpha_at_R2 F FC hmz hUW hS hU0 hside hz with h | h
    · left; refine ⟨z, ?_⟩; rw [h, U_eq F FC]; push_cast; rfl
    · right; exact ⟨z, h⟩
  · exfalso
    rcases mem_of_card_two hB12 gB1 gB2 (by omega) hz with rfl | rfl
    · exact ne_of_flank_Q2 F FC hmz hUW hS hU0 rB1 (d1 := -(1 + cb e f)) (e1 := 1) (d2 := -cb e f)
        (e2 := 1) (by ring) (by ring) (by ring) (by ring)
        (fun S' hS' h1 h2 => by linarith) (fun S' hS' h1 h2 => by linarith) rfl
    · exact hzB rfl
  · exfalso
    rcases mem_of_card_two hG12 gG1 gG2 (by omega) hz with rfl | rfl
    · exact ne_of_flank_Q2 F FC hmz hUW hS hU0 rG1 (d1 := -1) (e1 := 0) (d2 := cb e f) (e2 := -1)
        (by ring) (by ring) (by ring) (by ring)
        (fun S' hS' h1 h2 => by linarith)
        (fun S' hS' h1 h2 => by
          have : S' = 1 := by linarith
          subst this; linarith) rfl
    · exact ne_of_flank_Q2 F FC hmz hUW hS hU0 rG2 (d1 := -cb e f) (e1 := 1) (d2 := 1) (e2 := 0)
        (by ring) (by ring) (by ring) (by ring)
        (fun S' hS' h1 h2 => by linarith) (fun S' hS' h1 h2 => by linarith) rfl

/-- Membership in the band chain of `ℓ_t`. -/
theorem mem_bandChain (FC : ApexPlacement.FrameCoords F) {t i1 i2 : ℝ} {z : Fin N} {m : Fin 3}
    (h1 : (D.tile z).pts m = Q2 F i1 t) (h2 : (D.tile z).pts (m + 1) = Q2 F i2 t)
    (hall : ∀ k, ellF F F.A + t ≤ ellF F ((D.tile z).pts k)) : (z, m) ∈ bandChain F t := by
  rw [bandChain, Dissection.mem_lineChain]
  simp only [LinearMap.neg_apply, neg_inj, neg_le_neg_iff]
  exact ⟨by rw [h1, ellF_Q2 F FC], by rw [h2, ellF_Q2 F FC], hall⟩

/-- **The swap's `b`-edge is a band-side edge of `ℓ_t`** (the b-seed a swap hands to the recursion). -/
theorem seed_of_Sw (FC : ApexPlacement.FrameCoords F) (i t : ℝ) (hX : Present D (Sw F i t)) :
    ∃ ε ∈ bandChain F t, EdgeIs D ε (Q2 F i t) (Q2 F (i + bcr e f) t) := by
  obtain ⟨hbr0, -, -⟩ := bcr_facts F
  obtain ⟨hcb0, -⟩ := cb_pos F
  obtain ⟨iX, hr⟩ := hX
  have hP : Q2 F i t ∈ Set.range (D.tile iX).pts := by rw [hr, Sw]; exact mem3_1
  have hQ : Q2 F (i + bcr e f) t ∈ Set.range (D.tile iX).pts := by rw [hr, Sw]; exact mem3_2
  obtain ⟨m, hm⟩ := edge_idx hP hQ (Q2_ne F FC (Or.inl (by intro h; linarith)))
  have hall : ∀ k, ellF F F.A + t ≤ ellF F ((D.tile iX).pts k) := by
    intro k
    have : (D.tile iX).pts k ∈ Set.range (D.tile iX).pts := ⟨k, rfl⟩
    rw [hr, Sw] at this
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    rcases this with h | h | h <;> rw [h, ellF_Q2 F FC] <;> linarith
  rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨(iX, m), mem_bandChain F FC h1 h2 hall, by simp only [EdgeIs]; rw [h1, h2]⟩
  · exact ⟨(iX, m), mem_bandChain F FC h1 h2 hall,
      by simp only [EdgeIs]; rw [h1, h2, Set.pair_comm]⟩

/-! ## §7 Counting -/

include F in
/-- **Two straight tiles on two crossing lines, and an `α`**, at an interior point: impossible
(`n_α + 3n_π + 6n_{2π} + 2n_γ = 6`).  One tile cannot carry both straight edges (`same_edge`: the
edge would lie on both lines). -/
theorem no_two_straight {x : Plane} (hx : x ∈ interior D.target.carrier)
    {g1 g2 : Plane →ₗ[ℝ] ℝ} {d1 d2 : ℝ}
    (h1 : TraceCovering.Straddled D.toDissection g1 d1 x)
    (h2 : TraceCovering.Straddled D.toDissection g2 d2 x)
    (hind : ∀ v : Plane, g1 v = 0 → g2 v = 0 → v = 0)
    {iA : Fin N} (hA : (D.tile iA).localAngle x = α) : False := by
  classical
  obtain ⟨ε1, hε1, hx1⟩ := h1
  obtain ⟨ε2, hε2, hx2⟩ := h2
  obtain ⟨E1, E2⟩ := interior_card_eqs D F.hAng F.hM.hα' F.hM.hβ' F.hM.hγ' hx
  have cA := card_one hA
  by_cases h12 : ε1.1 = ε2.1
  · have hx2' : x ∈ openSegment ℝ ((D.tile ε1.1).pts ε2.2) ((D.tile ε1.1).pts (ε2.2 + 1)) := by
      rw [h12]; exact hx2
    have hm := Level2LemmaGReal.same_edge (D.tile ε1.1) hx1 hx2'
    obtain ⟨a1, a2, -⟩ := Dissection.mem_lineChain.mp hε1
    obtain ⟨b1, b2, -⟩ := Dissection.mem_lineChain.mp hε2
    rw [← h12, ← hm] at b1 b2
    have hv := hind ((D.tile ε1.1).pts (ε1.2 + 1) - (D.tile ε1.1).pts ε1.2)
      (by rw [map_sub, a1, a2, sub_self]) (by rw [map_sub, b1, b2, sub_self])
    exact pts_ne (D.tile ε1.1) (TraceCovering.fin3_succ_ne ε1.2) (sub_eq_zero.mp hv).symm
  · have := Level2LemmaGReal.two_straight h12 (straight_count hx1) (straight_count hx2)
    omega

/-- The three line families cross pairwise: a vector along two of them is `0`. -/
theorem ind_ell_ad (FC : ApexPlacement.FrameCoords F) :
    ∀ v : Plane, (-(ellF F)) v = 0 → (-(adF F)) v = 0 → v = 0 := by
  intro v h1 h2
  rw [vec_coords F FC v] at h1 h2 ⊢
  simp only [LinearMap.neg_apply, neg_eq_zero, ellF_vec F FC, adF_vec F FC] at h1 h2
  have hq : rho F v = 0 := by linarith
  have hp : col F v = 0 := by rw [hq] at h2; linarith
  rw [hp, hq, vec_zero]

theorem ind_rho_ad (FC : ApexPlacement.FrameCoords F) :
    ∀ v : Plane, (rho F) v = 0 → (-(adF F)) v = 0 → v = 0 := by
  intro v h1 h2
  rw [vec_coords F FC v] at h1 h2 ⊢
  simp only [LinearMap.neg_apply, neg_eq_zero, rho_vec F FC, adF_vec F FC] at h1 h2
  have hp : col F v = 0 := by rw [h1] at h2; linarith
  rw [hp, h1, vec_zero]

theorem ind_ell_rho (FC : ApexPlacement.FrameCoords F) :
    ∀ v : Plane, (-(ellF F)) v = 0 → (rho F) v = 0 → v = 0 := by
  intro v h1 h2
  rw [vec_coords F FC v] at h1 h2 ⊢
  simp only [LinearMap.neg_apply, neg_eq_zero, rho_vec F FC, ellF_vec F FC] at h1 h2
  have hp : col F v = 0 := by rw [h2] at h1; linarith
  rw [hp, h2, vec_zero]

end Erdos634.Draft.RowWallReal

#print axioms Erdos634.Draft.RowWallReal.O2
#print axioms Erdos634.Draft.RowWallReal.Q2_interior
#print axioms Erdos634.Draft.RowWallReal.wall_lattice
#print axioms Erdos634.Draft.RowWallReal.start_gen
#print axioms Erdos634.Draft.RowWallReal.band_str
#print axioms Erdos634.Draft.RowWallReal.r_str
#print axioms Erdos634.Draft.RowWallReal.alpha_at_R2
#print axioms Erdos634.Draft.RowWallReal.slot2
#print axioms Erdos634.Draft.RowWallReal.seed_of_Sw
#print axioms Erdos634.Draft.RowWallReal.no_two_straight

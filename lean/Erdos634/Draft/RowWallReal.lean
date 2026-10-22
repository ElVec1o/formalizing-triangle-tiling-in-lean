-- Draft/RowWallReal.lean — RW(j), the ROW-WALL LEMMA (the b-seeded row line), for REAL dissections
-- in the apex frame.  Statement of record: (private working notes, not included) S1 (RLL withdrawn),
-- proof_H_empty.md §5.5; reviews (private working notes, not included) review2_RW/REVIEW.md.
-- Imported by All.lean (All.lean line 420: import Erdos634.Draft.RowWallReal).
--
-- Build (scratch oleans; never .lake): Level2LemmaGReal olean in $S, then
--   lake env bash -c 'LEAN_PATH=$S:$LEAN_PATH lean Erdos634/Draft/RowWallReal.lean'
--
-- LAYOUT.  §1 the `Λ₃` lattice `Λ(x,y) = A + x·w + y·v` (`w = P′ − A`, `v = c·uL`), its dual
-- functionals `col` (constant on the row lines `L_j`) and `lev` (constant on the rows), and the
-- target's cone coordinates (interior / exterior of lattice points).  §2 generic tools (corner
-- identification, counting).  §3 the cells `Up i t = T₃ + Λ(i,t)`, `Dn i t = Z₀ + Λ(i,t)` and the
-- swap `Xs i t`.  The local steps are in Draft/RowWallLocal.lean, the induction (RW(j) itself,
-- `rw_frame`, `rw_real`) in Draft/RowWallInduction.lean, PK·a in Draft/MirrorLevelQReal.lean.
import Erdos634.Draft.Level2LemmaGReal

namespace Erdos634.Draft.RowWallReal

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.HalfTurnR3R4
open Erdos634.Draft.HalfTurnR3R4Glue Erdos634.Draft.CornerAdjacency
open Erdos634.Draft.HalfTurnR3R4Order Erdos634.Draft.MirrorStripR2Real
open Erdos634.Draft.HalfTurnR4Real

variable {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ}

/-! ## §1 The lattice frame -/

/-- **The `Λ₃` frame**: the apex frame `F` of a real `m = 1` dissection, with the target's cone
coordinates (`FrameCoords`) and the `b`-freeness of the leg `A + ℝ·uL` (`lem:sidenob`, an `m = 1`
input: at `N = 44` the leg word is `c c a a a a` but `c + 4b = 16` would also be legal there, and at
`m ≥ 2` an equal side can start with `b`).  Both are derived for every real dissection in
`lframe_real`. -/
structure LFrame (F : HFrame D e f α β γ) : Prop where
  FC : ApexPlacement.FrameCoords F
  hlegnob : ∀ (i : Fin N) (m : Fin 3) (s t : ℝ), (D.tile i).pts m = F.A + s • F.uL →
    (D.tile i).pts (m + 1) = F.A + t • F.uL →
    dist ((D.tile i).pts m) ((D.tile i).pts (m + 1)) ≠ (f : ℝ) ^ 2 - (e : ℝ) ^ 2

/-- `w = P′ − A` (the `b`-direction of the lattice, along the matched ray `m₀`). -/
def w (F : HFrame D e f α β γ) : Plane := F.P - F.A
/-- `v = c·uL` (the `c`-direction, along the leg). -/
noncomputable def v (F : HFrame D e f α β γ) : Plane := ((f : ℝ) ^ 2) • F.uL
/-- `vec p q = p·w + q·v`. -/
noncomputable def vec (F : HFrame D e f α β γ) (p q : ℝ) : Plane := p • w F + q • v F
/-- The lattice point `Λ(x, y) = A + x·w + y·v` (`x`: strips from the leg, `x + y`: the row). -/
noncomputable def Lam (F : HFrame D e f α β γ) (x y : ℝ) : Plane := F.A + vec F x y

variable (F : HFrame D e f α β γ)

theorem Lam_sub (x y x' y' : ℝ) : Lam F x y - Lam F x' y' = vec F (x - x') (y - y') := by
  simp only [Lam, vec]; module

theorem Lam_add (x y p q : ℝ) : Lam F x y + vec F p q = Lam F (x + p) (y + q) := by
  simp only [Lam, vec]; module

theorem vec_smul (S p q : ℝ) : S • vec F p q = vec F (S * p) (S * q) := by
  simp only [vec]; module

theorem vec_neg (p q : ℝ) : - vec F p q = vec F (-p) (-q) := by
  simp only [vec]; module

theorem vec_zero : vec F 0 0 = 0 := by simp [vec]

theorem Lam_zero_zero : Lam F 0 0 = F.A := by simp [Lam, vec]

/-- `κ = cross w uL ≠ 0`. -/
theorem kappa_ne (FC : ApexPlacement.FrameCoords F) : cross (w F) F.uL ≠ 0 :=
  Level2LemmaGReal.cross_w_uL F FC

include F in
theorem cf_pos : (0 : ℝ) < (f : ℝ) ^ 2 := by
  have : (0 : ℝ) < f := by exact_mod_cast (show 0 < f by have := F.hef; omega)
  positivity

include F in
theorem f_pos' : (0 : ℝ) < f := by exact_mod_cast (show 0 < f by have := F.hef; omega)

theorem cross_vec (p q r s : ℝ) :
    cross (vec F p q) (vec F r s) = (p * s - q * r) * ((f : ℝ) ^ 2 * cross (w F) F.uL) := by
  simp only [vec, v, NearBaseVertex.cross_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

theorem vec_inj (FC : ApexPlacement.FrameCoords F) {p q r s : ℝ}
    (h : vec F p q = vec F r s) : p = r ∧ q = s := by
  have hk := kappa_ne F FC
  have hc := (cf_pos F).ne'
  have h1 := congrArg (fun x => cross x (vec F 0 1)) h
  have h2 := congrArg (fun x => cross (vec F 1 0) x) h
  simp only [cross_vec] at h1 h2
  constructor
  · have : (p - r) * ((f : ℝ) ^ 2 * cross (w F) F.uL) = 0 := by linear_combination h1
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact absurd h (mul_ne_zero hc hk)
  · have : (q - s) * ((f : ℝ) ^ 2 * cross (w F) F.uL) = 0 := by linear_combination h2
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact absurd h (mul_ne_zero hc hk)

theorem Lam_inj (FC : ApexPlacement.FrameCoords F) {x y x' y' : ℝ}
    (h : Lam F x y = Lam F x' y') : x = x' ∧ y = y' :=
  vec_inj F FC (add_left_cancel h)

theorem Lam_ne (FC : ApexPlacement.FrameCoords F) {x y x' y' : ℝ} (h : x ≠ x' ∨ y ≠ y') :
    Lam F x y ≠ Lam F x' y' := by
  intro h'
  obtain ⟨h1, h2⟩ := Lam_inj F FC h'
  rcases h with h | h
  · exact h h1
  · exact h h2

/-- Inner-product data: `|w| = b`, `|v| = c`, `|v − w| = a`. -/
theorem norm_w : ‖w F‖ = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
  rw [w, ← dist_eq_norm, dist_comm]; exact F.hAP

theorem norm_v : ‖v F‖ = (f : ℝ) ^ 2 := by
  rw [v, norm_smul, F.huL, mul_one, Real.norm_of_nonneg (cf_pos F).le]

theorem norm_vw : ‖v F - w F‖ = (e : ℝ) * f := by
  have : v F - w F = (F.A + ((f : ℝ) ^ 2) • F.uL) - F.P := by rw [v, w]; abel
  rw [this, ← dist_eq_norm, dist_comm]; exact F.hPJ1

theorem inner_wv : 2 * inner ℝ (w F) (v F)
    = ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2 + ((f : ℝ) ^ 2) ^ 2 - ((e : ℝ) * f) ^ 2 := by
  have h := norm_sub_sq_real (v F) (w F)
  rw [norm_vw, norm_v, norm_w, real_inner_comm] at h
  linarith

/-- `‖vec p q‖² = p²b² + q²c² + pq·(b² + c² − a²)`. -/
theorem norm_vec_sq (p q : ℝ) : ‖vec F p q‖ ^ 2 = p ^ 2 * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2
    + q ^ 2 * ((f : ℝ) ^ 2) ^ 2
    + p * q * (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2 + ((f : ℝ) ^ 2) ^ 2 - ((e : ℝ) * f) ^ 2) := by
  have h := inner_wv F
  rw [vec, norm_add_sq_real, norm_smul, norm_smul, norm_w, norm_v, real_inner_smul_left,
    real_inner_smul_right, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs]
  linear_combination p * q * h

theorem norm_of_sq {x L : ℝ} (hL : 0 ≤ L) (h : x ^ 2 = L ^ 2) (hx : 0 ≤ x) : x = L :=
  (pow_left_inj₀ hx hL two_ne_zero).mp h

/-- The four lattice lengths used: `|w| = b`, `|v| = c`, `|v − w| = a`, `|(c/b)w − (b/c)v| = a`. -/
theorem norm_vec_10 : ‖vec F 1 0‖ = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
  simp [vec, norm_w]

theorem norm_vec_01 : ‖vec F 0 1‖ = (f : ℝ) ^ 2 := by
  simp [vec, norm_v]

theorem norm_vec_m11 : ‖vec F (-1) 1‖ = (e : ℝ) * f := by
  have : vec F (-1) 1 = v F - w F := by simp only [vec]; module
  rw [this, norm_vw]

theorem norm_vec_swap :
    ‖vec F ((f : ℝ) ^ 2 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) (-(((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2))‖
      = (e : ℝ) * f := by
  have heR : (2 : ℝ) ≤ e := by exact_mod_cast F.he
  have hefR : (e : ℝ) + 2 ≤ f := by exact_mod_cast F.hef
  have hb0 : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have hc0 := cf_pos F
  have hf0 : (f : ℝ) ≠ 0 := (f_pos' F).ne'
  apply norm_of_sq (by positivity) _ (norm_nonneg _)
  rw [norm_vec_sq]
  have h1 : ((f : ℝ) ^ 2 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) ^ 2 * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2
      = ((f : ℝ) ^ 2) ^ 2 := by field_simp
  have h2 : (-(((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2)) ^ 2 * ((f : ℝ) ^ 2) ^ 2
      = ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2 := by field_simp
  have h3 : (f : ℝ) ^ 2 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * (-(((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2))
      = -1 := by field_simp
  rw [h1, h2, h3]; ring

/-! ### The dual functionals -/

/-- `col`: `col w = 1`, `col v = 0` — constant on each row line `L_j = {col = col A + j}`. -/
noncomputable def col (F : HFrame D e f α β γ) : Plane →ₗ[ℝ] ℝ :=
  (1 / cross (w F) F.uL) • (-(crossL F.uL))
/-- `rho`: `rho w = 0`, `rho v = 1`. -/
noncomputable def rho (F : HFrame D e f α β γ) : Plane →ₗ[ℝ] ℝ :=
  (1 / ((f : ℝ) ^ 2 * cross (w F) F.uL)) • crossL (w F)
/-- `lev = col + rho` — constant on each row `{lev = lev A + n}`. -/
noncomputable def lev (F : HFrame D e f α β γ) : Plane →ₗ[ℝ] ℝ := col F + rho F

theorem col_vec (FC : ApexPlacement.FrameCoords F) (p q : ℝ) : col F (vec F p q) = p := by
  have hk := kappa_ne F FC
  simp only [col, vec, v, LinearMap.smul_apply, LinearMap.neg_apply, crossL_apply, smul_eq_mul]
  rw [cross_add_right, cross_smul_right, cross_smul_right, cross_smul_right, cross_self',
    cross_anti (w F) F.uL]
  field_simp
  ring

theorem rho_vec (FC : ApexPlacement.FrameCoords F) (p q : ℝ) : rho F (vec F p q) = q := by
  have hk := kappa_ne F FC
  have hc := (cf_pos F).ne'
  have hf0 : (f : ℝ) ≠ 0 := (f_pos' F).ne'
  simp only [rho, vec, v, LinearMap.smul_apply, crossL_apply, smul_eq_mul]
  rw [cross_add_right, cross_smul_right, cross_smul_right, cross_smul_right, cross_self']
  field_simp
  ring

theorem lev_vec (FC : ApexPlacement.FrameCoords F) (p q : ℝ) : lev F (vec F p q) = p + q := by
  simp only [lev, LinearMap.add_apply, col_vec F FC, rho_vec F FC]

theorem col_Lam (FC : ApexPlacement.FrameCoords F) (x y : ℝ) :
    col F (Lam F x y) = col F F.A + x := by
  rw [Lam, map_add, col_vec F FC]

theorem lev_Lam (FC : ApexPlacement.FrameCoords F) (x y : ℝ) :
    lev F (Lam F x y) = lev F F.A + (x + y) := by
  rw [Lam, map_add, lev_vec F FC]

theorem col_ne (FC : ApexPlacement.FrameCoords F) : col F ≠ 0 := by
  intro h; have := col_vec F FC 1 0; rw [h, LinearMap.zero_apply] at this; exact zero_ne_one this

theorem lev_ne (FC : ApexPlacement.FrameCoords F) : lev F ≠ 0 := by
  intro h; have := lev_vec F FC 1 0; rw [h, LinearMap.zero_apply] at this; norm_num at this

/-! ### Cone coordinates of lattice points -/

/-- `Λ(x, y) = A + (x·s + y/f)·(f³uL) + (x·t)·(R − A)` with `s, t > 0`, `s + t = 1/f`. -/
theorem cone_form (FC : ApexPlacement.FrameCoords F) :
    ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ s + t = 1 / (f : ℝ) ∧ ∀ x y : ℝ, Lam F x y = F.A +
      ((x * s + y * (1 / (f : ℝ))) • ((F.A + ((f : ℝ) ^ 3) • F.uL) - F.A) + (x * t) • (F.R - F.A)) := by
  obtain ⟨s, t, hs, ht, hP, -, hst⟩ := FC.hP
  have hf : (f : ℝ) ≠ 0 := (f_pos' F).ne'
  refine ⟨s, t, hs, ht, hst, fun x y => ?_⟩
  have hv : ((f : ℝ) ^ 2) • F.uL = (1 / (f : ℝ)) • (((f : ℝ) ^ 3) • F.uL) := by
    rw [smul_smul]; congr 1; field_simp
  simp only [Lam, vec, w, v]
  rw [hP, hv, add_sub_cancel_left]
  module

/-- A point `A + σ·(Q − A) + τ·(R − A)`, `σ, τ ≥ 0`, `σ + τ ≤ 1`, is in the target. -/
theorem cone_mem {σ τ : ℝ} (hσ : 0 ≤ σ) (hτ : 0 ≤ τ) (h1 : σ + τ ≤ 1) :
    F.A + (σ • ((F.A + ((f : ℝ) ^ 3) • F.uL) - F.A) + τ • (F.R - F.A)) ∈ D.target.carrier := by
  set Q := F.A + ((f : ℝ) ^ 3) • F.uL
  have hA : F.A ∈ D.target.carrier := by apply subset_convexHull ℝ _; rw [F.htarget]; simp
  have hQ : Q ∈ D.target.carrier := by apply subset_convexHull ℝ _; rw [F.htarget]; simp [Q]
  have hR : F.R ∈ D.target.carrier := by apply subset_convexHull ℝ _; rw [F.htarget]; simp
  rcases (add_nonneg hσ hτ).lt_or_eq with hs | hs
  · set s := σ + τ with hsdef
    have hB := D.target.convex.add_smul_sub_mem hQ hR (t := τ / s)
      ⟨div_nonneg hτ hs.le, (div_le_one hs).mpr (by linarith)⟩
    have hC := D.target.convex.add_smul_sub_mem hA hB (t := s) ⟨hs.le, h1⟩
    convert hC using 1
    rw [show Q + (τ / s) • (F.R - Q) - F.A = (Q - F.A) + (τ / s) • (F.R - Q) by abel, smul_add,
      smul_smul, mul_div_cancel₀ _ hs.ne']
    have : σ = s - τ := by rw [hsdef]; ring
    rw [this]; module
  · have hσ0 : σ = 0 := by linarith
    have hτ0 : τ = 0 := by linarith
    rw [hσ0, hτ0]; simpa using hA


/-- Lattice points with `x > 0`, `y ≥ 0`, `x + y < f` are interior to the target. -/
theorem Lam_interior (FC : ApexPlacement.FrameCoords F) {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y)
    (hxy : x + y < f) : Lam F x y ∈ interior D.target.carrier := by
  obtain ⟨s, t, hs, ht, hst, hL⟩ := cone_form F FC
  have hf := f_pos' F
  rw [hL x y]
  have h := FC.hcone.inter (x * s + y * (1 / (f : ℝ))) (x * t) 1 (by positivity) (by positivity)
    one_pos (by
      rw [one_mul, show x * s + y * (1 / (f : ℝ)) + x * t = x * (s + t) + y * (1 / f) by ring, hst,
        show x * (1 / (f : ℝ)) + y * (1 / f) = (x + y) / f by ring, div_lt_one hf]
      exact hxy)
  rwa [one_smul] at h

/-- Points with `x + y > f` are outside the target (beyond the base). -/
theorem Lam_out (FC : ApexPlacement.FrameCoords F) {x y : ℝ} (hxy : (f : ℝ) < x + y) :
    Lam F x y ∉ D.target.carrier := by
  obtain ⟨s, t, hs, ht, hst, hL⟩ := cone_form F FC
  have hf := f_pos' F
  rw [hL x y, show F.A + ((f : ℝ) ^ 3) • F.uL - F.A = ((f : ℝ) ^ 3) • F.uL by abel]
  apply FC.hout
  rw [show x * s + y * (1 / (f : ℝ)) + x * t = x * (s + t) + y * (1 / f) by ring, hst,
    show x * (1 / (f : ℝ)) + y * (1 / f) = (x + y) / f by ring, lt_div_iff₀ hf, one_mul]
  exact hxy

/-- Points with `x < 0` are outside the target (beyond the leg). -/
theorem Lam_neg (FC : ApexPlacement.FrameCoords F) {x : ℝ} (hx : x < 0) (y : ℝ) :
    Lam F x y ∉ D.target.carrier := by
  obtain ⟨s, t, hs, ht, hst, hL⟩ := cone_form F FC
  intro hmem
  rw [hL x y] at hmem
  have hmem' : F.A + (1 : ℝ) • ((x * s + y * (1 / (f : ℝ))) • ((F.A + ((f : ℝ) ^ 3) • F.uL) - F.A)
      + (x * t) • (F.R - F.A)) ∈ D.target.carrier := by rwa [one_smul]
  obtain ⟨s', t', hs', ht', hD⟩ := FC.hcone.cone _ 1 one_pos hmem'
  have hdet := FC.hcone.det
  have := congrArg (cross ((F.A + ((f : ℝ) ^ 3) • F.uL) - F.A)) hD
  simp only [cross_add_right, cross_smul_right, cross_self', mul_zero, zero_add] at this
  have ht'' : x * t = t' := by
    have h' : (x * t - t') * cross (F.A + ((f : ℝ) ^ 3) • F.uL - F.A) (F.R - F.A) = 0 := by
      linear_combination this
    rcases mul_eq_zero.mp h' with h | h
    · linarith
    · exact absurd h hdet
  have : x * t < 0 := mul_neg_of_neg_of_pos hx ht
  linarith

/-- Lattice points with `x ≥ 0`, `y ≥ 0`, `x + y ≤ f` are in the target. -/
theorem Lam_mem (FC : ApexPlacement.FrameCoords F) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : x + y ≤ f) : Lam F x y ∈ D.target.carrier := by
  obtain ⟨s, t, hs, ht, hst, hL⟩ := cone_form F FC
  have hf := f_pos' F
  rw [hL x y]
  apply cone_mem F (by positivity) (by positivity)
  rw [show x * s + y * (1 / (f : ℝ)) + x * t = x * (s + t) + y * (1 / f) by ring, hst,
    show x * (1 / (f : ℝ)) + y * (1 / f) = (x + y) / f by ring, div_le_one hf]
  exact hxy

/-- Leg points `Λ(0, y)`, `0 ≤ y ≤ f`, are on the frontier of the target. -/
theorem leg_frontier (FC : ApexPlacement.FrameCoords F) {y : ℝ} (hy : 0 ≤ y) (hyf : y ≤ f) :
    Lam F 0 y ∈ frontier D.target.carrier := by
  refine ⟨subset_closure (Lam_mem F FC le_rfl hy (by linarith)), fun hint => ?_⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hint)
  have hw0 : 0 < ‖vec F 1 0‖ := by
    rw [norm_vec_10]
    have heR : (2 : ℝ) ≤ e := by exact_mod_cast F.he
    have hefR : (e : ℝ) + 2 ≤ f := by exact_mod_cast F.hef
    nlinarith
  set δ := r / (2 * ‖vec F 1 0‖) with hδ
  have hδ0 : 0 < δ := by positivity
  apply Lam_neg F FC (neg_neg_iff_pos.mpr hδ0) y
  apply hball
  rw [Metric.mem_ball, dist_eq_norm, Lam_sub, sub_self, show -δ - 0 = -δ by ring,
    show vec F (-δ) 0 = (-δ) • vec F 1 0 by rw [vec_smul]; norm_num, norm_smul,
    Real.norm_eq_abs, abs_neg, abs_of_pos hδ0, hδ]
  field_simp
  linarith

/-- Leg points strictly between `A` and the base corner are not target vertices. -/
theorem leg_not_vertex (FC : ApexPlacement.FrameCoords F) {y : ℝ} (hy : 0 < y) (hyf : y < f) :
    Lam F 0 y ∉ Set.range D.target.pts := by
  rw [F.htarget]
  have hf := f_pos' F
  have hL : Lam F 0 y = F.A + (y * (f : ℝ) ^ 2) • F.uL := by
    simp only [Lam, vec, v]; rw [smul_smul]; module
  intro hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  have hu0 : F.uL ≠ 0 := TraceCovering.ne_zero_of_norm F.huL
  rcases hmem with h | h | h
  · rw [hL] at h
    have : (y * (f : ℝ) ^ 2) • F.uL = 0 := by
      have := congrArg (fun p => p - F.A) h; simpa using this
    rcases smul_eq_zero.mp this with h' | h'
    · have : 0 < y * (f : ℝ) ^ 2 := by positivity
      linarith
    · exact hu0 h'
  · rw [hL] at h
    have := add_left_cancel h
    have h' : (y * (f : ℝ) ^ 2 - (f : ℝ) ^ 3) • F.uL = 0 := by rw [sub_smul, this, sub_self]
    rcases smul_eq_zero.mp h' with h' | h'
    · have : y * (f : ℝ) ^ 2 < (f : ℝ) ^ 3 := by
        have : (f : ℝ) ^ 3 = f * (f : ℝ) ^ 2 := by ring
        rw [this]; exact mul_lt_mul_of_pos_right hyf (by positivity)
      linarith
    · exact hu0 h'
  · have hdet := FC.hcone.det
    rw [show F.A + ((f : ℝ) ^ 3) • F.uL - F.A = ((f : ℝ) ^ 3) • F.uL by abel, ← h, hL,
      add_sub_cancel_left, cross_smul_left', cross_smul_right, cross_self'] at hdet
    simp at hdet

/-! ## §2 Generic tools -/

/-- A tile given by its vertex set has a corner at each listed vertex with the other two as flanks. -/
theorem flank_of_range {i : Fin N} {X Y Z : Plane} (hr : Set.range (D.tile i).pts = {X, Y, Z}) :
    ∃ m, (D.tile i).pts m = X ∧ IsFlankPair (D.tile i) m X (Y - X) (Z - X) := by
  obtain ⟨m, hm⟩ := MarchInduction.mem_range_of_eq hr (Set.mem_insert _ _)
  refine ⟨m, hm, ?_⟩
  rcases MarchInduction.vertex_data_of_range hr hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; exact ⟨by rw [h1], by rw [h2]⟩
  · right; exact ⟨by rw [h2], by rw [h1]⟩

/-- Two tiles with different vertex sets are different tiles. -/
theorem ne_of_range {i1 i2 : Fin N} {S1 S2 : Set Plane} (h1 : Set.range (D.tile i1).pts = S1)
    (h2 : Set.range (D.tile i2).pts = S2) {p : Plane} (hp1 : p ∈ S1) (hp2 : p ∉ S2) : i1 ≠ i2 := by
  rintro rfl; rw [h1] at h2; rw [h2] at hp1; exact hp2 hp1

/-- A tile `z` with a corner at `X` and a flank `U` with `U0 = S·U` is not a tile `iT` whose flanks at
`X` are not positive multiples of `U0`'s direction. -/
theorem ne_of_flank {z iT : Fin N} {mz : Fin 3} {X U W U0 Y Z : Plane} {S : ℝ}
    (hmz : (D.tile z).pts mz = X) (hUW : IsFlankPair (D.tile z) mz X U W) (hS : 0 < S)
    (hU0 : U0 = S • U) (hr : Set.range (D.tile iT).pts = {X, Y, Z})
    (hY : ∀ S' : ℝ, 0 < S' → U0 ≠ S' • (Y - X)) (hZ : ∀ S' : ℝ, 0 < S' → U0 ≠ S' • (Z - X)) :
    z ≠ iT := by
  rintro rfl
  obtain ⟨m, hm, hfl⟩ := flank_of_range hr
  have hmm : m = mz := (D.tile z).indep.injective (hm.trans hmz.symm)
  subst hmm
  rcases ApexPlacement.flank_cases hfl hUW with ⟨hU', -⟩ | ⟨hU', -⟩
  · rw [hU'] at hU0; exact hY S hS hU0
  · rw [hU'] at hU0; exact hZ S hS hU0

/-- `vec p q ≠ S·vec r s` when no positive `S` scales `(r, s)` to `(p, q)`. -/
theorem vec_ne_smul (FC : ApexPlacement.FrameCoords F) {p q r s : ℝ}
    (h : ∀ S : ℝ, 0 < S → p = S * r → q = S * s → False) :
    ∀ S : ℝ, 0 < S → vec F p q ≠ S • vec F r s := by
  intro S hS h'
  rw [vec_smul] at h'
  obtain ⟨h1, h2⟩ := vec_inj F FC h'
  exact h S hS h1 h2

/-- **Corner identification.**  A tile `z` with a corner at `X`, flank pair `(U, W)`, `U = U1`, and
`W` strictly on the same side of `ℝU1` as a candidate `W1` with `|W| = |W1|`,
`|U1 − W| = |U1 − W1|`: `z = {X, X + U1, X + W1}` (`third_vertex_cross`, `range_of_flank`). -/
theorem ident {z : Fin N} {mz : Fin 3} {X U W U1 W1 : Plane}
    (hmz : (D.tile z).pts mz = X) (hUW : IsFlankPair (D.tile z) mz X U W) (hU : U = U1)
    (hU1 : U1 ≠ 0) (hside : 0 < cross U1 W * cross U1 W1) (hWn : ‖W‖ = ‖W1‖)
    (hopp : dist (X + U) (X + W) = dist (X + U1) (X + W1)) :
    Set.range (D.tile z).pts = {X, X + U1, X + W1} := by
  subst hU
  have hZ : X + W = X + W1 := by
    apply third_vertex_cross (X := X) (Y := X + U)
    · intro h; apply hU1; have := congrArg (fun p => p - X) h; simpa using this.symm
    · simpa using hside
    · rw [dist_comm, dist_eq_norm, add_sub_cancel_left, dist_comm, dist_eq_norm,
        add_sub_cancel_left, hWn]
    · exact hopp
  rw [ApexPlacement.range_of_flank hmz hUW, hZ]

/-- The side condition of `flank_neighbour` transported to a candidate: if `W'` and `W1` are both
strictly across `ℝU0` from `W0` and `U0 = S·U`, then `W'` and `W1` are on the same side of `ℝU`. -/
theorem side_of_across {U0 U W' W0 W1 : Plane} {S : ℝ} (hS : 0 < S) (hU0 : U0 = S • U)
    (h1 : cross U0 W' * cross U0 W0 < 0) (h2 : cross U0 W1 * cross U0 W0 < 0) :
    0 < cross U W' * cross U W1 := by
  subst hU0
  simp only [cross_smul_left'] at h1 h2
  have hprod : 0 < (S * cross U W' * (S * cross U W0)) * (S * cross U W1 * (S * cross U W0)) :=
    mul_pos_of_neg_of_neg h1 h2
  have : (S * cross U W' * (S * cross U W0)) * (S * cross U W1 * (S * cross U W0))
      = (S ^ 4 * cross U W0 ^ 2) * (cross U W' * cross U W1) := by ring
  rw [this] at hprod
  exact pos_of_mul_pos_right hprod (by positivity)

/-- A flank `U` of the corner with `U0 = S·U`, `|U| = ℓ`, `|U0| = L0 > 0` is `(ℓ/L0)·U0`. -/
theorem flank_eq {U U0 : Plane} {S ℓ L0 : ℝ} (hS : 0 < S) (hU0 : U0 = S • U) (hU : ‖U‖ = ℓ)
    (hL0 : ‖U0‖ = L0) (hL : 0 < L0) : U = (ℓ / L0) • U0 :=
  ApexPlacement.eq_smul_of_norms hS hU0 hL0 hU hL

include F in
/-- Local angle of a corner tile listed by its vertex set, by the opposite side. -/
theorem angle_of_range {i : Fin N} {X Y Z : Plane} (hr : Set.range (D.tile i).pts = {X, Y, Z}) :
    (dist Y Z = (e : ℝ) * f → (D.tile i).localAngle X = α) ∧
    (dist Y Z = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 → (D.tile i).localAngle X = β) ∧
    (dist Y Z = (f : ℝ) ^ 2 → (D.tile i).localAngle X = γ) := by
  obtain ⟨hab, hac, hbc⟩ := sides_distinct F.hco F.he (by have := F.hef; omega)
  exact localAngle_of_rangeE D hab hac hbc F.hM.hs0 F.hM.hs1 F.hM.hs2 F.hM.hα' F.hM.hβ' F.hM.hγ' hr

theorem dist_Lam (x y x' y' : ℝ) : dist (Lam F x y) (Lam F x' y') = ‖vec F (x - x') (y - y')‖ := by
  rw [dist_eq_norm, Lam_sub]

/-- A straight tile at `x`: `x` in the open edge `(pts a, pts (a+1))`. -/
theorem straight_count {x : Plane} {i : Fin N} {a : Fin 3}
    (hx : x ∈ openSegment ℝ ((D.tile i).pts a) ((D.tile i).pts (a + 1))) :
    (D.tile i).localAngle x = 2 * Real.pi ∨ (D.tile i).localAngle x = Real.pi :=
  (Level2LemmaGReal.straight_of_openSeg (D.tile i) hx).2

theorem card_two {x : Plane} {θ : ℝ} {i1 i2 : Fin N} (h12 : i1 ≠ i2)
    (h1 : (D.tile i1).localAngle x = θ) (h2 : (D.tile i2).localAngle x = θ) :
    2 ≤ ({i | (D.tile i).localAngle x = θ} : Finset (Fin N)).card := by
  classical
  have hsub : ({i1, i2} : Finset (Fin N)) ⊆ ({i | (D.tile i).localAngle x = θ} : Finset (Fin N)) := by
    intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact mem_filter_of h1
    · exact mem_filter_of h2
  have := Finset.card_le_card hsub; rwa [Finset.card_pair h12] at this

theorem card_one {x : Plane} {θ : ℝ} {i1 : Fin N} (h1 : (D.tile i1).localAngle x = θ) :
    1 ≤ ({i | (D.tile i).localAngle x = θ} : Finset (Fin N)).card :=
  Finset.card_pos.mpr ⟨i1, mem_filter_of h1⟩

/-- In a set of card `≤ 2` containing two distinct known members, every member is one of them. -/
theorem mem_of_card_two {x : Plane} {θ : ℝ} {i1 i2 z : Fin N} (h12 : i1 ≠ i2)
    (h1 : (D.tile i1).localAngle x = θ) (h2 : (D.tile i2).localAngle x = θ)
    (hc : ({i | (D.tile i).localAngle x = θ} : Finset (Fin N)).card ≤ 2)
    (hz : (D.tile z).localAngle x = θ) : z = i1 ∨ z = i2 := by
  classical
  have hsub : ({i1, i2} : Finset (Fin N)) ⊆ ({i | (D.tile i).localAngle x = θ} : Finset (Fin N)) := by
    intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact mem_filter_of h1
    · exact mem_filter_of h2
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair h12]; exact hc)
  have : z ∈ ({i1, i2} : Finset (Fin N)) := by rw [heq]; exact mem_filter_of hz
  simpa using this

/-! ## §3 The cells -/

/-- The up cell `T₃ + Λ(i,t) = (Λ(i,t)[α], Λ(i+1,t)[γ], Λ(i,t+1)[β])` (strip `i+1`, band `B_{i+t}`;
`b` along `w`, `c` on `L_i`'s right side, `a` on row `i+t+1`). -/
noncomputable def Up (F : HFrame D e f α β γ) (i t : ℕ) : Set Plane :=
  {Lam F i t, Lam F ((i : ℝ) + 1) t, Lam F i ((t : ℝ) + 1)}
/-- The down cell `Z₀ + Λ(i,t) = (Λ(i+1,t)[β], Λ(i,t+1)[γ], Λ(i+1,t+1)[α])` (strip `i+1`, band
`B_{i+t+1}`; `a` on row `i+t+1`, `c` on `L_{i+1}`'s left side, `b` the diagonal). -/
noncomputable def Dn (F : HFrame D e f α β γ) (i t : ℕ) : Set Plane :=
  {Lam F ((i : ℝ) + 1) t, Lam F i ((t : ℝ) + 1), Lam F ((i : ℝ) + 1) ((t : ℝ) + 1)}
/-- The swap at the slot `Λ(x,y)`: `α` there, `c` along `w`, `b` along the row line (down). -/
noncomputable def Xs (F : HFrame D e f α β γ) (x y : ℝ) : Set Plane :=
  {Lam F x y, Lam F (x + (f : ℝ) ^ 2 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) y,
    Lam F x (y + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2)}

theorem dist_ab {x y : ℝ} : dist (Lam F (x + 1) y) (Lam F x (y + 1)) = (e : ℝ) * f := by
  rw [dist_Lam, show x + 1 - x = 1 by ring, show y - (y + 1) = -1 by ring,
    show vec F 1 (-1) = - vec F (-1) 1 by rw [vec_neg]; norm_num, norm_neg, norm_vec_m11]

theorem dist_b {x y : ℝ} : dist (Lam F (x + 1) y) (Lam F x y) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
  rw [dist_Lam, show x + 1 - x = 1 by ring, sub_self, norm_vec_10]

theorem dist_c {x y : ℝ} : dist (Lam F x (y + 1)) (Lam F x y) = (f : ℝ) ^ 2 := by
  rw [dist_Lam, sub_self, show y + 1 - y = 1 by ring, norm_vec_01]

/-- Angles of the up cell: `α` at `Λ(i,t)`, `γ` at `Λ(i+1,t)`, `β` at `Λ(i,t+1)`. -/
theorem Up_angles {i t : ℕ} {k : Fin N} (hk : Set.range (D.tile k).pts = Up F i t) :
    (D.tile k).localAngle (Lam F i t) = α ∧ (D.tile k).localAngle (Lam F ((i : ℝ) + 1) t) = γ ∧
      (D.tile k).localAngle (Lam F i ((t : ℝ) + 1)) = β := by
  have h1 : Set.range (D.tile k).pts = {Lam F i t, Lam F ((i : ℝ) + 1) t, Lam F i ((t : ℝ) + 1)} :=
    hk
  have h2 : Set.range (D.tile k).pts = {Lam F ((i : ℝ) + 1) t, Lam F i ((t : ℝ) + 1), Lam F i t} := by
    rw [h1]; ext y; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have h3 : Set.range (D.tile k).pts = {Lam F i ((t : ℝ) + 1), Lam F i t, Lam F ((i : ℝ) + 1) t} := by
    rw [h1]; ext y; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  refine ⟨(angle_of_range F h1).1 (dist_ab F), (angle_of_range F h2).2.2 (dist_c F),
    (angle_of_range F h3).2.1 ?_⟩
  rw [dist_comm]; exact dist_b F

/-- Angles of the down cell: `β` at `Λ(i+1,t)`, `γ` at `Λ(i,t+1)`, `α` at `Λ(i+1,t+1)`. -/
theorem Dn_angles {i t : ℕ} {k : Fin N} (hk : Set.range (D.tile k).pts = Dn F i t) :
    (D.tile k).localAngle (Lam F ((i : ℝ) + 1) t) = β ∧
      (D.tile k).localAngle (Lam F i ((t : ℝ) + 1)) = γ ∧
      (D.tile k).localAngle (Lam F ((i : ℝ) + 1) ((t : ℝ) + 1)) = α := by
  have h1 : Set.range (D.tile k).pts
      = {Lam F ((i : ℝ) + 1) t, Lam F i ((t : ℝ) + 1), Lam F ((i : ℝ) + 1) ((t : ℝ) + 1)} := hk
  have h2 : Set.range (D.tile k).pts
      = {Lam F i ((t : ℝ) + 1), Lam F ((i : ℝ) + 1) ((t : ℝ) + 1), Lam F ((i : ℝ) + 1) t} := by
    rw [h1]; ext y; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have h3 : Set.range (D.tile k).pts
      = {Lam F ((i : ℝ) + 1) ((t : ℝ) + 1), Lam F ((i : ℝ) + 1) t, Lam F i ((t : ℝ) + 1)} := by
    rw [h1]; ext y; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  refine ⟨(angle_of_range F h1).2.1 ?_, (angle_of_range F h2).2.2 (dist_c F),
    (angle_of_range F h3).1 (dist_ab F)⟩
  rw [dist_comm]; exact dist_b F

end Erdos634.Draft.RowWallReal

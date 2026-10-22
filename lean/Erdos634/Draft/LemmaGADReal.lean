-- Draft/LemmaGADReal.lean — R8 (Lemma G at level `K`, (private working notes, not included) §5.8,
-- review_S2B, review2_R8S4) ON THE ANTI-DIAGONAL `AD_K`, for real `m = 1` dissections in the apex
-- frame: `AD_K` (through `KV` and `KP′`, rigid ends: `KP′` two `γ`'s, `KV` pierced) has far side
-- `a^K`; the tile across each `a`-edge of `K·T₂`'s top row is the half-turn (`K`-translate) or the
-- mirror; any mirror forces `N_K` at `KP′` (PROP).  The six-fill catalogue at `KP′` is NOT here.
-- Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
--
-- Build (scratch oleans; never .lake): LemmaGRowReal olean in $S, then
--   lake env bash -c 'LEAN_PATH=$S:$LEAN_PATH lean Erdos634/Draft/LemmaGADReal.lean'
import Erdos634.Draft.LemmaGRowReal

namespace Erdos634.Draft.RowWallReal

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.HalfTurnR3R4
open Erdos634.Draft.HalfTurnR3R4Glue Erdos634.Draft.CornerAdjacency
open Erdos634.Draft.HalfTurnR3R4Order Erdos634.Draft.MirrorStripR2Real
open Erdos634.Draft.HalfTurnR4Real

variable {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ}
variable (F : HFrame D e f α β γ)

/-! ## §1 The `Λ₂` cells in lattice coordinates -/

/-- `T₂ + iV + tP′` (translate of `T₂ = (A[α], V[β], P′[γ])` by `i(V − A) + t(P′ − A)`). -/
def T2c (F : HFrame D e f α β γ) (i t : ℕ) : Set Plane :=
  {F.A + (i : ℝ) • (F.V - F.A) + (t : ℝ) • (F.P - F.A),
    F.V + (i : ℝ) • (F.V - F.A) + (t : ℝ) • (F.P - F.A),
    F.P + (i : ℝ) • (F.V - F.A) + (t : ℝ) • (F.P - F.A)}

/-- `K + iV + tP′` (`K = (V[γ], P′[β], V + P′ − A[α])`, the half-turn of `T₂` across `VP′`). -/
def Kc (F : HFrame D e f α β γ) (i t : ℕ) : Set Plane :=
  {F.V + (i : ℝ) • (F.V - F.A) + (t : ℝ) • (F.P - F.A),
    F.P + (i : ℝ) • (F.V - F.A) + (t : ℝ) • (F.P - F.A),
    F.V + F.P - F.A + (i : ℝ) • (F.V - F.A) + (t : ℝ) • (F.P - F.A)}

theorem VA_vec (FC : ApexPlacement.FrameCoords F) : F.V - F.A = vec F (1 + cb e f) (-1) := by
  rw [V_eq F FC]; simp only [Lam]; abel

theorem PA_vec : F.P - F.A = vec F 1 0 := by simp [vec, w]

theorem T2c_eq (FC : ApexPlacement.FrameCoords F) (i t : ℕ) :
    T2c F i t = {Lam F ((i : ℝ) * (1 + cb e f) + t) (-(i : ℝ)),
      Lam F (((i : ℝ) + 1) * (1 + cb e f) + t) (-((i : ℝ) + 1)),
      Lam F ((i : ℝ) * (1 + cb e f) + t + 1) (-(i : ℝ))} := by
  have hV : F.V = F.A + vec F (1 + cb e f) (-1) := by rw [← VA_vec F FC]; abel
  have hP : F.P = F.A + vec F 1 0 := by rw [← PA_vec F]; abel
  rw [T2c, VA_vec F FC, PA_vec F, hV, hP]
  simp only [Lam, vec]
  congr 1
  · module
  congr 1
  · module
  · rw [Set.singleton_eq_singleton_iff]; module

theorem Kc_eq (FC : ApexPlacement.FrameCoords F) (i t : ℕ) :
    Kc F i t = {Lam F (((i : ℝ) + 1) * (1 + cb e f) + t) (-((i : ℝ) + 1)),
      Lam F ((i : ℝ) * (1 + cb e f) + t + 1) (-(i : ℝ)),
      Lam F (((i : ℝ) + 1) * (1 + cb e f) + t + 1) (-((i : ℝ) + 1))} := by
  have hV : F.V = F.A + vec F (1 + cb e f) (-1) := by rw [← VA_vec F FC]; abel
  have hP : F.P = F.A + vec F 1 0 := by rw [← PA_vec F]; abel
  rw [Kc, VA_vec F FC, PA_vec F, hV, hP]
  simp only [Lam, vec]
  congr 1
  · module
  congr 1
  · module
  · rw [Set.singleton_eq_singleton_iff]; module

/-- Points `Λ(x, y)` with `y < 0` (the `Λ₂` side of `m₀`): interior when `x > 0`,
`x(2f² − e²) + y(3f² − e²) > 0` (inside the apex cone) and `x + y < f` (above the base). -/
theorem Lam_interior2 (FC : ApexPlacement.FrameCoords F) {x y : ℝ} (hx : 0 < x)
    (hxy : 0 < x * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) + y * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))
    (hlt : x + y < f) : Lam F x y ∈ interior D.target.carrier := by
  obtain ⟨s3, t3, hs3, ht3, hP, hv3, hsum3⟩ := FC.hP
  have hf := f_pos' F
  have hf0 : (f : ℝ) ≠ 0 := hf.ne'
  have heR : (2 : ℝ) ≤ e := by exact_mod_cast F.he
  have hefR : (e : ℝ) + 2 ≤ f := by exact_mod_cast F.hef
  have hK3 : 0 < 3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have hL : Lam F x y = F.A + ((x * s3 + y * (1 / (f : ℝ))) • ((F.A + ((f : ℝ) ^ 3) • F.uL) - F.A)
      + (x * t3) • (F.R - F.A)) := by
    have hv : ((f : ℝ) ^ 2) • F.uL = (1 / (f : ℝ)) • (((f : ℝ) ^ 3) • F.uL) := by
      rw [smul_smul]; congr 1; field_simp
    simp only [Lam, vec, w, v]
    rw [hP, hv, add_sub_cancel_left]
    module
  rw [hL]
  have htv' : t3 = f / (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by
    rw [eq_div_iff hK3.ne']; exact hv3
  have hsv : s3 = 1 / (f : ℝ) - t3 := by linarith
  have h1 : 0 < x * s3 + y * (1 / (f : ℝ)) := by
    rw [hsv]
    have : x * (1 / (f : ℝ) - t3) + y * (1 / (f : ℝ))
        = (x * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) + y * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)) /
          ((f : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)) := by
      have hK3' : 3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ≠ 0 := hK3.ne'
      have hK3'' : (f : ℝ) ^ 2 * 3 - (e : ℝ) ^ 2 ≠ 0 := by intro h; apply hK3'; linarith
      rw [eq_div_iff (mul_ne_zero hf0 hK3'), htv']
      field_simp
      ring
    rw [this]; positivity
  have h := FC.hcone.inter (x * s3 + y * (1 / (f : ℝ))) (x * t3) 1 h1 (by positivity) one_pos (by
    rw [one_mul, show x * s3 + y * (1 / (f : ℝ)) + x * t3 = x * (s3 + t3) + y * (1 / f) by ring,
      hsum3, show x * (1 / (f : ℝ)) + y * (1 / f) = (x + y) / f by ring, div_lt_one hf]
    exact hlt)
  rwa [one_smul] at h

/-! ## §2 The anti-diagonal functional and chain -/

/-- `adF = col + (c/b)·rho`: constant on the anti-diagonals `AD_n = {adF = adF A + n}` (direction
`V − P′ = vec (c/b) (−1)`). -/
noncomputable def adF (F : HFrame D e f α β γ) : Plane →ₗ[ℝ] ℝ := col F + cb e f • rho F

theorem adF_vec (FC : ApexPlacement.FrameCoords F) (p q : ℝ) :
    adF F (vec F p q) = p + cb e f * q := by
  simp only [adF, LinearMap.add_apply, LinearMap.smul_apply, col_vec F FC, rho_vec F FC,
    smul_eq_mul]

theorem adF_Lam (FC : ApexPlacement.FrameCoords F) (x y : ℝ) :
    adF F (Lam F x y) = adF F F.A + (x + cb e f * y) := by
  rw [Lam, map_add, adF_vec F FC]

theorem adF_ne (FC : ApexPlacement.FrameCoords F) : adF F ≠ 0 := by
  intro h; have := adF_vec F FC 1 0; rw [h, LinearMap.zero_apply] at this; norm_num at this

/-- The far side (away from `A`) of `AD_x`: edges on `AD_x` whose tile lies in `{adF ≥ adF A + x}`. -/
noncomputable def adChain (F : HFrame D e f α β γ) (x : ℝ) : Finset (Fin N × Fin 3) :=
  D.toDissection.lineChain (-(adF F)) (-(adF F F.A + x))

theorem mem_adChain {x : ℝ} {z : Fin N} {m : Fin 3}
    (h1 : adF F ((D.tile z).pts m) = adF F F.A + x)
    (h2 : adF F ((D.tile z).pts (m + 1)) = adF F F.A + x)
    (hall : ∀ k, adF F F.A + x ≤ adF F ((D.tile z).pts k)) : (z, m) ∈ adChain F x := by
  rw [adChain, Dissection.mem_lineChain]
  simp only [LinearMap.neg_apply, neg_inj, neg_le_neg_iff]
  exact ⟨h1, h2, hall⟩

include F in
theorem cb_poly : (1 + cb e f) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) - (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    = (f : ℝ) ^ 4 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by
  obtain ⟨-, hb0, -, -, -⟩ := consts F
  rw [cb]; field_simp; ring

/-- The open stretch of `AD_K` from `KP′` (`s = 0`) to `KV` (`s = K`) is interior (`Kc < fb`). -/
theorem ad_interior (FC : ApexPlacement.FrameCoords F) (K : ℕ) (hK : 1 ≤ K)
    (hKc : (K : ℝ) * (f : ℝ) ^ 2 < (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) {s : ℝ} (hs0 : 0 ≤ s)
    (hsK : s ≤ K) : Lam F ((K : ℝ) + s * cb e f) (-s) ∈ interior D.target.carrier := by
  obtain ⟨ha0, hb0, hc0, hbc, hac⟩ := consts F
  obtain ⟨hcb0, hcb1⟩ := cb_pos F
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have heR : (2 : ℝ) ≤ e := by exact_mod_cast F.he
  have hefR : (e : ℝ) + 2 ≤ f := by exact_mod_cast F.hef
  have hq : 0 < (f : ℝ) ^ 4 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) :=
    div_pos (pow_pos (f_pos' F) 4) hb0
  have hpoly := cb_poly F
  have h2 : 0 < 2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have hKcb : (K : ℝ) * cb e f < f := by
    rw [cb, ← mul_div_assoc, div_lt_iff₀ hb0]; linarith
  apply Lam_interior2 F FC (by positivity)
  · -- inside the apex cone: linear in `s`, positive at `s = 0` and `s = K`
    set δ := cb e f * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) - (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) with hδ
    have hform : ((K : ℝ) + s * cb e f) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
        + -s * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) = K * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) + s * δ := by
      rw [hδ]; ring
    rw [hform]
    rcases le_or_gt 0 δ with hd | hd
    · have : 0 ≤ s * δ := mul_nonneg hs0 hd
      have : 0 < (K : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by positivity
      linarith
    · have h1 : (K : ℝ) * δ ≤ s * δ := mul_le_mul_of_nonpos_right hsK hd.le
      have h3 : 0 < (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) + δ := by rw [hδ]; linarith
      have : 0 < (K : ℝ) * ((2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) + δ) := by positivity
      nlinarith
  · -- above the base: `K + s(c/b − 1) ≤ K·c/b < f`
    have : s * (cb e f - 1) ≤ K * (cb e f - 1) := mul_le_mul_of_nonneg_right hsK (by linarith)
    nlinarith

set_option maxHeartbeats 1000000 in
/-- **(1) on `AD_K`: the far side is `a^K`.**  `[KP′, KV]` is a wall (near side: the `a`-edges of
`T₂ + iV + (K−1−i)P′`, `i < K`), interior (`Kc < fb`), with ends not straddled from the far side
(hypotheses `hs0`, `hsK`, discharged in `r8_ad`), so its far side is a whole-edge word of value `K·a`,
all `a` by **m = 1** (`Inflation.a_side_no_b`, `a_side_rigid`, `K < f`).  Stated for a far edge leaving
`Λ(p, q)` (`−K < q ≤ 0`) along `V − P′`. -/
theorem ad_all (L : LFrame F) (K : ℕ) (hK : 1 ≤ K) (hKf : K + 1 ≤ f)
    (hKc : (K : ℝ) * (f : ℝ) ^ 2 < (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))
    (hT2 : ∀ i t, i + t + 1 = K → Present D (T2c F i t))
    (hs0 : ¬ TraceCovering.Straddled D.toDissection (-(adF F)) (-(adF F F.A + (K : ℝ)))
      (Lam F (K : ℝ) 0))
    (hsK : ¬ TraceCovering.Straddled D.toDissection (-(adF F)) (-(adF F F.A + (K : ℝ)))
      (Lam F ((K : ℝ) + K * cb e f) (-(K : ℝ)))) :
    ∀ ε ∈ adChain F (K : ℝ), ∀ p q ℓ : ℝ, 0 < ℓ → -(K : ℝ) < q → q ≤ 0 →
      p + cb e f * q = (K : ℝ) →
      EdgeIs D ε (Lam F p q)
        (Lam F (p + ℓ / ((e : ℝ) * f) * cb e f) (q - ℓ / ((e : ℝ) * f))) →
      ℓ = (e : ℝ) * f := by
  classical
  have FC := L.FC
  obtain ⟨ha0, hb0, hc0, hbc, hac⟩ := consts F
  obtain ⟨hcb0, hcb1⟩ := cb_pos F
  have hKR : (K : ℝ) + 1 ≤ f := by exact_mod_cast hKf
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hu1 : ‖(1 / ((e : ℝ) * f)) • vec F (cb e f) (-1)‖ = 1 := by
    rw [norm_smul, norm_VP, Real.norm_of_nonneg (by positivity), one_div_mul_cancel ha0.ne']
  have hu0 := TraceCovering.ne_zero_of_norm hu1
  have hφu : adF F ((1 / ((e : ℝ) * f)) • vec F (cb e f) (-1)) = 0 := by
    rw [map_smul, adF_vec F FC]; simp
  have hg : adF F ≠ 0 := adF_ne F FC
  have hg' : (-(adF F) : Plane →ₗ[ℝ] ℝ) ≠ 0 := fun h => hg (neg_eq_zero.mp h)
  have hgd : ∀ y, (-(adF F)) y = -(adF F F.A + (K : ℝ)) ↔ adF F y = adF F F.A + (K : ℝ) :=
    TraceCovering.neg_iff
  have hX : adF F (Lam F (K : ℝ) 0) = adF F F.A + (K : ℝ) := by rw [adF_Lam F FC]; ring
  have hrow : ∀ x : ℝ, Lam F (K : ℝ) 0 + x • ((1 / ((e : ℝ) * f)) • vec F (cb e f) (-1))
      = Lam F ((K : ℝ) + x / ((e : ℝ) * f) * cb e f) (-(x / ((e : ℝ) * f))) := by
    intro x
    rw [smul_smul, vec_smul]
    apply Lam_add_eq F <;> ring
  have hst : (0 : ℝ) ≤ (K : ℝ) * ((e : ℝ) * f) := by positivity
  have hint : ∀ x ∈ Set.Ioo 0 ((K : ℝ) * ((e : ℝ) * f)),
      Lam F (K : ℝ) 0 + x • ((1 / ((e : ℝ) * f)) • vec F (cb e f) (-1))
        ∈ interior D.target.carrier := by
    intro x hx
    rw [hrow]
    have h1 : x / ((e : ℝ) * f) < (K : ℝ) := by rw [div_lt_iff₀ ha0]; exact hx.2
    exact ad_interior F FC K hK hKc (div_nonneg hx.1.le ha0.le) h1.le
  have hwall : ∀ x ∈ Set.Ioo 0 ((K : ℝ) * ((e : ℝ) * f)), ∀ i,
      Lam F (K : ℝ) 0 + x • ((1 / ((e : ℝ) * f)) • vec F (cb e f) (-1))
        ∉ interior (D.tile i).carrier := by
    intro x hx i
    have hq0 : 0 ≤ x / ((e : ℝ) * f) := div_nonneg hx.1.le ha0.le
    have hk1 : ((⌊x / ((e : ℝ) * f)⌋₊ : ℕ) : ℝ) ≤ x / ((e : ℝ) * f) := Nat.floor_le hq0
    have hk2 : x / ((e : ℝ) * f) < ((⌊x / ((e : ℝ) * f)⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
    set k := ⌊x / ((e : ℝ) * f)⌋₊ with hk
    have hkx : (k : ℝ) * ((e : ℝ) * f) ≤ x := by rwa [le_div_iff₀ ha0] at hk1
    have hxk : x < ((k : ℝ) + 1) * ((e : ℝ) * f) := by rwa [div_lt_iff₀ ha0] at hk2
    have hkK : k < K := by
      have h1 : (k : ℝ) * ((e : ℝ) * f) < (K : ℝ) * ((e : ℝ) * f) := lt_of_le_of_lt hkx hx.2
      exact_mod_cast lt_of_mul_lt_mul_right h1 ha0.le
    obtain ⟨t', ht'⟩ : ∃ t', k + t' + 1 = K := ⟨K - k - 1, by omega⟩
    have ht'R : (t' : ℝ) = (K : ℝ) - k - 1 := by
      have : ((k + t' + 1 : ℕ) : ℝ) = K := by exact_mod_cast ht'
      push_cast at this; linarith
    obtain ⟨iz, hiz⟩ := hT2 k t' ht'
    rw [T2c_eq F FC] at hiz
    have hP : Lam F ((k : ℝ) * (1 + cb e f) + t' + 1) (-(k : ℝ)) ∈ Set.range (D.tile iz).pts := by
      rw [hiz]; exact mem3_3
    have hQ : Lam F (((k : ℝ) + 1) * (1 + cb e f) + t') (-((k : ℝ) + 1))
        ∈ Set.range (D.tile iz).pts := by rw [hiz]; exact mem3_2
    obtain ⟨m, hm⟩ := edge_idx hP hQ (Lam_ne F FC (Or.inr (by intro h; linarith)))
    have e1 : Lam F ((k : ℝ) * (1 + cb e f) + t' + 1) (-(k : ℝ)) = Lam F (K : ℝ) 0
        + ((k : ℝ) * ((e : ℝ) * f)) • ((1 / ((e : ℝ) * f)) • vec F (cb e f) (-1)) := by
      rw [hrow, mul_div_cancel_right₀ _ ha0.ne']; congr 1; rw [ht'R]; ring
    have e2 : Lam F (((k : ℝ) + 1) * (1 + cb e f) + t') (-((k : ℝ) + 1)) = Lam F (K : ℝ) 0
        + (((k : ℝ) + 1) * ((e : ℝ) * f)) • ((1 / ((e : ℝ) * f)) • vec F (cb e f) (-1)) := by
      rw [hrow, mul_div_cancel_right₀ _ ha0.ne']; congr 1; rw [ht'R]; ring
    have hseg : Lam F (K : ℝ) 0 + x • ((1 / ((e : ℝ) * f)) • vec F (cb e f) (-1)) ∈
        segment ℝ (Lam F ((k : ℝ) * (1 + cb e f) + t' + 1) (-(k : ℝ)))
          (Lam F (((k : ℝ) + 1) * (1 + cb e f) + t') (-((k : ℝ) + 1))) := by
      rw [e1, e2, TraceCovering.segment_param]
      exact ⟨x, ⟨le_trans (min_le_left _ _) hkx, le_trans hxk.le (le_max_right _ _)⟩, rfl⟩
    have hmem : Lam F (K : ℝ) 0 + x • ((1 / ((e : ℝ) * f)) • vec F (cb e f) (-1))
        ∈ (D.tile iz).edge m := by
      rw [Tri.edge]
      rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact hseg
      · rw [h1, h2, segment_symm]; exact hseg
    exact D.toDissection.edge_point_not_interior hmem i
  have hs : ¬ TraceCovering.Straddled D.toDissection (-(adF F)) (-(adF F F.A + (K : ℝ)))
      (Lam F (K : ℝ) 0 + (0 : ℝ) • ((1 / ((e : ℝ) * f)) • vec F (cb e f) (-1))) := by
    rw [zero_smul, add_zero]; exact hs0
  have hKe : Lam F (K : ℝ) 0 + ((K : ℝ) * ((e : ℝ) * f)) • ((1 / ((e : ℝ) * f)) • vec F (cb e f) (-1))
      = Lam F ((K : ℝ) + K * cb e f) (-(K : ℝ)) := by
    rw [hrow, mul_div_cancel_right₀ _ ha0.ne']
  have ht : ¬ TraceCovering.Straddled D.toDissection (-(adF F)) (-(adF F F.A + (K : ℝ)))
      (Lam F (K : ℝ) 0 + ((K : ℝ) * ((e : ℝ) * f)) • ((1 / ((e : ℝ) * f)) • vec F (cb e f) (-1))) := by
    rw [hKe]; exact hsK
  have hsum := TraceCovering.wall_sum (D := D.toDissection) hg' hgd hg hX hφu hu1 hst hint hwall
    hs ht
  intro ε hε p q ℓ hℓ hq1 hq2 hpq hE
  have hpq' : (D.tile ε.1).pts ε.2 ≠ (D.tile ε.1).pts (ε.2 + 1) :=
    pts_ne _ (TraceCovering.fin3_succ_ne ε.2)
  have hPe : Lam F p q = Lam F (K : ℝ) 0 +
      ((-q) * ((e : ℝ) * f)) • ((1 / ((e : ℝ) * f)) • vec F (cb e f) (-1)) := by
    rw [hrow, mul_div_cancel_right₀ _ ha0.ne']; congr 1
    · linarith
    · ring
  have hQe : Lam F (p + ℓ / ((e : ℝ) * f) * cb e f) (q - ℓ / ((e : ℝ) * f)) =
      Lam F (K : ℝ) 0 + ((-q) * ((e : ℝ) * f) + ℓ) •
        ((1 / ((e : ℝ) * f)) • vec F (cb e f) (-1)) := by
    rw [hrow, add_div, mul_div_cancel_right₀ _ ha0.ne']; congr 1
    · linarith
    · ring
  have hx0 : 0 ≤ (-q) * ((e : ℝ) * f) := mul_nonneg (by linarith) ha0.le
  have hxK : (-q) * ((e : ℝ) * f) < (K : ℝ) * ((e : ℝ) * f) :=
    mul_lt_mul_of_pos_right (by linarith) ha0
  by_cases hin : (-q) * ((e : ℝ) * f) + ℓ ≤ (K : ℝ) * ((e : ℝ) * f)
  · have hseg : ∀ x, 0 ≤ x → x ≤ (K : ℝ) * ((e : ℝ) * f) →
        Lam F (K : ℝ) 0 + x • ((1 / ((e : ℝ) * f)) • vec F (cb e f) (-1)) ∈
          segment ℝ (Lam F (K : ℝ) 0 + (0 : ℝ) • ((1 / ((e : ℝ) * f)) • vec F (cb e f) (-1)))
            (Lam F (K : ℝ) 0 + ((K : ℝ) * ((e : ℝ) * f)) •
              ((1 / ((e : ℝ) * f)) • vec F (cb e f) (-1))) := by
      intro x hx0 hx1
      rw [TraceCovering.segment_param, min_eq_left hst, max_eq_right hst]
      exact ⟨x, ⟨hx0, hx1⟩, rfl⟩
    have hb1 := hseg _ hx0 hxK.le
    have hb2 := hseg _ (by linarith) hin
    rw [← hPe] at hb1
    rw [← hQe] at hb2
    have hsub : (D.tile ε.1).edge ε.2 ⊆ segment ℝ
        (Lam F (K : ℝ) 0 + (0 : ℝ) • ((1 / ((e : ℝ) * f)) • vec F (cb e f) (-1)))
        (Lam F (K : ℝ) 0 + ((K : ℝ) * ((e : ℝ) * f)) •
          ((1 / ((e : ℝ) * f)) • vec F (cb e f) (-1))) := by
      rw [Tri.edge]
      rcases pair_cases hE hpq' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
      · exact (convex_segment _ _).segment_subset hb1 hb2
      · exact (convex_segment _ _).segment_subset hb2 hb1
    have hd : dist (Lam F p q) (Lam F (p + ℓ / ((e : ℝ) * f) * cb e f) (q - ℓ / ((e : ℝ) * f)))
        = ℓ := by
      rw [hPe, hQe, TraceCovering.dist_param hu1, max_eq_right (by linarith),
        min_eq_left (by linarith)]; ring
    have hdM : dist ((D.tile ε.1).pts ε.2) ((D.tile ε.1).pts (ε.2 + 1)) = ℓ := by
      rcases pair_cases hE hpq' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact hd
      · rw [h1, h2, dist_comm]; exact hd
    set sF := (D.toDissection.lineChain (-(adF F)) (-(adF F F.A + (K : ℝ)))).filter
      (fun ε' => (D.tile ε'.1).edge ε'.2 ⊆ segment ℝ
        (Lam F (K : ℝ) 0 + (0 : ℝ) • ((1 / ((e : ℝ) * f)) • vec F (cb e f) (-1)))
        (Lam F (K : ℝ) 0 + ((K : ℝ) * ((e : ℝ) * f)) •
          ((1 / ((e : ℝ) * f)) • vec F (cb e f) (-1)))) with hsF
    have hmemS : ε ∈ sF := Finset.mem_filter.mpr ⟨hε, hsub⟩
    rw [← Finset.add_sum_erase sF _ hmemS] at hsum
    obtain ⟨P', Q', R', hPQR, -⟩ := Erdos634.Geometry.sum_three_values (sF.erase ε)
      (fun ε' => dist ((D.tile ε'.1).pts ε'.2) ((D.tile ε'.1).pts (ε'.2 + 1)))
      ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)
      (fun ε _ => edge_len_mem D F.hM.hs0 F.hM.hs1 F.hM.hs2 ε.1 ε.2)
    simp only at hsum hdM
    rw [hdM] at hsum
    have hee : e ^ 2 ≤ f ^ 2 := Nat.pow_le_pow_left (by have := F.hef; omega) 2
    have hb' : f ^ 2 - e ^ 2 + e ^ 2 = f ^ 2 := Nat.sub_add_cancel hee
    rcases edge_len_mem D F.hM.hs0 F.hM.hs1 F.hM.hs2 ε.1 ε.2 with h | h | h <;> rw [hdM] at h
    · exact h
    · exfalso
      have hreal : ((P' * (e * f) + (Q' + 1) * (f ^ 2 - e ^ 2) + R' * f ^ 2 : ℕ) : ℝ)
          = ((K * (e * f) : ℕ) : ℝ) := by
        push_cast [Nat.cast_sub hee]; rw [h] at hsum; linarith
      have hnat : P' * (e * f) + (Q' + 1) * (f ^ 2 - e ^ 2) + R' * f ^ 2 = K * (e * f) := by
        exact_mod_cast hreal
      have := Inflation.a_side_no_b e f (f ^ 2 - e ^ 2) K P' (Q' + 1) R'
        (by have := F.he; omega) (by have := F.hef; omega) F.hco hb' (by omega) hnat
      omega
    · exfalso
      have hreal : ((P' * (e * f) + Q' * (f ^ 2 - e ^ 2) + (R' + 1) * f ^ 2 : ℕ) : ℝ)
          = ((K * (e * f) : ℕ) : ℝ) := by
        push_cast [Nat.cast_sub hee]; rw [h] at hsum; linarith
      have hnat : P' * (e * f) + Q' * (f ^ 2 - e ^ 2) + (R' + 1) * f ^ 2 = K * (e * f) := by
        exact_mod_cast hreal
      have hQ0 := Inflation.a_side_no_b e f (f ^ 2 - e ^ 2) K P' Q' (R' + 1)
        (by have := F.he; omega) (by have := F.hef; omega) F.hco hb' (by omega) hnat
      rw [hQ0, zero_mul, add_zero] at hnat
      have := Inflation.a_side_rigid e f K P' (R' + 1) (by have := F.he; omega)
        (by have := F.hef; omega) F.hco (by omega) hnat
      omega
  · -- the edge would straddle `KV`
    exfalso
    push Not at hin
    apply ht
    refine ⟨ε, hε, ?_⟩
    have hopen : Lam F (K : ℝ) 0 + ((K : ℝ) * ((e : ℝ) * f)) •
        ((1 / ((e : ℝ) * f)) • vec F (cb e f) (-1)) ∈
        openSegment ℝ (Lam F p q) (Lam F (p + ℓ / ((e : ℝ) * f) * cb e f) (q - ℓ / ((e : ℝ) * f))) := by
      rw [hPe, hQe, TraceCovering.openSegment_param (by linarith), min_eq_left (by linarith),
        max_eq_right (by linarith)]
      exact ⟨_, ⟨hxK, hin⟩, rfl⟩
    rcases pair_cases hE hpq' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    · exact hopen
    · rw [openSegment_symm]; exact hopen

/-! ## §3 (2) The tile across each `a`-edge of `AD_K`: the half-turn or the mirror -/

/-- The mirror of `T₂ + sV + tP′` (`s + t + 1 = K`) across its `a`-edge `[X_{s+1}, X_s]`,
`X_s = Λ(K + s·c/b, −s) = sV + (K − s)P′`, is a tile (at `s = 0` this is `N_K`). -/
def MirT2 (F : HFrame D e f α β γ) (K s : ℕ) : Prop :=
  ∃ M : Plane, IsMirror (Lam F ((K : ℝ) - 1 + s * cb e f) (-(s : ℝ)))
      (Lam F ((K : ℝ) + ((s : ℝ) + 1) * cb e f) (-((s : ℝ) + 1)))
      (Lam F ((K : ℝ) + s * cb e f) (-(s : ℝ))) M ∧
    Present D {Lam F ((K : ℝ) + ((s : ℝ) + 1) * cb e f) (-((s : ℝ) + 1)),
      Lam F ((K : ℝ) + s * cb e f) (-(s : ℝ)), M}

theorem T2c_range (FC : ApexPlacement.FrameCoords F) {K s t : ℕ} (hst : s + t + 1 = K)
    {z : Fin N} (hz : Set.range (D.tile z).pts = T2c F s t) :
    Set.range (D.tile z).pts = {Lam F ((K : ℝ) + s * cb e f) (-(s : ℝ)),
      Lam F ((K : ℝ) + ((s : ℝ) + 1) * cb e f) (-((s : ℝ) + 1)),
      Lam F ((K : ℝ) - 1 + s * cb e f) (-(s : ℝ))} := by
  have hR : ((s + t + 1 : ℕ) : ℝ) = K := by exact_mod_cast hst
  push_cast at hR
  rw [hz, T2c_eq F FC]
  have a1 : Lam F ((s : ℝ) * (1 + cb e f) + t) (-(s : ℝ))
      = Lam F ((K : ℝ) - 1 + s * cb e f) (-(s : ℝ)) := by congr 1; linarith
  have a2 : Lam F (((s : ℝ) + 1) * (1 + cb e f) + t) (-((s : ℝ) + 1))
      = Lam F ((K : ℝ) + ((s : ℝ) + 1) * cb e f) (-((s : ℝ) + 1)) := by congr 1; linarith
  have a3 : Lam F ((s : ℝ) * (1 + cb e f) + t + 1) (-(s : ℝ))
      = Lam F ((K : ℝ) + s * cb e f) (-(s : ℝ)) := by congr 1; linarith
  rw [a1, a2, a3]
  ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto

theorem Kc_range (FC : ApexPlacement.FrameCoords F) {K s t : ℕ} (hst : s + t + 1 = K)
    {z : Fin N} (hz : Set.range (D.tile z).pts = Kc F s t) :
    Set.range (D.tile z).pts = {Lam F ((K : ℝ) + ((s : ℝ) + 1) * cb e f) (-((s : ℝ) + 1)),
      Lam F ((K : ℝ) + s * cb e f) (-(s : ℝ)),
      Lam F ((K : ℝ) + 1 + ((s : ℝ) + 1) * cb e f) (-((s : ℝ) + 1))} := by
  have hR : ((s + t + 1 : ℕ) : ℝ) = K := by exact_mod_cast hst
  push_cast at hR
  rw [hz, Kc_eq F FC]
  have a1 : Lam F (((s : ℝ) + 1) * (1 + cb e f) + t) (-((s : ℝ) + 1))
      = Lam F ((K : ℝ) + ((s : ℝ) + 1) * cb e f) (-((s : ℝ) + 1)) := by congr 1; linarith
  have a2 : Lam F ((s : ℝ) * (1 + cb e f) + t + 1) (-(s : ℝ))
      = Lam F ((K : ℝ) + s * cb e f) (-(s : ℝ)) := by congr 1; linarith
  have a3 : Lam F (((s : ℝ) + 1) * (1 + cb e f) + t + 1) (-((s : ℝ) + 1))
      = Lam F ((K : ℝ) + 1 + ((s : ℝ) + 1) * cb e f) (-((s : ℝ) + 1)) := by congr 1; linarith
  rw [a1, a2, a3]

set_option maxHeartbeats 1000000 in
/-- **R8 on `AD_K`, one junction: the half-turn or the mirror.**  At `X_s = sV + (K−s)P′` with no
straight tile through it, the tile across `T₂ + sV + tP′`'s `a`-flank (along `V − P′`) has an `a`-edge
on `AD_K` (`ad_all`), so it presents `β` (the half-turn `K + sV + tP′`) or `γ` (the mirror). -/
theorem ad_one (L : LFrame F) (K s t : ℕ) (hst : s + t + 1 = K) (hKf : K + 1 ≤ f)
    (hKc : (K : ℝ) * (f : ℝ) ^ 2 < (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))
    (hall : ∀ ε ∈ adChain F (K : ℝ), ∀ p q ℓ : ℝ, 0 < ℓ → -(K : ℝ) < q → q ≤ 0 →
      p + cb e f * q = (K : ℝ) →
      EdgeIs D ε (Lam F p q)
        (Lam F (p + ℓ / ((e : ℝ) * f) * cb e f) (q - ℓ / ((e : ℝ) * f))) →
      ℓ = (e : ℝ) * f)
    {iG : Fin N} (hrG : Set.range (D.tile iG).pts = T2c F s t)
    (hns : ∀ z, (D.tile z).localAngle (Lam F ((K : ℝ) + s * cb e f) (-(s : ℝ))) ≠ Real.pi ∧
      (D.tile z).localAngle (Lam F ((K : ℝ) + s * cb e f) (-(s : ℝ))) ≠ 2 * Real.pi) :
    Present D (Kc F s t) ∨ MirT2 F K s := by
  classical
  have FC := L.FC
  obtain ⟨ha0, hb0, hc0, hbc, hac⟩ := consts F
  obtain ⟨hab, hac', hbc'⟩ := sides_distinct F.hco F.he (by have := F.hef; omega)
  obtain ⟨hcb0, hcb1⟩ := cb_pos F
  have hK := K_ne F FC
  have hK2 := mul_self_pos.mpr hK
  have hR : ((s + t + 1 : ℕ) : ℝ) = K := by exact_mod_cast hst
  push_cast at hR
  have hsK : (s : ℝ) + 1 ≤ K := by linarith [(Nat.cast_nonneg t : (0 : ℝ) ≤ t)]
  have hYint : Lam F ((K : ℝ) + s * cb e f) (-(s : ℝ)) ∈ interior D.target.carrier :=
    ad_interior F FC K (by omega) hKc (by positivity) (by linarith)
  have rG := T2c_range F FC hst hrG
  obtain ⟨mG, hmG, hflG⟩ := flank_of_range rG
  rw [Lam_sub_eq F (by ring : ((K : ℝ) + ((s : ℝ) + 1) * cb e f) - ((K : ℝ) + s * cb e f) = cb e f)
      (by ring : (-((s : ℝ) + 1)) - (-(s : ℝ)) = -1),
    Lam_sub_eq F (by ring : ((K : ℝ) - 1 + s * cb e f) - ((K : ℝ) + s * cb e f) = -1)
      (by ring : (-(s : ℝ)) - (-(s : ℝ)) = 0)] at hflG
  obtain ⟨z, hzG, hYz, hcz⟩ := flank_neighbour_dissection D.toDissection hYint hmG hflG
  rcases hcz with ⟨mz, hmz, U, W, hUW, S, hS, hU0, hside⟩ | ⟨m', hm0, hmpos, hcr, -⟩
  swap
  · exact (hedge_of_ns hns (vec F (cb e f) (-1)) z m' hm0 hmpos hcr).elim
  have hU0n : ‖vec F (cb e f) (-1)‖ = (e : ℝ) * f := norm_VP F
  have hUne : U ≠ 0 := by
    intro h; rw [h, smul_zero] at hU0; rw [hU0, norm_zero] at hU0n; linarith
  obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ : ℝ, ‖U‖ = ℓ := ⟨_, rfl⟩
  have hℓ : 0 < ℓ := hℓdef ▸ norm_pos_iff.mpr hUne
  have hUe : U = (ℓ / ((e : ℝ) * f)) • vec F (cb e f) (-1) := flank_eq hS hU0 hℓdef hU0n ha0
  have hφU : adF F U = 0 := by
    have := congrArg (adF F) hU0
    rw [map_smul, adF_vec F FC, smul_eq_mul] at this
    rcases mul_eq_zero.mp (by linarith : S * adF F U = 0) with h | h
    · linarith
    · exact h
  have hφW : 0 < adF F W := by
    have hW := vec_coords F FC W
    rw [hW, cross_vec, cross_vec] at hside
    rw [hW, adF_vec F FC]
    nlinarith
  have hY : adF F (Lam F ((K : ℝ) + s * cb e f) (-(s : ℝ))) = adF F F.A + (K : ℝ) := by
    rw [adF_Lam F FC]; ring
  have hall3 : ∀ k, adF F F.A + (K : ℝ) ≤ adF F ((D.tile z).pts k) := by
    intro k
    have hk : (D.tile z).pts k ∈ Set.range (D.tile z).pts := ⟨k, rfl⟩
    rw [ApexPlacement.range_of_flank hmz hUW] at hk
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
    rcases hk with h | h | h <;> rw [h]
    · rw [hY]
    · rw [map_add, hY, hφU, add_zero]
    · rw [map_add, hY]; linarith
  obtain ⟨idx, hidx, hE⟩ : ∃ idx : Fin 3, (z, idx) ∈ adChain F (K : ℝ) ∧
      EdgeIs D (z, idx) (Lam F ((K : ℝ) + s * cb e f) (-(s : ℝ)))
        (Lam F ((K : ℝ) + s * cb e f) (-(s : ℝ)) + U) := by
    rcases hUW with ⟨h1, -⟩ | ⟨h1, -⟩
    · have e1 : (D.tile z).pts (mz + 1) = Lam F ((K : ℝ) + s * cb e f) (-(s : ℝ)) + U := by
        rw [h1]; abel
      refine ⟨mz, mem_adChain F (by rw [hmz, hY]) (by rw [e1, map_add, hY, hφU, add_zero])
        hall3, ?_⟩
      simp only [EdgeIs]; rw [hmz, e1]
    · have e1 : (D.tile z).pts (mz + 2) = Lam F ((K : ℝ) + s * cb e f) (-(s : ℝ)) + U := by
        rw [h1]; abel
      have e2 : (D.tile z).pts (mz + 2 + 1) = Lam F ((K : ℝ) + s * cb e f) (-(s : ℝ)) := by
        rw [fin3_add_two_add_one]; exact hmz
      refine ⟨mz + 2, mem_adChain F (by rw [e1, map_add, hY, hφU, add_zero])
        (by rw [e2, hY]) hall3, ?_⟩
      simp only [EdgeIs]; rw [e1, e2, Set.pair_comm]
  have hUlam : Lam F ((K : ℝ) + s * cb e f) (-(s : ℝ)) + U =
      Lam F ((K : ℝ) + s * cb e f + ℓ / ((e : ℝ) * f) * cb e f) (-(s : ℝ) - ℓ / ((e : ℝ) * f)) := by
    rw [hUe, vec_smul]; apply Lam_add_eq F <;> ring
  rw [hUlam] at hE
  have hla := hall (z, idx) hidx _ _ _ hℓ (by linarith) (by linarith) (by ring) hE
  have hU1 : U = vec F (cb e f) (-1) := by rw [hUe, hla, div_self ha0.ne', one_smul]
  have hang := localAngle_at_own_vertex_mem D α β γ F.hM.hα' F.hM.hβ' F.hM.hγ' z mz
  rw [hmz] at hang
  rcases hang with hz | hz | hz
  · exfalso
    obtain ⟨hn, -⟩ := (corner_dataH F hmz hUW).2 hz
    rcases hn with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [hℓdef, hla] at h1; exact hab h1
    · rw [hℓdef, hla] at h1; exact hac' h1
  · -- `β`: the half-turn `K + sV + tP′`
    left
    obtain ⟨hn, hopp⟩ := (corner_dataH F hmz hUW).1 hz
    have hWc : ‖W‖ = (f : ℝ) ^ 2 := by
      rcases hn with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact h2
      · rw [hℓdef, hla] at h1; exact absurd h1 hac'
    have hs2 : cross (vec F (cb e f) (-1)) (vec F (1 + cb e f) (-1)) *
        cross (vec F (cb e f) (-1)) (vec F (-1) 0) < 0 := by
      rw [cross_vec, cross_vec]; nlinarith
    have hr := ident hmz hUW hU1 (by intro h; rw [h, norm_zero] at hU0n; linarith)
      (by have := side_of_across hS hU0 hside hs2; rwa [hU1] at this)
      (by rw [hWc, norm_V]) (by rw [hopp, dist_add_vec, show cb e f - (1 + cb e f) = -1 by ring,
        show (-1 : ℝ) - -1 = 0 by ring, norm_vec_m10])
    obtain ⟨iK, hK'⟩ : ∃ iK, iK = z := ⟨z, rfl⟩
    refine ⟨z, ?_⟩
    rw [hr, Kc_eq F FC]
    have a1 : Lam F ((K : ℝ) + s * cb e f) (-(s : ℝ)) + vec F (cb e f) (-1)
        = Lam F (((s : ℝ) + 1) * (1 + cb e f) + t) (-((s : ℝ) + 1)) :=
      Lam_add_eq F (by linarith) (by ring)
    have a2 : Lam F ((K : ℝ) + s * cb e f) (-(s : ℝ)) + vec F (1 + cb e f) (-1)
        = Lam F (((s : ℝ) + 1) * (1 + cb e f) + t + 1) (-((s : ℝ) + 1)) :=
      Lam_add_eq F (by linarith) (by ring)
    have a3 : Lam F ((K : ℝ) + s * cb e f) (-(s : ℝ))
        = Lam F ((s : ℝ) * (1 + cb e f) + t + 1) (-(s : ℝ)) := by congr 1; linarith
    rw [a1, a2, a3]
    ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  · -- `γ`: the mirror
    right
    obtain ⟨hn, hopp⟩ := corner_dataG F hmz hUW hz
    have hWb : ‖W‖ = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
      rcases hn with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact h2
      · rw [hℓdef, hla] at h1; exact absurd h1 hab
    have eY1 : Lam F ((K : ℝ) + ((s : ℝ) + 1) * cb e f) (-((s : ℝ) + 1))
        = Lam F ((K : ℝ) + s * cb e f) (-(s : ℝ)) + U := by
      rw [hU1]; exact (Lam_add_eq F (by ring) (by ring)).symm
    refine ⟨Lam F ((K : ℝ) + s * cb e f) (-(s : ℝ)) + W, ⟨?_, ?_, ?_⟩, z, ?_⟩
    · intro h
      have := congrArg (adF F) h
      rw [map_add, adF_Lam F FC, adF_Lam F FC] at this
      linarith
    · rw [dist_Lam F ((K : ℝ) - 1 + s * cb e f) (-(s : ℝ)) ((K : ℝ) + ((s : ℝ) + 1) * cb e f)
        (-((s : ℝ) + 1)), show (K : ℝ) - 1 + s * cb e f - ((K : ℝ) + ((s : ℝ) + 1) * cb e f)
          = -(1 + cb e f) by ring, show (-(s : ℝ)) - (-((s : ℝ) + 1)) = 1 by ring,
        show vec F (-(1 + cb e f)) 1 = - vec F (1 + cb e f) (-1) by rw [vec_neg]; norm_num,
        norm_neg, norm_V, eY1, dist_comm, hopp]
    · rw [dist_eq_norm, add_sub_cancel_left, hWb, dist_Lam,
        show (K : ℝ) - 1 + s * cb e f - ((K : ℝ) + s * cb e f) = -1 by ring, sub_self,
        norm_vec_m10]
    · rw [ApexPlacement.range_of_flank hmz hUW, ← eY1]
      ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto

/-! ## §4 The assembly: R8 on `AD_K` -/

/-- Angles of `T₂ + sV + tP′` in the `AD_K` frame (`s + t + 1 = K`): `γ` at `X_s`, `β` at `X_{s+1}`. -/
theorem T2c_angles (FC : ApexPlacement.FrameCoords F) {K s t : ℕ} (hst : s + t + 1 = K)
    {z : Fin N} (hz : Set.range (D.tile z).pts = T2c F s t) :
    (D.tile z).localAngle (Lam F ((K : ℝ) + s * cb e f) (-(s : ℝ))) = γ ∧
      (D.tile z).localAngle (Lam F ((K : ℝ) + ((s : ℝ) + 1) * cb e f) (-((s : ℝ) + 1))) = β := by
  have r := T2c_range F FC hst hz
  have r2 : Set.range (D.tile z).pts = {Lam F ((K : ℝ) + ((s : ℝ) + 1) * cb e f) (-((s : ℝ) + 1)),
      Lam F ((K : ℝ) - 1 + s * cb e f) (-(s : ℝ)), Lam F ((K : ℝ) + s * cb e f) (-(s : ℝ))} := by
    rw [r]; ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  refine ⟨(angle_of_range F r).2.2 ?_, (angle_of_range F r2).2.1 ?_⟩
  · rw [dist_Lam, show (K : ℝ) + ((s : ℝ) + 1) * cb e f - ((K : ℝ) - 1 + s * cb e f) = 1 + cb e f
      by ring, show (-((s : ℝ) + 1)) - (-(s : ℝ)) = -1 by ring, norm_V]
  · rw [dist_Lam, show (K : ℝ) - 1 + s * cb e f - ((K : ℝ) + s * cb e f) = -1 by ring, sub_self,
      norm_vec_m10]

/-- Angles of `K + sV + tP′` (`s + t + 1 = K`): `γ` at `X_{s+1}`, `β` at `X_s`, `α` at `X_{s+1} + w`. -/
theorem Kc_angles (FC : ApexPlacement.FrameCoords F) {K s t : ℕ} (hst : s + t + 1 = K)
    {z : Fin N} (hz : Set.range (D.tile z).pts = Kc F s t) :
    (D.tile z).localAngle (Lam F ((K : ℝ) + ((s : ℝ) + 1) * cb e f) (-((s : ℝ) + 1))) = γ ∧
      (D.tile z).localAngle (Lam F ((K : ℝ) + s * cb e f) (-(s : ℝ))) = β ∧
      (D.tile z).localAngle (Lam F ((K : ℝ) + 1 + ((s : ℝ) + 1) * cb e f) (-((s : ℝ) + 1))) = α := by
  have r := Kc_range F FC hst hz
  have r2 : Set.range (D.tile z).pts = {Lam F ((K : ℝ) + s * cb e f) (-(s : ℝ)),
      Lam F ((K : ℝ) + 1 + ((s : ℝ) + 1) * cb e f) (-((s : ℝ) + 1)),
      Lam F ((K : ℝ) + ((s : ℝ) + 1) * cb e f) (-((s : ℝ) + 1))} := by
    rw [r]; ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have r3 : Set.range (D.tile z).pts = {Lam F ((K : ℝ) + 1 + ((s : ℝ) + 1) * cb e f) (-((s : ℝ) + 1)),
      Lam F ((K : ℝ) + ((s : ℝ) + 1) * cb e f) (-((s : ℝ) + 1)),
      Lam F ((K : ℝ) + s * cb e f) (-(s : ℝ))} := by
    rw [r]; ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  refine ⟨(angle_of_range F r).2.2 ?_, (angle_of_range F r2).2.1 ?_, (angle_of_range F r3).1 ?_⟩
  · rw [dist_Lam, show (K : ℝ) + s * cb e f - ((K : ℝ) + 1 + ((s : ℝ) + 1) * cb e f)
      = -(1 + cb e f) by ring, show (-(s : ℝ)) - (-((s : ℝ) + 1)) = 1 by ring,
      show vec F (-(1 + cb e f)) 1 = - vec F (1 + cb e f) (-1) by rw [vec_neg]; norm_num,
      norm_neg, norm_V]
  · rw [dist_Lam, show (K : ℝ) + 1 + ((s : ℝ) + 1) * cb e f - ((K : ℝ) + ((s : ℝ) + 1) * cb e f)
      = 1 by ring, sub_self, norm_vec_10]
  · rw [dist_Lam, show (K : ℝ) + ((s : ℝ) + 1) * cb e f - ((K : ℝ) + s * cb e f) = cb e f by ring,
      show (-((s : ℝ) + 1)) - (-(s : ℝ)) = -1 by ring, norm_VP]

/-- Angles of the mirror of `T₂ + sV + tP′`: `γ` at `X_s`, `β` at `X_{s+1}`. -/
theorem MirT2_angles {K s : ℕ} {M : Plane}
    (hM : IsMirror (Lam F ((K : ℝ) - 1 + s * cb e f) (-(s : ℝ)))
      (Lam F ((K : ℝ) + ((s : ℝ) + 1) * cb e f) (-((s : ℝ) + 1)))
      (Lam F ((K : ℝ) + s * cb e f) (-(s : ℝ))) M) {z : Fin N}
    (hz : Set.range (D.tile z).pts = {Lam F ((K : ℝ) + ((s : ℝ) + 1) * cb e f) (-((s : ℝ) + 1)),
      Lam F ((K : ℝ) + s * cb e f) (-(s : ℝ)), M}) :
    (D.tile z).localAngle (Lam F ((K : ℝ) + s * cb e f) (-(s : ℝ))) = γ ∧
      (D.tile z).localAngle (Lam F ((K : ℝ) + ((s : ℝ) + 1) * cb e f) (-((s : ℝ) + 1))) = β := by
  obtain ⟨-, h1, h2⟩ := hM
  have r1 : Set.range (D.tile z).pts = {Lam F ((K : ℝ) + s * cb e f) (-(s : ℝ)), M,
      Lam F ((K : ℝ) + ((s : ℝ) + 1) * cb e f) (-((s : ℝ) + 1))} := by
    rw [hz]; ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  refine ⟨(angle_of_range F r1).2.2 ?_, (angle_of_range F hz).2.1 ?_⟩
  · rw [h1, dist_Lam, show (K : ℝ) - 1 + s * cb e f - ((K : ℝ) + ((s : ℝ) + 1) * cb e f)
      = -(1 + cb e f) by ring, show (-(s : ℝ)) - (-((s : ℝ) + 1)) = 1 by ring,
      show vec F (-(1 + cb e f)) 1 = - vec F (1 + cb e f) (-1) by rw [vec_neg]; norm_num,
      norm_neg, norm_V]
  · rw [dist_comm, h2, dist_Lam, show (K : ℝ) - 1 + s * cb e f - ((K : ℝ) + s * cb e f) = -1 by ring,
      sub_self, norm_vec_m10]

/-- `L_i = T₂ + iV` (the chain tiles of `HalfTurnR4Real`) is `T₂ + iV + 0·P′`. -/
theorem Lc_eq (i : ℕ) : F.Lc i = T2c F i 0 := by
  have hVA : F.V - F.A = ((f : ℝ) ^ 2) • F.uR := by rw [F.hV]; abel
  have e1 : F.Vk i = F.A + (i : ℝ) • (F.V - F.A) + ((0 : ℕ) : ℝ) • (F.P - F.A) := by
    rw [HFrame.Vk, hVA, Nat.cast_zero, zero_smul, add_zero, smul_smul]
  have e2 : F.Vk (i + 1) = F.V + (i : ℝ) • (F.V - F.A) + ((0 : ℕ) : ℝ) • (F.P - F.A) := by
    rw [HFrame.Vk, hVA, Nat.cast_zero, zero_smul, add_zero, smul_smul, F.hV]; push_cast; module
  have e3 : F.Qk i = F.P + (i : ℝ) • (F.V - F.A) + ((0 : ℕ) : ℝ) • (F.P - F.A) := by
    rw [HFrame.Qk, hVA, Nat.cast_zero, zero_smul, add_zero, smul_smul]
  rw [HFrame.Lc, e1, e2, e3, T2c]

theorem Vk_eq (FC : ApexPlacement.FrameCoords F) (k : ℕ) :
    F.Vk k = Lam F ((k : ℝ) + k * cb e f) (-(k : ℝ)) := by
  have hVA : ((f : ℝ) ^ 2) • F.uR = vec F (1 + cb e f) (-1) := by
    rw [← VA_vec F FC, F.hV]; abel
  have h1 : ((k : ℝ) * (f : ℝ) ^ 2) • F.uR = (k : ℝ) • (((f : ℝ) ^ 2) • F.uR) := by
    rw [smul_smul]
  rw [HFrame.Vk, h1, hVA, vec_smul, Lam]
  congr 2 <;> ring

set_option maxHeartbeats 2000000 in
/-- **R8 ON `AD_K` — PROVED (clauses (1)–(3) of `proof_H_empty.md` §5.8, anti-diagonal half).**
Given `K·T₂` (`T₂ + iV + tP′`, `i + t ≤ K − 1`; `K + iV + tP′`, `i + t ≤ K − 2` — this contains the
chain `T₂ + jV`, `j < K`), `T₃ + (K−1)P′` (so `KP′` carries two `γ`'s), and `Kc < fb` (so `KV` is
interior, and pierced: `HalfTurnR4Real.pierced_of`, Lemma A):
(1) the far side of `AD_K` from `KP′` to `KV` is `a^K` (**m = 1**: `Inflation.a_side_no_b`,
`a_side_rigid`; both ends rigid: `KP′` by the two `γ`'s, `KV` since the piercer and the `β` of
`T₂ + (K−1)V` leave no room for a second straight tile);
(2) the tile across each `a`-edge `[X_{s+1}, X_s]` of `AD_K` is the half-turn `K + sV + tP′` or the
mirror of `T₂ + sV + tP′`;
(3) PROP: a mirror anywhere on `AD_K` forces the mirror `N_K` at `KP′`. -/
theorem r8_ad (L : LFrame F) (K' : ℕ) (hKf : K' + 2 ≤ f)
    (hKc : ((K' + 1 : ℕ) : ℝ) * (f : ℝ) ^ 2 < (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))
    (hT2 : ∀ i t, i + t + 1 ≤ K' + 1 → Present D (T2c F i t))
    (hK2 : ∀ i t, i + t + 2 ≤ K' + 1 → Present D (Kc F i t))
    (hU : Present D (Up F K' 0)) :
    (∀ ε ∈ adChain F ((K' + 1 : ℕ) : ℝ), ∀ p q ℓ : ℝ, 0 < ℓ → -((K' + 1 : ℕ) : ℝ) < q → q ≤ 0 →
      p + cb e f * q = ((K' + 1 : ℕ) : ℝ) →
      EdgeIs D ε (Lam F p q)
        (Lam F (p + ℓ / ((e : ℝ) * f) * cb e f) (q - ℓ / ((e : ℝ) * f))) →
      ℓ = (e : ℝ) * f) ∧
    (∀ s t, s + t + 1 = K' + 1 → Present D (Kc F s t) ∨ MirT2 F (K' + 1) s) ∧
    (∀ s t, s + t + 1 = K' + 1 → MirT2 F (K' + 1) s → MirT2 F (K' + 1) 0) := by
  classical
  have FC := L.FC
  obtain ⟨ha0, hb0, hc0, hbc, hac⟩ := consts F
  obtain ⟨hcb0, hcb1⟩ := cb_pos F
  obtain ⟨K, hKdef⟩ : ∃ K, K' + 1 = K := ⟨_, rfl⟩
  rw [hKdef] at hKc hT2 hK2 ⊢
  have hKK : (K : ℝ) = (K' : ℝ) + 1 := by rw [← hKdef]; push_cast; ring
  have hKR : (K : ℝ) + 1 ≤ f := by exact_mod_cast (by omega : K + 1 ≤ f)
  -- the corner `KP′ = X₀`: two `γ`'s
  have hX0 : Lam F (K : ℝ) 0 = Lam F ((K : ℝ) + ((0 : ℕ) : ℝ) * cb e f) (-((0 : ℕ) : ℝ)) := by
    simp
  have hK1R : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
  have hX0int : Lam F (K : ℝ) 0 ∈ interior D.target.carrier :=
    Lam_interior F FC (by linarith) le_rfl (by linarith)
  obtain ⟨iT, hrT⟩ := hT2 0 K' (by omega)
  have gT : (D.tile iT).localAngle (Lam F (K : ℝ) 0) = γ := by
    rw [hX0]; exact (T2c_angles F FC (s := 0) (t := K') (K := K) (by omega) hrT).1
  obtain ⟨iU, hrU⟩ := hU
  have gU : (D.tile iU).localAngle (Lam F (K : ℝ) 0) = γ := by
    have := (Up_angles F hrU).2.1; simp only [Nat.cast_zero] at this
    rw [hKK]; exact this
  have hTU : iT ≠ iU := by
    intro h
    have h1 : Lam F (K' : ℝ) 1 ∈ Set.range (D.tile iU).pts := by
      rw [hrU]; simp only [Up, Nat.cast_zero, zero_add]; exact mem3_3
    rw [← h, T2c_range F FC (s := 0) (t := K') (K := K) (by omega) hrT] at h1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    rcases h1 with h1 | h1 | h1 <;> have := (Lam_inj F FC h1).2 <;> push_cast at this <;>
      linarith
  have hns0 := count_gg F hX0int hTU gT gU
  -- the corner `KV = X_K`: the piercer and the `β` of `T₂ + (K−1)V`
  obtain ⟨iL, hrL⟩ := hT2 K' 0 (by omega)
  have hKVeq : Lam F ((K : ℝ) + K * cb e f) (-(K : ℝ))
      = Lam F ((K : ℝ) + ((K' : ℝ) + 1) * cb e f) (-((K' : ℝ) + 1)) := by
    rw [← hKK]
  have gL : (D.tile iL).localAngle (Lam F ((K : ℝ) + K * cb e f) (-(K : ℝ))) = β := by
    rw [hKVeq]; exact (T2c_angles F FC (s := K') (t := 0) (K := K) (by omega) hrL).2
  have hKVint : Lam F ((K : ℝ) + K * cb e f) (-(K : ℝ)) ∈ interior D.target.carrier :=
    ad_interior F FC K (by omega) hKc (by positivity) le_rfl
  have hVK : F.Vk (K' + 1) = Lam F ((K : ℝ) + K * cb e f) (-(K : ℝ)) := by
    rw [Vk_eq F FC, hKdef]
  have hpier := pierced_of F K' (fun i hi => by rw [Lc_eq F]; exact hT2 i 0 (by omega))
    (by rw [hVK]; exact interior_subset hKVint)
  rw [hVK] at hpier
  have hsK : ¬ TraceCovering.Straddled D.toDissection (-(adF F)) (-(adF F F.A + (K : ℝ)))
      (Lam F ((K : ℝ) + K * cb e f) (-(K : ℝ))) := by
    rintro ⟨ε, hε, hxε⟩
    obtain ⟨ε', hε', hxε'⟩ := hpier
    have s1 := straight_count hxε
    have s2 := straight_count hxε'
    obtain ⟨E1, E2⟩ := interior_card_eqs D F.hAng F.hM.hα' F.hM.hβ' F.hM.hγ' hKVint
    have cB := card_one gL
    by_cases heq : ε.1 = ε'.1
    · rw [← heq] at hxε'
      have hme := Level2LemmaGReal.same_edge (D.tile ε.1) hxε hxε'
      obtain ⟨a0, a1, -⟩ := Dissection.mem_lineChain.mp hε
      obtain ⟨b0, b1, -⟩ := Dissection.mem_lineChain.mp hε'
      simp only [LinearMap.neg_apply, neg_inj] at a0 a1 b0 b1
      rw [← heq, ← hme] at b0 b1
      -- the edge would lie on both `r` and `AD_K`
      apply pts_ne (D.tile ε.1) (TraceCovering.fin3_succ_ne ε.2)
      set d := (D.tile ε.1).pts ε.2 - (D.tile ε.1).pts (ε.2 + 1) with hd
      have hφd : adF F d = 0 := by rw [hd, map_sub, a0, a1, sub_self]
      have hhd : F.h d = 0 := by rw [hd, map_sub, b0, b1, sub_self]
      have hdv := vec_coords F FC d
      have hhv : F.h (vec F (1 + cb e f) (-1)) = 0 := by
        rw [← VA_vec F FC, F.hV, add_sub_cancel_left, map_smul, F.hhuR, smul_zero]
      have hlin : ∀ p q : ℝ, F.h (vec F p q) = p * F.h (w F) + q * F.h (v F) := by
        intro p q; simp only [vec, map_add, map_smul, smul_eq_mul]
      rw [hlin] at hhv
      rw [hdv, adF_vec F FC] at hφd
      rw [hdv, hlin] at hhd
      have hw := F.hw_neg
      have hw' : F.h (w F) ≠ 0 := by rw [w]; exact hw.ne
      have hr0 : rho F d = 0 := by
        have : rho F d * F.h (w F) = 0 := by
          have hc : col F d = -(cb e f * rho F d) := by linarith
          rw [hc] at hhd
          linear_combination hhd + rho F d * hhv
        rcases mul_eq_zero.mp this with h | h
        · exact h
        · exact absurd h hw'
      have hc0' : col F d = 0 := by rw [hr0] at hφd; linarith
      rw [hc0', hr0, vec_zero] at hdv
      exact sub_eq_zero.mp hdv
    · have := Level2LemmaGReal.two_straight heq s1 s2
      omega
  have hall := ad_all F L K (by omega) (by omega) hKc (fun i t h => hT2 i t (by omega))
    (nstr_of_ns hns0 _ _) hsK
  -- (2) the dichotomy, from `KP′` outwards
  have key : ∀ s t, s + t + 1 = K → Present D (Kc F s t) ∨ MirT2 F K s := by
    intro s
    induction s with
    | zero =>
      intro t ht
      obtain ⟨iG, hrG⟩ := hT2 0 t (by omega)
      exact ad_one F L K 0 t ht (by omega) hKc hall hrG (by rw [← hX0]; exact hns0)
    | succ s ih =>
      intro t ht
      obtain ⟨iG, hrG⟩ := hT2 (s + 1) t (by omega)
      obtain ⟨iB, hrB⟩ := hT2 s (t + 1) (by omega)
      obtain ⟨iA, hrA⟩ := hK2 s t (by omega)
      have hsR : ((s + 1 + t + 1 : ℕ) : ℝ) = K := by exact_mod_cast ht
      push_cast at hsR
      have hYint : Lam F ((K : ℝ) + ((s + 1 : ℕ) : ℝ) * cb e f) (-((s + 1 : ℕ) : ℝ))
          ∈ interior D.target.carrier :=
        ad_interior F FC K (by omega) hKc (by positivity) (by push_cast; linarith)
      have gG := (T2c_angles F FC ht hrG).1
      have gB : (D.tile iB).localAngle (Lam F ((K : ℝ) + ((s + 1 : ℕ) : ℝ) * cb e f)
          (-((s + 1 : ℕ) : ℝ))) = β := by
        have := (T2c_angles F FC (by omega : s + (t + 1) + 1 = K) hrB).2
        push_cast at this ⊢; exact this
      have gA : (D.tile iA).localAngle (Lam F ((K : ℝ) + ((s + 1 : ℕ) : ℝ) * cb e f)
          (-((s + 1 : ℕ) : ℝ))) = α := by
        have := (Kc_angles F FC (by omega : s + t + 1 = K') hrA).2.2
        have e1 : Lam F ((K' : ℝ) + 1 + ((s : ℝ) + 1) * cb e f) (-((s : ℝ) + 1))
            = Lam F ((K : ℝ) + ((s + 1 : ℕ) : ℝ) * cb e f) (-((s + 1 : ℕ) : ℝ)) := by
          rw [hKK]; congr 1 <;> push_cast <;> ring
        rw [e1] at this; exact this
      have hns : ∀ z, (D.tile z).localAngle (Lam F ((K : ℝ) + ((s + 1 : ℕ) : ℝ) * cb e f)
          (-((s + 1 : ℕ) : ℝ))) ≠ Real.pi ∧ (D.tile z).localAngle (Lam F ((K : ℝ) +
          ((s + 1 : ℕ) : ℝ) * cb e f) (-((s + 1 : ℕ) : ℝ))) ≠ 2 * Real.pi := by
        rcases ih (t + 1) (by omega) with ⟨iD, hrD⟩ | ⟨M, hM, iM, hrM⟩
        · have gD : (D.tile iD).localAngle (Lam F ((K : ℝ) + ((s + 1 : ℕ) : ℝ) * cb e f)
              (-((s + 1 : ℕ) : ℝ))) = γ := by
            have := (Kc_angles F FC (by omega : s + (t + 1) + 1 = K) hrD).1
            push_cast at this ⊢; exact this
          have hGD : iG ≠ iD := by
            intro h
            have h1 : Lam F ((K : ℝ) - 1 + ((s + 1 : ℕ) : ℝ) * cb e f) (-((s + 1 : ℕ) : ℝ))
                ∈ Set.range (D.tile iG).pts := by rw [T2c_range F FC ht hrG]; exact mem3_3
            rw [h, Kc_range F FC (by omega : s + (t + 1) + 1 = K) hrD] at h1
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
            rcases h1 with h1 | h1 | h1 <;> have := Lam_inj F FC h1 <;> push_cast at this <;>
              nlinarith [this.1, this.2]
          exact (count_ag F hYint hGD gA gG gD).1
        · have gM : (D.tile iM).localAngle (Lam F ((K : ℝ) + ((s + 1 : ℕ) : ℝ) * cb e f)
              (-((s + 1 : ℕ) : ℝ))) = β := by
            have := (MirT2_angles F hM hrM).2
            push_cast at this ⊢; exact this
          have hBM : iB ≠ iM := by
            intro h
            have h1 : Lam F ((K : ℝ) - 1 + (s : ℝ) * cb e f) (-(s : ℝ))
                ∈ Set.range (D.tile iB).pts := by
              rw [T2c_range F FC (by omega : s + (t + 1) + 1 = K) hrB]; exact mem3_3
            rw [h, hrM] at h1
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
            rcases h1 with h1 | h1 | h1
            · have := Lam_inj F FC h1; linarith [this.2]
            · have := Lam_inj F FC h1; linarith [this.1]
            · exact hM.1 h1.symm
          obtain ⟨E1, E2⟩ := interior_card_eqs D F.hAng F.hM.hα' F.hM.hβ' F.hM.hγ' hYint
          have cB2 := card_two hBM gB gM
          have cG := card_one gG
          exact fun z => ⟨fun h => by have := card_one h; omega,
            fun h => by have := card_one h; omega⟩
      exact ad_one F L K (s + 1) t ht (by omega) hKc hall hrG hns
  refine ⟨hall, key, ?_⟩
  -- (3) PROP
  intro s
  induction s with
  | zero => intro t ht hM; exact hM
  | succ s ih =>
    intro t ht hMs
    apply ih (t + 1) (by omega)
    rcases key s (t + 1) (by omega) with ⟨iD, hrD⟩ | hM'
    · exfalso
      obtain ⟨M, hM, iM, hrM⟩ := hMs
      obtain ⟨iG, hrG⟩ := hT2 (s + 1) t (by omega)
      obtain ⟨iA, hrA⟩ := hK2 s t (by omega)
      have hsR : ((s + 1 + t + 1 : ℕ) : ℝ) = K := by exact_mod_cast ht
      push_cast at hsR
      have hYint : Lam F ((K : ℝ) + ((s + 1 : ℕ) : ℝ) * cb e f) (-((s + 1 : ℕ) : ℝ))
          ∈ interior D.target.carrier :=
        ad_interior F FC K (by omega) hKc (by positivity) (by push_cast; linarith)
      have gG := (T2c_angles F FC ht hrG).1
      have gA : (D.tile iA).localAngle (Lam F ((K : ℝ) + ((s + 1 : ℕ) : ℝ) * cb e f)
          (-((s + 1 : ℕ) : ℝ))) = α := by
        have := (Kc_angles F FC (by omega : s + t + 1 = K') hrA).2.2
        have e1 : Lam F ((K' : ℝ) + 1 + ((s : ℝ) + 1) * cb e f) (-((s : ℝ) + 1))
            = Lam F ((K : ℝ) + ((s + 1 : ℕ) : ℝ) * cb e f) (-((s + 1 : ℕ) : ℝ)) := by
          rw [hKK]; congr 1 <;> push_cast <;> ring
        rw [e1] at this; exact this
      have gD : (D.tile iD).localAngle (Lam F ((K : ℝ) + ((s + 1 : ℕ) : ℝ) * cb e f)
          (-((s + 1 : ℕ) : ℝ))) = γ := by
        have := (Kc_angles F FC (by omega : s + (t + 1) + 1 = K) hrD).1
        push_cast at this ⊢; exact this
      have gM := (MirT2_angles F hM hrM).1
      have hGD : iG ≠ iD := by
        intro h
        have h1 : Lam F ((K : ℝ) - 1 + ((s + 1 : ℕ) : ℝ) * cb e f) (-((s + 1 : ℕ) : ℝ))
            ∈ Set.range (D.tile iG).pts := by rw [T2c_range F FC ht hrG]; exact mem3_3
        rw [h, Kc_range F FC (by omega : s + (t + 1) + 1 = K) hrD] at h1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
        rcases h1 with h1 | h1 | h1 <;> have := Lam_inj F FC h1 <;> push_cast at this <;>
          nlinarith [this.1, this.2]
      have hGM : iG ≠ iM := by
        intro h
        have h1 : Lam F ((K : ℝ) - 1 + ((s + 1 : ℕ) : ℝ) * cb e f) (-((s + 1 : ℕ) : ℝ))
            ∈ Set.range (D.tile iG).pts := by rw [T2c_range F FC ht hrG]; exact mem3_3
        rw [h, hrM] at h1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
        rcases h1 with h1 | h1 | h1
        · have := Lam_inj F FC h1; push_cast at this; linarith [this.2]
        · have := Lam_inj F FC h1; linarith [this.1]
        · exact hM.1 h1.symm
      have hDM : iD ≠ iM := by
        intro h
        have h1 : Lam F ((K : ℝ) + s * cb e f) (-(s : ℝ)) ∈ Set.range (D.tile iD).pts := by
          rw [Kc_range F FC (by omega : s + (t + 1) + 1 = K) hrD]; exact mem3_2
        rw [h, hrM] at h1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
        rcases h1 with h1 | h1 | h1
        · have := Lam_inj F FC h1; push_cast at this; linarith [this.2]
        · have := Lam_inj F FC h1; push_cast at this; linarith [this.2]
        · -- `M` is at distance `b` from `X_{s+1}`, the point `X_s` at distance `a`
          have hb := hM.2.2
          rw [← h1, dist_Lam, dist_Lam] at hb
          have e1 : ‖vec F ((K : ℝ) + s * cb e f - ((K : ℝ) + ((s + 1 : ℕ) : ℝ) * cb e f))
              (-(s : ℝ) - -((s + 1 : ℕ) : ℝ))‖ = (e : ℝ) * f := by
            push_cast
            rw [show (K : ℝ) + s * cb e f - ((K : ℝ) + ((s : ℝ) + 1) * cb e f) = -cb e f by ring,
              show -(s : ℝ) - -((s : ℝ) + 1) = 1 by ring,
              show vec F (-cb e f) 1 = - vec F (cb e f) (-1) by rw [vec_neg]; norm_num, norm_neg,
              norm_VP]
          have e2 : ‖vec F ((K : ℝ) - 1 + ((s + 1 : ℕ) : ℝ) * cb e f -
              ((K : ℝ) + ((s + 1 : ℕ) : ℝ) * cb e f))
              (-((s + 1 : ℕ) : ℝ) - -((s + 1 : ℕ) : ℝ))‖ = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
            rw [show (K : ℝ) - 1 + ((s + 1 : ℕ) : ℝ) * cb e f - ((K : ℝ) + ((s + 1 : ℕ) : ℝ) * cb e f)
              = -1 by ring, sub_self, norm_vec_m10]
          rw [e1, e2] at hb
          obtain ⟨hab, -, -⟩ := sides_distinct F.hco F.he (by have := F.hef; omega)
          exact hab hb
      obtain ⟨E1, E2⟩ := interior_card_eqs D F.hAng F.hM.hα' F.hM.hβ' F.hM.hγ' hYint
      have h3 : 3 ≤ ({j | (D.tile j).localAngle (Lam F ((K : ℝ) + ((s + 1 : ℕ) : ℝ) * cb e f)
          (-((s + 1 : ℕ) : ℝ))) = γ} : Finset (Fin N)).card := by
        have hsub : ({iG, iD, iM} : Finset (Fin N)) ⊆
            ({j | (D.tile j).localAngle (Lam F ((K : ℝ) + ((s + 1 : ℕ) : ℝ) * cb e f)
              (-((s + 1 : ℕ) : ℝ))) = γ} : Finset (Fin N)) := by
          intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl | rfl
          · exact mem_filter_of gG
          · exact mem_filter_of gD
          · exact mem_filter_of gM
        have := Finset.card_le_card hsub
        rwa [Finset.card_eq_three.mpr ⟨iG, iD, iM, hGD, hGM, hDM, rfl⟩] at this
      have := card_one gA
      omega
    · exact hM'

theorem Col_T2c (j : ℕ) : Col F j = T2c F 0 j := by
  simp [Col, T2c]

/-- **R8 AT LEVEL `K = K' + 1`, CLAUSES (1)–(3) ON BOTH LINES, FOR EVERY APEX FRAME OF A REAL
`m = 1` DISSECTION — PROVED.**  Given `Π(K) = K·T₂ ∪ K·T₃` (this contains the chain `T₂ + jV`,
`j < K`) and `Kc < fb`: on `AD_K` and on row `K` the far side is `a^K`, the tile across each `a`-edge is
the half-turn or the mirror, and any mirror forces the mirror at `KP′` (`N_K` on `AD_K`, `G_K` on
row `K`).  (`r8_ad`, `r8_row`; the six-fill catalogue at `KP′`, clause (4), is not formalized.) -/
theorem r8_real {k : Fin 3} (h : ApexFrameReal.M1Data D e f α β γ k)
    (FC : ApexPlacement.FrameCoords F) (K' : ℕ) (hKf : K' + 2 ≤ f)
    (hKc : ((K' + 1 : ℕ) : ℝ) * (f : ℝ) ^ 2 < (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))
    (hT2 : ∀ i t, i + t + 1 ≤ K' + 1 → Present D (T2c F i t))
    (hK2 : ∀ i t, i + t + 2 ≤ K' + 1 → Present D (Kc F i t))
    (hUp : ∀ i t, i + t + 1 ≤ K' + 1 → Present D (Up F i t))
    (hDn : ∀ i t, i + t + 2 ≤ K' + 1 → Present D (Dn F i t)) :
    ((∀ s t, s + t + 1 = K' + 1 → Present D (Kc F s t) ∨ MirT2 F (K' + 1) s) ∧
      (∀ s t, s + t + 1 = K' + 1 → MirT2 F (K' + 1) s → MirT2 F (K' + 1) 0)) ∧
    ((∀ i t, i + t = K' → Present D (Dn F i t) ∨ MirUp F i t) ∧
      (∀ i t, i + t = K' → MirUp F i t → MirUp F K' 0)) := by
  have L := lframe_real F h FC
  have hcol : Present D (Col F K') := by rw [Col_T2c F]; exact hT2 0 K' (by omega)
  obtain ⟨-, a2, a3⟩ := r8_ad F L K' hKf hKc hT2 hK2 (hUp K' 0 (by omega))
  obtain ⟨-, r2, r3⟩ := r8_row F L K' hKf hUp hDn hcol
  exact ⟨⟨a2, a3⟩, ⟨r2, r3⟩⟩

end Erdos634.Draft.RowWallReal

#print axioms Erdos634.Draft.RowWallReal.ad_all
#print axioms Erdos634.Draft.RowWallReal.ad_one
#print axioms Erdos634.Draft.RowWallReal.r8_ad
#print axioms Erdos634.Draft.RowWallReal.r8_real

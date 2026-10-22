/-
Draft/SideRunLattice.lean -- Stage 2 of the formalization of the side theorem of room GAP3: the lattice of a run of
`c`-tiles on a side of the target ((private working notes, not included), notation of section 0).

A run starts at `P = (x, 0)` and goes to the right (`ε = 1`, tiles of type `C1`) or to the left (`ε = −1`, tiles of
type `C2`); one development covers both.  `u = (ε c, 0)`, `v = (ε (c − uu), hh)` (`|u| = c`, `|v| = b`,
`|v − u| = a`), and

    lp ξ η = P + ξ u + η v                     (the paper's `p(i,j)` for integers `ξ = i`, `η = j`).

* the three side functionals: `FX` (constant on the lines of direction `v`; `FX ≤ lv ξ₀` is the side `σ`),
  `GS` (constant on the lines `m_s` of direction `v − u`; `GS ≤ −lv s` is the side `ρ_s`),
  `GH` (constant on the rows; `GH ≤ −c hh η₀` is the side above the row);
* distances between lattice points (`dist_lp_sq`, the quadratic form `Qf`), `lineMap_lp`, `lp_ext`, `seg_split_lp`;
* the lattice triangles `U(ξ,η) = (lp ξ η, lp (ξ+1) η, lp ξ (η+1))` and
  `D(ξ,η) = (lp (ξ+1) η, lp ξ (η+1), lp (ξ+1) (η+1))` as tiles (`UT`, `DT`), their angles; the mirror image
  `N(ξ,η)` of `U(ξ,η)` in its `a`-edge has the third vertex `lp (ξ − ν) (η + 2 + ν)`, `ν = b/c`;
* recognition: a tile of the side `ρ` with the `a`-edge `[lp (ξ+1) η, lp ξ (η+1)]` is `D(ξ,η)` or `N(ξ,η)`
  (`m_edge_cases`); a tile above a row with the edge `[lp ξ η, lp (ξ+1) η]` and the angle `α` at `lp ξ η` is
  `U(ξ,η)` (`row_edge_U`).

Composite-N work; not prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.SideRunFrame

namespace Erdos634.Draft.SideRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.RunPartition Erdos634.Draft.W2E1 Set

/-! ## 1. Lattice points and the three functionals -/

/-- the lattice point `P + ξ u + η v`, `P = (x, 0)` -/
noncomputable def lp (n ε x ξ η : ℝ) : Plane :=
  mkPt (x + ε * ((ξ + η) * n ^ 2 - η * uu n)) (η * hh n)

theorem lp_congr {n ε x ξ η ξ' η' : ℝ} (h1 : ξ = ξ') (h2 : η = η') :
    lp n ε x ξ η = lp n ε x ξ' η' := by rw [h1, h2]

theorem lp_zero (n ε x : ℝ) : lp n ε x 0 0 = mkPt x 0 := by
  unfold lp; exact mkPt_congr (by ring) (by ring)

/-- the level of the lattice coordinate `s` -/
noncomputable def lv (n ε x s : ℝ) : ℝ := ε * hh n * x + n ^ 2 * hh n * s

/-- constant on the lines of direction `v`; grows with `ξ` -/
noncomputable def FX (n ε : ℝ) : Plane →ₗ[ℝ] ℝ := lin (ε * hh n) (uu n - n ^ 2)

/-- constant on the lines of direction `v − u`; decreases with `ξ + η` -/
noncomputable def GS (n ε : ℝ) : Plane →ₗ[ℝ] ℝ := lin (-(ε * hh n)) (-(uu n))

/-- constant on the rows; decreases with `η` -/
noncomputable def GH (n : ℝ) : Plane →ₗ[ℝ] ℝ := lin 0 (-(n ^ 2))

theorem FX_lp {n ε x : ℝ} (hε : ε ^ 2 = 1) (ξ η : ℝ) : FX n ε (lp n ε x ξ η) = lv n ε x ξ := by
  unfold FX lp lv
  rw [lin_mk]
  linear_combination (hh n * ((ξ + η) * n ^ 2 - η * uu n)) * hε

theorem GS_lp {n ε x : ℝ} (hε : ε ^ 2 = 1) (ξ η : ℝ) :
    GS n ε (lp n ε x ξ η) = -lv n ε x (ξ + η) := by
  unfold GS lp lv
  rw [lin_mk]
  linear_combination (-(hh n * ((ξ + η) * n ^ 2 - η * uu n))) * hε

theorem GH_lp (n ε x ξ η : ℝ) : GH n (lp n ε x ξ η) = -(n ^ 2 * hh n * η) := by
  unfold GH lp
  rw [lin_mk]
  ring

theorem GH_apply (n : ℝ) (p : Plane) : GH n p = -(n ^ 2 * p 1) := by
  unfold GH; rw [lin_apply]; ring

theorem eps_ne {ε : ℝ} (hε : ε ^ 2 = 1) : ε ≠ 0 := by
  rintro rfl
  norm_num at hε

theorem nh_pos {n : ℝ} (hn : 1 < n) : 0 < n ^ 2 * hh n :=
  mul_pos (by nlinarith) (hh_pos hn)

theorem FX_ne {n ε : ℝ} (hn : 1 < n) (hε : ε ^ 2 = 1) : FX n ε ≠ 0 :=
  lin_ne_zero (Or.inl (mul_ne_zero (eps_ne hε) (hh_pos hn).ne'))

theorem GS_ne {n ε : ℝ} (hn : 1 < n) (hε : ε ^ 2 = 1) : GS n ε ≠ 0 :=
  lin_ne_zero (Or.inl (neg_ne_zero.mpr (mul_ne_zero (eps_ne hε) (hh_pos hn).ne')))

theorem GH_ne {n : ℝ} (hn : 1 < n) : GH n ≠ 0 :=
  lin_ne_zero (Or.inr (neg_ne_zero.mpr (by
    have h : (0:ℝ) < n ^ 2 := by nlinarith
    exact h.ne')))

theorem lv_lt {n ε x s s' : ℝ} (hn : 1 < n) (h : s < s') : lv n ε x s < lv n ε x s' := by
  unfold lv
  nlinarith [mul_pos (nh_pos hn) (sub_pos.mpr h)]

theorem lv_le {n ε x s s' : ℝ} (hn : 1 < n) (h : s ≤ s') : lv n ε x s ≤ lv n ε x s' := by
  unfold lv
  nlinarith [mul_nonneg (nh_pos hn).le (sub_nonneg.mpr h)]

theorem lv_inj {n ε x s s' : ℝ} (hn : 1 < n) (h : lv n ε x s = lv n ε x s') : s = s' := by
  rcases lt_trichotomy s s' with h1 | h1 | h1
  · exact absurd h (lv_lt hn h1).ne
  · exact h1
  · exact absurd h (lv_lt hn h1).ne'

theorem lp_eta_eq {n ε x ξ η ξ' η' : ℝ} (hn : 1 < n) (h : lp n ε x ξ η = lp n ε x ξ' η') :
    η = η' := by
  have h1 : (lp n ε x ξ η) 1 = (lp n ε x ξ' η') 1 := by rw [h]
  unfold lp at h1
  rw [mkPt_one, mkPt_one] at h1
  exact mul_right_cancel₀ (hh_pos hn).ne' h1

theorem lp_xi_eq {n ε x ξ η ξ' η' : ℝ} (hn : 1 < n) (hε : ε ^ 2 = 1)
    (h : lp n ε x ξ η = lp n ε x ξ' η') : ξ = ξ' := by
  have h1 : FX n ε (lp n ε x ξ η) = FX n ε (lp n ε x ξ' η') := by rw [h]
  rw [FX_lp hε, FX_lp hε] at h1
  exact lv_inj hn h1

theorem lp_ne_eta {n ε x ξ η ξ' η' : ℝ} (hn : 1 < n) (h : η ≠ η') :
    lp n ε x ξ η ≠ lp n ε x ξ' η' := fun he => h (lp_eta_eq hn he)

theorem lp_ne_xi {n ε x ξ η ξ' η' : ℝ} (hn : 1 < n) (hε : ε ^ 2 = 1) (h : ξ ≠ ξ') :
    lp n ε x ξ η ≠ lp n ε x ξ' η' := fun he => h (lp_xi_eq hn hε he)

/-! ## 2. Distances and segments -/

/-- the squared length of `dξ u + dη v` -/
def Qf (n dξ dη : ℝ) : ℝ :=
  n ^ 4 * dξ ^ 2 + (2 * n ^ 4 - 3 * n ^ 2 + 1) * (dξ * dη) + (n ^ 2 - 1) ^ 2 * dη ^ 2

theorem dist_lp_sq {n ε x : ℝ} (hn : 1 < n) (hε : ε ^ 2 = 1) (ξ η ξ' η' : ℝ) :
    dist (lp n ε x ξ η) (lp n ε x ξ' η') ^ 2 = Qf n (ξ - ξ') (η - η') := by
  have hu := uu_spec hn
  have hsq := hh_sq' hn
  unfold lp Qf
  rw [dist_sq_mkPt]
  linear_combination ((ξ - ξ') * n ^ 2 + (η - η') * (n ^ 2 - uu n)) ^ 2 * hε
    - (ξ - ξ') * (η - η') * hu + (η - η') ^ 2 * hsq

theorem dist_lp {n ε x : ℝ} (hn : 1 < n) (hε : ε ^ 2 = 1) {ξ η ξ' η' d : ℝ} (hd0 : 0 ≤ d)
    (hd : Qf n (ξ - ξ') (η - η') = d ^ 2) : dist (lp n ε x ξ η) (lp n ε x ξ' η') = d :=
  dist_eq_of_sq_eq (by rw [dist_lp_sq hn hε, hd]) dist_nonneg hd0

theorem lineMap_lp (n ε x ξ η ξ' η' t : ℝ) :
    AffineMap.lineMap (lp n ε x ξ η) (lp n ε x ξ' η') t
      = lp n ε x (ξ + t * (ξ' - ξ)) (η + t * (η' - η)) := by
  unfold lp
  rw [CSlot.lineMap_mkPt]
  exact mkPt_congr (by ring) (by ring)

theorem lp_ext (n ε x ξ η ξ' η' s : ℝ) :
    lp n ε x ξ η + s • (lp n ε x ξ η - lp n ε x ξ' η')
      = lp n ε x (ξ + s * (ξ - ξ')) (η + s * (η - η')) := by
  unfold lp
  apply plane_ext <;>
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, mkPt_zero, mkPt_one] <;>
    ring

/-- a point of a segment between lattice points, in lattice coordinates -/
theorem lp_seg_param {n ε x ξ η ξ' η' : ℝ} {y : Plane}
    (hy : y ∈ segment ℝ (lp n ε x ξ η) (lp n ε x ξ' η')) :
    ∃ τ : ℝ, 0 ≤ τ ∧ τ ≤ 1 ∧ y = lp n ε x (ξ + τ * (ξ' - ξ)) (η + τ * (η' - η)) := by
  rw [segment_eq_image_lineMap] at hy
  obtain ⟨τ, ⟨h0, h1⟩, rfl⟩ := hy
  exact ⟨τ, h0, h1, lineMap_lp n ε x ξ η ξ' η' τ⟩

theorem lp_mem_seg {n ε x ξ η ξ' η' τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1) :
    lp n ε x (ξ + τ * (ξ' - ξ)) (η + τ * (η' - η)) ∈ segment ℝ (lp n ε x ξ η) (lp n ε x ξ' η') := by
  rw [segment_eq_image_lineMap]
  exact ⟨τ, ⟨h0, h1⟩, lineMap_lp n ε x ξ η ξ' η' τ⟩

/-- **A segment of `q` lattice steps is the union of its steps.** -/
theorem seg_split_lp {n ε x ξ η dξ dη : ℝ} {q : ℕ} (hq : 1 ≤ q) {y : Plane}
    (hy : y ∈ segment ℝ (lp n ε x ξ η) (lp n ε x (ξ + q * dξ) (η + q * dη))) :
    ∃ i : ℕ, i < q ∧ y ∈ segment ℝ (lp n ε x (ξ + i * dξ) (η + i * dη))
      (lp n ε x (ξ + (i + 1) * dξ) (η + (i + 1) * dη)) := by
  obtain ⟨τ, h0, h1, rfl⟩ := lp_seg_param hy
  have hq' : (0:ℝ) < q := by exact_mod_cast hq
  obtain ⟨i, hi, hi1, hi2⟩ := exists_nat_between hq (s := τ * q) (mul_nonneg h0 hq'.le)
    (by nlinarith [mul_nonneg (sub_nonneg.mpr h1) hq'.le])
  refine ⟨i, hi, ?_⟩
  have h := lp_mem_seg (n := n) (ε := ε) (x := x) (ξ := ξ + i * dξ) (η := η + i * dη)
    (ξ' := ξ + (i + 1) * dξ) (η' := η + (i + 1) * dη) (τ := τ * q - i) (by linarith) (by linarith)
  have e : lp n ε x (ξ + τ * (ξ + q * dξ - ξ)) (η + τ * (η + q * dη - η))
      = lp n ε x (ξ + i * dξ + (τ * q - i) * (ξ + (i + 1) * dξ - (ξ + i * dξ)))
          (η + i * dη + (τ * q - i) * (η + (i + 1) * dη - (η + i * dη))) :=
    lp_congr (by ring) (by ring)
  rw [e]; exact h

/-! ## 3. The lattice triangles as tiles -/

variable {N : ℕ} {D : CongruentDissection N}

/-- `U(ξ,η)` is a tile -/
def UT (D : CongruentDissection N) (n ε x ξ η : ℝ) : Prop :=
  ∃ t, HasV D t (lp n ε x ξ η) (lp n ε x (ξ + 1) η) (lp n ε x ξ (η + 1))

/-- `D(ξ,η)` is a tile -/
def DT (D : CongruentDissection N) (n ε x ξ η : ℝ) : Prop :=
  ∃ t, HasV D t (lp n ε x (ξ + 1) η) (lp n ε x ξ (η + 1)) (lp n ε x (ξ + 1) (η + 1))

/-- `ν = b/c` -/
noncomputable def nu (n : ℝ) : ℝ := (n ^ 2 - 1) / n ^ 2

theorem nu_spec {n : ℝ} (hn : 1 < n) : n ^ 2 * nu n = n ^ 2 - 1 := by
  have h : n ^ 2 ≠ 0 := by nlinarith
  unfold nu
  rw [mul_comm]
  exact div_mul_cancel₀ _ h

theorem nu_pos {n : ℝ} (hn : 1 < n) : 0 < nu n := by
  unfold nu
  exact div_pos (by nlinarith) (by nlinarith)

theorem dist_step_u {n ε x : ℝ} (hn : 1 < n) (hε : ε ^ 2 = 1) (ξ η : ℝ) :
    dist (lp n ε x ξ η) (lp n ε x (ξ + 1) η) = n ^ 2 :=
  dist_lp hn hε (by positivity) (by unfold Qf; ring)

theorem dist_step_v {n ε x : ℝ} (hn : 1 < n) (hε : ε ^ 2 = 1) (ξ η : ℝ) :
    dist (lp n ε x ξ η) (lp n ε x ξ (η + 1)) = n ^ 2 - 1 :=
  dist_lp hn hε (by nlinarith) (by unfold Qf; ring)

theorem dist_step_a {n ε x : ℝ} (hn : 1 < n) (hε : ε ^ 2 = 1) (ξ η : ℝ) :
    dist (lp n ε x (ξ + 1) η) (lp n ε x ξ (η + 1)) = n :=
  dist_lp hn hε (by linarith) (by unfold Qf; ring)

section angles

variable {n : ℕ} {α β γ L ax ay ε x : ℝ}

/-- the angles of `U(ξ,η)`: `α`, `β`, `γ` -/
theorem U_angles (S : Setup D n α β γ L ax ay) (hε : ε ^ 2 = 1) {t : Fin N} {ξ η : ℝ}
    (h : HasV D t (lp n ε x ξ η) (lp n ε x (ξ + 1) η) (lp n ε x ξ (η + 1))) :
    (D.tile t).localAngle (lp n ε x ξ η) = α ∧ (D.tile t).localAngle (lp n ε x (ξ + 1) η) = β ∧
    (D.tile t).localAngle (lp n ε x ξ (η + 1)) = γ := by
  refine ⟨(h.angles S.f2 S.hM).1 (dist_step_a S.f1 hε ξ η), (h.rot.angles S.f2 S.hM).2.1 ?_,
    (h.rot.rot.angles S.f2 S.hM).2.2 (dist_step_u S.f1 hε ξ η)⟩
  rw [dist_comm]; exact dist_step_v S.f1 hε ξ η

/-- the angles of `D(ξ,η)`: `γ`, `β`, `α` -/
theorem D_angles (S : Setup D n α β γ L ax ay) (hε : ε ^ 2 = 1) {t : Fin N} {ξ η : ℝ}
    (h : HasV D t (lp n ε x (ξ + 1) η) (lp n ε x ξ (η + 1)) (lp n ε x (ξ + 1) (η + 1))) :
    (D.tile t).localAngle (lp n ε x (ξ + 1) η) = γ ∧ (D.tile t).localAngle (lp n ε x ξ (η + 1)) = β ∧
    (D.tile t).localAngle (lp n ε x (ξ + 1) (η + 1)) = α := by
  refine ⟨(h.angles S.f2 S.hM).2.2 (dist_step_u S.f1 hε ξ (η + 1)), (h.rot.angles S.f2 S.hM).2.1 ?_,
    (h.rot.rot.angles S.f2 S.hM).1 (dist_step_a S.f1 hε ξ η)⟩
  rw [dist_comm]; exact dist_step_v S.f1 hε (ξ + 1) η

theorem dist_N_V {n ε x : ℝ} (hn : 1 < n) (hε : ε ^ 2 = 1) (ξ η : ℝ) :
    dist (lp n ε x (ξ - nu n) (η + 2 + nu n)) (lp n ε x (ξ + 1) η) = n ^ 2 := by
  have hν := nu_spec hn
  refine dist_lp hn hε (by positivity) ?_
  unfold Qf
  linear_combination (nu n + 2) * hν

theorem dist_N_G {n ε x : ℝ} (hn : 1 < n) (hε : ε ^ 2 = 1) (ξ η : ℝ) :
    dist (lp n ε x (ξ - nu n) (η + 2 + nu n)) (lp n ε x ξ (η + 1)) = n ^ 2 - 1 := by
  have hν := nu_spec hn
  refine dist_lp hn hε (by nlinarith) ?_
  unfold Qf
  linear_combination (nu n) * hν

/-- the angles of `N(ξ,η)` at the ends of its `a`-edge: `β` at `lp (ξ+1) η`, `γ` at `lp ξ (η+1)` -/
theorem N_angles (S : Setup D n α β γ L ax ay) (hε : ε ^ 2 = 1) {t : Fin N} {ξ η : ℝ}
    (h : HasV D t (lp n ε x (ξ + 1) η) (lp n ε x ξ (η + 1)) (lp n ε x (ξ - nu n) (η + 2 + nu n))) :
    (D.tile t).localAngle (lp n ε x (ξ + 1) η) = β ∧
    (D.tile t).localAngle (lp n ε x ξ (η + 1)) = γ := by
  refine ⟨(h.angles S.f2 S.hM).2.1 ?_, (h.rot.angles S.f2 S.hM).2.2 (dist_N_V S.f1 hε ξ η)⟩
  rw [dist_comm]; exact dist_N_G S.f1 hε ξ η

/-! ## 4. Recognition -/

theorem cross_m {n ε x : ℝ} (hε : ε ^ 2 = 1) (ξ η : ℝ) (y : Plane) :
    cross (lp n ε x ξ (η + 1) - lp n ε x (ξ + 1) η) y = ε * GS n ε y := by
  unfold GS lp
  rw [lin_apply]
  simp only [cross, PiLp.sub_apply, mkPt_zero, mkPt_one]
  linear_combination (hh n * y 0) * hε

theorem cross_row {n ε x : ℝ} (ξ η : ℝ) (y : Plane) :
    cross (lp n ε x (ξ + 1) η - lp n ε x ξ η) y = (-ε) * GH n y := by
  unfold lp
  rw [GH_apply]
  simp only [cross, PiLp.sub_apply, mkPt_zero, mkPt_one]
  ring

/-- **A tile of the side `ρ` with the `a`-edge `[lp (ξ+1) η, lp ξ (η+1)]` is `D(ξ,η)` or `N(ξ,η)`.** -/
theorem m_edge_cases (S : Setup D n α β γ L ax ay) (hε : ε ^ 2 = 1) {t : Fin N} {k m : Fin 3}
    (hkm : k ≠ m) {ξ η : ℝ} (hk : (D.tile t).pts k = lp n ε x (ξ + 1) η)
    (hm : (D.tile t).pts m = lp n ε x ξ (η + 1))
    (hle : ∀ i, GS n ε ((D.tile t).pts i) ≤ -lv n ε x (ξ + η + 1)) :
    HasV D t (lp n ε x (ξ + 1) η) (lp n ε x ξ (η + 1)) (lp n ε x (ξ + 1) (η + 1)) ∨
    HasV D t (lp n ε x (ξ + 1) η) (lp n ε x ξ (η + 1)) (lp n ε x (ξ - nu n) (η + 2 + nu n)) := by
  obtain ⟨j, hjk, hjm⟩ := fin3_third k m hkm
  have hf1 := S.f1
  have hnh := nh_pos hf1
  have hd : dist ((D.tile t).pts k) ((D.tile t).pts m) = n := by
    rw [hk, hm]; exact dist_step_a hf1 hε ξ η
  have hGk : GS n ε ((D.tile t).pts k) = -lv n ε x (ξ + η + 1) := by
    rw [hk, GS_lp hε]; unfold lv; ring
  have hGm : GS n ε ((D.tile t).pts m) = -lv n ε x (ξ + η + 1) := by
    rw [hm, GS_lp hε]; unfold lv; ring
  have hlt := third_strict (D.tile t) hkm (Ne.symm hjk) (Ne.symm hjm) (GS n ε) (GS_ne hf1 hε) _
    hGk hGm hle
  rw [hk] at hGk
  rcases sides_of_a_edge D S.f2 S.hM t hkm (Ne.symm hjk) (Ne.symm hjm) hd with ⟨s1, s2⟩ | ⟨s1, s2⟩
  · right
    rw [hk] at s1
    rw [hm] at s2
    have hj : (D.tile t).pts j = lp n ε x (ξ - nu n) (η + 2 + nu n) := by
      refine third_unique_F (GS n ε) (eps_ne hε) (cross_m hε ξ η) hGk ?_ ?_ hlt ?_
      · rw [s1, dist_N_V hf1 hε ξ η]
      · rw [s2, dist_N_G hf1 hε ξ η]
      · rw [GS_lp hε]; unfold lv; nlinarith
    exact ⟨k, m, j, hkm, Ne.symm hjk, Ne.symm hjm, hk, hm, hj⟩
  · left
    rw [hk] at s1
    rw [hm] at s2
    have hj : (D.tile t).pts j = lp n ε x (ξ + 1) (η + 1) := by
      refine third_unique_F (GS n ε) (eps_ne hε) (cross_m hε ξ η) hGk ?_ ?_ hlt ?_
      · rw [s1, dist_comm]; exact (dist_step_v hf1 hε (ξ + 1) η).symm
      · rw [s2, dist_comm]; exact (dist_step_u hf1 hε ξ (η + 1)).symm
      · rw [GS_lp hε]; unfold lv; nlinarith
    exact ⟨k, m, j, hkm, Ne.symm hjk, Ne.symm hjm, hk, hm, hj⟩

/-- **A tile above a row with the edge `[lp ξ η, lp (ξ+1) η]` whose third vertex is at the distances `b`, `a` from
its ends is `U(ξ,η)`.** -/
theorem row_edge_U (S : Setup D n α β γ L ax ay) (hε : ε ^ 2 = 1) {t : Fin N} {k m j : Fin 3}
    (hkm : k ≠ m) (hkj : k ≠ j) (hmj : m ≠ j) {ξ η : ℝ} (hk : (D.tile t).pts k = lp n ε x ξ η)
    (hm : (D.tile t).pts m = lp n ε x (ξ + 1) η)
    (hle : ∀ i, GH n ((D.tile t).pts i) ≤ -((n:ℝ) ^ 2 * hh n * η))
    (s1 : dist ((D.tile t).pts j) ((D.tile t).pts k) = (n:ℝ) ^ 2 - 1)
    (s2 : dist ((D.tile t).pts j) ((D.tile t).pts m) = n) :
    HasV D t (lp n ε x ξ η) (lp n ε x (ξ + 1) η) (lp n ε x ξ (η + 1)) := by
  have hf1 := S.f1
  have hnh := nh_pos hf1
  have hGk : GH n ((D.tile t).pts k) = -((n:ℝ) ^ 2 * hh n * η) := by rw [hk, GH_lp]
  have hGm : GH n ((D.tile t).pts m) = -((n:ℝ) ^ 2 * hh n * η) := by rw [hm, GH_lp]
  have hlt := third_strict (D.tile t) hkm hkj hmj (GH n) (GH_ne hf1) _ hGk hGm hle
  rw [hk] at hGk s1
  rw [hm] at s2
  have hj : (D.tile t).pts j = lp n ε x ξ (η + 1) := by
    refine third_unique_F (GH n) (neg_ne_zero.mpr (eps_ne hε)) (cross_row ξ η) hGk ?_ ?_ hlt ?_
    · rw [s1, dist_comm]; exact (dist_step_v hf1 hε ξ η).symm
    · rw [s2, dist_comm]; exact (dist_step_a hf1 hε ξ η).symm
    · rw [GH_lp]; nlinarith
  exact ⟨k, m, j, hkm, hkj, hmj, hk, hm, hj⟩

end angles

end Erdos634.Draft.SideRun

#print axioms Erdos634.Draft.SideRun.dist_lp_sq
#print axioms Erdos634.Draft.SideRun.seg_split_lp
#print axioms Erdos634.Draft.SideRun.m_edge_cases
#print axioms Erdos634.Draft.SideRun.row_edge_U

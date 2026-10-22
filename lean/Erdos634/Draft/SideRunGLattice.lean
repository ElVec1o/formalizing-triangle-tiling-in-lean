/-
Draft/SideRunGLattice.lean -- written 14 October 2026.  UNAUDITED.  In `AllThreshold`.

The lattice over a run of `c`-tiles on a side, for EVERY member `(e, f)`: the generalization of `Draft/SideRunLattice.lean`
(the tile `(n, n² − 1, n²)` built in) to the tile `(a, b, c) = (e f, f² − e², f²)`.  Paper: Theorem `thm:siderunall`,
paragraph "Lattice".

A run starts at `P = (x, 0)` and goes to the right (`ε = 1`, tiles of type `C1`) or to the left (`ε = −1`, `C2`);
`u = (ε c, 0)`, `v = (ε (c − uuG), hhG)` (`|u| = c`, `|v| = b`, `|v − u| = a`), and

    lpG e f ε x ξ η = P + ξ u + η v          (the paper's `p(i, j)` for integers `ξ = i`, `η = j`).

* the three side functionals `FXG`, `GSG`, `GHG` and the levels `lvG`;
* the quadratic form `QfG e f dξ dη = f⁴ dξ² + (2f² − e²)(f² − e²) dξ dη + (f² − e²)² dη²` (the squared length of
  `dξ u + dη v`; for `e = 1` the middle coefficient is `2n⁴ − 3n² + 1`), `dist_lpG`, `lineMap_lpG`, `lp_extG`, `seg_split_lpG`;
* the lattice triangles `U(ξ,η)`, `D(ξ,η)` (`UTG`, `DTG`), their angles; the mirror image `N(ξ,η)` of `U(ξ,η)` in its
  `a`-edge has the third vertex `lpG (ξ − ν) (η + 2 + ν)`, `ν = nuG = b/c` (`dist_N_VG`, `dist_N_GG`: the quotients of the
  polynomial identities by `f² ν − (f² − e²)` are `e² (ν + 2)` and `e² ν`);
* recognition: a tile of the side `ρ` with the `a`-edge `[lp (ξ+1) η, lp ξ (η+1)]` is `D(ξ,η)` or `N(ξ,η)`
  (`m_edge_casesG`); a tile above a row with the edge `[lp ξ η, lp (ξ+1) η]` and the angle `α` at `lp ξ η` is `U(ξ,η)`
  (`row_edge_UG`).

Nothing here uses `3α < β`, `α < β`, `j a < b` or an order between `a` and `b`; the only facts about the tile used are
`0 < e < f` (and `a ≠ b` through `SetupG.tile`, for the angle reading).

WITNESSES.  The lemmas are stated under `SetupG` (see `SideRunGFrame`).  For `e = 1` a real dissection satisfies the
hypotheses: `side_theorem_witness` (SideRun.lean) gives a `Setup` for a normal form of the seed tiling of `W_f(1, f)`,
and `SideRunGFrame.setupG_one_iff` turns it into a `SetupG` (verified in `SideRunGWitness.lean`).  For `e ≥ 2` the
analogous witness is the normal form of the seed tiling of `W_f(e, f)` (`CollarG.wTilable_seed e f`, every member), or
of the kernel-checked tiling of `W_4(2, 3)` by 224 tiles `(6, 5, 9)` (`Draft/W23.lean`, `w23_scale4`); the passage from
a `CongruentDissection` with `HasSides` to a `SetupG` is `setup_of_sides` for general `e`, which is a later piece
(SideRunGMain).  NAMED, NOT VERIFIED for `e ≥ 2`.

Specialisation checks at `e = 1` at the end of the file.  No sorry, no native_decide.
-/
import Erdos634.Draft.SideRunGFrame
import Erdos634.Draft.SideRunLattice

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.SideRunG

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.MarchKills Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.RunPartition Erdos634.E1BaseWord Erdos634.WallEndpoints Erdos634.BaseChain
  Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.TilePlacement
  Erdos634.Geometry.Dissection Erdos634.Draft.W2E1 Erdos634.Draft.SideRun Set

/-! ## 1. Lattice points and the three functionals -/

/-- the lattice point `P + ξ u + η v`, `P = (x, 0)` -/
noncomputable def lpG (e f ε x ξ η : ℝ) : Plane :=
  mkPt (x + ε * ((ξ + η) * f ^ 2 - η * uuG e f)) (η * hhG e f)

theorem lpG_congr {e f ε x ξ η ξ' η' : ℝ} (h1 : ξ = ξ') (h2 : η = η') :
    lpG e f ε x ξ η = lpG e f ε x ξ' η' := by rw [h1, h2]

theorem lpG_zero (e f ε x : ℝ) : lpG e f ε x 0 0 = mkPt x 0 := by
  unfold lpG; exact mkPt_congr (by ring) (by ring)

theorem eps_neG {ε : ℝ} (hε : ε ^ 2 = 1) : ε ≠ 0 := by
  rintro rfl
  norm_num at hε

/-- the level of the lattice coordinate `s` -/
noncomputable def lvG (e f ε x s : ℝ) : ℝ := ε * hhG e f * x + f ^ 2 * hhG e f * s

/-- constant on the lines of direction `v`; grows with `ξ` -/
noncomputable def FXG (e f ε : ℝ) : Plane →ₗ[ℝ] ℝ := lin (ε * hhG e f) (uuG e f - f ^ 2)

/-- constant on the lines of direction `v − u`; decreases with `ξ + η` -/
noncomputable def GSG (e f ε : ℝ) : Plane →ₗ[ℝ] ℝ := lin (-(ε * hhG e f)) (-(uuG e f))

/-- constant on the rows; decreases with `η` -/
noncomputable def GHG (f : ℝ) : Plane →ₗ[ℝ] ℝ := lin 0 (-(f ^ 2))

theorem FXG_lp {e f ε x : ℝ} (hε : ε ^ 2 = 1) (ξ η : ℝ) :
    FXG e f ε (lpG e f ε x ξ η) = lvG e f ε x ξ := by
  unfold FXG lpG lvG
  rw [lin_mk]
  linear_combination (hhG e f * ((ξ + η) * f ^ 2 - η * uuG e f)) * hε

theorem GSG_lp {e f ε x : ℝ} (hε : ε ^ 2 = 1) (ξ η : ℝ) :
    GSG e f ε (lpG e f ε x ξ η) = -lvG e f ε x (ξ + η) := by
  unfold GSG lpG lvG
  rw [lin_mk]
  linear_combination (-(hhG e f * ((ξ + η) * f ^ 2 - η * uuG e f))) * hε

theorem GHG_lp (e f ε x ξ η : ℝ) : GHG f (lpG e f ε x ξ η) = -(f ^ 2 * hhG e f * η) := by
  unfold GHG lpG
  rw [lin_mk]
  ring

theorem GHG_apply (f : ℝ) (p : Plane) : GHG f p = -(f ^ 2 * p 1) := by
  unfold GHG; rw [lin_apply]; ring

theorem nhG_pos {e f : ℝ} (he : 0 < e) (hef : e < f) : 0 < f ^ 2 * hhG e f :=
  mul_pos (by have := he.trans hef; positivity) (hhG_pos he hef)

theorem FXG_ne {e f ε : ℝ} (he : 0 < e) (hef : e < f) (hε : ε ^ 2 = 1) : FXG e f ε ≠ 0 :=
  lin_ne_zero (Or.inl (mul_ne_zero (eps_neG hε) (hhG_pos he hef).ne'))

theorem GSG_ne {e f ε : ℝ} (he : 0 < e) (hef : e < f) (hε : ε ^ 2 = 1) : GSG e f ε ≠ 0 :=
  lin_ne_zero (Or.inl (neg_ne_zero.mpr (mul_ne_zero (eps_neG hε) (hhG_pos he hef).ne')))

theorem GHG_ne {e f : ℝ} (he : 0 < e) (hef : e < f) : GHG f ≠ 0 :=
  lin_ne_zero (Or.inr (neg_ne_zero.mpr (by
    have h : (0 : ℝ) < f ^ 2 := by have := he.trans hef; positivity
    exact h.ne')))

theorem lvG_lt {e f ε x s s' : ℝ} (he : 0 < e) (hef : e < f) (h : s < s') :
    lvG e f ε x s < lvG e f ε x s' := by
  unfold lvG
  nlinarith [mul_pos (nhG_pos he hef) (sub_pos.mpr h)]

theorem lvG_le {e f ε x s s' : ℝ} (he : 0 < e) (hef : e < f) (h : s ≤ s') :
    lvG e f ε x s ≤ lvG e f ε x s' := by
  unfold lvG
  nlinarith [mul_nonneg (nhG_pos he hef).le (sub_nonneg.mpr h)]

theorem lvG_inj {e f ε x s s' : ℝ} (he : 0 < e) (hef : e < f) (h : lvG e f ε x s = lvG e f ε x s') :
    s = s' := by
  rcases lt_trichotomy s s' with h1 | h1 | h1
  · exact absurd h (lvG_lt he hef h1).ne
  · exact h1
  · exact absurd h (lvG_lt he hef h1).ne'

theorem lpG_eta_eq {e f ε x ξ η ξ' η' : ℝ} (he : 0 < e) (hef : e < f)
    (h : lpG e f ε x ξ η = lpG e f ε x ξ' η') : η = η' := by
  have h1 : (lpG e f ε x ξ η) 1 = (lpG e f ε x ξ' η') 1 := by rw [h]
  unfold lpG at h1
  rw [mkPt_one, mkPt_one] at h1
  exact mul_right_cancel₀ (hhG_pos he hef).ne' h1

theorem lpG_xi_eq {e f ε x ξ η ξ' η' : ℝ} (he : 0 < e) (hef : e < f) (hε : ε ^ 2 = 1)
    (h : lpG e f ε x ξ η = lpG e f ε x ξ' η') : ξ = ξ' := by
  have h1 : FXG e f ε (lpG e f ε x ξ η) = FXG e f ε (lpG e f ε x ξ' η') := by rw [h]
  rw [FXG_lp hε, FXG_lp hε] at h1
  exact lvG_inj he hef h1

theorem lpG_ne_eta {e f ε x ξ η ξ' η' : ℝ} (he : 0 < e) (hef : e < f) (h : η ≠ η') :
    lpG e f ε x ξ η ≠ lpG e f ε x ξ' η' := fun he' => h (lpG_eta_eq he hef he')

theorem lpG_ne_xi {e f ε x ξ η ξ' η' : ℝ} (he : 0 < e) (hef : e < f) (hε : ε ^ 2 = 1) (h : ξ ≠ ξ') :
    lpG e f ε x ξ η ≠ lpG e f ε x ξ' η' := fun he' => h (lpG_xi_eq he hef hε he')

/-! ## 2. Distances and segments -/

/-- the squared length of `dξ u + dη v` -/
def QfG (e f dξ dη : ℝ) : ℝ :=
  f ^ 4 * dξ ^ 2 + (2 * f ^ 2 - e ^ 2) * (f ^ 2 - e ^ 2) * (dξ * dη) + (f ^ 2 - e ^ 2) ^ 2 * dη ^ 2

theorem dist_lpG_sq {e f ε x : ℝ} (he : 0 < e) (hef : e < f) (hε : ε ^ 2 = 1) (ξ η ξ' η' : ℝ) :
    dist (lpG e f ε x ξ η) (lpG e f ε x ξ' η') ^ 2 = QfG e f (ξ - ξ') (η - η') := by
  have hu := uuG_spec he hef
  have hsq := hhG_sq' he hef
  unfold lpG QfG
  rw [dist_sq_mkPt]
  linear_combination ((ξ - ξ') * f ^ 2 + (η - η') * (f ^ 2 - uuG e f)) ^ 2 * hε
    - (ξ - ξ') * (η - η') * hu + (η - η') ^ 2 * hsq

theorem dist_lpG {e f ε x : ℝ} (he : 0 < e) (hef : e < f) (hε : ε ^ 2 = 1) {ξ η ξ' η' d : ℝ}
    (hd0 : 0 ≤ d) (hd : QfG e f (ξ - ξ') (η - η') = d ^ 2) :
    dist (lpG e f ε x ξ η) (lpG e f ε x ξ' η') = d :=
  dist_eq_of_sq_eq (by rw [dist_lpG_sq he hef hε, hd]) dist_nonneg hd0

theorem lineMap_lpG (e f ε x ξ η ξ' η' t : ℝ) :
    AffineMap.lineMap (lpG e f ε x ξ η) (lpG e f ε x ξ' η') t
      = lpG e f ε x (ξ + t * (ξ' - ξ)) (η + t * (η' - η)) := by
  unfold lpG
  rw [CSlot.lineMap_mkPt]
  exact mkPt_congr (by ring) (by ring)

theorem lp_extG (e f ε x ξ η ξ' η' s : ℝ) :
    lpG e f ε x ξ η + s • (lpG e f ε x ξ η - lpG e f ε x ξ' η')
      = lpG e f ε x (ξ + s * (ξ - ξ')) (η + s * (η - η')) := by
  unfold lpG
  apply plane_ext <;>
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, mkPt_zero, mkPt_one] <;>
    ring

/-- a point of a segment between lattice points, in lattice coordinates -/
theorem lp_seg_paramG {e f ε x ξ η ξ' η' : ℝ} {y : Plane}
    (hy : y ∈ segment ℝ (lpG e f ε x ξ η) (lpG e f ε x ξ' η')) :
    ∃ τ : ℝ, 0 ≤ τ ∧ τ ≤ 1 ∧ y = lpG e f ε x (ξ + τ * (ξ' - ξ)) (η + τ * (η' - η)) := by
  rw [segment_eq_image_lineMap] at hy
  obtain ⟨τ, ⟨h0, h1⟩, rfl⟩ := hy
  exact ⟨τ, h0, h1, lineMap_lpG e f ε x ξ η ξ' η' τ⟩

theorem lp_mem_segG {e f ε x ξ η ξ' η' τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1) :
    lpG e f ε x (ξ + τ * (ξ' - ξ)) (η + τ * (η' - η)) ∈
      segment ℝ (lpG e f ε x ξ η) (lpG e f ε x ξ' η') := by
  rw [segment_eq_image_lineMap]
  exact ⟨τ, ⟨h0, h1⟩, lineMap_lpG e f ε x ξ η ξ' η' τ⟩

/-- **A segment of `q` lattice steps is the union of its steps.** -/
theorem seg_split_lpG {e f ε x ξ η dξ dη : ℝ} {q : ℕ} (hq : 1 ≤ q) {y : Plane}
    (hy : y ∈ segment ℝ (lpG e f ε x ξ η) (lpG e f ε x (ξ + q * dξ) (η + q * dη))) :
    ∃ i : ℕ, i < q ∧ y ∈ segment ℝ (lpG e f ε x (ξ + i * dξ) (η + i * dη))
      (lpG e f ε x (ξ + (i + 1) * dξ) (η + (i + 1) * dη)) := by
  obtain ⟨τ, h0, h1, rfl⟩ := lp_seg_paramG hy
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  obtain ⟨i, hi, hi1, hi2⟩ := exists_nat_between hq (s := τ * q) (mul_nonneg h0 hq'.le)
    (by nlinarith [mul_nonneg (sub_nonneg.mpr h1) hq'.le])
  refine ⟨i, hi, ?_⟩
  have h := lp_mem_segG (e := e) (f := f) (ε := ε) (x := x) (ξ := ξ + i * dξ) (η := η + i * dη)
    (ξ' := ξ + (i + 1) * dξ) (η' := η + (i + 1) * dη) (τ := τ * q - i) (by linarith) (by linarith)
  have e' : lpG e f ε x (ξ + τ * (ξ + q * dξ - ξ)) (η + τ * (η + q * dη - η))
      = lpG e f ε x (ξ + i * dξ + (τ * q - i) * (ξ + (i + 1) * dξ - (ξ + i * dξ)))
          (η + i * dη + (τ * q - i) * (η + (i + 1) * dη - (η + i * dη))) :=
    lpG_congr (by ring) (by ring)
  rw [e']; exact h

/-! ## 3. The lattice triangles as tiles -/

variable {N : ℕ} {D : CongruentDissection N}

/-- `U(ξ,η)` is a tile -/
def UTG (D : CongruentDissection N) (e f ε x ξ η : ℝ) : Prop :=
  ∃ t, HasV D t (lpG e f ε x ξ η) (lpG e f ε x (ξ + 1) η) (lpG e f ε x ξ (η + 1))

/-- `D(ξ,η)` is a tile -/
def DTG (D : CongruentDissection N) (e f ε x ξ η : ℝ) : Prop :=
  ∃ t, HasV D t (lpG e f ε x (ξ + 1) η) (lpG e f ε x ξ (η + 1)) (lpG e f ε x (ξ + 1) (η + 1))

theorem dist_step_uG {e f ε x : ℝ} (he : 0 < e) (hef : e < f) (hε : ε ^ 2 = 1) (ξ η : ℝ) :
    dist (lpG e f ε x ξ η) (lpG e f ε x (ξ + 1) η) = f ^ 2 :=
  dist_lpG he hef hε (by have := he.trans hef; positivity) (by unfold QfG; ring)

theorem dist_step_vG {e f ε x : ℝ} (he : 0 < e) (hef : e < f) (hε : ε ^ 2 = 1) (ξ η : ℝ) :
    dist (lpG e f ε x ξ η) (lpG e f ε x ξ (η + 1)) = f ^ 2 - e ^ 2 :=
  dist_lpG he hef hε (b_posG he hef).le (by unfold QfG; ring)

theorem dist_step_aG {e f ε x : ℝ} (he : 0 < e) (hef : e < f) (hε : ε ^ 2 = 1) (ξ η : ℝ) :
    dist (lpG e f ε x (ξ + 1) η) (lpG e f ε x ξ (η + 1)) = e * f :=
  dist_lpG he hef hε (mul_pos he (he.trans hef)).le (by unfold QfG; ring)

section angles

variable {e f : ℕ} {α β γ L ax ay ε x : ℝ}

/-- the angles of `U(ξ,η)`: `α`, `β`, `γ` -/
theorem U_anglesG (S : SetupG D e f α β γ L ax ay) (hε : ε ^ 2 = 1) {t : Fin N} {ξ η : ℝ}
    (h : HasV D t (lpG (e : ℝ) (f : ℝ) ε x ξ η) (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) η)
      (lpG (e : ℝ) (f : ℝ) ε x ξ (η + 1))) :
    (D.tile t).localAngle (lpG (e : ℝ) (f : ℝ) ε x ξ η) = α ∧
    (D.tile t).localAngle (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) η) = β ∧
    (D.tile t).localAngle (lpG (e : ℝ) (f : ℝ) ε x ξ (η + 1)) = γ := by
  refine ⟨(h.anglesG S.tile S.hM).1 (dist_step_aG S.e0 S.hef' hε ξ η),
    (h.rot.anglesG S.tile S.hM).2.1 ?_,
    (h.rot.rot.anglesG S.tile S.hM).2.2 (dist_step_uG S.e0 S.hef' hε ξ η)⟩
  rw [dist_comm]; exact dist_step_vG S.e0 S.hef' hε ξ η

/-- the angles of `D(ξ,η)`: `γ`, `β`, `α` -/
theorem D_anglesG (S : SetupG D e f α β γ L ax ay) (hε : ε ^ 2 = 1) {t : Fin N} {ξ η : ℝ}
    (h : HasV D t (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) η) (lpG (e : ℝ) (f : ℝ) ε x ξ (η + 1))
      (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) (η + 1))) :
    (D.tile t).localAngle (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) η) = γ ∧
    (D.tile t).localAngle (lpG (e : ℝ) (f : ℝ) ε x ξ (η + 1)) = β ∧
    (D.tile t).localAngle (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) (η + 1)) = α := by
  refine ⟨(h.anglesG S.tile S.hM).2.2 (dist_step_uG S.e0 S.hef' hε ξ (η + 1)),
    (h.rot.anglesG S.tile S.hM).2.1 ?_,
    (h.rot.rot.anglesG S.tile S.hM).1 (dist_step_aG S.e0 S.hef' hε ξ η)⟩
  rw [dist_comm]; exact dist_step_vG S.e0 S.hef' hε (ξ + 1) η

end angles

theorem dist_N_VG {e f ε x : ℝ} (he : 0 < e) (hef : e < f) (hε : ε ^ 2 = 1) (ξ η : ℝ) :
    dist (lpG e f ε x (ξ - nuG e f) (η + 2 + nuG e f)) (lpG e f ε x (ξ + 1) η) = f ^ 2 := by
  have hν := nuG_spec he hef
  refine dist_lpG he hef hε (by have := he.trans hef; positivity) ?_
  unfold QfG
  linear_combination (e ^ 2 * (nuG e f + 2)) * hν

theorem dist_N_GG {e f ε x : ℝ} (he : 0 < e) (hef : e < f) (hε : ε ^ 2 = 1) (ξ η : ℝ) :
    dist (lpG e f ε x (ξ - nuG e f) (η + 2 + nuG e f)) (lpG e f ε x ξ (η + 1)) = f ^ 2 - e ^ 2 := by
  have hν := nuG_spec he hef
  refine dist_lpG he hef hε (b_posG he hef).le ?_
  unfold QfG
  linear_combination (e ^ 2 * nuG e f) * hν

section angles2

variable {e f : ℕ} {α β γ L ax ay ε x : ℝ}

/-- the angles of `N(ξ,η)` at the ends of its `a`-edge: `β` at `lp (ξ+1) η`, `γ` at `lp ξ (η+1)` -/
theorem N_anglesG (S : SetupG D e f α β γ L ax ay) (hε : ε ^ 2 = 1) {t : Fin N} {ξ η : ℝ}
    (h : HasV D t (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) η) (lpG (e : ℝ) (f : ℝ) ε x ξ (η + 1))
      (lpG (e : ℝ) (f : ℝ) ε x (ξ - nuG (e : ℝ) (f : ℝ)) (η + 2 + nuG (e : ℝ) (f : ℝ)))) :
    (D.tile t).localAngle (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) η) = β ∧
    (D.tile t).localAngle (lpG (e : ℝ) (f : ℝ) ε x ξ (η + 1)) = γ := by
  refine ⟨(h.anglesG S.tile S.hM).2.1 ?_,
    (h.rot.anglesG S.tile S.hM).2.2 (dist_N_VG S.e0 S.hef' hε ξ η)⟩
  rw [dist_comm]; exact dist_N_GG S.e0 S.hef' hε ξ η

end angles2

/-! ## 4. Recognition -/

theorem cross_mG {e f ε x : ℝ} (hε : ε ^ 2 = 1) (ξ η : ℝ) (y : Plane) :
    cross (lpG e f ε x ξ (η + 1) - lpG e f ε x (ξ + 1) η) y = ε * GSG e f ε y := by
  unfold GSG lpG
  rw [lin_apply]
  simp only [cross, PiLp.sub_apply, mkPt_zero, mkPt_one]
  linear_combination (hhG e f * y 0) * hε

theorem cross_rowG {e f ε x : ℝ} (ξ η : ℝ) (y : Plane) :
    cross (lpG e f ε x (ξ + 1) η - lpG e f ε x ξ η) y = (-ε) * GHG f y := by
  unfold lpG
  rw [GHG_apply]
  simp only [cross, PiLp.sub_apply, mkPt_zero, mkPt_one]
  ring

section recog

variable {e f : ℕ} {α β γ L ax ay ε x : ℝ}

/-- **A tile of the side `ρ` with the `a`-edge `[lp (ξ+1) η, lp ξ (η+1)]` is `D(ξ,η)` or `N(ξ,η)`.** -/
theorem m_edge_casesG (S : SetupG D e f α β γ L ax ay) (hε : ε ^ 2 = 1) {t : Fin N} {k m : Fin 3}
    (hkm : k ≠ m) {ξ η : ℝ} (hk : (D.tile t).pts k = lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) η)
    (hm : (D.tile t).pts m = lpG (e : ℝ) (f : ℝ) ε x ξ (η + 1))
    (hle : ∀ i, GSG (e : ℝ) (f : ℝ) ε ((D.tile t).pts i) ≤ -lvG (e : ℝ) (f : ℝ) ε x (ξ + η + 1)) :
    HasV D t (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) η) (lpG (e : ℝ) (f : ℝ) ε x ξ (η + 1))
      (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) (η + 1)) ∨
    HasV D t (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) η) (lpG (e : ℝ) (f : ℝ) ε x ξ (η + 1))
      (lpG (e : ℝ) (f : ℝ) ε x (ξ - nuG (e : ℝ) (f : ℝ)) (η + 2 + nuG (e : ℝ) (f : ℝ))) := by
  obtain ⟨j, hjk, hjm⟩ := fin3_third k m hkm
  have he0 := S.e0
  have hef := S.hef'
  have hnh := nhG_pos he0 hef
  have hd : dist ((D.tile t).pts k) ((D.tile t).pts m) = (e : ℝ) * f := by
    rw [hk, hm]; exact dist_step_aG he0 hef hε ξ η
  have hGk : GSG (e : ℝ) (f : ℝ) ε ((D.tile t).pts k) = -lvG (e : ℝ) (f : ℝ) ε x (ξ + η + 1) := by
    rw [hk, GSG_lp hε]; unfold lvG; ring
  have hGm : GSG (e : ℝ) (f : ℝ) ε ((D.tile t).pts m) = -lvG (e : ℝ) (f : ℝ) ε x (ξ + η + 1) := by
    rw [hm, GSG_lp hε]; unfold lvG; ring
  have hlt := third_strict (D.tile t) hkm (Ne.symm hjk) (Ne.symm hjm) (GSG (e : ℝ) (f : ℝ) ε)
    (GSG_ne he0 hef hε) _ hGk hGm hle
  rw [hk] at hGk
  rcases sides_of_a_edgeG D S.tile S.hM t hkm (Ne.symm hjk) (Ne.symm hjm) hd with
    ⟨s1, s2⟩ | ⟨s1, s2⟩
  · right
    rw [hk] at s1
    rw [hm] at s2
    have hj : (D.tile t).pts j =
        lpG (e : ℝ) (f : ℝ) ε x (ξ - nuG (e : ℝ) (f : ℝ)) (η + 2 + nuG (e : ℝ) (f : ℝ)) := by
      refine third_unique_F (GSG (e : ℝ) (f : ℝ) ε) (eps_neG hε) (cross_mG hε ξ η) hGk ?_ ?_ hlt ?_
      · rw [s1, dist_N_VG he0 hef hε ξ η]
      · rw [s2, dist_N_GG he0 hef hε ξ η]
      · rw [GSG_lp hε]; unfold lvG; nlinarith
    exact ⟨k, m, j, hkm, Ne.symm hjk, Ne.symm hjm, hk, hm, hj⟩
  · left
    rw [hk] at s1
    rw [hm] at s2
    have hj : (D.tile t).pts j = lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) (η + 1) := by
      refine third_unique_F (GSG (e : ℝ) (f : ℝ) ε) (eps_neG hε) (cross_mG hε ξ η) hGk ?_ ?_ hlt ?_
      · rw [s1, dist_comm]; exact (dist_step_vG he0 hef hε (ξ + 1) η).symm
      · rw [s2, dist_comm]; exact (dist_step_uG he0 hef hε ξ (η + 1)).symm
      · rw [GSG_lp hε]; unfold lvG; nlinarith
    exact ⟨k, m, j, hkm, Ne.symm hjk, Ne.symm hjm, hk, hm, hj⟩

/-- **A tile above a row with the edge `[lp ξ η, lp (ξ+1) η]` whose third vertex is at the distances `b`, `a` from
its ends is `U(ξ,η)`.** -/
theorem row_edge_UG (S : SetupG D e f α β γ L ax ay) (hε : ε ^ 2 = 1) {t : Fin N} {k m j : Fin 3}
    (hkm : k ≠ m) (hkj : k ≠ j) (hmj : m ≠ j) {ξ η : ℝ}
    (hk : (D.tile t).pts k = lpG (e : ℝ) (f : ℝ) ε x ξ η)
    (hm : (D.tile t).pts m = lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) η)
    (hle : ∀ i, GHG (f : ℝ) ((D.tile t).pts i) ≤ -((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ) * η))
    (s1 : dist ((D.tile t).pts j) ((D.tile t).pts k) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (s2 : dist ((D.tile t).pts j) ((D.tile t).pts m) = (e : ℝ) * f) :
    HasV D t (lpG (e : ℝ) (f : ℝ) ε x ξ η) (lpG (e : ℝ) (f : ℝ) ε x (ξ + 1) η)
      (lpG (e : ℝ) (f : ℝ) ε x ξ (η + 1)) := by
  have he0 := S.e0
  have hef := S.hef'
  have hnh := nhG_pos he0 hef
  have hGk : GHG (f : ℝ) ((D.tile t).pts k) = -((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ) * η) := by
    rw [hk, GHG_lp]
  have hGm : GHG (f : ℝ) ((D.tile t).pts m) = -((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ) * η) := by
    rw [hm, GHG_lp]
  have hlt := third_strict (D.tile t) hkm hkj hmj (GHG (f : ℝ)) (GHG_ne he0 hef) _ hGk hGm hle
  rw [hk] at hGk s1
  rw [hm] at s2
  have hj : (D.tile t).pts j = lpG (e : ℝ) (f : ℝ) ε x ξ (η + 1) := by
    refine third_unique_F (GHG (f : ℝ)) (neg_ne_zero.mpr (eps_neG hε)) (cross_rowG ξ η) hGk ?_ ?_
      hlt ?_
    · rw [s1, dist_comm]; exact (dist_step_vG he0 hef hε ξ η).symm
    · rw [s2, dist_comm]; exact (dist_step_aG he0 hef hε ξ η).symm
    · rw [GHG_lp]; nlinarith
  exact ⟨k, m, j, hkm, hkj, hmj, hk, hm, hj⟩

end recog


/-! ## 5. Specialisation to `e = 1`: the general statements give the statements of `SideRunLattice` -/

section e_one

theorem nuG_one (f : ℝ) : nuG 1 f = nu f := by unfold nuG nu; ring

theorem lpG_one (n ε x ξ η : ℝ) : lpG 1 n ε x ξ η = lp n ε x ξ η := by
  unfold lpG lp; rw [uuG_one, hhG_one]

theorem lvG_one (n ε x s : ℝ) : lvG 1 n ε x s = lv n ε x s := by
  unfold lvG lv; rw [hhG_one]

theorem GSG_one (n ε : ℝ) : GSG 1 n ε = GS n ε := by
  unfold GSG GS; rw [uuG_one, hhG_one]

theorem FXG_one (n ε : ℝ) : FXG 1 n ε = FX n ε := by
  unfold FXG FX; rw [uuG_one, hhG_one]

theorem GHG_eq (n : ℝ) : GHG n = GH n := rfl

theorem QfG_one (n dξ dη : ℝ) : QfG 1 n dξ dη = Qf n dξ dη := by unfold QfG Qf; ring

/-- `dist_lpG_sq` at `e = 1` is `SideRun.dist_lp_sq` -/
theorem dist_lp_sq_e1 {n ε x : ℝ} (hn : 1 < n) (hε : ε ^ 2 = 1) (ξ η ξ' η' : ℝ) :
    dist (lp n ε x ξ η) (lp n ε x ξ' η') ^ 2 = Qf n (ξ - ξ') (η - η') := by
  have h := dist_lpG_sq (e := 1) (f := n) (ε := ε) (x := x) one_pos hn hε ξ η ξ' η'
  rwa [lpG_one, lpG_one, QfG_one] at h

/-- `dist_N_VG` at `e = 1` is `SideRun.dist_N_V` -/
theorem dist_N_V_e1 {n ε x : ℝ} (hn : 1 < n) (hε : ε ^ 2 = 1) (ξ η : ℝ) :
    dist (lp n ε x (ξ - nu n) (η + 2 + nu n)) (lp n ε x (ξ + 1) η) = n ^ 2 := by
  have h := dist_N_VG (e := 1) (f := n) (ε := ε) (x := x) one_pos hn hε ξ η
  rwa [nuG_one, lpG_one, lpG_one] at h

section checks

variable {N : ℕ} {D : CongruentDissection N} {n : ℕ} {α β γ L ax ay ε x : ℝ}

/-- `m_edge_casesG` at `e = 1` is `SideRun.m_edge_cases` -/
theorem m_edge_cases_e1 (S : Setup D n α β γ L ax ay) (hε : ε ^ 2 = 1) {t : Fin N} {k m : Fin 3}
    (hkm : k ≠ m) {ξ η : ℝ} (hk : (D.tile t).pts k = lp n ε x (ξ + 1) η)
    (hm : (D.tile t).pts m = lp n ε x ξ (η + 1))
    (hle : ∀ i, GS n ε ((D.tile t).pts i) ≤ -lv n ε x (ξ + η + 1)) :
    HasV D t (lp n ε x (ξ + 1) η) (lp n ε x ξ (η + 1)) (lp n ε x (ξ + 1) (η + 1)) ∨
    HasV D t (lp n ε x (ξ + 1) η) (lp n ε x ξ (η + 1)) (lp n ε x (ξ - nu n) (η + 2 + nu n)) := by
  have h := m_edge_casesG (setupG_one_iff.mpr S) hε hkm (x := x) (ξ := ξ) (η := η)
    (by rw [Nat.cast_one, lpG_one]; exact hk) (by rw [Nat.cast_one, lpG_one]; exact hm)
    (by intro i; have h1 := hle i; rw [Nat.cast_one, GSG_one, lvG_one]; exact h1)
  simpa only [Nat.cast_one, lpG_one, nuG_one] using h

/-- `row_edge_UG` at `e = 1` is `SideRun.row_edge_U` -/
theorem row_edge_U_e1 (S : Setup D n α β γ L ax ay) (hε : ε ^ 2 = 1) {t : Fin N} {k m j : Fin 3}
    (hkm : k ≠ m) (hkj : k ≠ j) (hmj : m ≠ j) {ξ η : ℝ} (hk : (D.tile t).pts k = lp n ε x ξ η)
    (hm : (D.tile t).pts m = lp n ε x (ξ + 1) η)
    (hle : ∀ i, GH n ((D.tile t).pts i) ≤ -((n : ℝ) ^ 2 * hh n * η))
    (s1 : dist ((D.tile t).pts j) ((D.tile t).pts k) = (n : ℝ) ^ 2 - 1)
    (s2 : dist ((D.tile t).pts j) ((D.tile t).pts m) = n) :
    HasV D t (lp n ε x ξ η) (lp n ε x (ξ + 1) η) (lp n ε x ξ (η + 1)) := by
  have h := row_edge_UG (setupG_one_iff.mpr S) hε hkm hkj hmj (x := x) (ξ := ξ) (η := η)
    (by rw [Nat.cast_one, lpG_one]; exact hk) (by rw [Nat.cast_one, lpG_one]; exact hm)
    (by intro i; have h1 := hle i; rw [Nat.cast_one, hhG_one]; exact h1)
    (by rw [Nat.cast_one]; simpa using s1) (by rw [Nat.cast_one]; simpa using s2)
  simpa only [Nat.cast_one, lpG_one] using h

end checks

end e_one

end Erdos634.Draft.SideRunG

#print axioms Erdos634.Draft.SideRunG.dist_lpG_sq
#print axioms Erdos634.Draft.SideRunG.seg_split_lpG
#print axioms Erdos634.Draft.SideRunG.dist_N_VG
#print axioms Erdos634.Draft.SideRunG.dist_N_GG
#print axioms Erdos634.Draft.SideRunG.m_edge_casesG
#print axioms Erdos634.Draft.SideRunG.row_edge_UG
#print axioms Erdos634.Draft.SideRunG.m_edge_cases_e1
#print axioms Erdos634.Draft.SideRunG.row_edge_U_e1

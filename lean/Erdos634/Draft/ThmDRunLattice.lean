import Erdos634.Draft.SideRunGFrame
import Erdos634.Draft.ThmDRunConst

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours. Here: the row induction on a run (their Lemmas 32-34, Theorem 37).
# Theorem D' run port, module 2: the lattice over a side for the gamma = 2 alpha tile  (DRAFT, NOT COMPILED, UNAUDITED)

Written 2026-10-18 while the Lean slot was busy; never run through `lake`/`lean`.  Not in `All`.

Port of `Draft/SideRunGLattice.lean`, sections 1-2 (lattice points, side functionals, levels, the quadratic form, segments),
to the tile `(a, b, c) = (u^2, v^2 - u^2, u v)`.  Everything there that is free of a `SetupG` is re-stated with the constants
of `ThmDRunConst`; the proofs are those of the `G` files with `f^2 → u v`, `e f → u^2`, `f^2 - e^2 → v^2 - u^2`, and the
one genuinely different identity: the middle coefficient of the quadratic form is `2 c b cos α = v^2 (v^2 - u^2)`
(base-beta: `(2f^2 - e^2)(f^2 - e^2)`), proved in `dist_lpT_sq` from `cu_spec`.

GENERALISATION NOTE (answer to "abstract instead of copying").  `SideRunGLattice` can be made tile-generic by replacing the
two real constants `uuG, hhG` and the three side lengths by a record
`structure LTile where (a b c uu hh : ℝ)  (hc : 0 < c) (hb : 0 < b) (hh : 0 < hh) (h1 : hh^2 = a^2 - uu^2) (h2 : 0 < ...)`
with `lp T ε x ξ η := mkPt (x + ε((ξ+η)c − η uu)) (η hh)` and `Qf T dξ dη := c² dξ² + 2 c (c − uu) dξ dη + b² dη²`.
The base-beta family and the gamma = 2 alpha tile are two instances.  Doing it that way would make 5 of the 47 SideRunG
modules (Lattice, ChordB's `lpG_between` part, Row's `dist_rowG`, K3G, ClampedBelow) reusable verbatim; the cost is
re-proving the 8 G-modules over `LTile`.  The plan (`thmD_port_plan.md`) records this as option B and chooses option A (copy)
for the first modules because the compiled G files must not be touched while the Lean slot is shared.
-/

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.RunPartition Erdos634.Draft.SideRun Set

variable {u v : ℝ}

/-! ## 1. Lattice points and the three functionals -/

/-- the lattice point `P + ξ u⃗ + η v⃗`, `P = (x, 0)` (`|u⃗| = c = uv`, `|v⃗| = b`, `|v⃗ − u⃗| = a`) -/
noncomputable def lpT (u v ε x ξ η : ℝ) : Plane :=
  mkPt (x + ε * ((ξ + η) * (u * v) - η * uuT u v)) (η * hhT u v)

theorem lpT_congr {ε x ξ η ξ' η' : ℝ} (h1 : ξ = ξ') (h2 : η = η') :
    lpT u v ε x ξ η = lpT u v ε x ξ' η' := by rw [h1, h2]

theorem lpT_zero (u v ε x : ℝ) : lpT u v ε x 0 0 = mkPt x 0 := by
  unfold lpT; exact mkPt_congr (by ring) (by ring)

theorem eps_neT {ε : ℝ} (hε : ε ^ 2 = 1) : ε ≠ 0 := by
  rintro rfl
  norm_num at hε

/-- the level of the lattice coordinate `s` -/
noncomputable def lvT (u v ε x s : ℝ) : ℝ := ε * hhT u v * x + (u * v) * hhT u v * s

/-- constant on the lines of direction `v⃗`; grows with `ξ` -/
noncomputable def FXT (u v ε : ℝ) : Plane →ₗ[ℝ] ℝ := lin (ε * hhT u v) (uuT u v - u * v)

/-- constant on the lines of direction `v⃗ − u⃗`; decreases with `ξ + η` -/
noncomputable def GST (u v ε : ℝ) : Plane →ₗ[ℝ] ℝ := lin (-(ε * hhT u v)) (-(uuT u v))

/-- constant on the rows; decreases with `η` -/
noncomputable def GHT (u v : ℝ) : Plane →ₗ[ℝ] ℝ := lin 0 (-(u * v))

theorem FXT_lp {ε x : ℝ} (hε : ε ^ 2 = 1) (ξ η : ℝ) :
    FXT u v ε (lpT u v ε x ξ η) = lvT u v ε x ξ := by
  unfold FXT lpT lvT
  rw [lin_mk]
  linear_combination (hhT u v * ((ξ + η) * (u * v) - η * uuT u v)) * hε

theorem GST_lp {ε x : ℝ} (hε : ε ^ 2 = 1) (ξ η : ℝ) :
    GST u v ε (lpT u v ε x ξ η) = -lvT u v ε x (ξ + η) := by
  unfold GST lpT lvT
  rw [lin_mk]
  linear_combination (-(hhT u v * ((ξ + η) * (u * v) - η * uuT u v))) * hε

theorem GHT_lp (ε x ξ η : ℝ) : GHT u v (lpT u v ε x ξ η) = -((u * v) * hhT u v * η) := by
  unfold GHT lpT
  rw [lin_mk]
  ring

theorem GHT_apply (p : Plane) : GHT u v p = -((u * v) * p 1) := by
  unfold GHT; rw [lin_apply]; ring

theorem nhT_pos (hu : 0 < u) (huv : u < v) (hv : v < 2 * u) : 0 < (u * v) * hhT u v :=
  mul_pos (mul_pos hu (hu.trans huv)) (hhT_pos hu huv hv)

theorem FXT_ne {ε : ℝ} (hu : 0 < u) (huv : u < v) (hv : v < 2 * u) (hε : ε ^ 2 = 1) : FXT u v ε ≠ 0 :=
  lin_ne_zero (Or.inl (mul_ne_zero (eps_neT hε) (hhT_pos hu huv hv).ne'))

theorem GST_ne {ε : ℝ} (hu : 0 < u) (huv : u < v) (hv : v < 2 * u) (hε : ε ^ 2 = 1) : GST u v ε ≠ 0 :=
  lin_ne_zero (Or.inl (neg_ne_zero.mpr (mul_ne_zero (eps_neT hε) (hhT_pos hu huv hv).ne')))

theorem GHT_ne (hu : 0 < u) (huv : u < v) : GHT u v ≠ 0 :=
  lin_ne_zero (Or.inr (neg_ne_zero.mpr (mul_pos hu (hu.trans huv)).ne'))

theorem lvT_lt {ε x s s' : ℝ} (hu : 0 < u) (huv : u < v) (hv : v < 2 * u) (h : s < s') :
    lvT u v ε x s < lvT u v ε x s' := by
  unfold lvT
  nlinarith [mul_pos (nhT_pos hu huv hv) (sub_pos.mpr h)]

theorem lvT_le {ε x s s' : ℝ} (hu : 0 < u) (huv : u < v) (hv : v < 2 * u) (h : s ≤ s') :
    lvT u v ε x s ≤ lvT u v ε x s' := by
  unfold lvT
  nlinarith [mul_nonneg (nhT_pos hu huv hv).le (sub_nonneg.mpr h)]

theorem lvT_inj {ε x s s' : ℝ} (hu : 0 < u) (huv : u < v) (hv : v < 2 * u)
    (h : lvT u v ε x s = lvT u v ε x s') : s = s' := by
  rcases lt_trichotomy s s' with h1 | h1 | h1
  · exact absurd h (lvT_lt hu huv hv h1).ne
  · exact h1
  · exact absurd h (lvT_lt hu huv hv h1).ne'

theorem lpT_eta_eq {ε x ξ η ξ' η' : ℝ} (hu : 0 < u) (huv : u < v) (hv : v < 2 * u)
    (h : lpT u v ε x ξ η = lpT u v ε x ξ' η') : η = η' := by
  have h1 : (lpT u v ε x ξ η) 1 = (lpT u v ε x ξ' η') 1 := by rw [h]
  unfold lpT at h1
  rw [mkPt_one, mkPt_one] at h1
  exact mul_right_cancel₀ (hhT_pos hu huv hv).ne' h1

theorem lpT_xi_eq {ε x ξ η ξ' η' : ℝ} (hu : 0 < u) (huv : u < v) (hv : v < 2 * u) (hε : ε ^ 2 = 1)
    (h : lpT u v ε x ξ η = lpT u v ε x ξ' η') : ξ = ξ' := by
  have h1 : FXT u v ε (lpT u v ε x ξ η) = FXT u v ε (lpT u v ε x ξ' η') := by rw [h]
  rw [FXT_lp hε, FXT_lp hε] at h1
  exact lvT_inj hu huv hv h1

theorem lpT_ne_eta {ε x ξ η ξ' η' : ℝ} (hu : 0 < u) (huv : u < v) (hv : v < 2 * u) (h : η ≠ η') :
    lpT u v ε x ξ η ≠ lpT u v ε x ξ' η' := fun he' => h (lpT_eta_eq hu huv hv he')

theorem lpT_ne_xi {ε x ξ η ξ' η' : ℝ} (hu : 0 < u) (huv : u < v) (hv : v < 2 * u) (hε : ε ^ 2 = 1)
    (h : ξ ≠ ξ') : lpT u v ε x ξ η ≠ lpT u v ε x ξ' η' := fun he' => h (lpT_xi_eq hu huv hv hε he')

/-! ## 2. Distances and segments -/

/-- the squared length of `dξ u⃗ + dη v⃗`; middle coefficient `2 c b cos α = v² b` -/
def QfT (u v dξ dη : ℝ) : ℝ :=
  (u * v) ^ 2 * dξ ^ 2 + v ^ 2 * (v ^ 2 - u ^ 2) * (dξ * dη) + (v ^ 2 - u ^ 2) ^ 2 * dη ^ 2

theorem dist_lpT_sq {ε x : ℝ} (hu : 0 < u) (huv : u < v) (hv : v < 2 * u) (hε : ε ^ 2 = 1)
    (ξ η ξ' η' : ℝ) :
    dist (lpT u v ε x ξ η) (lpT u v ε x ξ' η') ^ 2 = QfT u v (ξ - ξ') (η - η') := by
  have hu1 := uuT_spec (v := v) hu
  have hsq := hhT_sq' hu hv (hu.trans huv)
  unfold lpT QfT
  rw [dist_sq_mkPt]
  linear_combination (((ξ - ξ') * (u * v) + (η - η') * (u * v - uuT u v)) ^ 2) * hε
    + (η - η') ^ 2 * hsq - v * ((ξ - ξ') * (η - η')) * hu1

theorem dist_lpT {ε x : ℝ} (hu : 0 < u) (huv : u < v) (hv : v < 2 * u) (hε : ε ^ 2 = 1)
    {ξ η ξ' η' d : ℝ} (hd0 : 0 ≤ d) (hd : QfT u v (ξ - ξ') (η - η') = d ^ 2) :
    dist (lpT u v ε x ξ η) (lpT u v ε x ξ' η') = d :=
  dist_eq_of_sq_eq (by rw [dist_lpT_sq hu huv hv hε, hd]) dist_nonneg hd0

theorem lineMap_lpT (u v ε x ξ η ξ' η' t : ℝ) :
    AffineMap.lineMap (lpT u v ε x ξ η) (lpT u v ε x ξ' η') t
      = lpT u v ε x (ξ + t * (ξ' - ξ)) (η + t * (η' - η)) := by
  unfold lpT
  rw [CSlot.lineMap_mkPt]
  exact mkPt_congr (by ring) (by ring)

theorem lp_extT (u v ε x ξ η ξ' η' s : ℝ) :
    lpT u v ε x ξ η + s • (lpT u v ε x ξ η - lpT u v ε x ξ' η')
      = lpT u v ε x (ξ + s * (ξ - ξ')) (η + s * (η - η')) := by
  unfold lpT
  apply plane_ext <;>
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, mkPt_zero, mkPt_one] <;>
    ring

/-- a point of a segment between lattice points, in lattice coordinates -/
theorem lp_seg_paramT {ε x ξ η ξ' η' : ℝ} {y : Plane}
    (hy : y ∈ segment ℝ (lpT u v ε x ξ η) (lpT u v ε x ξ' η')) :
    ∃ τ : ℝ, 0 ≤ τ ∧ τ ≤ 1 ∧ y = lpT u v ε x (ξ + τ * (ξ' - ξ)) (η + τ * (η' - η)) := by
  rw [segment_eq_image_lineMap] at hy
  obtain ⟨τ, ⟨h0, h1⟩, rfl⟩ := hy
  exact ⟨τ, h0, h1, lineMap_lpT u v ε x ξ η ξ' η' τ⟩

theorem lp_mem_segT {ε x ξ η ξ' η' τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1) :
    lpT u v ε x (ξ + τ * (ξ' - ξ)) (η + τ * (η' - η)) ∈
      segment ℝ (lpT u v ε x ξ η) (lpT u v ε x ξ' η') := by
  rw [segment_eq_image_lineMap]
  exact ⟨τ, ⟨h0, h1⟩, lineMap_lpT u v ε x ξ η ξ' η' τ⟩

/-- **A segment of `q` lattice steps is the union of its steps.** -/
theorem seg_split_lpT {ε x ξ η dξ dη : ℝ} {q : ℕ} (hq : 1 ≤ q) {y : Plane}
    (hy : y ∈ segment ℝ (lpT u v ε x ξ η) (lpT u v ε x (ξ + q * dξ) (η + q * dη))) :
    ∃ i : ℕ, i < q ∧ y ∈ segment ℝ (lpT u v ε x (ξ + i * dξ) (η + i * dη))
      (lpT u v ε x (ξ + (i + 1) * dξ) (η + (i + 1) * dη)) := by
  obtain ⟨τ, h0, h1, rfl⟩ := lp_seg_paramT hy
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  obtain ⟨i, hi, hi1, hi2⟩ := exists_nat_between hq (s := τ * q) (mul_nonneg h0 hq'.le)
    (by nlinarith [mul_nonneg (sub_nonneg.mpr h1) hq'.le])
  refine ⟨i, hi, ?_⟩
  have h := lp_mem_segT (u := u) (v := v) (ε := ε) (x := x) (ξ := ξ + i * dξ) (η := η + i * dη)
    (ξ' := ξ + (i + 1) * dξ) (η' := η + (i + 1) * dη) (τ := τ * q - i) (by linarith) (by linarith)
  have e' : lpT u v ε x (ξ + τ * (ξ + q * dξ - ξ)) (η + τ * (η + q * dη - η))
      = lpT u v ε x (ξ + i * dξ + (τ * q - i) * (ξ + (i + 1) * dξ - (ξ + i * dξ)))
          (η + i * dη + (τ * q - i) * (η + (i + 1) * dη - (η + i * dη))) :=
    lpT_congr (by ring) (by ring)
  rw [e']; exact h

/-! ## 3. The three step lengths (the lattice triangle `U(ξ,η)` has sides `c, b, a`) -/

theorem dist_step_uT {ε x : ℝ} (hu : 0 < u) (huv : u < v) (hv : v < 2 * u) (hε : ε ^ 2 = 1) (ξ η : ℝ) :
    dist (lpT u v ε x ξ η) (lpT u v ε x (ξ + 1) η) = u * v :=
  dist_lpT hu huv hv hε (mul_pos hu (hu.trans huv)).le (by unfold QfT; ring)

theorem dist_step_vT {ε x : ℝ} (hu : 0 < u) (huv : u < v) (hv : v < 2 * u) (hε : ε ^ 2 = 1) (ξ η : ℝ) :
    dist (lpT u v ε x ξ η) (lpT u v ε x ξ (η + 1)) = v ^ 2 - u ^ 2 :=
  dist_lpT hu huv hv hε (b_posT huv hu).le (by unfold QfT; ring)

theorem dist_step_aT {ε x : ℝ} (hu : 0 < u) (huv : u < v) (hv : v < 2 * u) (hε : ε ^ 2 = 1) (ξ η : ℝ) :
    dist (lpT u v ε x (ξ + 1) η) (lpT u v ε x ξ (η + 1)) = u ^ 2 :=
  dist_lpT hu huv hv hε (sq_nonneg u) (by unfold QfT; ring)

/-- **The mirror coordinate.**  The mirror image `N(ξ,η)` of `U(ξ,η)` in its `a`-edge has third vertex
`lp (ξ + 2 − μ) (η + μ)` with `μ = 2 c uu / a² = v² (3u² − v²) / u⁴`.
WARNING (difference from base-beta): there the same vertex is `lp (ξ − ν) (η + 2 + ν)`, i.e. `μ = 2 + ν`, with
`ν = b/c`.  That identity (`c·uu/a² = 1 + ν/2`) is special to the base-beta family; for the gamma = 2 alpha tile
`μ = 50/81` at `(u,v) = (3,5)` while `2 + ν = 46/15`.  Everything in `SideRunGChord`/`SideRunGMStep*` that uses the
height `η + 2 + ν` of the mirror vertex (the mirror case `MirrorAt`, `m_next_casesG`, bounds `δ (2 + ν) < 1`) must be
redone with `μ`; `μ` is small, possibly negative (negative iff `v² > 3u²`). -/
noncomputable def muT (u v : ℝ) : ℝ := v ^ 2 * (3 * u ^ 2 - v ^ 2) / u ^ 4

theorem muT_spec (hu : 0 < u) : muT u v * u ^ 4 = v ^ 2 * (3 * u ^ 2 - v ^ 2) := by
  unfold muT
  exact div_mul_cancel₀ _ (pow_ne_zero 4 hu.ne')

theorem dist_N_VT {ε x : ℝ} (hu : 0 < u) (huv : u < v) (hv : v < 2 * u) (hε : ε ^ 2 = 1) (ξ η : ℝ) :
    dist (lpT u v ε x (ξ + 2 - muT u v) (η + muT u v)) (lpT u v ε x (ξ + 1) η) = u * v := by
  have hμ := muT_spec (v := v) hu
  refine dist_lpT hu huv hv hε (mul_pos hu (hu.trans huv)).le ?_
  unfold QfT
  linear_combination (muT u v) * hμ

theorem dist_N_GT {ε x : ℝ} (hu : 0 < u) (huv : u < v) (hv : v < 2 * u) (hε : ε ^ 2 = 1) (ξ η : ℝ) :
    dist (lpT u v ε x (ξ + 2 - muT u v) (η + muT u v)) (lpT u v ε x ξ (η + 1)) = v ^ 2 - u ^ 2 := by
  have hμ := muT_spec (v := v) hu
  refine dist_lpT hu huv hv hε (b_posT huv hu).le ?_
  unfold QfT
  linear_combination (muT u v - 2) * hμ

end Erdos634.Draft.ThmDRun

#print axioms Erdos634.Draft.ThmDRun.lpT_congr
#print axioms Erdos634.Draft.ThmDRun.lpT_zero
#print axioms Erdos634.Draft.ThmDRun.eps_neT
#print axioms Erdos634.Draft.ThmDRun.FXT_lp
#print axioms Erdos634.Draft.ThmDRun.GST_lp
#print axioms Erdos634.Draft.ThmDRun.GHT_lp
#print axioms Erdos634.Draft.ThmDRun.GHT_apply
#print axioms Erdos634.Draft.ThmDRun.nhT_pos
#print axioms Erdos634.Draft.ThmDRun.FXT_ne
#print axioms Erdos634.Draft.ThmDRun.GST_ne
#print axioms Erdos634.Draft.ThmDRun.GHT_ne
#print axioms Erdos634.Draft.ThmDRun.lvT_lt
#print axioms Erdos634.Draft.ThmDRun.lvT_le
#print axioms Erdos634.Draft.ThmDRun.lvT_inj
#print axioms Erdos634.Draft.ThmDRun.lpT_eta_eq
#print axioms Erdos634.Draft.ThmDRun.lpT_xi_eq
#print axioms Erdos634.Draft.ThmDRun.lpT_ne_eta
#print axioms Erdos634.Draft.ThmDRun.lpT_ne_xi
#print axioms Erdos634.Draft.ThmDRun.dist_lpT_sq
#print axioms Erdos634.Draft.ThmDRun.dist_lpT
#print axioms Erdos634.Draft.ThmDRun.lineMap_lpT
#print axioms Erdos634.Draft.ThmDRun.lp_extT
#print axioms Erdos634.Draft.ThmDRun.lp_seg_paramT
#print axioms Erdos634.Draft.ThmDRun.lp_mem_segT
#print axioms Erdos634.Draft.ThmDRun.seg_split_lpT
#print axioms Erdos634.Draft.ThmDRun.dist_step_uT
#print axioms Erdos634.Draft.ThmDRun.dist_step_vT
#print axioms Erdos634.Draft.ThmDRun.dist_step_aT
#print axioms Erdos634.Draft.ThmDRun.muT_spec
#print axioms Erdos634.Draft.ThmDRun.dist_N_VT
#print axioms Erdos634.Draft.ThmDRun.dist_N_GT

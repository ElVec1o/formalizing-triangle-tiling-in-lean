-- Draft/FDBBaseBetaE1.lean -- FDB item 9: `thm:basebeta-e1` (companion), `thm:realize12`
-- (main + companion), `cor:elevenm` (main), assembled from existing Lean:
--   `E1FamilyFull.e1_family_congruent` / `R1Final.r1_n11`   (exclusion at m = 1),
--   `CollarInputs.realize12_region` + `Realizable.scaleDissection`  (existence, m >= 2).
-- The paper speaks of a tile with sides (2,3,4) and a target with sides (8m,8m,11m); the Lean it
-- is assembled from speaks of `baseBetaTarget 1 2` / `modelTri 2` (m = 1, up to congruence) and
-- of the scale-8 data `Phi`-triangle `Delta_m` / `M44` (tile (16,24,32)).  The new content here is
-- ONLY the bridge (SSS + a 1/8 homothety) from those to the paper's side lengths.
-- Side lengths are stated through `HasSides` (some vertex order, sides opposite the vertices),
-- so no labelling or orientation convention is assumed.
-- STATEMENT MATCH recorded in (private working notes, not included)  UNAUDITED; promotes no label.
-- Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).  No sorry, no native_decide.
import Erdos634.Draft.E1FamilyFull
import Erdos634.Draft.CollarInputs

namespace Erdos634.Draft.FDBBaseBetaE1
open Erdos634.Geometry Erdos634.BaseBetaTargetCoord Erdos634.CertCoord

/-- `T` has side lengths `a, b, c`, in some vertex order `τ` (the sides opposite `τ 0, τ 1, τ 2`). -/
def HasSides (T : Tri) (a b c : ℝ) : Prop :=
  ∃ τ : Equiv.Perm (Fin 3), dist (T.pts (τ 1)) (T.pts (τ 2)) = a ∧
    dist (T.pts (τ 2)) (T.pts (τ 0)) = b ∧ dist (T.pts (τ 0)) (T.pts (τ 1)) = c

/-- SSS: a triangle with sides `(a,b,c)` in some order is congruent to any `U` whose sides opposite
`U.pts 0, 1, 2` are `a, b, c`. -/
theorem congruent_of_hasSides {T U : Tri} {a b c : ℝ} (hT : HasSides T a b c)
    (h12 : dist (U.pts 1) (U.pts 2) = a) (h20 : dist (U.pts 2) (U.pts 0) = b)
    (h01 : dist (U.pts 0) (U.pts 1) = c) : T.Congruent U := by
  obtain ⟨τ, ha, hb, hc⟩ := hT
  refine (Tri.congruent_relabel T τ).trans
    (Erdos634.SssCongruent.congruent_of_dist_three ?_ ?_ ?_)
  · simp only [Tri.relabel_pts]; rw [hc, h01]
  · simp only [Tri.relabel_pts]; rw [ha, h12]
  · simp only [Tri.relabel_pts]; rw [hb, h20]

/-! ## The m = 1 exclusion, in the paper's side-length form -/

theorem target11_congruent {T : Tri} (h : HasSides T 8 8 11) :
    T.Congruent (baseBetaTarget 1 ((2 : ℕ) : ℝ) one_pos (by norm_num)) := by
  refine congruent_of_hasSides h ?_ ?_ ?_
  · rw [baseBetaTarget_dist_leg₁]; norm_num
  · rw [dist_comm, baseBetaTarget_dist_leg₀]; norm_num
  · rw [baseBetaTarget_dist_base]; norm_num

theorem tile234_congruent {T : Tri} (h : HasSides T 2 3 4) :
    T.Congruent (MarchCompose.modelTri ((2 : ℕ) : ℝ) (by norm_num)) := by
  obtain ⟨m0, m1, m2⟩ := MarchCompose.modelTri_sides (f := ((2 : ℕ) : ℝ)) (by norm_num)
  have d12 : dist ((MarchCompose.modelTri ((2 : ℕ) : ℝ) (by norm_num)).pts 1)
      ((MarchCompose.modelTri ((2 : ℕ) : ℝ) (by norm_num)).pts 2) = ((2 : ℕ) : ℝ) := m0
  have d20 : dist ((MarchCompose.modelTri ((2 : ℕ) : ℝ) (by norm_num)).pts 2)
      ((MarchCompose.modelTri ((2 : ℕ) : ℝ) (by norm_num)).pts 0) = (((2 : ℕ) : ℝ) ^ 2 - 1) := m1
  have d01 : dist ((MarchCompose.modelTri ((2 : ℕ) : ℝ) (by norm_num)).pts 0)
      ((MarchCompose.modelTri ((2 : ℕ) : ℝ) (by norm_num)).pts 1) = (((2 : ℕ) : ℝ) ^ 2) := m2
  refine congruent_of_hasSides h ?_ ?_ ?_
  · rw [d12]; norm_num
  · rw [d20]; norm_num
  · rw [d01]; norm_num

/-- **`thm:basebeta-e1` (companion, erdos-634-companion.tex:113).**  The isosceles triangle with
base angles `β` and sides `(8,8,11)` admits no tiling by copies of the tile `(2,3,4)`.  Lean quantifies
over EVERY tile count `N` (the paper's `N = 11`; `N = 11` is forced by area, but is not assumed). -/
theorem thm_basebeta_e1 {N : ℕ} (D : CongruentDissection N)
    (htgt : HasSides D.target 8 8 11) (hmod : HasSides D.model 2 3 4) : False :=
  Erdos634.Draft.E1FamilyFull.e1_family_congruent D (n := 2) le_rfl
    (target11_congruent htgt) (tile234_congruent hmod)

/-- The same with the paper's `N = 11` written in. -/
theorem thm_basebeta_e1_N11 :
    ¬ ∃ D : CongruentDissection 11, HasSides D.target 8 8 11 ∧ HasSides D.model 2 3 4 := by
  rintro ⟨D, h1, h2⟩
  exact thm_basebeta_e1 D h1 h2

/-- **Non-vacuity (m = 1).**  Each hypothesis of `thm_basebeta_e1` is individually satisfiable: the
canonical `baseBetaTarget 1 2` really has sides `(8,8,11)` and `modelTri 2` really has sides `(2,3,4)`.
(They are jointly unsatisfiable on a dissection: that is the theorem.  At `m ≥ 2` the joint
hypotheses ARE satisfied, by `realize12_existence`.) -/
theorem hasSides_witnesses :
    HasSides (baseBetaTarget 1 ((2 : ℕ) : ℝ) one_pos (by norm_num)) 8 8 11 ∧
    HasSides (MarchCompose.modelTri ((2 : ℕ) : ℝ) (by norm_num)) 2 3 4 := by
  obtain ⟨m0, m1, m2⟩ := MarchCompose.modelTri_sides (f := ((2 : ℕ) : ℝ)) (by norm_num)
  refine ⟨⟨1, ?_, ?_, ?_⟩, ⟨1, ?_, ?_, ?_⟩⟩
  · show dist ((baseBetaTarget 1 ((2 : ℕ) : ℝ) one_pos (by norm_num)).pts 1)
      ((baseBetaTarget 1 ((2 : ℕ) : ℝ) one_pos (by norm_num)).pts 2) = 8
    rw [baseBetaTarget_dist_leg₁]; norm_num
  · show dist ((baseBetaTarget 1 ((2 : ℕ) : ℝ) one_pos (by norm_num)).pts 2)
      ((baseBetaTarget 1 ((2 : ℕ) : ℝ) one_pos (by norm_num)).pts 0) = 8
    rw [dist_comm, baseBetaTarget_dist_leg₀]; norm_num
  · show dist ((baseBetaTarget 1 ((2 : ℕ) : ℝ) one_pos (by norm_num)).pts 0)
      ((baseBetaTarget 1 ((2 : ℕ) : ℝ) one_pos (by norm_num)).pts 1) = 11
    rw [baseBetaTarget_dist_base]; norm_num
  · show dist ((MarchCompose.modelTri ((2 : ℕ) : ℝ) (by norm_num)).pts 1)
      ((MarchCompose.modelTri ((2 : ℕ) : ℝ) (by norm_num)).pts 2) = 2
    have : dist ((MarchCompose.modelTri ((2 : ℕ) : ℝ) (by norm_num)).pts 1)
      ((MarchCompose.modelTri ((2 : ℕ) : ℝ) (by norm_num)).pts 2) = ((2 : ℕ) : ℝ) := m0
    rw [this]; norm_num
  · show dist ((MarchCompose.modelTri ((2 : ℕ) : ℝ) (by norm_num)).pts 2)
      ((MarchCompose.modelTri ((2 : ℕ) : ℝ) (by norm_num)).pts 0) = 3
    have : dist ((MarchCompose.modelTri ((2 : ℕ) : ℝ) (by norm_num)).pts 2)
      ((MarchCompose.modelTri ((2 : ℕ) : ℝ) (by norm_num)).pts 0) = (((2 : ℕ) : ℝ) ^ 2 - 1) := m1
    rw [this]; norm_num
  · show dist ((MarchCompose.modelTri ((2 : ℕ) : ℝ) (by norm_num)).pts 0)
      ((MarchCompose.modelTri ((2 : ℕ) : ℝ) (by norm_num)).pts 1) = 4
    have : dist ((MarchCompose.modelTri ((2 : ℕ) : ℝ) (by norm_num)).pts 0)
      ((MarchCompose.modelTri ((2 : ℕ) : ℝ) (by norm_num)).pts 1) = (((2 : ℕ) : ℝ) ^ 2) := m2
    rw [this]; norm_num

/-! ## Existence for m >= 2 -/

set_option linter.unusedSimpArgs false in
theorem delta_dists (m : ℝ) (hm : 0 < m) :
    dist ((Erdos634.Draft.CollarInputs.deltaTri m hm).pts 1)
        ((Erdos634.Draft.CollarInputs.deltaTri m hm).pts 2) = 64 * m ∧
    dist ((Erdos634.Draft.CollarInputs.deltaTri m hm).pts 2)
        ((Erdos634.Draft.CollarInputs.deltaTri m hm).pts 0) = 64 * m ∧
    dist ((Erdos634.Draft.CollarInputs.deltaTri m hm).pts 0)
        ((Erdos634.Draft.CollarInputs.deltaTri m hm).pts 1) = 88 * m := by
  have hs := Erdos634.Draft.CollarParam.s15_sq
  refine ⟨?_, ?_, ?_⟩
  · refine Erdos634.Draft.CollarInputs.eq_of_sq_eq dist_nonneg (by positivity) ?_
    simp only [Erdos634.Draft.CollarInputs.deltaTri, mkTri_pts, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    rw [dist_sq_mkPt]
    linear_combination (144 * m ^ 2) * hs
  · refine Erdos634.Draft.CollarInputs.eq_of_sq_eq dist_nonneg (by positivity) ?_
    simp only [Erdos634.Draft.CollarInputs.deltaTri, mkTri_pts, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    rw [dist_sq_mkPt]
    linear_combination (144 * m ^ 2) * hs
  · refine Erdos634.Draft.CollarInputs.eq_of_sq_eq dist_nonneg (by positivity) ?_
    simp only [Erdos634.Draft.CollarInputs.deltaTri, mkTri_pts, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    rw [dist_sq_mkPt]
    ring

theorem M44_dists :
    dist (Erdos634.Draft.CollarInputs.M44.pts 0) (Erdos634.Draft.CollarInputs.M44.pts 1) = 16 ∧
    dist (Erdos634.Draft.CollarInputs.M44.pts 1) (Erdos634.Draft.CollarInputs.M44.pts 2) = 24 ∧
    dist (Erdos634.Draft.CollarInputs.M44.pts 2) (Erdos634.Draft.CollarInputs.M44.pts 0) = 32 := by
  obtain ⟨a, b, c⟩ := Erdos634.Draft.CollarInputs.M44_sq
  refine ⟨?_, ?_, ?_⟩
  · exact Erdos634.Draft.CollarInputs.eq_of_sq_eq dist_nonneg (by norm_num) (by rw [a]; norm_num)
  · exact Erdos634.Draft.CollarInputs.eq_of_sq_eq dist_nonneg (by norm_num) (by rw [b]; norm_num)
  · exact Erdos634.Draft.CollarInputs.eq_of_sq_eq dist_nonneg (by norm_num) (by rw [c]; norm_num)

/-- The vertex order `0 ↦ 2, 1 ↦ 0, 2 ↦ 1`. -/
def tau3 : Equiv.Perm (Fin 3) := ⟨![2, 0, 1], ![1, 2, 0], by decide, by decide⟩

/-- **Existence half of `thm:realize12`.**  For `m ≥ 2` there is a dissection into `11 m²` tiles
`(2,3,4)` of a triangle with sides `(8m, 8m, 11m)` (the scale-8 `Delta_m` of `CollarInputs`, shrunk
by `1/8`). -/
theorem realize12_existence (m : ℕ) (hm : 2 ≤ m) :
    ∃ D : CongruentDissection (11 * (m * m)),
      HasSides D.target (8 * m) (8 * m) (11 * m) ∧ HasSides D.model 2 3 4 := by
  open Erdos634.Draft.CollarInputs Erdos634.Draft.RegionTiling Erdos634.Draft.CollarParam in
  obtain ⟨R⟩ := realize12_region m hm
  have hpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have R' : Erdos634.Draft.RegionTiling.RTiling
      (Erdos634.Draft.CollarInputs.deltaTri (m : ℝ) hpos).carrier
      Erdos634.Draft.CollarInputs.M44 (11 * (m * m)) :=
    Erdos634.Draft.CollarParam.RTiling.cast
      (Erdos634.Draft.CollarInputs.deltaTri_carrier _ hpos).symm R
  let D0 : CongruentDissection (11 * (m * m)) := Erdos634.Draft.RegionTiling.toCD R'
  have hD0t : D0.target = Erdos634.Draft.CollarInputs.deltaTri (m : ℝ) hpos := rfl
  have hD0m : D0.model = Erdos634.Draft.CollarInputs.M44 := rfl
  have hr : (1 / 8 : ℝ) ≠ 0 := by norm_num
  refine ⟨Erdos634.Realizable.scaleDissection (0 : Plane) (1 / 8) hr D0, ⟨1, ?_, ?_, ?_⟩, ⟨tau3, ?_, ?_, ?_⟩⟩
  · rw [Erdos634.Realizable.scaleDissection_target_pts, Erdos634.Realizable.scaleDissection_target_pts,
      Erdos634.Realizable.homothetyEquiv_dist, hD0t]
    show |(1 / 8 : ℝ)| * dist ((Erdos634.Draft.CollarInputs.deltaTri (m : ℝ) hpos).pts 1)
      ((Erdos634.Draft.CollarInputs.deltaTri (m : ℝ) hpos).pts 2) = _
    rw [(delta_dists m hpos).1]; norm_num [abs_of_pos]; ring
  · rw [Erdos634.Realizable.scaleDissection_target_pts, Erdos634.Realizable.scaleDissection_target_pts,
      Erdos634.Realizable.homothetyEquiv_dist, hD0t]
    show |(1 / 8 : ℝ)| * dist ((Erdos634.Draft.CollarInputs.deltaTri (m : ℝ) hpos).pts 2)
      ((Erdos634.Draft.CollarInputs.deltaTri (m : ℝ) hpos).pts 0) = _
    rw [(delta_dists m hpos).2.1]; norm_num [abs_of_pos]; ring
  · rw [Erdos634.Realizable.scaleDissection_target_pts, Erdos634.Realizable.scaleDissection_target_pts,
      Erdos634.Realizable.homothetyEquiv_dist, hD0t]
    show |(1 / 8 : ℝ)| * dist ((Erdos634.Draft.CollarInputs.deltaTri (m : ℝ) hpos).pts 0)
      ((Erdos634.Draft.CollarInputs.deltaTri (m : ℝ) hpos).pts 1) = _
    rw [(delta_dists m hpos).2.2]; norm_num [abs_of_pos]; ring
  · have e1 : tau3 1 = 0 := rfl
    have e2 : tau3 2 = 1 := rfl
    rw [e1, e2, Erdos634.Realizable.scaleDissection_model_pts, Erdos634.Realizable.scaleDissection_model_pts,
      Erdos634.Realizable.homothetyEquiv_dist]
    show |(1 / 8 : ℝ)| * dist (Erdos634.Draft.CollarInputs.M44.pts 0)
      (Erdos634.Draft.CollarInputs.M44.pts 1) = _
    rw [M44_dists.1]; norm_num [abs_of_pos]
  · have e2 : tau3 2 = 1 := rfl
    have e0 : tau3 0 = 2 := rfl
    rw [e2, e0, Erdos634.Realizable.scaleDissection_model_pts, Erdos634.Realizable.scaleDissection_model_pts,
      Erdos634.Realizable.homothetyEquiv_dist]
    show |(1 / 8 : ℝ)| * dist (Erdos634.Draft.CollarInputs.M44.pts 1)
      (Erdos634.Draft.CollarInputs.M44.pts 2) = _
    rw [M44_dists.2.1]; norm_num [abs_of_pos]
  · have e0 : tau3 0 = 2 := rfl
    have e1 : tau3 1 = 0 := rfl
    rw [e0, e1, Erdos634.Realizable.scaleDissection_model_pts, Erdos634.Realizable.scaleDissection_model_pts,
      Erdos634.Realizable.homothetyEquiv_dist]
    show |(1 / 8 : ℝ)| * dist (Erdos634.Draft.CollarInputs.M44.pts 2)
      (Erdos634.Draft.CollarInputs.M44.pts 0) = _
    rw [M44_dists.2.2]; norm_num [abs_of_pos]

/-- **`thm:realize12` (main erdos-634.tex:308; companion erdos-634-companion.tex:4537).**
Tile `(2,3,4)`, target the isosceles triangle with sides `(8m,8m,11m)` (base angles `β`, the member
`(e,f) = (1,2)`), `N = 11 m²`: tileable iff `m ≠ 1`.  Existence at `N = 11 m²` for `m ≥ 2`; at
`m = 1` no dissection for ANY `N`. -/
theorem thm_realize12 (m : ℕ) (hm : 1 ≤ m) :
    (m ≠ 1 → ∃ D : CongruentDissection (11 * (m * m)),
        HasSides D.target (8 * m) (8 * m) (11 * m) ∧ HasSides D.model 2 3 4) ∧
    (m = 1 → ∀ (N : ℕ) (D : CongruentDissection N),
        ¬ (HasSides D.target (8 * m) (8 * m) (11 * m) ∧ HasSides D.model 2 3 4)) := by
  refine ⟨fun h => realize12_existence m (by omega), ?_⟩
  rintro rfl N D ⟨h1, h2⟩
  apply thm_basebeta_e1 D _ h2
  simpa using h1

/-- `thm:realize12` as a single `iff`: some `N`, some dissection. -/
theorem thm_realize12_iff (m : ℕ) (hm : 1 ≤ m) :
    (∃ N : ℕ, ∃ D : CongruentDissection N,
        HasSides D.target (8 * m) (8 * m) (11 * m) ∧ HasSides D.model 2 3 4) ↔ m ≠ 1 := by
  constructor
  · rintro ⟨N, D, h1, h2⟩ rfl
    exact (thm_realize12 1 le_rfl).2 rfl N D ⟨h1, h2⟩
  · intro h
    obtain ⟨D, hD⟩ := (thm_realize12 m hm).1 h
    exact ⟨_, D, hD⟩

/-! ## `cor:elevenm` -/

/-- The set `S` of `cor:elevenm`, up to congruence: `m ∈ S` iff the triangle `(8m,8m,11m)` is cut
into `11 m²` copies of `(2,3,4)`. -/
def InS (m : ℕ) : Prop :=
  ∃ D : CongruentDissection (11 * (m * m)),
    HasSides D.target (8 * m) (8 * m) (11 * m) ∧ HasSides D.model 2 3 4

/-- **`cor:elevenm` (erdos-634.tex:1436), as written.**  (i) `1 ∉ S` (stronger: no `N` at all);
(ii) `2 ∈ S`, `3 ∈ S`; (iii) `S ⊇ 2ℤ≥1 ∪ 3ℤ≥1`, so `N = 11 m²` is a tile count for every `m`
divisible by `2` or `3`; (iv) primitivity of the `44`- and `99`-tilings: no proper divisor of
`2` or `3` lies in `S` (the ladder would need `1 ∈ S`). -/
theorem cor_elevenm :
    (¬ InS 1) ∧ InS 2 ∧ InS 3 ∧
    (∀ m : ℕ, 1 ≤ m → (2 ∣ m ∨ 3 ∣ m) → InS m) ∧
    (∀ m : ℕ, 1 ≤ m → (2 ∣ m ∨ 3 ∣ m) → Nonempty (CongruentDissection (11 * (m * m)))) ∧
    (∀ m' : ℕ, m' ∣ 2 → InS m' → m' = 2) ∧ (∀ m' : ℕ, m' ∣ 3 → InS m' → m' = 3) := by
  have h1 : ¬ InS 1 := by
    rintro ⟨D, h, h'⟩
    exact thm_basebeta_e1 D (by simpa using h) h'
  have hge : ∀ m : ℕ, 1 ≤ m → (2 ∣ m ∨ 3 ∣ m) → 2 ≤ m := by
    intro m hm h
    rcases h with ⟨k, rfl⟩ | ⟨k, rfl⟩ <;> omega
  have hS : ∀ m : ℕ, 1 ≤ m → (2 ∣ m ∨ 3 ∣ m) → InS m :=
    fun m hm h => realize12_existence m (hge m hm h)
  refine ⟨h1, hS 2 (by norm_num) (Or.inl dvd_rfl), hS 3 (by norm_num) (Or.inr dvd_rfl), hS,
    fun m hm h => (hS m hm h).elim fun D _ => ⟨D⟩, ?_, ?_⟩
  · intro m' hd hm'
    have := Nat.le_of_dvd (by norm_num) hd
    interval_cases m'
    · exact absurd (Nat.eq_zero_of_zero_dvd hd) (by norm_num)
    · exact absurd hm' h1
    · rfl
  · intro m' hd hm'
    have := Nat.le_of_dvd (by norm_num) hd
    interval_cases m'
    · exact absurd (Nat.eq_zero_of_zero_dvd hd) (by norm_num)
    · exact absurd hm' h1
    · omega
    · rfl

/-- The listed values `44, 99, 176, 396, 704, 891, 1100` are tile counts. -/
theorem listed_tile_counts :
    Nonempty (CongruentDissection 44) ∧ Nonempty (CongruentDissection 99) ∧
    Nonempty (CongruentDissection 176) ∧ Nonempty (CongruentDissection 396) ∧
    Nonempty (CongruentDissection 704) ∧ Nonempty (CongruentDissection 891) ∧
    Nonempty (CongruentDissection 1100) := by
  have h := cor_elevenm.2.2.2.2.1
  exact ⟨h 2 (by norm_num) (by norm_num), h 3 (by norm_num) (by norm_num),
    h 4 (by norm_num) (by norm_num), h 6 (by norm_num) (by norm_num),
    h 8 (by norm_num) (by norm_num), h 9 (by norm_num) (by norm_num),
    h 10 (by norm_num) (by norm_num)⟩

/-- NOTE (stale text in the paper): `thm:realize12` gives `m ∈ S` for EVERY `m ≥ 2`, including
`gcd(m,6) = 1` (e.g. `m = 5`, `N = 275`), which `cor:elevenm` calls "undetermined". -/
theorem InS_all (m : ℕ) (hm : 2 ≤ m) : InS m := realize12_existence m hm

end Erdos634.Draft.FDBBaseBetaE1

#print axioms Erdos634.Draft.FDBBaseBetaE1.thm_basebeta_e1
#print axioms Erdos634.Draft.FDBBaseBetaE1.hasSides_witnesses
#print axioms Erdos634.Draft.FDBBaseBetaE1.thm_basebeta_e1_N11
#print axioms Erdos634.Draft.FDBBaseBetaE1.realize12_existence
#print axioms Erdos634.Draft.FDBBaseBetaE1.thm_realize12
#print axioms Erdos634.Draft.FDBBaseBetaE1.thm_realize12_iff
#print axioms Erdos634.Draft.FDBBaseBetaE1.cor_elevenm
#print axioms Erdos634.Draft.FDBBaseBetaE1.listed_tile_counts
#print axioms Erdos634.Draft.FDBBaseBetaE1.InS_all

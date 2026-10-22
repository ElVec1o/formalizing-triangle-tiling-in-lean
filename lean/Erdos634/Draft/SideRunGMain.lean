/-
Draft/SideRunGMain.lean -- written 14 October 2026.  UNAUDITED.  In `AllThreshold`.  Module 10 of ten.

**The side theorem and its corollary for every member**, for an arbitrary `CongruentDissection` (the target and the model given
by their side lengths, as in `SideRunMain`), together with the witness for `e ≥ 2` and the checks at `e = 1`.

PAPER STATEMENTS (`paper/erdos-634.tex`, Theorem `thm:siderunall`, Corollary `cor:ebelow`).
* `thm:siderunall`: `1 ≤ e < f` coprime, `(a, b, c) = (ef, f² − e², f²)`; a triangle `Δ` with a side `s` whose two corners have the
  angles `β, β` or `α + β, β`, cut into congruent triangles `(a, b, c)`; then `s` carries `f` consecutive tiles of type `C_1` or `f`
  of type `C_2` (tiles that lay their side `c` on `s` and show `α` at the same end), and `|s| ≥ f³`.
* `cor:ebelow`: arithmetic of the counts on a segment of length `M e (2f² − e²)` or `M e (3f² − e²)`; (a) `M e < f`: `W_M(e, f)` cannot
  be cut; (b) `2 M e < f`: `T_M(e, f)` cannot be cut.

CONTENTS.
1. `modelAngles_of_sidesG`, `modelDataG_of_sides`, `exists_iso_of_dist3`, `setup_of_sidesG_pinned`, `setup_of_sidesG`: the NORMAL FORM
   for every member (the analogue of `SideRunMain.setup_of_sides`): a congruent dissection `D₀` whose target has the sides
   `(t a, dq, L)` and whose model has the sides `(ef, f² − e², f²)` is moved by an isometry `g` (with the model relabelled so that
   side `j` is opposite vertex `j`) to a `SetupG` on the triangle `Q = (0, 0)`, `B = (L, 0)`, `A = (L − t uuG, t hhG)`; the tiles of
   `D` are the `g`-images of those of `D₀`, vertex for vertex, and `g` sends two named vertices of the target of `D₀` to `Q` and `B`
   (`_pinned`: with the vertex order `τ` given; the plain version takes the target as `HasSides`, i.e. in some vertex order).
2. The two families of the paper at a REAL scale `s > 0` (so that every size of `Δ` is covered): `T_s(e, f)` (isosceles, base
   `s e (3f² − e²)`, legs `s f³`; corners `β, β`) and `W_s(e, f)` (sides `s f (f² − e²)`, `s e (2f² − e²)`, `s f³`; corners `α + β`,
   `β`): `eq_T`, `eq_W1`, `eq_W2`, `dq_TG`, `dq_WG`, `cornersG_T`, `cornersG_W`, `setup_TG`, `setup_WG` (+ `_pinned`; the analogues of
   `corners_T`, `corners_W`, `setup_T`, `setup_W`).
3. `LaysBaseOn`, `siderunall_pullback`: the statement of the run for the ORIGINAL dissection `D₀` (no isometry in the statement): the
   tile `i` has two vertices on the segment `[P, B]` at the distances `x` and `x + len` from `P` and its third vertex at the distances
   of the type.
4. **`thm_siderunall_T`, `thm_siderunall_W`** (+ `_pinned`): THE PAPER THEOREM `thm:siderunall` for `D₀`, the triangle given by its side
   lengths.  The same theorem with the triangle given by its CORNER ANGLES is in `Draft/SideRunGAngles.lean`.
5. **`cor_ebelow_arith_QB`, `cor_ebelow_arith_base`, `ebelow_a`, `ebelow_b`, `not_wTilable_ebelow`, `not_betaTilable_ebelow`**: THE PAPER
   COROLLARY `cor:ebelow`, for an arbitrary `CongruentDissection` and for the project predicates `WTilable e f M`, `BetaTilable e f M`.
6. The witness: `setupG_witness_member` (every coprime member, in particular `e ≥ 2`), `setupG_witness_e2` (the member `(2, 3)`),
   `siderunall_seed` (the run in the seed tiling of `W_f(e, f)`).  Where it stands: for `M = f` the triangle `W_M(e, f)` HAS a tiling
   (the seed), and there `M e = f e ≥ f`, so the hypothesis `M e < f` of `ebelow_a` fails; hence `ebelow_a` cannot be extended to
   `M = f`.  For `e = 1` this is sharp (`W_M(1, f)` is tiled exactly for `M ≥ f`).  For `e ≥ 2` the exact threshold between
   `M e < f` and `M = f` is not decided by this file.
7. Checks at `e = 1`: `no_dissection_T_of_G`, `no_dissection_W_of_G` re-derive `SideRunMain.no_dissection_T`, `no_dissection_W` from
   `ebelow_b`, `ebelow_a`.

WHAT RESTS ON WHAT.  `SetupG.side_theorem_paperG`, `SetupG.no_tiling_QB`, `SetupG.no_tiling_base` (`SideRunGRules`), the normal form
(`E1NormalForm.normalFormC`, `FDBBaseBetaE1.congruent_of_hasSides`), `angleData_model`, and `Draft.CollarG.wTilable_seed` for the
witness.  Standard axioms only; no certificate module (`Refl.*`) is in the import closure.

No sorry, no native_decide.
-/
import Erdos634.Draft.SideRunGRules
import Erdos634.Draft.SideRunMain
import Erdos634.Draft.CollarG
import Erdos634.Draft.UniformThreshold

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.SideRunG

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.TilePlacement Erdos634.Draft.FDBBaseBetaE1 Erdos634.Draft.W2E1 Erdos634.Draft.SideRun Set

variable {N : ℕ}

/-! ## 1. The normal form for every member -/

/-- The cosine rule, read backwards: an angle in `[0, π]` with the right cosine is the corner. -/
theorem cornerAngle_eq_of_cosG {p q r : Plane} {a b d θ : ℝ} (ha : dist p q = a)
    (hb : dist r q = b) (hd : dist p r = d) (ha0 : 0 < a) (hb0 : 0 < b) (hθ0 : 0 ≤ θ)
    (hθπ : θ ≤ Real.pi) (hcos : Real.cos θ = (a ^ 2 + b ^ 2 - d ^ 2) / (2 * a * b)) :
    cornerAngle p q r = θ := by
  have hlaw :=
    EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle p q r
  rw [ha, hb, hd] at hlaw
  have hc : Real.cos (cornerAngle p q r) = Real.cos θ := by
    rw [hcos]; unfold cornerAngle; field_simp; linarith
  exact Real.injOn_cos ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
    ⟨hθ0, hθπ⟩ hc

/-- **The model angles from the model sides, on the triangle itself.**  A triangle `R` with sides `(ef, f² − e², f²)` (side `j`
opposite vertex `j`) has the corner angles `modelAlpha e f`, `modelBeta e f`, `2 α + β`. -/
theorem modelAngles_of_sidesG (R : Erdos634.Geometry.Tri) {e f : ℕ} (he : 1 ≤ e) (hef : e < f)
    (hs0 : sideOpp R 0 = (e : ℝ) * f) (hs1 : sideOpp R 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (hs2 : sideOpp R 2 = (f : ℝ) ^ 2) :
    cornerAngle (R.pts 1) (R.pts 0) (R.pts 2) = modelAlpha (e : ℝ) (f : ℝ) ∧
    cornerAngle (R.pts 2) (R.pts 1) (R.pts 0) = modelBeta (e : ℝ) (f : ℝ) ∧
    cornerAngle (R.pts 0) (R.pts 2) (R.pts 1) =
      2 * modelAlpha (e : ℝ) (f : ℝ) + modelBeta (e : ℝ) (f : ℝ) := by
  have heR : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hefR : (e : ℝ) < f := by exact_mod_cast hef
  have he0 : (0 : ℝ) < e := by linarith
  have hf0 : (0 : ℝ) < f := by linarith
  have hb0 : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have d12 : dist (R.pts 1) (R.pts 2) = (e : ℝ) * f := by rw [← hs0]; rfl
  have d20 : dist (R.pts 2) (R.pts 0) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by rw [← hs1]; rfl
  have d01 : dist (R.pts 0) (R.pts 1) = (f : ℝ) ^ 2 := by rw [← hs2]; rfl
  obtain ⟨hβ0, hβ2⟩ := modelBeta_mem he0 hefR
  have hrel := modelAngle_rel (e : ℝ) f
  have hα0 : 0 < modelAlpha (e : ℝ) f := by unfold modelAlpha; linarith
  have hαπ : modelAlpha (e : ℝ) f ≤ Real.pi := by unfold modelAlpha; linarith [Real.pi_pos]
  have hα' : cornerAngle (R.pts 1) (R.pts 0) (R.pts 2) = modelAlpha (e : ℝ) f := by
    have h1 : dist (R.pts 1) (R.pts 0) = (f : ℝ) ^ 2 := by rw [dist_comm]; exact d01
    refine cornerAngle_eq_of_cosG (a := (f : ℝ) ^ 2) (b := (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
      (d := (e : ℝ) * f) h1 d20 d12 (by positivity) hb0 hα0.le hαπ ?_
    rw [cos_modelAlpha he0 hefR]
    field_simp
    ring
  have hβ' : cornerAngle (R.pts 2) (R.pts 1) (R.pts 0) = modelBeta (e : ℝ) f := by
    have h1 : dist (R.pts 2) (R.pts 1) = (e : ℝ) * f := by rw [dist_comm]; exact d12
    refine cornerAngle_eq_of_cosG (a := (e : ℝ) * f) (b := (f : ℝ) ^ 2)
      (d := (f : ℝ) ^ 2 - (e : ℝ) ^ 2) h1 d01 d20 (by positivity) (by positivity)
      hβ0.le (by linarith [Real.pi_pos]) ?_
    obtain ⟨hc0, hc1⟩ := cosBeta_mem he0 hefR
    unfold modelBeta
    rw [Real.cos_arccos (by linarith) hc1.le]
    unfold baseLen Nq
    field_simp
    ring
  have hγ' : cornerAngle (R.pts 0) (R.pts 2) (R.pts 1) = 2 * modelAlpha (e : ℝ) f + modelBeta (e : ℝ) f := by
    have hsum := Erdos634.Geometry.cornerAngle_sum R
    rw [hα', hβ'] at hsum
    linarith
  exact ⟨hα', hβ', hγ'⟩

/-- **`ModelDataG` from the model sides** -/
theorem modelDataG_of_sides (D : CongruentDissection N) {e f : ℕ} (he : 1 ≤ e) (hef : e < f)
    (hs0 : sideOpp D.model 0 = (e : ℝ) * f) (hs1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (hs2 : sideOpp D.model 2 = (f : ℝ) ^ 2) :
    ModelDataG D (e : ℝ) (f : ℝ) (modelAlpha (e : ℝ) (f : ℝ)) (modelBeta (e : ℝ) (f : ℝ))
      (2 * modelAlpha (e : ℝ) (f : ℝ) + modelBeta (e : ℝ) (f : ℝ)) := by
  obtain ⟨h1, h2, h3⟩ := modelAngles_of_sidesG D.model he hef hs0 hs1 hs2
  exact ⟨hs0, hs1, hs2, h1, h2, h3⟩

/-- the sides of a triangle with `HasSides`, in the labelling `sideOpp`: some relabelling of the vertices makes side `j` the one
opposite vertex `j` -/
theorem sideOpp_relabel_of_hasSides {M : Erdos634.Geometry.Tri} {a b c : ℝ} (h : HasSides M a b c) :
    ∃ σ : Equiv.Perm (Fin 3), sideOpp (M.relabel σ) 0 = a ∧ sideOpp (M.relabel σ) 1 = b ∧
      sideOpp (M.relabel σ) 2 = c := by
  obtain ⟨τ, m0, m1, m2⟩ := h
  refine ⟨τ, ?_, ?_, ?_⟩
  · show dist ((M.relabel τ).pts 1) ((M.relabel τ).pts 2) = a
    rw [Tri.relabel_pts, Tri.relabel_pts]; exact m0
  · show dist ((M.relabel τ).pts 2) ((M.relabel τ).pts 0) = b
    rw [Tri.relabel_pts, Tri.relabel_pts]; exact m1
  · show dist ((M.relabel τ).pts 0) ((M.relabel τ).pts 1) = c
    rw [Tri.relabel_pts, Tri.relabel_pts]; exact m2

/-- cyclic rotation of the sides of `HasSides` -/
theorem hasSides_rotG {T : Erdos634.Geometry.Tri} {a b c : ℝ} (h : HasSides T a b c) : HasSides T b c a := by
  obtain ⟨τ, h1, h2, h3⟩ := h
  have e0 : ((finRotate 3).trans τ) 0 = τ 1 := by rw [Equiv.trans_apply]; rfl
  have e1 : ((finRotate 3).trans τ) 1 = τ 2 := by rw [Equiv.trans_apply]; rfl
  have e2 : ((finRotate 3).trans τ) 2 = τ 0 := by rw [Equiv.trans_apply]; rfl
  exact ⟨(finRotate 3).trans τ, by rw [e1, e2]; exact h2, by rw [e2, e0]; exact h3, by rw [e0, e1]; exact h1⟩

open Erdos634.SssCongruent in
/-- **SSS with the labelling kept**: two triangles whose corresponding sides are equal are carried one onto the other, vertex for
vertex, by an isometry of the plane (`SssCongruent.congruent_of_dist_three` hides the relabelling in `Tri.Congruent`). -/
theorem exists_iso_of_dist3 {T U : Erdos634.Geometry.Tri}
    (h01 : dist (T.pts 0) (T.pts 1) = dist (U.pts 0) (U.pts 1))
    (h12 : dist (T.pts 1) (T.pts 2) = dist (U.pts 1) (U.pts 2))
    (h20 : dist (T.pts 2) (T.pts 0) = dist (U.pts 2) (U.pts 0)) :
    ∃ g : Plane ≃ᵢ Plane, ∀ k, g (T.pts k) = U.pts k := by
  have htri : ∀ y : Fin 3, y = 0 ∨ y = 1 ∨ y = 2 := by decide
  have hd : ∀ i j, dist (T.pts i) (T.pts j) = dist (U.pts i) (U.pts j) := by
    intro i j
    rcases htri i with rfl | rfl | rfl <;> rcases htri j with rfl | rfl | rfl <;>
      simp_all [dist_comm]
  refine ⟨sssIso hd, ?_⟩
  intro k
  rcases htri k with rfl | rfl | rfl
  · rw [sssIso_apply]
    have h0 : T.pts 0 + -T.pts 0 = (0 : Plane) := by abel
    rw [h0, map_zero, zero_add]
  · rw [sssIso_apply]
    have h1 : T.pts 1 + -T.pts 0 = ev T 0 := by simp [ev]; abel
    rw [h1, evMap_basis]
    show U.pts 1 - U.pts 0 + U.pts 0 = U.pts 1
    abel
  · rw [sssIso_apply]
    have h2 : T.pts 2 + -T.pts 0 = ev T 1 := by simp [ev]; abel
    rw [h2, evMap_basis]
    show U.pts 2 - U.pts 0 + U.pts 0 = U.pts 2
    abel

/-- **THE NORMAL FORM, every member, with the vertices named** (the analogue of `SideRunMain.setup_of_sides`).  A congruent
dissection `D₀` whose target has `dist (τ 1, τ 2) = t · ef`, `dist (τ 2, τ 0) = dq`, `dist (τ 0, τ 1) = L` (the sides of the triangle
`Q = (0, 0)`, `B = (L, 0)`, `A = (L − t uuG, t hhG)`; the vertices `τ 0`, `τ 1` are `Q`, `B`) and whose model has the sides `ef`,
`f² − e²`, `f²` gives, after an isometry `g` (the tiles of `D` are the `g`-images of those of `D₀`, vertex for vertex), a `SetupG`
on that triangle, with `g (τ 0) = Q`, `g (τ 1) = B`. -/
theorem setup_of_sidesG_pinned (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) {L t dq : ℝ}
    (hL : 0 < L) (ht : 0 < t)
    (hdq : dist (mkPt (L - t * uuG (e : ℝ) (f : ℝ)) (t * hhG (e : ℝ) (f : ℝ))) (mkPt 0 0) = dq)
    (D₀ : CongruentDissection N) (τ : Equiv.Perm (Fin 3))
    (h1 : dist (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) = t * ((e : ℝ) * f))
    (h2 : dist (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) = dq)
    (h3 : dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) = L)
    (hMod : HasSides D₀.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)) :
    ∃ (D : CongruentDissection N) (g : Plane ≃ᵢ Plane),
      (∀ i m, (D.tile i).pts m = g ((D₀.tile i).pts m)) ∧
      g (D₀.target.pts (τ 0)) = mkPt 0 0 ∧ g (D₀.target.pts (τ 1)) = mkPt L 0 ∧
      SetupG D e f (modelAlpha (e : ℝ) (f : ℝ)) (modelBeta (e : ℝ) (f : ℝ))
        (2 * modelAlpha (e : ℝ) (f : ℝ) + modelBeta (e : ℝ) (f : ℝ)) L
        (L - t * uuG (e : ℝ) (f : ℝ)) (t * hhG (e : ℝ) (f : ℝ)) := by
  have he0 : (0 : ℝ) < e := Nat.cast_pos.mpr (by omega)
  have hefR : (e : ℝ) < f := by exact_mod_cast hef
  have hf0 : (0 : ℝ) < f := he0.trans hefR
  have hay : 0 < t * hhG (e : ℝ) (f : ℝ) := mul_pos ht (hhG_pos he0 hefR)
  have hsq := hhG_sq he0 hefR
  have h12 : dist ((Tg L (L - t * uuG (e : ℝ) (f : ℝ)) (t * hhG (e : ℝ) (f : ℝ)) hL hay).pts 1)
      ((Tg L (L - t * uuG (e : ℝ) (f : ℝ)) (t * hhG (e : ℝ) (f : ℝ)) hL hay).pts 2)
      = t * ((e : ℝ) * f) := by
    show dist (mkPt L 0) (mkPt (L - t * uuG (e : ℝ) (f : ℝ)) (t * hhG (e : ℝ) (f : ℝ)))
      = t * ((e : ℝ) * f)
    refine dist_eq_of_sq_eq ?_ dist_nonneg (by positivity)
    rw [dist_sq_mkPt]
    linear_combination t ^ 2 * hsq
  have h20 : dist ((Tg L (L - t * uuG (e : ℝ) (f : ℝ)) (t * hhG (e : ℝ) (f : ℝ)) hL hay).pts 2)
      ((Tg L (L - t * uuG (e : ℝ) (f : ℝ)) (t * hhG (e : ℝ) (f : ℝ)) hL hay).pts 0) = dq := hdq
  have h01 : dist ((Tg L (L - t * uuG (e : ℝ) (f : ℝ)) (t * hhG (e : ℝ) (f : ℝ)) hL hay).pts 0)
      ((Tg L (L - t * uuG (e : ℝ) (f : ℝ)) (t * hhG (e : ℝ) (f : ℝ)) hL hay).pts 1) = L := by
    show dist (mkPt 0 0) (mkPt L 0) = L
    have := dist_mkPt_base 0 L hL.le
    rwa [zero_add] at this
  obtain ⟨g, hg0⟩ := exists_iso_of_dist3 (T := D₀.target.relabel τ)
    (U := Tg L (L - t * uuG (e : ℝ) (f : ℝ)) (t * hhG (e : ℝ) (f : ℝ)) hL hay)
    (by rw [Tri.relabel_pts, Tri.relabel_pts]; exact h3.trans h01.symm)
    (by rw [Tri.relabel_pts, Tri.relabel_pts]; exact h1.trans h12.symm)
    (by rw [Tri.relabel_pts, Tri.relabel_pts]; exact h2.trans h20.symm)
  have hg : ∀ k, g (D₀.target.pts k)
      = (Tg L (L - t * uuG (e : ℝ) (f : ℝ)) (t * hhG (e : ℝ) (f : ℝ)) hL hay).pts (τ.symm k) := by
    intro k
    have := hg0 (τ.symm k)
    rwa [Tri.relabel_pts, Equiv.apply_symm_apply] at this
  obtain ⟨σm, m0, m1, m2⟩ := sideOpp_relabel_of_hasSides hMod
  have hmod : D₀.model.Congruent (D₀.model.relabel σm) := Tri.congruent_relabel D₀.model σm
  have hMD := modelDataG_of_sides (Erdos634.E1NormalForm.normalFormC D₀ g τ.symm hmod) he hef m0 m1 m2
  exact ⟨Erdos634.E1NormalForm.normalFormC D₀ g τ.symm hmod, g, fun _ _ => rfl, hg0 0, hg0 1,
    ⟨he, hef, hco, hMD, angleData_model e f he hef, hL, hay,
      fun _ _ => Erdos634.E1NormalForm.normalFormC_target D₀ hg hmod⟩⟩

/-- **THE NORMAL FORM, every member** (the analogue of `SideRunMain.setup_of_sides`): the target given by its three side lengths
(in some order of its vertices). -/
theorem setup_of_sidesG (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) {L t dq : ℝ}
    (hL : 0 < L) (ht : 0 < t)
    (hdq : dist (mkPt (L - t * uuG (e : ℝ) (f : ℝ)) (t * hhG (e : ℝ) (f : ℝ))) (mkPt 0 0) = dq)
    (D₀ : CongruentDissection N) (hT : HasSides D₀.target (t * ((e : ℝ) * f)) dq L)
    (hMod : HasSides D₀.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)) :
    ∃ (D : CongruentDissection N) (g : Plane ≃ᵢ Plane) (k₀ k₁ : Fin 3), k₀ ≠ k₁ ∧
      (∀ i m, (D.tile i).pts m = g ((D₀.tile i).pts m)) ∧
      g (D₀.target.pts k₀) = mkPt 0 0 ∧ g (D₀.target.pts k₁) = mkPt L 0 ∧
      SetupG D e f (modelAlpha (e : ℝ) (f : ℝ)) (modelBeta (e : ℝ) (f : ℝ))
        (2 * modelAlpha (e : ℝ) (f : ℝ) + modelBeta (e : ℝ) (f : ℝ)) L
        (L - t * uuG (e : ℝ) (f : ℝ)) (t * hhG (e : ℝ) (f : ℝ)) := by
  obtain ⟨τ, h1, h2, h3⟩ := hT
  obtain ⟨D, g, hD, hP, hB, S⟩ := setup_of_sidesG_pinned e f he hef hco hL ht hdq D₀ τ h1 h2 h3 hMod
  exact ⟨D, g, τ 0, τ 1, τ.injective.ne (by decide), hD, hP, hB, S⟩

/-! ## 2. The two families at a real scale -/

section scale

variable {e f s t : ℝ}

/-- `L = 2 t u` for the triangle `T_s(e, f)` (`t e = s f²`) -/
theorem eq_T (he0 : 0 < e) (hef : e < f) (hte : t * e = s * f ^ 2) :
    s * (e * (3 * f ^ 2 - e ^ 2)) - t * uuG e f = t * uuG e f := by
  have hf0 : 0 < f := he0.trans hef
  have hu := uuG_spec he0 hef
  have key : f ^ 2 * (s * (e * (3 * f ^ 2 - e ^ 2)) - t * uuG e f - t * uuG e f) = 0 := by
    linear_combination (-(e * (3 * f ^ 2 - e ^ 2))) * hte + (-t) * hu
  have hf2 : f ^ 2 ≠ 0 := by positivity
  have := (mul_eq_zero.mp key).resolve_left hf2
  linarith

/-- the corner `Q` of `W_s(e, f)`: `L − t u = t' e` with `t' = s (f² − e²) / 2` -/
theorem eq_W1 (he0 : 0 < e) (hef : e < f) (hte : t * e = s * f ^ 2) :
    s * (e * (2 * f ^ 2 - e ^ 2)) - t * uuG e f = (s * (f ^ 2 - e ^ 2) / 2) * e := by
  have hf0 : 0 < f := he0.trans hef
  have hu := uuG_spec he0 hef
  have key : f ^ 2 * (s * (e * (2 * f ^ 2 - e ^ 2)) - t * uuG e f - (s * (f ^ 2 - e ^ 2) / 2) * e) = 0 := by
    linear_combination (-(t / 2)) * hu + (-(e * (3 * f ^ 2 - e ^ 2) / 2)) * hte
  have hf2 : f ^ 2 ≠ 0 := by positivity
  have := (mul_eq_zero.mp key).resolve_left hf2
  linarith

/-- the corner `Q` of `W_s(e, f)`: `t h = t' r` -/
theorem eq_W2 (he0 : 0 < e) (hef : e < f) (hte : t * e = s * f ^ 2) :
    t * hhG e f = (s * (f ^ 2 - e ^ 2) / 2) * rtG e f := by
  have hf0 : 0 < f := he0.trans hef
  have hh' := hhG_spec he0 hef
  have key : f ^ 2 * (t * hhG e f - (s * (f ^ 2 - e ^ 2) / 2) * rtG e f) = 0 := by
    linear_combination (t / 2) * hh' + ((f ^ 2 - e ^ 2) * rtG e f / 2) * hte
  have hf2 : f ^ 2 ≠ 0 := by positivity
  have := (mul_eq_zero.mp key).resolve_left hf2
  linarith

/-- the third side of `T_s(e, f)`: `|QA| = t · ef` -/
theorem dq_TG {L : ℝ} (he0 : 0 < e) (hef : e < f) (ht : 0 < t) (e1 : L - t * uuG e f = t * uuG e f) :
    dist (mkPt (L - t * uuG e f) (t * hhG e f)) (mkPt 0 0) = t * (e * f) := by
  have hsq := hhG_sq he0 hef
  have hf0 := he0.trans hef
  refine dist_eq_of_sq_eq ?_ dist_nonneg (by positivity)
  rw [dist_sq_mkPt, e1]
  linear_combination t ^ 2 * hsq

/-- the third side of `W_s(e, f)`: `|QA| = t' · 2f` -/
theorem dq_WG {L t' : ℝ} (he0 : 0 < e) (hef : e < f) (ht' : 0 < t') (e1 : L - t * uuG e f = t' * e)
    (e2 : t * hhG e f = t' * rtG e f) :
    dist (mkPt (L - t * uuG e f) (t * hhG e f)) (mkPt 0 0) = t' * (2 * f) := by
  have hr := rtG_sq he0 hef
  have hf0 := he0.trans hef
  refine dist_eq_of_sq_eq ?_ dist_nonneg (by positivity)
  rw [dist_sq_mkPt, e1, e2]
  linear_combination t' ^ 2 * hr

end scale

/-- the corners of `T_s(e, f)`: `β` and `β` -/
theorem cornersG_T {e f : ℕ} (he0 : (0 : ℝ) < e) (hefR : (e : ℝ) < f) {s t : ℝ} (ht : 0 < t)
    (hte : t * (e : ℝ) = s * (f : ℝ) ^ 2) :
    CornersG e f (s * ((e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
      (s * ((e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)) - t * uuG (e : ℝ) (f : ℝ))
      (t * hhG (e : ℝ) (f : ℝ)) :=
  ⟨⟨t, ht, rfl, rfl⟩, Or.inl ⟨t, ht, eq_T he0 hefR hte, rfl⟩⟩

/-- the corners of `W_s(e, f)`: `α + β` at `Q` and `β` at `B` -/
theorem cornersG_W {e f : ℕ} (he0 : (0 : ℝ) < e) (hefR : (e : ℝ) < f) {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hte : t * (e : ℝ) = s * (f : ℝ) ^ 2) :
    CornersG e f (s * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
      (s * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)) - t * uuG (e : ℝ) (f : ℝ))
      (t * hhG (e : ℝ) (f : ℝ)) := by
  have hb := b_posG he0 hefR
  have ht' : 0 < s * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / 2 := by have := mul_pos hs hb; linarith
  exact ⟨⟨t, ht, rfl, rfl⟩, Or.inr ⟨s * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / 2, ht', eq_W1 he0 hefR hte,
    eq_W2 he0 hefR hte⟩⟩

/-- **The normal form of a dissection of `T_s(e, f)`, vertices named** (`τ 0` is `Q`, `τ 1` is `B`, `τ 2` is the apex `A`) -/
theorem setup_TG_pinned (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) {s : ℝ} (hs : 0 < s)
    (D₀ : CongruentDissection N) (τ : Equiv.Perm (Fin 3))
    (h1 : dist (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) = s * (f : ℝ) ^ 3)
    (h2 : dist (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) = s * (f : ℝ) ^ 3)
    (h3 : dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1))
      = s * ((e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
    (hMod : HasSides D₀.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)) :
    ∃ (D : CongruentDissection N) (g : Plane ≃ᵢ Plane) (ax ay : ℝ),
      (∀ i m, (D.tile i).pts m = g ((D₀.tile i).pts m)) ∧
      g (D₀.target.pts (τ 0)) = mkPt 0 0 ∧
      g (D₀.target.pts (τ 1)) = mkPt (s * ((e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))) 0 ∧
      SetupG D e f (modelAlpha (e : ℝ) (f : ℝ)) (modelBeta (e : ℝ) (f : ℝ))
        (2 * modelAlpha (e : ℝ) (f : ℝ) + modelBeta (e : ℝ) (f : ℝ))
        (s * ((e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))) ax ay ∧
      CornersG e f (s * ((e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))) ax ay := by
  have he0 : (0 : ℝ) < e := Nat.cast_pos.mpr (by omega)
  have hefR : (e : ℝ) < f := by exact_mod_cast hef
  have hf0 : (0 : ℝ) < f := he0.trans hefR
  have hb := b_posG he0 hefR
  have hK : (0 : ℝ) < 3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    have := sq_nonneg (f : ℝ); linarith
  have hL : 0 < s * ((e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)) := mul_pos hs (mul_pos he0 hK)
  obtain ⟨t, ht, hte⟩ : ∃ t : ℝ, 0 < t ∧ t * (e : ℝ) = s * (f : ℝ) ^ 2 :=
    ⟨s * (f : ℝ) ^ 2 / e, by positivity, div_mul_cancel₀ _ he0.ne'⟩
  have e1 := eq_T he0 hefR hte (s := s) (t := t)
  have hdq := dq_TG (L := s * ((e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))) he0 hefR ht e1
  have ha : s * (f : ℝ) ^ 3 = t * ((e : ℝ) * f) := by linear_combination (-(f : ℝ)) * hte
  obtain ⟨D, g, hD, hP, hB, S⟩ :=
    setup_of_sidesG_pinned e f he hef hco hL ht hdq D₀ τ (h1.trans ha) (h2.trans ha) h3 hMod
  exact ⟨D, g, _, _, hD, hP, hB, S, cornersG_T he0 hefR ht hte⟩

/-- **The normal form of a dissection of `T_s(e, f)`** (the analogue of `SideRunMain.setup_T`) -/
theorem setup_TG (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) {s : ℝ} (hs : 0 < s)
    (D₀ : CongruentDissection N)
    (hT : HasSides D₀.target (s * (f : ℝ) ^ 3) (s * (f : ℝ) ^ 3)
      (s * ((e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))))
    (hMod : HasSides D₀.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)) :
    ∃ (D : CongruentDissection N) (g : Plane ≃ᵢ Plane) (k₀ k₁ : Fin 3) (ax ay : ℝ), k₀ ≠ k₁ ∧
      (∀ i m, (D.tile i).pts m = g ((D₀.tile i).pts m)) ∧
      g (D₀.target.pts k₀) = mkPt 0 0 ∧
      g (D₀.target.pts k₁) = mkPt (s * ((e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))) 0 ∧
      SetupG D e f (modelAlpha (e : ℝ) (f : ℝ)) (modelBeta (e : ℝ) (f : ℝ))
        (2 * modelAlpha (e : ℝ) (f : ℝ) + modelBeta (e : ℝ) (f : ℝ))
        (s * ((e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))) ax ay ∧
      CornersG e f (s * ((e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))) ax ay := by
  obtain ⟨τ, h1, h2, h3⟩ := hT
  obtain ⟨D, g, ax, ay, hD, hP, hB, S, Co⟩ := setup_TG_pinned e f he hef hco hs D₀ τ h1 h2 h3 hMod
  exact ⟨D, g, τ 0, τ 1, ax, ay, τ.injective.ne (by decide), hD, hP, hB, S, Co⟩

/-- **The normal form of a dissection of `W_s(e, f)`, vertices named** (`τ 0` is `Q`, `τ 1` is `B`, `τ 2` is `A`) -/
theorem setup_WG_pinned (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) {s : ℝ} (hs : 0 < s)
    (D₀ : CongruentDissection N) (τ : Equiv.Perm (Fin 3))
    (h1 : dist (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) = s * (f : ℝ) ^ 3)
    (h2 : dist (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0))
      = s * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
    (h3 : dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1))
      = s * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
    (hMod : HasSides D₀.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)) :
    ∃ (D : CongruentDissection N) (g : Plane ≃ᵢ Plane) (ax ay : ℝ),
      (∀ i m, (D.tile i).pts m = g ((D₀.tile i).pts m)) ∧
      g (D₀.target.pts (τ 0)) = mkPt 0 0 ∧
      g (D₀.target.pts (τ 1)) = mkPt (s * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))) 0 ∧
      SetupG D e f (modelAlpha (e : ℝ) (f : ℝ)) (modelBeta (e : ℝ) (f : ℝ))
        (2 * modelAlpha (e : ℝ) (f : ℝ) + modelBeta (e : ℝ) (f : ℝ))
        (s * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))) ax ay ∧
      CornersG e f (s * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))) ax ay := by
  have he0 : (0 : ℝ) < e := Nat.cast_pos.mpr (by omega)
  have hefR : (e : ℝ) < f := by exact_mod_cast hef
  have hf0 : (0 : ℝ) < f := he0.trans hefR
  have hb := b_posG he0 hefR
  have hK : (0 : ℝ) < 2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    have := sq_nonneg (f : ℝ); linarith
  have hL : 0 < s * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)) := mul_pos hs (mul_pos he0 hK)
  obtain ⟨t, ht, hte⟩ : ∃ t : ℝ, 0 < t ∧ t * (e : ℝ) = s * (f : ℝ) ^ 2 :=
    ⟨s * (f : ℝ) ^ 2 / e, by positivity, div_mul_cancel₀ _ he0.ne'⟩
  have ht' : 0 < s * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / 2 := by have := mul_pos hs hb; linarith
  have hdq := dq_WG (L := s * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))) he0 hefR ht'
    (eq_W1 he0 hefR hte) (eq_W2 he0 hefR hte)
  have hdq' : dist (mkPt (s * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)) - t * uuG (e : ℝ) (f : ℝ))
      (t * hhG (e : ℝ) (f : ℝ))) (mkPt 0 0) = s * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) := by
    rw [hdq]; ring
  have ha : s * (f : ℝ) ^ 3 = t * ((e : ℝ) * f) := by linear_combination (-(f : ℝ)) * hte
  obtain ⟨D, g, hD, hP, hB, S⟩ :=
    setup_of_sidesG_pinned e f he hef hco hL ht hdq' D₀ τ (h1.trans ha) h2 h3 hMod
  exact ⟨D, g, _, _, hD, hP, hB, S, cornersG_W he0 hefR hs ht hte⟩

/-- **The normal form of a dissection of `W_s(e, f)`** (the analogue of `SideRunMain.setup_W`) -/
theorem setup_WG (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) {s : ℝ} (hs : 0 < s)
    (D₀ : CongruentDissection N)
    (hT : HasSides D₀.target (s * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
      (s * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))) (s * (f : ℝ) ^ 3))
    (hMod : HasSides D₀.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)) :
    ∃ (D : CongruentDissection N) (g : Plane ≃ᵢ Plane) (k₀ k₁ : Fin 3) (ax ay : ℝ), k₀ ≠ k₁ ∧
      (∀ i m, (D.tile i).pts m = g ((D₀.tile i).pts m)) ∧
      g (D₀.target.pts k₀) = mkPt 0 0 ∧
      g (D₀.target.pts k₁) = mkPt (s * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))) 0 ∧
      SetupG D e f (modelAlpha (e : ℝ) (f : ℝ)) (modelBeta (e : ℝ) (f : ℝ))
        (2 * modelAlpha (e : ℝ) (f : ℝ) + modelBeta (e : ℝ) (f : ℝ))
        (s * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))) ax ay ∧
      CornersG e f (s * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))) ax ay := by
  obtain ⟨τ, h1, h2, h3⟩ := hasSides_rotG (hasSides_rotG hT)
  obtain ⟨D, g, ax, ay, hD, hP, hB, S, Co⟩ := setup_WG_pinned e f he hef hco hs D₀ τ h1 h2 h3 hMod
  exact ⟨D, g, τ 0, τ 1, ax, ay, τ.injective.ne (by decide), hD, hP, hB, S, Co⟩

/-! ## 3. The run, for the original dissection -/

/-- **The tile `i` of `D₀` lays a base of the type `T` on the segment `[P, B]` at the distance `x` from `P`**: it has two vertices on
`[P, B]`, at the distances `x` and `x + len T` from `P`, and its third vertex is at the distances `sL T`, `sR T` from these two
(`C1`: it lays its side `c` on the segment and shows `α` at the end nearer to `P`; `C2`: at the end nearer to `B`). -/
def LaysBaseOn (D₀ : CongruentDissection N) (e f : ℝ) (P B : Plane) (i : Fin N) (T : Ty) (x : ℝ) : Prop :=
  ∃ k m j : Fin 3, k ≠ m ∧ k ≠ j ∧ m ≠ j ∧
    (D₀.tile i).pts k = AffineMap.lineMap P B (x / dist P B) ∧
    (D₀.tile i).pts m = AffineMap.lineMap P B ((x + T.lenG e f) / dist P B) ∧
    dist ((D₀.tile i).pts j) ((D₀.tile i).pts k) = T.sLG e f ∧
    dist ((D₀.tile i).pts j) ((D₀.tile i).pts m) = T.sRG e f

/-- a base tile of the normal form is a tile of `D₀` laid on the segment between the two vertices that `g` sends to `Q` and `B` -/
theorem laysOn_of_baseTile {D₀ D : CongruentDissection N} {g : Plane ≃ᵢ Plane} {P B : Plane} {L e f x : ℝ}
    {i : Fin N} {T : Ty} (hL : 0 < L) (hD : ∀ i m, (D.tile i).pts m = g ((D₀.tile i).pts m))
    (hP : g P = mkPt 0 0) (hB : g B = mkPt L 0) (h : BaseTileG D e f i T x) :
    LaysBaseOn D₀ e f P B i T x := by
  have hdist : dist P B = L := by
    rw [← g.dist_eq, hP, hB]
    have := dist_mkPt_base 0 L hL.le
    rwa [zero_add] at this
  have hL' : L ≠ 0 := hL.ne'
  have hpt : ∀ y : ℝ, ∀ p : Plane, g p = mkPt y 0 → p = AffineMap.lineMap P B (y / dist P B) := by
    intro y p hp
    apply g.injective
    rw [hp, Erdos634.E1NormalForm.iso_lineMap, hP, hB, hdist, Erdos634.RunPartition.CSlot.lineMap_mkPt]
    exact mkPt_congr (by field_simp; ring) (by ring)
  obtain ⟨k, m, j, hkm, hkj, hmj, hk, hm, hsL, hsR⟩ := h
  refine ⟨k, m, j, hkm, hkj, hmj, hpt x _ ?_, hpt (x + T.lenG e f) _ ?_, ?_, ?_⟩
  · rw [← hD]; exact hk
  · rw [← hD]; exact hm
  · rw [← hsL, hD, hD, g.dist_eq]
  · rw [← hsR, hD, hD, g.dist_eq]

/-- **THE RUN, for the original dissection**: from a `SetupG` with `CornersG` that is the normal form of `D₀`, the side `[P, B]` of
the target of `D₀` (`P`, `B` the vertices that `g` sends to `Q`, `B`) carries `f` consecutive tiles of `D₀` that lay a base `c` on it
and show `α` at the same end, and `f³ ≤ |PB|`. -/
theorem siderunall_pullback {e f : ℕ} {D₀ D : CongruentDissection N} {g : Plane ≃ᵢ Plane} {k₀ k₁ : Fin 3}
    {α β γ L ax ay : ℝ} (hL : 0 < L) (hD : ∀ i m, (D.tile i).pts m = g ((D₀.tile i).pts m))
    (hP : g (D₀.target.pts k₀) = mkPt 0 0) (hB : g (D₀.target.pts k₁) = mkPt L 0)
    (S : SetupG D e f α β γ L ax ay) (Co : CornersG e f L ax ay) :
    dist (D₀.target.pts k₀) (D₀.target.pts k₁) = L ∧
    ∃ (x₀ : ℝ) (t : ℕ → Fin N), 0 ≤ x₀ ∧ x₀ + (f : ℝ) * (f : ℝ) ^ 2 ≤ L ∧
      ((∀ j, j < f → LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts k₀) (D₀.target.pts k₁) (t j) Ty.C1
          (x₀ + j * (f : ℝ) ^ 2)) ∨
       (∀ j, j < f → LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts k₀) (D₀.target.pts k₁) (t j) Ty.C2
          (x₀ + j * (f : ℝ) ^ 2))) ∧
      (f : ℝ) ^ 3 ≤ L := by
  obtain ⟨x₀, t, h0, hend, hrun, h3⟩ := S.side_theorem_paperG Co
  refine ⟨?_, x₀, t, h0, hend, ?_, h3⟩
  · rw [← g.dist_eq, hP, hB]
    have := dist_mkPt_base 0 L hL.le
    rwa [zero_add] at this
  · rcases hrun with hr | hr
    · exact Or.inl (fun j hj => laysOn_of_baseTile hL hD hP hB (hr j hj))
    · exact Or.inr (fun j hj => laysOn_of_baseTile hL hD hP hB (hr j hj))

/-! ## 4. `thm:siderunall` for an arbitrary congruent dissection -/

/-- **THEOREM `thm:siderunall`, corners `β, β`, vertices named** (the isosceles triangle `T_s(e, f)`, base `s e (3f² − e²)` from the
vertex `τ 0` to the vertex `τ 1`, legs `s f³`, any real `s > 0`): in every congruent dissection of it into copies of
`(ef, f² − e², f²)` (any number of tiles, reflections allowed) the base carries `f` consecutive tiles that lay their side `c` on it
and show `α` at the same end of it, and the base has length at least `f³`. -/
theorem thm_siderunall_T_pinned (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) {s : ℝ}
    (hs : 0 < s) (D₀ : CongruentDissection N) (τ : Equiv.Perm (Fin 3))
    (h1 : dist (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) = s * (f : ℝ) ^ 3)
    (h2 : dist (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) = s * (f : ℝ) ^ 3)
    (h3 : dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1))
      = s * ((e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
    (hMod : HasSides D₀.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)) :
    ∃ (x₀ : ℝ) (t : ℕ → Fin N), 0 ≤ x₀ ∧
      x₀ + (f : ℝ) * (f : ℝ) ^ 2 ≤ s * ((e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)) ∧
      ((∀ j, j < f → LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (t j) Ty.C1
          (x₀ + j * (f : ℝ) ^ 2)) ∨
       (∀ j, j < f → LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (t j) Ty.C2
          (x₀ + j * (f : ℝ) ^ 2))) ∧
      (f : ℝ) ^ 3 ≤ s * ((e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)) := by
  obtain ⟨D, g, ax, ay, hD, hP, hB, S, Co⟩ := setup_TG_pinned e f he hef hco hs D₀ τ h1 h2 h3 hMod
  have he0 : (0 : ℝ) < e := Nat.cast_pos.mpr (by omega)
  have hefR : (e : ℝ) < f := by exact_mod_cast hef
  have hb := b_posG he0 hefR
  have hK : (0 : ℝ) < 3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    have := sq_nonneg (f : ℝ); linarith
  have hL : 0 < s * ((e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)) := mul_pos hs (mul_pos he0 hK)
  obtain ⟨-, x₀, t, h0, hend, hrun, h3'⟩ := siderunall_pullback hL hD hP hB S Co
  exact ⟨x₀, t, h0, hend, hrun, h3'⟩

/-- **THEOREM `thm:siderunall`, corners `α + β, β`, vertices named** (the triangle `W_s(e, f)` with sides `s f (f² − e²)`,
`s e (2f² − e²)`, `s f³`, any real `s > 0`; `QB`, of length `s e (2f² − e²)`, runs from the vertex `τ 0` to the vertex `τ 1`): the
side `QB` carries `f` consecutive tiles that lay their side `c` on it and show `α` at the same end of it, and has length at least
`f³`. -/
theorem thm_siderunall_W_pinned (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) {s : ℝ}
    (hs : 0 < s) (D₀ : CongruentDissection N) (τ : Equiv.Perm (Fin 3))
    (h1 : dist (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) = s * (f : ℝ) ^ 3)
    (h2 : dist (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0))
      = s * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
    (h3 : dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1))
      = s * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
    (hMod : HasSides D₀.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)) :
    ∃ (x₀ : ℝ) (t : ℕ → Fin N), 0 ≤ x₀ ∧
      x₀ + (f : ℝ) * (f : ℝ) ^ 2 ≤ s * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)) ∧
      ((∀ j, j < f → LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (t j) Ty.C1
          (x₀ + j * (f : ℝ) ^ 2)) ∨
       (∀ j, j < f → LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (t j) Ty.C2
          (x₀ + j * (f : ℝ) ^ 2))) ∧
      (f : ℝ) ^ 3 ≤ s * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)) := by
  obtain ⟨D, g, ax, ay, hD, hP, hB, S, Co⟩ := setup_WG_pinned e f he hef hco hs D₀ τ h1 h2 h3 hMod
  have he0 : (0 : ℝ) < e := Nat.cast_pos.mpr (by omega)
  have hefR : (e : ℝ) < f := by exact_mod_cast hef
  have hb := b_posG he0 hefR
  have hK : (0 : ℝ) < 2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    have := sq_nonneg (f : ℝ); linarith
  have hL : 0 < s * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)) := mul_pos hs (mul_pos he0 hK)
  obtain ⟨-, x₀, t, h0, hend, hrun, h3'⟩ := siderunall_pullback hL hD hP hB S Co
  exact ⟨x₀, t, h0, hend, hrun, h3'⟩

/-- **THEOREM `thm:siderunall`, corners `β, β`** (the isosceles triangle `T_s(e, f)`, base `s e (3f² − e²)`, legs `s f³`, any real
`s > 0`), the triangle given by its side lengths: in every congruent dissection of it into copies of `(ef, f² − e², f²)` (any number
of tiles, reflections allowed) the base carries `f` consecutive tiles that lay their side `c` on it and show `α` at the same end of
it, and the base has length at least `f³`. -/
theorem thm_siderunall_T (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) {s : ℝ} (hs : 0 < s)
    (D₀ : CongruentDissection N)
    (hT : HasSides D₀.target (s * (f : ℝ) ^ 3) (s * (f : ℝ) ^ 3)
      (s * ((e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))))
    (hMod : HasSides D₀.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)) :
    ∃ (k₀ k₁ : Fin 3) (x₀ : ℝ) (t : ℕ → Fin N), k₀ ≠ k₁ ∧
      dist (D₀.target.pts k₀) (D₀.target.pts k₁) = s * ((e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)) ∧
      0 ≤ x₀ ∧ x₀ + (f : ℝ) * (f : ℝ) ^ 2 ≤ s * ((e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)) ∧
      ((∀ j, j < f → LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts k₀) (D₀.target.pts k₁) (t j) Ty.C1
          (x₀ + j * (f : ℝ) ^ 2)) ∨
       (∀ j, j < f → LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts k₀) (D₀.target.pts k₁) (t j) Ty.C2
          (x₀ + j * (f : ℝ) ^ 2))) ∧
      (f : ℝ) ^ 3 ≤ s * ((e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)) := by
  obtain ⟨τ, h1, h2, h3⟩ := hT
  obtain ⟨x₀, t, h0, hend, hrun, h3'⟩ := thm_siderunall_T_pinned e f he hef hco hs D₀ τ h1 h2 h3 hMod
  exact ⟨τ 0, τ 1, x₀, t, τ.injective.ne (by decide), h3, h0, hend, hrun, h3'⟩

/-- **THEOREM `thm:siderunall`, corners `α + β, β`** (the triangle `W_s(e, f)` with sides `s f (f² − e²)`, `s e (2f² − e²)`,
`s f³`, any real `s > 0`), the triangle given by its side lengths: the side `QB` of length `s e (2f² − e²)` carries `f` consecutive
tiles that lay their side `c` on it and show `α` at the same end of it, and has length at least `f³`. -/
theorem thm_siderunall_W (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) {s : ℝ} (hs : 0 < s)
    (D₀ : CongruentDissection N)
    (hT : HasSides D₀.target (s * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
      (s * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))) (s * (f : ℝ) ^ 3))
    (hMod : HasSides D₀.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)) :
    ∃ (k₀ k₁ : Fin 3) (x₀ : ℝ) (t : ℕ → Fin N), k₀ ≠ k₁ ∧
      dist (D₀.target.pts k₀) (D₀.target.pts k₁) = s * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)) ∧
      0 ≤ x₀ ∧ x₀ + (f : ℝ) * (f : ℝ) ^ 2 ≤ s * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)) ∧
      ((∀ j, j < f → LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts k₀) (D₀.target.pts k₁) (t j) Ty.C1
          (x₀ + j * (f : ℝ) ^ 2)) ∨
       (∀ j, j < f → LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts k₀) (D₀.target.pts k₁) (t j) Ty.C2
          (x₀ + j * (f : ℝ) ^ 2))) ∧
      (f : ℝ) ^ 3 ≤ s * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)) := by
  obtain ⟨τ, h1, h2, h3⟩ := hasSides_rotG (hasSides_rotG hT)
  obtain ⟨x₀, t, h0, hend, hrun, h3'⟩ := thm_siderunall_W_pinned e f he hef hco hs D₀ τ h1 h2 h3 hMod
  exact ⟨τ 0, τ 1, x₀, t, τ.injective.ne (by decide), h3, h0, hend, hrun, h3'⟩

/-! ## 5. `cor:ebelow` -/

/-- **`cor:ebelow`, the counts on a segment of length `M e (2f² − e²)`**: if the segment is a union of `x`, `y`, `z` segments of
lengths `a`, `b`, `c`, then `y ≡ M e (mod f)`, and if `M e < f` then `M e ≤ y` and `z ≤ M e`. -/
theorem cor_ebelow_arith_QB {e f M x y z : ℕ} (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f)
    (h : (x : ℝ) * ((e : ℝ) * f) + y * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) + z * (f : ℝ) ^ 2
      = (M : ℝ) * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))) :
    y ≡ M * e [MOD f] ∧ (M * e < f → M * e ≤ y ∧ z ≤ M * e) :=
  SideRunGArith.C_QB he hef hco
    (rep_nat_len (x := x) (y := y) (z := z) (M := M) (κ := 2) hef (by norm_num) (by rw [h]; push_cast; ring))

/-- **`cor:ebelow`, the counts on a segment of length `M e (3f² − e²)`**: `y ≡ M e (mod f)`, and if `M e < f` then `M e ≤ y` and
`z ≤ 2 M e`. -/
theorem cor_ebelow_arith_base {e f M x y z : ℕ} (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f)
    (h : (x : ℝ) * ((e : ℝ) * f) + y * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) + z * (f : ℝ) ^ 2
      = (M : ℝ) * ((e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))) :
    y ≡ M * e [MOD f] ∧ (M * e < f → M * e ≤ y ∧ z ≤ 2 * (M * e)) :=
  SideRunGArith.C_base he hef hco
    (rep_nat_len (x := x) (y := y) (z := z) (M := M) (κ := 3) hef (by norm_num) (by rw [h]; push_cast; ring))

/-- **`cor:ebelow` (a), for an arbitrary congruent dissection**: if `M e < f`, the triangle `W_M(e, f)` (sides `M f (f² − e²)`,
`M e (2f² − e²)`, `M f³`) cannot be cut into copies of `(ef, f² − e², f²)` (any number of tiles). -/
theorem ebelow_a (e f M : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) (hM : 1 ≤ M)
    (hMe : M * e < f) (D₀ : CongruentDissection N)
    (hT : HasSides D₀.target ((M : ℝ) * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
      ((M : ℝ) * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))) ((M : ℝ) * (f : ℝ) ^ 3))
    (hMod : HasSides D₀.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)) : False := by
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr (by omega)
  obtain ⟨D, g, k₀, k₁, ax, ay, -, -, -, -, S, Co⟩ := setup_WG e f he hef hco hMr D₀ hT hMod
  exact S.no_tiling_QB Co hMe (by ring)

/-- **`cor:ebelow` (b), for an arbitrary congruent dissection**: if `2 M e < f`, the isosceles triangle `T_M(e, f)` (legs `M f³`,
base `M e (3f² − e²)`) cannot be cut into copies of `(ef, f² − e², f²)`. -/
theorem ebelow_b (e f M : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) (hM : 1 ≤ M)
    (hMe : 2 * M * e < f) (D₀ : CongruentDissection N)
    (hT : HasSides D₀.target ((M : ℝ) * (f : ℝ) ^ 3) ((M : ℝ) * (f : ℝ) ^ 3)
      ((M : ℝ) * ((e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))))
    (hMod : HasSides D₀.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)) : False := by
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr (by omega)
  obtain ⟨D, g, k₀, k₁, ax, ay, -, -, -, -, S, Co⟩ := setup_TG e f he hef hco hMr D₀ hT hMod
  exact S.no_tiling_base Co (by rw [← Nat.mul_assoc]; exact hMe) (by ring)

/-- **`cor:ebelow` (a) for the project predicate `WTilable e f M`** (`Draft.CollarG`): if `M e < f`, `W_M(e, f)` has no tiling.
(`WTilable` fixes the number of tiles at `(2f² − e²) M²`; `ebelow_a` allows any number.) -/
theorem not_wTilable_ebelow (e f M : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) (hM : 1 ≤ M)
    (hMe : M * e < f) : ¬ Erdos634.Draft.CollarG.WTilable e f M := by
  rintro ⟨D, hT, hMod⟩
  exact ebelow_a e f M he hef hco hM hMe D hT hMod

/-- **`cor:ebelow` (b) for the project predicate `BetaTilable e f M`** (`Draft.UniformThreshold`): if `2 M e < f`, `T_M(e, f)` has
no tiling. -/
theorem not_betaTilable_ebelow (e f M : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) (hM : 1 ≤ M)
    (hMe : 2 * M * e < f) : ¬ Erdos634.Draft.UniformThreshold.BetaTilable e f M := by
  rintro ⟨N, D, hT, hMod⟩
  exact ebelow_b e f M he hef hco hM hMe D hT hMod

/-! ## 6. The witness for `e ≥ 2` -/

/-- **A REAL DISSECTION SATISFIES `SetupG` AND `CornersG` FOR EVERY COPRIME MEMBER**, in particular for `e ≥ 2`: the seed tiling of
`W_f(e, f)` (`CollarG.wTilable_seed`, credited to M. Beeson; `WSeedG.w_seed`), moved into normal position by `setup_WG`. -/
theorem setupG_witness_member (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) :
    ∃ (N : ℕ) (D : CongruentDissection N) (L ax ay : ℝ),
      SetupG D e f (modelAlpha (e : ℝ) (f : ℝ)) (modelBeta (e : ℝ) (f : ℝ))
        (2 * modelAlpha (e : ℝ) (f : ℝ) + modelBeta (e : ℝ) (f : ℝ)) L ax ay ∧
      CornersG e f L ax ay := by
  obtain ⟨D₀, hT, hMod⟩ := Erdos634.Draft.CollarG.wTilable_seed e f he hef
  have hfr : (0 : ℝ) < (f : ℝ) := Nat.cast_pos.mpr (by omega)
  obtain ⟨D, g, k₀, k₁, ax, ay, -, -, -, -, S, Co⟩ := setup_WG e f he hef hco hfr D₀ hT hMod
  exact ⟨_, D, _, ax, ay, S, Co⟩

/-- the member `(2, 3)` (`e ≥ 2`): a real dissection (126 tiles) with `SetupG` and `CornersG` -/
theorem setupG_witness_e2 :
    ∃ (N : ℕ) (D : CongruentDissection N) (L ax ay : ℝ),
      SetupG D 2 3 (modelAlpha ((2 : ℕ) : ℝ) ((3 : ℕ) : ℝ)) (modelBeta ((2 : ℕ) : ℝ) ((3 : ℕ) : ℝ))
        (2 * modelAlpha ((2 : ℕ) : ℝ) ((3 : ℕ) : ℝ) + modelBeta ((2 : ℕ) : ℝ) ((3 : ℕ) : ℝ)) L ax ay ∧
      CornersG 2 3 L ax ay :=
  setupG_witness_member 2 3 (by norm_num) (by norm_num) (by decide)

/-- **The side theorem applies to the seed tiling**: for every coprime member the seed tiling of `W_f(e, f)` has, on its side `QB`
(length `f e (2f² − e²)`), `f` consecutive tiles laying their side `c` on it and showing `α` at the same end. -/
theorem siderunall_seed (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) :
    ∃ (N : ℕ) (D₀ : CongruentDissection N) (k₀ k₁ : Fin 3) (x₀ : ℝ) (t : ℕ → Fin N), k₀ ≠ k₁ ∧
      dist (D₀.target.pts k₀) (D₀.target.pts k₁) = (f : ℝ) * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)) ∧
      0 ≤ x₀ ∧ x₀ + (f : ℝ) * (f : ℝ) ^ 2 ≤ (f : ℝ) * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)) ∧
      ((∀ j, j < f → LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts k₀) (D₀.target.pts k₁) (t j) Ty.C1
          (x₀ + j * (f : ℝ) ^ 2)) ∨
       (∀ j, j < f → LaysBaseOn D₀ (e : ℝ) (f : ℝ) (D₀.target.pts k₀) (D₀.target.pts k₁) (t j) Ty.C2
          (x₀ + j * (f : ℝ) ^ 2))) := by
  obtain ⟨D₀, hT, hMod⟩ := Erdos634.Draft.CollarG.wTilable_seed e f he hef
  have hfr : (0 : ℝ) < (f : ℝ) := Nat.cast_pos.mpr (by omega)
  obtain ⟨k₀, k₁, x₀, t, hk, hd, h0, hend, hrun, -⟩ := thm_siderunall_W e f he hef hco hfr D₀ hT hMod
  exact ⟨_, D₀, k₀, k₁, x₀, t, hk, hd, h0, hend, hrun⟩

/-! ## 7. Checks at `e = 1` -/

/-- **`SideRunMain.no_dissection_T` from `ebelow_b`** (Theorem B at `e = 1`) -/
theorem no_dissection_T_of_G (n M : ℕ) (hM : 1 ≤ M) (h : 2 * M < n) (D₀ : CongruentDissection N)
    (hT : HasSides D₀.target ((M : ℝ) * (n : ℝ) ^ 3) ((M : ℝ) * (n : ℝ) ^ 3)
      ((M : ℝ) * (3 * (n : ℝ) ^ 2 - 1)))
    (hMod : HasSides D₀.model (n : ℝ) ((n : ℝ) ^ 2 - 1) ((n : ℝ) ^ 2)) : False := by
  have hn2 : 2 ≤ n := by omega
  have hT' : HasSides D₀.target ((M : ℝ) * ((n : ℝ) ^ 3)) ((M : ℝ) * ((n : ℝ) ^ 3))
      ((M : ℝ) * (((1 : ℕ) : ℝ) * (3 * (n : ℝ) ^ 2 - ((1 : ℕ) : ℝ) ^ 2))) :=
    hasSides_cast' hT rfl rfl (by push_cast; ring)
  have hMod' : HasSides D₀.model (((1 : ℕ) : ℝ) * (n : ℝ)) ((n : ℝ) ^ 2 - ((1 : ℕ) : ℝ) ^ 2) ((n : ℝ) ^ 2) :=
    hasSides_cast' hMod (by push_cast; ring) (by push_cast; ring) rfl
  exact ebelow_b 1 n M le_rfl (by omega) (Nat.coprime_one_left n) hM (by omega) D₀ hT' hMod'

/-- **`SideRunMain.no_dissection_W` from `ebelow_a`** (Theorem C at `e = 1`) -/
theorem no_dissection_W_of_G (n M : ℕ) (hM : 1 ≤ M) (h : M < n) (D₀ : CongruentDissection N)
    (hT : HasSides D₀.target ((M : ℝ) * (n : ℝ) ^ 3) ((M : ℝ) * ((n : ℝ) * ((n : ℝ) ^ 2 - 1)))
      ((M : ℝ) * (2 * (n : ℝ) ^ 2 - 1)))
    (hMod : HasSides D₀.model (n : ℝ) ((n : ℝ) ^ 2 - 1) ((n : ℝ) ^ 2)) : False := by
  have hn2 : 2 ≤ n := by omega
  have hT' : HasSides D₀.target ((M : ℝ) * ((n : ℝ) * ((n : ℝ) ^ 2 - ((1 : ℕ) : ℝ) ^ 2)))
      ((M : ℝ) * (((1 : ℕ) : ℝ) * (2 * (n : ℝ) ^ 2 - ((1 : ℕ) : ℝ) ^ 2))) ((M : ℝ) * (n : ℝ) ^ 3) :=
    hasSides_cast' (hasSides_rotG hT) (by push_cast; ring) (by push_cast; ring) rfl
  have hMod' : HasSides D₀.model (((1 : ℕ) : ℝ) * (n : ℝ)) ((n : ℝ) ^ 2 - ((1 : ℕ) : ℝ) ^ 2) ((n : ℝ) ^ 2) :=
    hasSides_cast' hMod (by push_cast; ring) (by push_cast; ring) rfl
  exact ebelow_a 1 n M le_rfl (by omega) (Nat.coprime_one_left n) hM (by omega) D₀ hT' hMod'

end Erdos634.Draft.SideRunG

#print axioms Erdos634.Draft.SideRunG.modelAngles_of_sidesG
#print axioms Erdos634.Draft.SideRunG.exists_iso_of_dist3
#print axioms Erdos634.Draft.SideRunG.setup_of_sidesG_pinned
#print axioms Erdos634.Draft.SideRunG.setup_of_sidesG
#print axioms Erdos634.Draft.SideRunG.setup_TG_pinned
#print axioms Erdos634.Draft.SideRunG.setup_WG_pinned
#print axioms Erdos634.Draft.SideRunG.thm_siderunall_T_pinned
#print axioms Erdos634.Draft.SideRunG.thm_siderunall_W_pinned
#print axioms Erdos634.Draft.SideRunG.setup_TG
#print axioms Erdos634.Draft.SideRunG.setup_WG
#print axioms Erdos634.Draft.SideRunG.thm_siderunall_T
#print axioms Erdos634.Draft.SideRunG.thm_siderunall_W
#print axioms Erdos634.Draft.SideRunG.cor_ebelow_arith_QB
#print axioms Erdos634.Draft.SideRunG.cor_ebelow_arith_base
#print axioms Erdos634.Draft.SideRunG.ebelow_a
#print axioms Erdos634.Draft.SideRunG.ebelow_b
#print axioms Erdos634.Draft.SideRunG.not_wTilable_ebelow
#print axioms Erdos634.Draft.SideRunG.not_betaTilable_ebelow
#print axioms Erdos634.Draft.SideRunG.setupG_witness_member
#print axioms Erdos634.Draft.SideRunG.setupG_witness_e2
#print axioms Erdos634.Draft.SideRunG.siderunall_seed
#print axioms Erdos634.Draft.SideRunG.no_dissection_T_of_G
#print axioms Erdos634.Draft.SideRunG.no_dissection_W_of_G

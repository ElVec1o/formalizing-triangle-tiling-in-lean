/-
Draft/SideRunGCornerMain.lean -- written 14 October 2026.  UNAUDITED.  In `AllThreshold`.  Module R2 (first file) of the plan for
`thm:cornerrun`: **the normal form for a side that starts at a corner `A'` of angle `2α` or `3α`**, for an arbitrary `CongruentDissection` whose target is given by its CORNER ANGLES.
(The statement `thm_cornerrun` is in `Draft/SideRunGCornerMainB.lean`; the witnesses are in `Draft/SideRunGCornerWitness.lean`.)

PAPER.  `thm:cornerrun`: "Let `s` be a side of a triangle `Δ` that is cut into congruent triangles with sides `(a, b, c)`, from a corner `A'` of angle `2α` or `3α` to a corner `Q'` of angle `β` or `α + β`, and read the types of the tiles
on `s` with `A'` on the left."

WHAT IS PROVED HERE.  `setup_of_corners`: a congruent dissection `D₀` (model with the sides `ef, f² − e², f²`, any number of tiles, reflections allowed) whose target has, at the vertices `A' = target.pts (τ 0)`, `Q' = target.pts (τ 1)`, the corner
angles `cornerAngle = 2α` or `3α` (at `A'`) and `β` or `α + β` (at `Q'`) (`α = modelAlpha e f`, `β = modelBeta e f`) is moved by an isometry `g` to a `SetupG` on the triangle `A' = (0, 0)`, `Q' = (L, 0)`, apex `(ax, ay)` with
`CornersA e f L ax ay` (the apex is on the ray of `A'` and on the ray of `Q'`), the tiles of `D` being the `g`-images of those of `D₀`, vertex for vertex.

HOW.  The apex is `(d₁ cos θ, d₁ sin θ)`, `θ` the corner angle at `A'` and `d₁ = |A'P|`; the law of cosines at `A'` gives `|Q'P|`, so `setup_of_apex_pinned` (the generalisation of `setup_of_sidesG_pinned` of `Draft/SideRunGMain.lean` to an arbitrary
apex) applies (SSS: `exists_iso_of_dist3`).  The law of cosines at `Q'` gives `L − ax = d₂ cos θ_Q`, `ay = d₂ sin θ_Q` (`d₂ = |Q'P|`).  The cosines of `2α`, `3α`, `β`, `α + β` are those of the `SetupG` (`cos_two_alpha`, `cos_three_alpha`,
`cos_modelBeta`, `cos_gamma`), and `ray_coords` turns `d (cos θ, sin θ)` into `t (X, Y)` with `X² + Y² = n²`: this is the form of `CornersA`.  No difference of the corners is computed from side lengths (the corner `3α` with `α + β` has no analogue in
`Draft/SideRunGAngles.lean`, which has only `β, β` and `α + β, β`).

WITNESSES.  The hypotheses of `setup_of_corners` are satisfied by the seed tilings of `W_f(e, f)` and `T_f(e, f)` (`Draft/SideRunGCornerWitness.lean`).

No sorry, no native_decide.
-/
import Erdos634.Draft.SideRunGMo
import Erdos634.Draft.SideRunGMain

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.SideRunGA

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.MarchKills Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.RunPartition Erdos634.E1BaseWord Erdos634.WallEndpoints Erdos634.BaseChain
  Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.TilePlacement
  Erdos634.Geometry.Dissection Erdos634.Draft.W2E1 Erdos634.Draft.SideRun Erdos634.Draft.SideRunG
  Erdos634.Draft.SideRunGJ Erdos634.Draft.FDBBaseBetaE1 Set

variable {N : ℕ} {D : CongruentDissection N}

/-! ## 0. Elementary tools -/

theorem eq_of_sq_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : a ^ 2 = b ^ 2) : a = b := by
  have h0 : (a - b) * (a + b) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h0 with h1 | h1
  · linarith
  · linarith

/-- the point `d (cos θ, sin θ)` is `(d / n) (X, Y)` when `(cos θ, sin θ) = (X, Y) / n` -/
theorem ray_coords {d c s X Y n : ℝ} (hd : 0 < d) (hn : 0 < n) (hY : 0 < Y) (hc : c = X / n)
    (hs : 0 < s) (hid : c ^ 2 + s ^ 2 = 1) (hXY : X ^ 2 + Y ^ 2 = n ^ 2) :
    d * c = (d / n) * X ∧ d * s = (d / n) * Y := by
  have hn' : n ≠ 0 := hn.ne'
  have hs2 : s ^ 2 = (Y / n) ^ 2 := by
    have h1 : s ^ 2 = 1 - c ^ 2 := by linarith
    rw [h1, hc]
    field_simp
    linarith [hXY]
  have hs' : s = Y / n := eq_of_sq_pos hs (div_pos hY hn) hs2
  refine ⟨by rw [hc]; ring, by rw [hs']; ring⟩

/-- **the apex `d₁ (cos θ, sin θ)` has the distances `d₁` from `(0,0)` and `d₂` from `(L, 0)`** when `d₂² = d₁² + L² − 2 d₁ L cos θ` -/
theorem apex_dists {d1 d2 L θ : ℝ} (hd1 : 0 < d1) (hd2 : 0 ≤ d2) (hθ0 : 0 < θ) (hθπ : θ < Real.pi)
    (hlaw : d2 ^ 2 = d1 ^ 2 + L ^ 2 - 2 * d1 * L * Real.cos θ) :
    0 < d1 * Real.sin θ ∧
    dist (mkPt L 0) (mkPt (d1 * Real.cos θ) (d1 * Real.sin θ)) = d2 ∧
    dist (mkPt (d1 * Real.cos θ) (d1 * Real.sin θ)) (mkPt 0 0) = d1 := by
  have hsin := Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ
  have hid := Real.cos_sq_add_sin_sq θ
  refine ⟨mul_pos hd1 hsin, ?_, ?_⟩
  · refine dist_eq_of_sq_eq ?_ dist_nonneg hd2
    rw [dist_sq_mkPt]
    linear_combination d1 ^ 2 * hid - hlaw
  · refine dist_eq_of_sq_eq ?_ dist_nonneg hd1.le
    rw [dist_sq_mkPt]
    linear_combination d1 ^ 2 * hid

/-! ## 1. The normal form with an arbitrary apex -/

/-- **THE NORMAL FORM, any apex** (the generalisation of `setup_of_sidesG_pinned` of `Draft/SideRunGMain.lean`, whose apex is `(L − t uuG, t hhG)`): a congruent dissection `D₀` whose target has the sides
`|τ 1 τ 2| = |Q P|`, `|τ 2 τ 0| = |P A'|`, `|τ 0 τ 1| = L` of the triangle `A' = (0,0)`, `Q' = (L, 0)`, `P = (ax, ay)`, `ay > 0`, and whose model has the sides `ef, f² − e², f²`, gives, after an isometry `g`, a `SetupG` on that
triangle with `g (τ 0) = (0, 0)`, `g (τ 1) = (L, 0)`. -/
theorem setup_of_apex_pinned (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) {L ax ay : ℝ}
    (hL : 0 < L) (hay : 0 < ay) (D₀ : CongruentDissection N) (τ : Equiv.Perm (Fin 3))
    (h1 : dist (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) = dist (mkPt L 0) (mkPt ax ay))
    (h2 : dist (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) = dist (mkPt ax ay) (mkPt 0 0))
    (h3 : dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) = L)
    (hMod : HasSides D₀.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)) :
    ∃ (D : CongruentDissection N) (g : Plane ≃ᵢ Plane),
      (∀ i m, (D.tile i).pts m = g ((D₀.tile i).pts m)) ∧
      g (D₀.target.pts (τ 0)) = mkPt 0 0 ∧ g (D₀.target.pts (τ 1)) = mkPt L 0 ∧
      SetupG D e f (modelAlpha (e : ℝ) (f : ℝ)) (modelBeta (e : ℝ) (f : ℝ))
        (2 * modelAlpha (e : ℝ) (f : ℝ) + modelBeta (e : ℝ) (f : ℝ)) L ax ay := by
  have h12 : dist ((Tg L ax ay hL hay).pts 1) ((Tg L ax ay hL hay).pts 2)
      = dist (mkPt L 0) (mkPt ax ay) := rfl
  have h20 : dist ((Tg L ax ay hL hay).pts 2) ((Tg L ax ay hL hay).pts 0)
      = dist (mkPt ax ay) (mkPt 0 0) := rfl
  have h01 : dist ((Tg L ax ay hL hay).pts 0) ((Tg L ax ay hL hay).pts 1) = L := by
    show dist (mkPt 0 0) (mkPt L 0) = L
    have := dist_mkPt_base 0 L hL.le
    rwa [zero_add] at this
  obtain ⟨g, hg0⟩ := exists_iso_of_dist3 (T := D₀.target.relabel τ) (U := Tg L ax ay hL hay)
    (by rw [Tri.relabel_pts, Tri.relabel_pts]; exact h3.trans h01.symm)
    (by rw [Tri.relabel_pts, Tri.relabel_pts]; exact h1.trans h12.symm)
    (by rw [Tri.relabel_pts, Tri.relabel_pts]; exact h2.trans h20.symm)
  have hg : ∀ k, g (D₀.target.pts k) = (Tg L ax ay hL hay).pts (τ.symm k) := by
    intro k
    have := hg0 (τ.symm k)
    rwa [Tri.relabel_pts, Equiv.apply_symm_apply] at this
  obtain ⟨σm, m0, m1, m2⟩ := sideOpp_relabel_of_hasSides hMod
  have hmod : D₀.model.Congruent (D₀.model.relabel σm) := Tri.congruent_relabel D₀.model σm
  have hMD := modelDataG_of_sides (Erdos634.E1NormalForm.normalFormC D₀ g τ.symm hmod) he hef m0 m1 m2
  exact ⟨Erdos634.E1NormalForm.normalFormC D₀ g τ.symm hmod, g, fun _ _ => rfl, hg0 0, hg0 1,
    ⟨he, hef, hco, hMD, angleData_model e f he hef, hL, hay,
      fun _ _ => Erdos634.E1NormalForm.normalFormC_target D₀ hg hmod⟩⟩

/-! ## 2. The forms of `CornersA` from the coordinates of the apex -/

section forms

variable {e f : ℕ} {α β γ L ax ay : ℝ}

/-- the apex `d₁ (cos θ, sin θ)` with `θ = 2α` is on the ray of the corner `2α`: `(ax, ay) = t (X₂, Y₂)` -/
theorem leftForm_two (S : SetupG D e f α β γ L ax ay) {d1 θ : ℝ} (hd1 : 0 < d1) (hθ : θ = 2 * α)
    (hax : ax = d1 * Real.cos θ) (hay : ay = d1 * Real.sin θ) :
    ∃ t : ℝ, 0 < t ∧ ax = t * ((2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2 - 2 * (f : ℝ) ^ 4) ∧
      ay = t * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) * rtG (e : ℝ) (f : ℝ)) := by
  have he0 := S.e0
  have hef := S.hef'
  have hf0 := S.f0
  obtain ⟨hα, hβ, hγ2, hsum, hγπ⟩ := angle_facts S.hA
  have hrel := S.hA.hrel
  have hθ0 : 0 < θ := by rw [hθ]; linarith
  have hθπ : θ < Real.pi := by rw [hθ]; linarith
  have hcos : Real.cos θ = ((2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2 - 2 * (f : ℝ) ^ 4) / (2 * (f : ℝ) ^ 4) := by
    rw [hθ]; exact cos_two_alpha S
  have hsin := Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ
  have hid := Real.cos_sq_add_sin_sq θ
  have hP : 0 < 2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hef) (add_pos he0 hf0), mul_pos hf0 hf0]
  have hrt := rtG_pos he0 hef
  have hrt2 := rtG_sq he0 hef
  have hY : 0 < (e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) * rtG (e : ℝ) (f : ℝ) :=
    mul_pos (mul_pos he0 hP) hrt
  have hXY : ((2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2 - 2 * (f : ℝ) ^ 4) ^ 2
      + ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) * rtG (e : ℝ) (f : ℝ)) ^ 2
      = (2 * (f : ℝ) ^ 4) ^ 2 := by
    linear_combination ((e : ℝ) ^ 2 * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2) * hrt2
  obtain ⟨h1, h2⟩ := ray_coords (d := d1) hd1 (by positivity) hY hcos hsin hid hXY
  exact ⟨d1 / (2 * (f : ℝ) ^ 4), div_pos hd1 (by positivity), by rw [hax]; exact h1,
    by rw [hay]; exact h2⟩

/-- the apex `d₁ (cos θ, sin θ)` with `θ = 3α` is on the ray of the corner `3α` -/
theorem leftForm_three (S : SetupG D e f α β γ L ax ay) {d1 θ : ℝ} (hd1 : 0 < d1) (hθ : θ = 3 * α)
    (hax : ax = d1 * Real.cos θ) (hay : ay = d1 * Real.sin θ) :
    ∃ t : ℝ, 0 < t ∧ ax = t * ((2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) *
        ((2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2 - 3 * (f : ℝ) ^ 4)) ∧
      ay = t * ((e : ℝ) * rtG (e : ℝ) (f : ℝ) *
        ((2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2 - (f : ℝ) ^ 4)) := by
  have he0 := S.e0
  have hef := S.hef'
  have hf0 := S.f0
  obtain ⟨hα, hβ, hγ2, hsum, hγπ⟩ := angle_facts S.hA
  have hrel := S.hA.hrel
  have hθ0 : 0 < θ := by rw [hθ]; linarith
  have hθπ : θ < Real.pi := by rw [hθ]; linarith
  have hcos : Real.cos θ = ((2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) *
      ((2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2 - 3 * (f : ℝ) ^ 4)) / (2 * (f : ℝ) ^ 6) := by
    rw [hθ]; exact cos_three_alpha S
  have hsin := Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ
  have hid := Real.cos_sq_add_sin_sq θ
  have hP : (f : ℝ) ^ 2 < 2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hef) (add_pos he0 hf0)]
  have hf2 : 0 < (f : ℝ) ^ 2 := by positivity
  have hPP : (f : ℝ) ^ 4 < (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hP) (add_pos hf2 (hf2.trans hP))]
  have hrt := rtG_pos he0 hef
  have hrt2 := rtG_sq he0 hef
  have hY : 0 < (e : ℝ) * rtG (e : ℝ) (f : ℝ) * ((2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2 - (f : ℝ) ^ 4) :=
    mul_pos (mul_pos he0 hrt) (by linarith)
  have hXY : ((2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) *
        ((2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2 - 3 * (f : ℝ) ^ 4)) ^ 2
      + ((e : ℝ) * rtG (e : ℝ) (f : ℝ) *
        ((2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2 - (f : ℝ) ^ 4)) ^ 2
      = (2 * (f : ℝ) ^ 6) ^ 2 := by
    linear_combination ((e : ℝ) ^ 2 * ((2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2 - (f : ℝ) ^ 4) ^ 2) * hrt2
  obtain ⟨h1, h2⟩ := ray_coords (d := d1) hd1 (by positivity) hY hcos hsin hid hXY
  exact ⟨d1 / (2 * (f : ℝ) ^ 6), div_pos hd1 (by positivity), by rw [hax]; exact h1,
    by rw [hay]; exact h2⟩

/-- the right corner `β`: `(L − ax, ay) = d₂ (cos β, sin β)` is `t (uuG, hhG)` -/
theorem rightForm_beta (S : SetupG D e f α β γ L ax ay) {d2 θQ : ℝ} (hd2 : 0 < d2) (hθ : θQ = β)
    (hax : L - ax = d2 * Real.cos θQ) (hay : ay = d2 * Real.sin θQ) :
    ∃ t : ℝ, 0 < t ∧ ax = L - t * uuG (e : ℝ) (f : ℝ) ∧ ay = t * hhG (e : ℝ) (f : ℝ) := by
  have he0 := S.e0
  have hef := S.hef'
  have hf0 := S.f0
  have hβ := S.hA.hβ
  have hβ' : β = modelBeta (e : ℝ) (f : ℝ) := S.beta_eq
  obtain ⟨hb0, hb2⟩ := modelBeta_mem he0 hef
  have hθ0 : 0 < θQ := by rw [hθ]; exact hβ
  have hθπ : θQ < Real.pi := by rw [hθ, hβ']; linarith [Real.pi_pos]
  have hcos : Real.cos θQ = uuG (e : ℝ) (f : ℝ) / ((e : ℝ) * f) := by
    rw [hθ, hβ', cos_modelBeta he0 hef]
    unfold baseLen Nq uuG
    field_simp
  have hsin := Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ
  have hid := Real.cos_sq_add_sin_sq θQ
  have hhp := hhG_pos he0 hef
  have hXY : uuG (e : ℝ) (f : ℝ) ^ 2 + hhG (e : ℝ) (f : ℝ) ^ 2 = ((e : ℝ) * f) ^ 2 := by
    have := hhG_sq he0 hef
    linarith
  obtain ⟨h1, h2⟩ := ray_coords (d := d2) hd2 (mul_pos he0 hf0) hhp hcos hsin hid hXY
  exact ⟨d2 / ((e : ℝ) * f), div_pos hd2 (mul_pos he0 hf0), by linarith, by rw [hay]; exact h2⟩

/-- the right corner `α + β`: `(L − ax, ay) = d₂ (cos (α + β), sin (α + β))` is `t (e, √(4f² − e²))` -/
theorem rightForm_ab (S : SetupG D e f α β γ L ax ay) {d2 θQ : ℝ} (hd2 : 0 < d2) (hθ : θQ = α + β)
    (hax : L - ax = d2 * Real.cos θQ) (hay : ay = d2 * Real.sin θQ) :
    ∃ t : ℝ, 0 < t ∧ ax = L - t * (e : ℝ) ∧ ay = t * rtG (e : ℝ) (f : ℝ) := by
  have he0 := S.e0
  have hef := S.hef'
  have hf0 := S.f0
  obtain ⟨hα, hβ, hγ2, hsum, hγπ⟩ := angle_facts S.hA
  have hγdef := S.hA.hγdef
  have hrel := S.hA.hrel
  have hθ0 : 0 < θQ := by rw [hθ]; linarith
  have hθπ : θQ < Real.pi := by rw [hθ]; linarith
  have hπγ : θQ = Real.pi - γ := by rw [hθ]; linarith
  have hcos : Real.cos θQ = (e : ℝ) / (2 * (f : ℝ)) := by
    rw [hπγ, Real.cos_pi_sub, S.cos_gamma]
    ring
  have hsin := Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ
  have hid := Real.cos_sq_add_sin_sq θQ
  have hrt := rtG_pos he0 hef
  have hrt2 := rtG_sq he0 hef
  have hXY : (e : ℝ) ^ 2 + rtG (e : ℝ) (f : ℝ) ^ 2 = (2 * (f : ℝ)) ^ 2 := by
    linear_combination hrt2
  obtain ⟨h1, h2⟩ := ray_coords (d := d2) hd2 (by positivity) hrt hcos hsin hid hXY
  exact ⟨d2 / (2 * (f : ℝ)), div_pos hd2 (by positivity), by linarith, by rw [hay]; exact h2⟩

/-- **`CornersA` from the coordinates of the apex** -/
theorem cornersA_of_coords (S : SetupG D e f α β γ L ax ay) {d1 d2 θ θQ : ℝ} (hd1 : 0 < d1) (hd2 : 0 < d2)
    (hax : ax = d1 * Real.cos θ) (hay : ay = d1 * Real.sin θ) (hA : θ = 2 * α ∨ θ = 3 * α)
    (hax' : L - ax = d2 * Real.cos θQ) (hay' : ay = d2 * Real.sin θQ) (hQ : θQ = β ∨ θQ = α + β) :
    CornersA e f L ax ay :=
  ⟨hA.elim (fun h => Or.inl (leftForm_two S hd1 h hax hay))
      (fun h => Or.inr (leftForm_three S hd1 h hax hay)),
   hQ.elim (fun h => Or.inl (rightForm_beta S hd2 h hax' hay'))
      (fun h => Or.inr (rightForm_ab S hd2 h hax' hay'))⟩

end forms

/-! ## 3. The normal form from the corner angles -/

/-- **THE NORMAL FORM OF A SIDE FROM A CORNER `A'` OF ANGLE `2α` OR `3α` TO A CORNER `Q'` OF ANGLE `β` OR `α + β`** (corners given by `cornerAngle`; the vertices named by `τ`: `τ 0 = A'`, `τ 1 = Q'`, `τ 2` the third vertex). -/
theorem setup_of_corners (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f)
    (D₀ : CongruentDissection N)
    (hMod : HasSides D₀.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2))
    (τ : Equiv.Perm (Fin 3))
    (hA : cornerAngle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) =
        2 * modelAlpha (e : ℝ) (f : ℝ) ∨
      cornerAngle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) =
        3 * modelAlpha (e : ℝ) (f : ℝ))
    (hQ : cornerAngle (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) =
        modelBeta (e : ℝ) (f : ℝ) ∨
      cornerAngle (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) =
        modelAlpha (e : ℝ) (f : ℝ) + modelBeta (e : ℝ) (f : ℝ)) :
    ∃ (D : CongruentDissection N) (g : Plane ≃ᵢ Plane) (L ax ay : ℝ),
      0 < L ∧ dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) = L ∧
      (∀ i m, (D.tile i).pts m = g ((D₀.tile i).pts m)) ∧
      g (D₀.target.pts (τ 0)) = mkPt 0 0 ∧ g (D₀.target.pts (τ 1)) = mkPt L 0 ∧
      ∃ S : SetupG D e f (modelAlpha (e : ℝ) (f : ℝ)) (modelBeta (e : ℝ) (f : ℝ))
          (2 * modelAlpha (e : ℝ) (f : ℝ) + modelBeta (e : ℝ) (f : ℝ)) L ax ay,
        CornersA e f L ax ay ∧
        (cornerAngle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) =
            2 * modelAlpha (e : ℝ) (f : ℝ) →
          D.target.localAngle (mkPt 0 0) = 2 * modelAlpha (e : ℝ) (f : ℝ)) := by
  have he0 : (0 : ℝ) < e := Nat.cast_pos.mpr (by omega)
  have hefR : (e : ℝ) < f := by exact_mod_cast hef
  have hf0 : (0 : ℝ) < f := he0.trans hefR
  obtain ⟨hβ0, hβ2⟩ := modelBeta_mem he0 hefR
  have hrel := modelAngle_rel (e : ℝ) (f : ℝ)
  have hα0 : 0 < modelAlpha (e : ℝ) (f : ℝ) := by unfold modelAlpha; linarith
  have hpi := Real.pi_pos
  have hT := D₀.target.indep.injective
  have h01 : D₀.target.pts (τ 0) ≠ D₀.target.pts (τ 1) :=
    fun h => absurd (τ.injective (hT h)) (by decide)
  have h02 : D₀.target.pts (τ 0) ≠ D₀.target.pts (τ 2) :=
    fun h => absurd (τ.injective (hT h)) (by decide)
  have h12 : D₀.target.pts (τ 1) ≠ D₀.target.pts (τ 2) :=
    fun h => absurd (τ.injective (hT h)) (by decide)
  obtain ⟨L, hLdef⟩ : ∃ L, L = dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) := ⟨_, rfl⟩
  obtain ⟨d1, hd1def⟩ : ∃ d1, d1 = dist (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) := ⟨_, rfl⟩
  obtain ⟨d2, hd2def⟩ : ∃ d2, d2 = dist (D₀.target.pts (τ 2)) (D₀.target.pts (τ 1)) := ⟨_, rfl⟩
  have hL : 0 < L := by rw [hLdef]; exact dist_pos.mpr h01
  have hd1 : 0 < d1 := by rw [hd1def]; exact dist_pos.mpr h02.symm
  have hd2 : 0 < d2 := by rw [hd2def]; exact dist_pos.mpr h12.symm
  obtain ⟨θ, hθdef⟩ : ∃ θ, θ = cornerAngle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0))
    (D₀.target.pts (τ 1)) := ⟨_, rfl⟩
  obtain ⟨θQ, hθQdef⟩ : ∃ θQ, θQ = cornerAngle (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1))
    (D₀.target.pts (τ 2)) := ⟨_, rfl⟩
  have hA' : θ = 2 * modelAlpha (e : ℝ) (f : ℝ) ∨ θ = 3 * modelAlpha (e : ℝ) (f : ℝ) := by
    rw [hθdef]; exact hA
  have hQ' : θQ = modelBeta (e : ℝ) (f : ℝ) ∨ θQ = modelAlpha (e : ℝ) (f : ℝ) + modelBeta (e : ℝ) (f : ℝ) := by
    rw [hθQdef]; exact hQ
  have hθ0 : 0 < θ := by rcases hA' with h | h <;> rw [h] <;> linarith
  have hθπ : θ < Real.pi := by rcases hA' with h | h <;> rw [h] <;> linarith
  have hθQ0 : 0 < θQ := by rcases hQ' with h | h <;> rw [h] <;> linarith
  have hθQπ : θQ < Real.pi := by rcases hQ' with h | h <;> rw [h] <;> linarith
  -- the laws of cosines at `A'` and `Q'`
  have e_rp : dist (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) = d1 := hd1def.symm
  have e_rq : dist (D₀.target.pts (τ 2)) (D₀.target.pts (τ 1)) = d2 := hd2def.symm
  have e_pq : dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) = L := hLdef.symm
  have e_qp : dist (D₀.target.pts (τ 1)) (D₀.target.pts (τ 0)) = L := by rw [dist_comm]; exact e_pq
  have e_pr : dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 2)) = d1 := by rw [dist_comm]; exact e_rp
  have e_qr : dist (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) = d2 := by rw [dist_comm]; exact e_rq
  have lawA : d2 ^ 2 = d1 ^ 2 + L ^ 2 - 2 * d1 * L * Real.cos θ := by
    have h := EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle
      (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1))
    rw [e_rq, e_rp, e_qp] at h
    have hc : Real.cos (EuclideanGeometry.angle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0))
        (D₀.target.pts (τ 1))) = Real.cos θ := by rw [hθdef]; rfl
    rw [hc] at h
    linear_combination h
  have lawQ : d1 ^ 2 = d2 ^ 2 + L ^ 2 - 2 * d2 * L * Real.cos θQ := by
    have h := EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle
      (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2))
    rw [e_pr, e_pq, e_rq] at h
    have hc : Real.cos (EuclideanGeometry.angle (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1))
        (D₀.target.pts (τ 2))) = Real.cos θQ := by rw [hθQdef]; rfl
    rw [hc] at h
    linear_combination h
  -- the apex
  obtain ⟨hay, hdQ, hdA⟩ := apex_dists hd1 hd2.le hθ0 hθπ lawA
  obtain ⟨D, g, hD, hP, hB, S⟩ := setup_of_apex_pinned e f he hef hco (L := L)
    (ax := d1 * Real.cos θ) (ay := d1 * Real.sin θ) hL hay D₀ τ
    (by rw [hdQ, dist_comm, ← hd2def]) (by rw [hdA, ← hd1def]) hLdef.symm hMod
  -- the right corner: `L − ax = d₂ cos θ_Q`, `ay = d₂ sin θ_Q`
  have hLsum : L = d1 * Real.cos θ + d2 * Real.cos θQ := by
    have h : L * (L - d1 * Real.cos θ - d2 * Real.cos θQ) = 0 := by
      linear_combination (-1 / 2 : ℝ) * lawA + (-1 / 2 : ℝ) * lawQ
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hL.ne'
    · linarith
  have hsinQ : d1 * Real.sin θ = d2 * Real.sin θQ := by
    have hsθ := Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ
    have hsQ := Real.sin_pos_of_pos_of_lt_pi hθQ0 hθQπ
    have hidA := Real.cos_sq_add_sin_sq θ
    have hidQ := Real.cos_sq_add_sin_sq θQ
    refine eq_of_sq_pos (mul_pos hd1 hsθ) (mul_pos hd2 hsQ) ?_
    linear_combination d1 ^ 2 * hidA - d2 ^ 2 * hidQ - lawA
      - (d2 * Real.cos θQ + L - d1 * Real.cos θ) * hLsum
  have hCo : CornersA e f L (d1 * Real.cos θ) (d1 * Real.sin θ) :=
    cornersA_of_coords S hd1 hd2 rfl rfl hA' (by linarith) hsinQ hQ'
  refine ⟨D, g, L, d1 * Real.cos θ, d1 * Real.sin θ, hL, hLdef.symm, hD, hP, hB, S, hCo, ?_⟩
  intro h2
  have h2' : θ = 2 * modelAlpha (e : ℝ) (f : ℝ) := by rw [hθdef]; exact h2
  obtain ⟨t, ht, hax2, hay2⟩ := leftForm_two S hd1 h2' rfl rfl
  exact corner_left_two S ht hax2 hay2

end Erdos634.Draft.SideRunGA

#print axioms Erdos634.Draft.SideRunGA.eq_of_sq_pos
#print axioms Erdos634.Draft.SideRunGA.ray_coords
#print axioms Erdos634.Draft.SideRunGA.apex_dists
#print axioms Erdos634.Draft.SideRunGA.setup_of_apex_pinned
#print axioms Erdos634.Draft.SideRunGA.leftForm_two
#print axioms Erdos634.Draft.SideRunGA.leftForm_three
#print axioms Erdos634.Draft.SideRunGA.rightForm_beta
#print axioms Erdos634.Draft.SideRunGA.rightForm_ab
#print axioms Erdos634.Draft.SideRunGA.cornersA_of_coords
#print axioms Erdos634.Draft.SideRunGA.setup_of_corners

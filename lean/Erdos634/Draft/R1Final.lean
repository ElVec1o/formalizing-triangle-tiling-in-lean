-- Draft/R1Final.lean — R1 (proof_R1_compressed.md, room W2) for the paper's class of tilings:
-- for every f ≥ 2 and e = f − 1, no congruent dissection of (a congruent copy of) the m = 1 base-β
-- target Δ₁(e, f) into copies of the tile (ef, f² − e², f²) exists.  Imported into All.lean (header updated 2026-10-01).
--
-- FORM (as `E1BaseWord.e1_family_f_ge_3_congruent`): quantify over `CongruentDissection`s whose
-- target is congruent to `baseBetaTarget e f` and whose model is congruent to a triangle `T` with
-- sides `(ef, f² − e², f²)` (side `j` opposite vertex `j`; any vertex order is covered by
-- `r1_no_tiling_perm`).  Isometries include reflections; tiles need not meet edge-to-edge; `N` free.
-- Normal position is `E1NormalForm.normalFormC` (general in target and tile); the model's angle data
-- is `ApexNormal.modelData_of_sides`, the target data `ApexWitness44.m1_target_witness`, the angle
-- bundle (α/π irrational, Niven) `ApexWitness44.angleData_member` — all cited, none re-derived.
--
-- f = 2 (e = 1, N = 11) IS COVERED, and is a REPRODUCTION of a settled row (N = 11, engine search;
-- `thm:basebeta-e1`), by a second, search-free route.  f ≥ 3 is new Lean for thm:thick (R1, I2).
--
-- Build (scratch oleans; never .lake): R1Kill, ApexNormal oleans in $S, then lean_guard.sh.
import Erdos634.Draft.R1Kill
import Erdos634.Draft.ApexNormal

namespace Erdos634.Draft.R1Final

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.BaseBetaTargetCoord
open Erdos634.Draft.R1Frame Erdos634.Draft.R1Kill Erdos634.Draft.ApexWitness44

variable {N : ℕ}

/-- **The frame `R1Frame` for a dissection in normal position with the paper's tile**, every coprime
`1 ≤ e < f` (apex `k = 2`, model angles). -/
theorem exists_r1frame_normal (D : CongruentDissection N) {e f : ℕ}
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (he0 : (0 : ℝ) < e) (hefR : (e : ℝ) < f)
    (htgt : D.target = baseBetaTarget e f he0 hefR)
    (hs0 : sideOpp D.model 0 = (e : ℝ) * f) (hs1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (hs2 : sideOpp D.model 2 = (f : ℝ) ^ 2) :
    Nonempty (R1Frame D e f (modelAlpha e f) (modelBeta e f)
      (2 * modelAlpha e f + modelBeta e f)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := m1_target_witness he0 hefR
  apply exists_r1frame_m1 D hco he hef (ApexNormal.modelData_of_sides D he hef hs0 hs1 hs2)
    (angleData_member e f he hef) 2 <;> rw [htgt] <;> assumption

/-- **R1 in normal position** (`D.target = baseBetaTarget e f`, model sides `(ef, f² − e², f²)`),
`e + 1 = f`, `f ≥ 2`. -/
theorem r1_normal (D : CongruentDissection N) {e f : ℕ} (he : 1 ≤ e) (hef1 : e + 1 = f)
    (he0 : (0 : ℝ) < e) (hefR : (e : ℝ) < f)
    (htgt : D.target = baseBetaTarget e f he0 hefR)
    (hs0 : sideOpp D.model 0 = (e : ℝ) * f) (hs1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (hs2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False := by
  have hco : Nat.Coprime e f := by rw [← hef1]; simp [Nat.coprime_self_add_right]
  obtain ⟨F⟩ := exists_r1frame_normal D hco he (by omega) he0 hefR htgt hs0 hs1 hs2
  exact r1_frame_false_thick F hef1

/-- **R1 — THE THICK LINE `e = f − 1`, `f ≥ 2`, FOR THE PAPER'S CLASS OF TILINGS.**  No congruent
dissection whose target is congruent to the `m = 1` base-β target `baseBetaTarget e f` and whose
model is congruent to a triangle `T` with sides `(ef, f² − e², f²)` exists. -/
theorem r1_no_tiling (D₀ : CongruentDissection N) {e f : ℕ} (he : 1 ≤ e) (hef1 : e + 1 = f)
    (htgt : D₀.target.Congruent (baseBetaTarget e f (by exact_mod_cast (show 0 < e by omega))
      (by exact_mod_cast (show e < f by omega))))
    (T : Tri) (hT0 : sideOpp T 0 = (e : ℝ) * f) (hT1 : sideOpp T 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (hT2 : sideOpp T 2 = (f : ℝ) ^ 2) (hmod : D₀.model.Congruent T) : False := by
  obtain ⟨g, σ, hg⟩ := htgt
  exact r1_normal (Erdos634.E1NormalForm.normalFormC D₀ g σ hmod) he hef1 _ _
    (Erdos634.E1NormalForm.normalFormC_target D₀ hg hmod) hT0 hT1 hT2

/-- The same, the model's own vertices in any order (`ApexNormal.split_congruent`'s form). -/
theorem r1_no_tiling_perm (D₀ : CongruentDissection N) {e f : ℕ} (he : 1 ≤ e) (hef1 : e + 1 = f)
    (htgt : D₀.target.Congruent (baseBetaTarget e f (by exact_mod_cast (show 0 < e by omega))
      (by exact_mod_cast (show e < f by omega))))
    (τ : Equiv.Perm (Fin 3))
    (hs0 : sideOpp (D₀.model.relabel τ) 0 = (e : ℝ) * f)
    (hs1 : sideOpp (D₀.model.relabel τ) 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (hs2 : sideOpp (D₀.model.relabel τ) 2 = (f : ℝ) ^ 2) : False :=
  r1_no_tiling D₀ he hef1 htgt _ hs0 hs1 hs2 (Tri.congruent_relabel D₀.model τ)

/-- The same, indexed by `f ≥ 2` alone (`e = f − 1`). -/
theorem r1_no_tiling_all_f (D₀ : CongruentDissection N) {f : ℕ} (hf : 2 ≤ f)
    (htgt : D₀.target.Congruent (baseBetaTarget ((f - 1 : ℕ) : ℝ) f
      (by exact_mod_cast (show 0 < f - 1 by omega)) (by exact_mod_cast (show f - 1 < f by omega))))
    (T : Tri) (hT0 : sideOpp T 0 = ((f - 1 : ℕ) : ℝ) * f)
    (hT1 : sideOpp T 1 = (f : ℝ) ^ 2 - ((f - 1 : ℕ) : ℝ) ^ 2) (hT2 : sideOpp T 2 = (f : ℝ) ^ 2)
    (hmod : D₀.model.Congruent T) : False :=
  r1_no_tiling D₀ (e := f - 1) (by omega) (by omega) htgt T hT0 hT1 hT2 hmod

/-- **The member `f = 2` (`N = 11`), in `E1BaseWord`'s exact form** (target congruent to
`baseBetaTarget 1 2`, model congruent to `MarchCompose.modelTri 2`).  A REPRODUCTION of the settled
`N = 11` row by a search-free route (`E1BaseWord` covers `e = 1` only for `f ≥ 3`). -/
theorem r1_n11 (D₀ : CongruentDissection N)
    (htgt : D₀.target.Congruent (baseBetaTarget 1 ((2 : ℕ) : ℝ) one_pos (by norm_num)))
    (hmod : D₀.model.Congruent (MarchCompose.modelTri ((2 : ℕ) : ℝ) (by norm_num))) : False := by
  obtain ⟨m0, m1, m2⟩ := MarchCompose.modelTri_sides (f := ((2 : ℕ) : ℝ)) (by norm_num)
  refine r1_no_tiling D₀ (e := 1) (f := 2) le_rfl rfl ?_ _ ?_ ?_ ?_ hmod
  · simpa only [Nat.cast_one] using htgt
  · rw [m0]; norm_num
  · rw [m1]; norm_num
  · rw [m2]

/-! ## Controls and ablations (Rule 3 / Rule 25) -/

/-- **Sharpness of the only member-dependent input.**  For coprime `1 ≤ e < f`, the depth inequality
`f·b < 2c` that `r1_frame_false` consumes holds EXACTLY on the line `e = f − 1`: every other input
of the R1 chain (`V_pierced`, two `γ` at `P′`, `Lprime_exists`, `Z_exists`, `Z_alpha`) is proved
here for all coprime `1 ≤ e < f`. -/
theorem depth_iff_thick {e f : ℕ} (he : 1 ≤ e) (hef : e < f) :
    (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) < 2 * (f : ℝ) ^ 2 ↔ e + 1 = f := by
  refine ⟨fun h => ?_, fun h => depth_thick h⟩
  by_contra hne
  have h2 : e + 2 ≤ f := by omega
  have h2R : (e : ℝ) + 2 ≤ f := by exact_mod_cast h2
  have heR : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hsq : (e : ℝ) ^ 2 ≤ ((f : ℝ) - 2) ^ 2 := by nlinarith
  nlinarith

/-- **Control (the real `N = 44` tiling, `(e,f) = (1,2)`, `m = 2`).**  At `m = 1` the mismatch ray
meets the base at `f·b = 6 < 8 = 2c` (the kill fires); on the real 44-tiling (`m = 2`) it meets the
base at `m·f·b = 12 > 8`, so the `α`-tile's `c`-endpoint stays inside: exactly the depth step
fails there, as it must.  (Observed on the certified tiling, exact in ℚ(√15), by
`review2_R1_fresh/r1_real_tiling_control.py`: steps 0–3 hold, step 4 fails.) -/
theorem depth_control_44 :
    ((2 : ℝ) * ((2 : ℝ) ^ 2 - (1 : ℝ) ^ 2) < 2 * (2 : ℝ) ^ 2) ∧
      ¬ (2 * (2 : ℝ) * ((2 : ℝ) ^ 2 - (1 : ℝ) ^ 2) < 2 * (2 : ℝ) ^ 2) := by
  norm_num

/-- At `m = 2` the depth inequality `m·f·b < 2c` fails on the WHOLE thick line (so the argument
proves nothing at `m = 2`, as the real 44-tiling requires). -/
theorem depth_fails_m2 {e f : ℕ} (hef1 : e + 1 = f) :
    ¬ (2 * (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) < 2 * (f : ℝ) ^ 2) := by
  have h : (e : ℝ) = f - 1 := by
    have : ((e + 1 : ℕ) : ℝ) = f := by exact_mod_cast hef1
    push_cast at this; linarith
  rw [h]
  have hf : (1 : ℝ) ≤ f := by exact_mod_cast (show 1 ≤ f by omega)
  intro hc
  nlinarith

/-- **Frame-free helper, witnessed on the real 44-tiling**: every corner of every tile of the certified
`N = 44` dissection is `α`, `β` or `γ` (`vertex_angle_mem` with `ApexWitness44`'s model data). -/
theorem control_vertex_angle_44 (j : Fin Tiling44.tiles.length) (m : Fin 3) :
    (D44.tile j).localAngle ((D44.tile j).pts m) = modelAlpha 1 ((2 : ℕ) : ℝ) ∨
      (D44.tile j).localAngle ((D44.tile j).pts m) = modelBeta 1 ((2 : ℕ) : ℝ) ∨
      (D44.tile j).localAngle ((D44.tile j).pts m)
        = 2 * modelAlpha 1 ((2 : ℕ) : ℝ) + modelBeta 1 ((2 : ℕ) : ℝ) :=
  vertex_angle_mem D44 D44_hα D44_hβ D44_hγ j m

/-- **Non-vacuity of the hypotheses of `r1_no_tiling` at `f = 2`** (they are jointly unsatisfiable —
that is the theorem): `1 ≤ e`, `e + 1 = f`; the target congruence is satisfiable (reflexivity); a
triangle `T` with sides `(ef, f² − e², f²) = (2, 3, 4)` exists (`modelTri 2`), and the model
congruence is satisfiable (reflexivity). -/
theorem hyps_nonvacuous_f2 :
    1 ≤ (1 : ℕ) ∧ (1 : ℕ) + 1 = 2 ∧
    (baseBetaTarget 1 ((2 : ℕ) : ℝ) one_pos (by norm_num)).Congruent
      (baseBetaTarget 1 ((2 : ℕ) : ℝ) one_pos (by norm_num)) ∧
    sideOpp (MarchCompose.modelTri ((2 : ℕ) : ℝ) (by norm_num)) 0 = ((1 : ℕ) : ℝ) * ((2 : ℕ) : ℝ) ∧
    sideOpp (MarchCompose.modelTri ((2 : ℕ) : ℝ) (by norm_num)) 1
      = ((2 : ℕ) : ℝ) ^ 2 - ((1 : ℕ) : ℝ) ^ 2 ∧
    sideOpp (MarchCompose.modelTri ((2 : ℕ) : ℝ) (by norm_num)) 2 = ((2 : ℕ) : ℝ) ^ 2 ∧
    (MarchCompose.modelTri ((2 : ℕ) : ℝ) (by norm_num)).Congruent
      (MarchCompose.modelTri ((2 : ℕ) : ℝ) (by norm_num)) := by
  obtain ⟨m0, m1, m2⟩ := MarchCompose.modelTri_sides (f := ((2 : ℕ) : ℝ)) (by norm_num)
  refine ⟨le_rfl, rfl, Tri.Congruent.refl _, ?_, ?_, m2, Tri.Congruent.refl _⟩
  · rw [m0]; norm_num
  · rw [m1]; norm_num

end Erdos634.Draft.R1Final

#print axioms Erdos634.Draft.R1Final.exists_r1frame_normal
#print axioms Erdos634.Draft.R1Final.r1_normal
#print axioms Erdos634.Draft.R1Final.r1_no_tiling
#print axioms Erdos634.Draft.R1Final.r1_no_tiling_perm
#print axioms Erdos634.Draft.R1Final.r1_no_tiling_all_f
#print axioms Erdos634.Draft.R1Final.r1_n11
#print axioms Erdos634.Draft.R1Final.depth_iff_thick
#print axioms Erdos634.Draft.R1Final.depth_control_44
#print axioms Erdos634.Draft.R1Final.depth_fails_m2
#print axioms Erdos634.Draft.R1Final.control_vertex_angle_44
#print axioms Erdos634.Draft.R1Final.hyps_nonvacuous_f2

-- Draft/ApexNormal.lean — the frame of branch (H) for a congruent dissection of the m = 1 base-β
-- target GIVEN AS THE PAPER GIVES IT: target in normal position (`D.target = baseBetaTarget e f`,
-- the corpus' coordinate target) and model with sides `(ef, f² − e², f²)` (labelled so that side `j`
-- is opposite vertex `j`; any model can be so relabelled by `CongruentDissection.relabelModel`).
-- Every other hypothesis of `ApexLegWord.exists_hframe_m1` (model angles, `AngleData`, the target's
-- corner angles and side lengths) is DERIVED.  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
--
-- Build: ApexLegWord, ApexWitness44, ApexFrameReal (and their deps) oleans in $S, then
--   (plus ApexR2Frame, MirrorStripR2Glue oleans)
--   lake env bash -c 'LEAN_PATH=$S:$LEAN_PATH lean Erdos634/Draft/ApexNormal.lean'
import Erdos634.Draft.ApexFrameReal
import Erdos634.Draft.ApexWitness44
import Erdos634.Draft.ApexR2Frame
import Erdos634.E1NormalForm

namespace Erdos634.Draft.ApexNormal

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.BaseBetaTargetCoord
open Erdos634.Draft.ApexWitness44

variable {N : ℕ}

/-- **The model angles from the model sides.**  A model with sides `(ef, f² − e², f²)` (side `j`
opposite vertex `j`) has corner angles `modelAlpha e f`, `modelBeta e f`, `2α + β`. -/
theorem modelData_of_sides (D : CongruentDissection N) {e f : ℕ} (he : 1 ≤ e) (hef : e < f)
    (hs0 : sideOpp D.model 0 = (e : ℝ) * f) (hs1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (hs2 : sideOpp D.model 2 = (f : ℝ) ^ 2) :
    HalfTurnR3R4Glue.ModelDataE D e f (modelAlpha e f) (modelBeta e f)
      (2 * modelAlpha e f + modelBeta e f) := by
  have heR : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hefR : (e : ℝ) < f := by exact_mod_cast hef
  have he0 : (0 : ℝ) < e := by linarith
  have hf0 : (0 : ℝ) < f := by linarith
  have hb0 : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  set M := D.model
  have d12 : dist (M.pts 1) (M.pts 2) = (e : ℝ) * f := by rw [← hs0]; rfl
  have d20 : dist (M.pts 2) (M.pts 0) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by rw [← hs1]; rfl
  have d01 : dist (M.pts 0) (M.pts 1) = (f : ℝ) ^ 2 := by rw [← hs2]; rfl
  obtain ⟨hβ0, hβ2⟩ := modelBeta_mem he0 hefR
  have hrel := modelAngle_rel (e : ℝ) f
  have hα0 : 0 < modelAlpha e f := by unfold modelAlpha; linarith
  have hαπ : modelAlpha e f ≤ Real.pi := by unfold modelAlpha; linarith [Real.pi_pos]
  have hα' : cornerAngle (M.pts 1) (M.pts 0) (M.pts 2) = modelAlpha e f := by
    have h1 : dist (M.pts 1) (M.pts 0) = (f : ℝ) ^ 2 := by rw [dist_comm]; exact d01
    refine cornerAngle_eq_of_cos (a := (f : ℝ) ^ 2) (b := (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
      (d := (e : ℝ) * f) h1 d20 d12 (by positivity) hb0 hα0.le hαπ ?_
    rw [cos_modelAlpha he0 hefR]
    field_simp
    ring
  have hβ' : cornerAngle (M.pts 2) (M.pts 1) (M.pts 0) = modelBeta e f := by
    have h1 : dist (M.pts 2) (M.pts 1) = (e : ℝ) * f := by rw [dist_comm]; exact d12
    refine cornerAngle_eq_of_cos (a := (e : ℝ) * f) (b := (f : ℝ) ^ 2)
      (d := (f : ℝ) ^ 2 - (e : ℝ) ^ 2) h1 d01 d20 (by positivity) (by positivity)
      hβ0.le (by linarith [Real.pi_pos]) ?_
    obtain ⟨hc0, hc1⟩ := cosBeta_mem he0 hefR
    unfold modelBeta
    rw [Real.cos_arccos (by linarith) hc1.le]
    unfold baseLen Nq
    field_simp
    ring
  have hγ' : cornerAngle (M.pts 0) (M.pts 2) (M.pts 1) = 2 * modelAlpha e f + modelBeta e f := by
    have hsum := Erdos634.Geometry.cornerAngle_sum M
    rw [hα', hβ'] at hsum
    linarith
  exact ⟨hs0, hs1, hs2, hα', hβ', hγ'⟩

/-- **`M1Data` for a dissection in normal position with the paper's tile** (apex `k = 2`). -/
theorem m1Data_normal (D : CongruentDissection N) {e f : ℕ}
    (hco : Nat.Coprime e f) (he : 2 ≤ e) (hef : e + 2 ≤ f)
    (he0 : (0 : ℝ) < e) (hefR : (e : ℝ) < f)
    (htgt : D.target = baseBetaTarget e f he0 hefR)
    (hs0 : sideOpp D.model 0 = (e : ℝ) * f) (hs1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (hs2 : sideOpp D.model 2 = (f : ℝ) ^ 2) :
    ApexFrameReal.M1Data D e f (modelAlpha e f) (modelBeta e f)
      (2 * modelAlpha e f + modelBeta e f) 2 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := m1_target_witness he0 hefR
  refine ⟨hco, he, hef, modelData_of_sides D (by omega) (by omega) hs0 hs1 hs2,
    angleData_member e f (by omega) (by omega), ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [htgt] <;>
    assumption

/-- **THE FRAME, FOR THE PAPER'S CLASS OF DISSECTIONS — PROVED.**  Every congruent dissection of
the `m = 1` base-β target `baseBetaTarget e f` (normal position) by the tile with sides
`(ef, f² − e², f²)`, at a coprime member `2 ≤ e ≤ f − 2`, carries the apex frame `HFrame` of branch
(H), at the model angles. -/
theorem exists_hframe_normal (D : CongruentDissection N) {e f : ℕ}
    (hco : Nat.Coprime e f) (he : 2 ≤ e) (hef : e + 2 ≤ f)
    (he0 : (0 : ℝ) < e) (hefR : (e : ℝ) < f)
    (htgt : D.target = baseBetaTarget e f he0 hefR)
    (hs0 : sideOpp D.model 0 = (e : ℝ) * f) (hs1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (hs2 : sideOpp D.model 2 = (f : ℝ) ^ 2) :
    Nonempty (HalfTurnR3R4Glue.HFrame D e f (modelAlpha e f) (modelBeta e f)
      (2 * modelAlpha e f + modelBeta e f)) :=
  ApexFrameReal.frame (m1Data_normal D hco he hef he0 hefR htgt hs0 hs1 hs2)

/-- **Lemma G's (H)/(M) split, for the paper's class of dissections.** -/
theorem lemmaG_normal (D : CongruentDissection N) {e f : ℕ}
    (hco : Nat.Coprime e f) (he : 2 ≤ e) (hef : e + 2 ≤ f)
    (he0 : (0 : ℝ) < e) (hefR : (e : ℝ) < f)
    (htgt : D.target = baseBetaTarget e f he0 hefR)
    (hs0 : sideOpp D.model 0 = (e : ℝ) * f) (hs1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (hs2 : sideOpp D.model 2 = (f : ℝ) ^ 2) :
    ∃ F : HalfTurnR3R4Glue.HFrame D e f (modelAlpha e f) (modelBeta e f)
        (2 * modelAlpha e f + modelBeta e f),
      HalfTurnR3R4Glue.Present D F.K ∨ ∃ M : Plane, HalfTurnR3R4Glue.IsMirror F.A F.V F.P M ∧
        HalfTurnR3R4Glue.Present D {F.V, F.P, M} :=
  ApexFrameReal.lemmaG_real (m1Data_normal D hco he hef he0 hefR htgt hs0 hs1 hs2)

/-- **Both branches framed, for the paper's class of dissections**: the apex frame `F` of branch
(H) exists, and either `K` is present (H) or the mirror-strip frame `R2Frame` of branch (M) exists. -/
theorem split_normal (D : CongruentDissection N) {e f : ℕ}
    (hco : Nat.Coprime e f) (he : 2 ≤ e) (hef : e + 2 ≤ f)
    (he0 : (0 : ℝ) < e) (hefR : (e : ℝ) < f)
    (htgt : D.target = baseBetaTarget e f he0 hefR)
    (hs0 : sideOpp D.model 0 = (e : ℝ) * f) (hs1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (hs2 : sideOpp D.model 2 = (f : ℝ) ^ 2) :
    ∃ F : HalfTurnR3R4Glue.HFrame D e f (modelAlpha e f) (modelBeta e f)
        (2 * modelAlpha e f + modelBeta e f),
      HalfTurnR3R4Glue.Present D F.K ∨
        Nonempty (MirrorStripR2Glue.R2Frame D e f (modelAlpha e f) (modelBeta e f)
          (2 * modelAlpha e f + modelBeta e f)) :=
  ApexR2Frame.split_real (m1Data_normal D hco he hef he0 hefR htgt hs0 hs1 hs2)

/-- **Both branches framed, for ANY congruent dissection of a congruent copy of the target** (the
paper's class verbatim: target congruent to `baseBetaTarget e f`, tile with sides
`(ef, f² − e², f²)` in some vertex order).  The dissection is moved into normal position by the
isometry `g` of the target congruence (`E1NormalForm.normalFormC`, general in the target and tile);
its tiles are the `g`-images of `D₀`'s, vertex for vertex. -/
theorem split_congruent (D₀ : CongruentDissection N) {e f : ℕ}
    (hco : Nat.Coprime e f) (he : 2 ≤ e) (hef : e + 2 ≤ f)
    (he0 : (0 : ℝ) < e) (hefR : (e : ℝ) < f)
    (hT : D₀.target.Congruent (baseBetaTarget e f he0 hefR)) (τ : Equiv.Perm (Fin 3))
    (hs0 : sideOpp (D₀.model.relabel τ) 0 = (e : ℝ) * f)
    (hs1 : sideOpp (D₀.model.relabel τ) 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (hs2 : sideOpp (D₀.model.relabel τ) 2 = (f : ℝ) ^ 2) :
    ∃ (g : Plane ≃ᵢ Plane) (D : CongruentDissection N),
      (∀ i m, (D.tile i).pts m = g ((D₀.tile i).pts m)) ∧
      ∃ F : HalfTurnR3R4Glue.HFrame D e f (modelAlpha e f) (modelBeta e f)
          (2 * modelAlpha e f + modelBeta e f),
        HalfTurnR3R4Glue.Present D F.K ∨
          Nonempty (MirrorStripR2Glue.R2Frame D e f (modelAlpha e f) (modelBeta e f)
            (2 * modelAlpha e f + modelBeta e f)) := by
  obtain ⟨g, σ, hg⟩ := hT
  let D := Erdos634.E1NormalForm.normalFormC D₀ g σ (Tri.congruent_relabel D₀.model τ)
  refine ⟨g, D, fun i m => rfl, ?_⟩
  exact split_normal D hco he hef he0 hefR
    (Erdos634.E1NormalForm.normalFormC_target D₀ hg _) hs0 hs1 hs2

end Erdos634.Draft.ApexNormal

#print axioms Erdos634.Draft.ApexNormal.modelData_of_sides
#print axioms Erdos634.Draft.ApexNormal.m1Data_normal
#print axioms Erdos634.Draft.ApexNormal.exists_hframe_normal
#print axioms Erdos634.Draft.ApexNormal.lemmaG_normal
#print axioms Erdos634.Draft.ApexNormal.split_normal
#print axioms Erdos634.Draft.ApexNormal.split_congruent

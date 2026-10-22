-- Draft/ModelWitnessE.lean — VACUITY WITNESS for the MODEL half of `ApexFrameReal.M1Data` at every
-- member `0 < e < f` (so in particular at every coprime `2 ≤ e ≤ f − 2`, e.g. `(e, f) = (2, 5)`):
-- the one-tile `CongruentDissection` of the triangle with sides `(ef, f² − e², f²)` satisfies
-- `ModelDataE` with `α = modelAlpha e f`, `β = modelBeta e f`, `γ = 2α + β` — the SAME `α, β` for which
-- the target half (`ApexWitness44.m1_target_witness`) and the angle bundle
-- (`ApexWitness44.angleData_member`) are already witnessed.  This closes the gap recorded in
-- Draft/ApexWitness44.lean ("`ModelDataE` at e ≥ 2 … not built here"): every field of `M1Data` is now
-- witnessed separately at `e ≥ 2`; jointly (one dissection of the base-β target) it is not, and cannot
-- be — that is Theorem H (`Draft/L3MReal.theorem_H_real`).  Imported by All.lean (All.lean line 437: import Erdos634.Draft.ModelWitnessE).
import Erdos634.Draft.ApexWitness44

namespace Erdos634.Draft.ModelWitnessE

open Erdos634.Geometry Erdos634.CertCoord Erdos634.BaseBetaTargetCoord Erdos634.Draft.ApexWitness44
open Erdos634.Draft.HalfTurnR3R4Glue (ModelDataE)

/-- `cos α = (2f² − e²)/(2f²)` and its sine. -/
noncomputable def cA (e f : ℝ) : ℝ := (2 * f ^ 2 - e ^ 2) / (2 * f ^ 2)
noncomputable def sA (e f : ℝ) : ℝ := Real.sqrt (1 - cA e f ^ 2)

theorem cA_facts {e f : ℝ} (he : 0 < e) (hef : e < f) : 0 < cA e f ∧ cA e f < 1 := by
  have hf : 0 < f := lt_trans he hef
  unfold cA
  constructor
  · apply div_pos _ (by positivity); nlinarith
  · rw [div_lt_one (by positivity)]; nlinarith

theorem sA_facts {e f : ℝ} (he : 0 < e) (hef : e < f) :
    0 < sA e f ∧ sA e f ^ 2 = 1 - cA e f ^ 2 := by
  obtain ⟨h0, h1⟩ := cA_facts he hef
  have hpos : 0 < 1 - cA e f ^ 2 := by nlinarith
  exact ⟨Real.sqrt_pos.mpr hpos, Real.sq_sqrt hpos.le⟩

/-- **The base-β tile** `(ef, f² − e², f²)` in coordinates: `p₀ = (0,0)`, `p₁ = (f², 0)`,
`p₂ = (f² − e²)(cos α, sin α)`. -/
noncomputable def tileTri (e f : ℝ) (he : 0 < e) (hef : e < f) : Tri :=
  mkTri 0 0 (f ^ 2) 0 ((f ^ 2 - e ^ 2) * cA e f) ((f ^ 2 - e ^ 2) * sA e f) (by
    unfold det3
    have hf : 0 < f := lt_trans he hef
    have hb : 0 < f ^ 2 - e ^ 2 := by nlinarith
    have := (sA_facts he hef).1
    have : 0 < f ^ 2 * ((f ^ 2 - e ^ 2) * sA e f) := by positivity
    intro h; nlinarith)

/-- **The one-tile dissection** of a triangle by itself. -/
noncomputable def single (T : Tri) : CongruentDissection 1 where
  target := T
  tile := fun _ => T
  covers := by
    show (⋃ _ : Fin 1, T.carrier) = T.carrier
    exact Set.iUnion_const _
  interiors_disjoint := fun i j hij => absurd (Subsingleton.elim i j) hij
  model := T
  tiles_congruent := fun _ => Tri.Congruent.refl T

theorem dist_eq_of_sq {x y : Plane} {s : ℝ} (hs : 0 ≤ s) (h : dist x y ^ 2 = s ^ 2) :
    dist x y = s := (pow_left_inj₀ dist_nonneg hs two_ne_zero).mp h

set_option maxHeartbeats 1000000 in
/-- **`ModelDataE` holds on the one-tile dissection of the base-β tile, every `0 < e < f`**, with
`α = modelAlpha e f`, `β = modelBeta e f`, `γ = 2α + β` (sides by the coordinates; `α` and `β` by the
cosine rule, `ApexWitness44.cornerAngle_eq_of_cos` with `BaseBetaTargetCoord.cos_modelAlpha`,
`cos_modelBeta`; `γ` by the angle sum `cornerAngle_sum` and `3α + 2β = π`). -/
theorem model_witness {e f : ℝ} (he : 0 < e) (hef : e < f) :
    ModelDataE (single (tileTri e f he hef)) e f (modelAlpha e f) (modelBeta e f)
      (2 * modelAlpha e f + modelBeta e f) := by
  have hf : 0 < f := lt_trans he hef
  have hb : 0 < f ^ 2 - e ^ 2 := by nlinarith
  obtain ⟨hc0, hc1⟩ := cA_facts he hef
  obtain ⟨hs0, hs2⟩ := sA_facts he hef
  set T := tileTri e f he hef with hT
  have p0 : T.pts 0 = mkPt 0 0 := rfl
  have p1 : T.pts 1 = mkPt (f ^ 2) 0 := rfl
  have p2 : T.pts 2 = mkPt ((f ^ 2 - e ^ 2) * cA e f) ((f ^ 2 - e ^ 2) * sA e f) := rfl
  have hcA : 2 * f ^ 2 * cA e f = 2 * f ^ 2 - e ^ 2 := by unfold cA; field_simp
  -- the three sides
  have d01 : dist (T.pts 0) (T.pts 1) = f ^ 2 := by
    rw [p0, p1]; apply dist_eq_of_sq (by positivity); rw [dist_sq_mkPt]; ring
  have d20 : dist (T.pts 2) (T.pts 0) = f ^ 2 - e ^ 2 := by
    rw [p2, p0]; apply dist_eq_of_sq hb.le; rw [dist_sq_mkPt]
    have : ((f ^ 2 - e ^ 2) * cA e f - 0) ^ 2 + ((f ^ 2 - e ^ 2) * sA e f - 0) ^ 2
        = (f ^ 2 - e ^ 2) ^ 2 * (cA e f ^ 2 + sA e f ^ 2) := by ring
    rw [this, hs2]; ring
  have d12 : dist (T.pts 1) (T.pts 2) = e * f := by
    rw [p1, p2]; apply dist_eq_of_sq (by positivity); rw [dist_sq_mkPt]
    have : (f ^ 2 - (f ^ 2 - e ^ 2) * cA e f) ^ 2 + (0 - (f ^ 2 - e ^ 2) * sA e f) ^ 2
        = f ^ 4 - (f ^ 2 - e ^ 2) * (2 * f ^ 2 * cA e f)
          + (f ^ 2 - e ^ 2) ^ 2 * (cA e f ^ 2 + sA e f ^ 2) := by ring
    rw [this, hs2, hcA]; ring
  -- the angles
  obtain ⟨hβ0, hβ1⟩ := modelBeta_mem he hef
  have hrel := modelAngle_rel e f
  have hα0 : 0 ≤ modelAlpha e f := by unfold modelAlpha; linarith [Real.pi_pos]
  have hαπ : modelAlpha e f ≤ Real.pi := by unfold modelAlpha; linarith [Real.pi_pos]
  have hα : cornerAngle (T.pts 1) (T.pts 0) (T.pts 2) = modelAlpha e f := by
    apply cornerAngle_eq_of_cos (a := f ^ 2) (b := f ^ 2 - e ^ 2) (d := e * f)
      (by rw [dist_comm]; exact d01) d20 d12 (by positivity) hb hα0 hαπ
    rw [cos_modelAlpha he hef]
    field_simp; ring
  have hβ : cornerAngle (T.pts 2) (T.pts 1) (T.pts 0) = modelBeta e f := by
    apply cornerAngle_eq_of_cos (a := e * f) (b := f ^ 2) (d := f ^ 2 - e ^ 2)
      (by rw [dist_comm]; exact d12) d01 d20 (by positivity) (by positivity) hβ0.le
      (by linarith [Real.pi_pos])
    rw [cos_modelBeta he hef, baseLen, Nq]
    field_simp; ring
  have hsum := cornerAngle_sum T
  refine ⟨?_, ?_, ?_, hα, hβ, ?_⟩
  · show dist (T.pts (0 + 1)) (T.pts (0 + 2)) = e * f
    exact d12
  · show dist (T.pts (1 + 1)) (T.pts (1 + 2)) = f ^ 2 - e ^ 2
    exact d20
  · show dist (T.pts (2 + 1)) (T.pts (2 + 2)) = f ^ 2
    exact d01
  · show cornerAngle (T.pts 0) (T.pts 2) (T.pts 1) = 2 * modelAlpha e f + modelBeta e f
    rw [hα, hβ] at hsum; linarith

/-- **Every field of `M1Data` is witnessed at a member of Theorem H's range**, `(e, f) = (2, 5)`
(coprime, `2 ≤ e ≤ f − 2`), with ONE pair `(α, β) = (modelAlpha 2 5, modelBeta 2 5)`: the model half
on the one-tile dissection of the tile `(10, 21, 25)`, the angle bundle, and the target half on the
coordinate target `baseBetaTarget 2 5` (legs `125`, base `2·71 = 142`, apex `3α`). -/
theorem m1_fields_witness_2_5 :
    Nat.Coprime 2 5 ∧ 2 ≤ 2 ∧ 2 + 2 ≤ 5 ∧
    ModelDataE (single (tileTri 2 5 (by norm_num) (by norm_num))) ((2 : ℕ) : ℝ) ((5 : ℕ) : ℝ)
      (modelAlpha ((2 : ℕ) : ℝ) ((5 : ℕ) : ℝ)) (modelBeta ((2 : ℕ) : ℝ) ((5 : ℕ) : ℝ))
      (2 * modelAlpha ((2 : ℕ) : ℝ) ((5 : ℕ) : ℝ) + modelBeta ((2 : ℕ) : ℝ) ((5 : ℕ) : ℝ)) ∧
    MarchSlots.AngleData (modelAlpha ((2 : ℕ) : ℝ) ((5 : ℕ) : ℝ)) (modelBeta ((2 : ℕ) : ℝ) ((5 : ℕ) : ℝ))
      (2 * modelAlpha ((2 : ℕ) : ℝ) ((5 : ℕ) : ℝ) + modelBeta ((2 : ℕ) : ℝ) ((5 : ℕ) : ℝ)) := by
  refine ⟨by norm_num, le_rfl, by norm_num, ?_, angleData_member 2 5 (by norm_num) (by norm_num)⟩
  have := model_witness (e := ((2 : ℕ) : ℝ)) (f := ((5 : ℕ) : ℝ)) (by norm_num) (by norm_num)
  convert this using 2

end Erdos634.Draft.ModelWitnessE

#print axioms Erdos634.Draft.ModelWitnessE.model_witness
#print axioms Erdos634.Draft.ModelWitnessE.m1_fields_witness_2_5
